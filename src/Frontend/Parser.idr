module Frontend.Parser

import Derive.Prelude
import Language.Reflection

import Frontend.AST
import Frontend.Token

-- idris2-parser manual tooling for span tracking:
-- Position, begin, next, Bounded, bounded, ...
import Text.Parse.Manual

%default total
%language ElabReflection

--------------------------------------------------------------------------------
-- Parser errors (kept small and explicit).
-- We wrap errors in `Bounded` so we can attach the source span of the token that
-- caused the error.
--------------------------------------------------------------------------------
public export
data ParseErr
  = ParseUnexpectedEOF
  | ParseUnexpectedToken Token
  | ParseExpected String
  | ParseFuelExhausted String

%runElab derive "ParseErr" [Show, Eq]

outOfFuelErr : List (Bounded Token) -> Bounded ParseErr
outOfFuelErr tokens =
  let err = ParseFuelExhausted "parser fuel exhausted" in
  case tokens of
    [] => bounded err begin begin
    (B _ tokBounds) :: _ => B err tokBounds

--------------------------------------------------------------------------------
-- Parser type:
--   a parser consumes a list of (Bounded Token) and either:
--     * returns an error with source span, OR
--     * returns a value + remaining tokens
--------------------------------------------------------------------------------
public export
Parser : Type -> Type
Parser a = List (Bounded Token) -> Either (Bounded ParseErr) (a, List (Bounded Token))

--------------------------------------------------------------------------------
-- Basic token stream helpers.
--------------------------------------------------------------------------------

-- Look at the next token without consuming it.
peekToken : List (Bounded Token) -> Maybe Token
peekToken [] = Nothing
peekToken (B tok _ :: _) = Just tok

-- Consume exactly one token and return it.
popToken : Parser Token
popToken [] = Left (bounded ParseUnexpectedEOF begin begin)
popToken (B tok _ :: remainingTokens) = Right (tok, remainingTokens)

-- Produce an error located at the next token if possible; otherwise at begin..begin.
failAtHead : ParseErr -> List (Bounded Token) -> Either (Bounded ParseErr) a
failAtHead parseErr [] = Left (bounded parseErr begin begin)
failAtHead parseErr (B _ tokenBounds :: _) = Left (B parseErr tokenBounds)

--------------------------------------------------------------------------------
-- “expect” / “accept” helpers.
-- - expectX: must match, otherwise error
-- - acceptX: optionally consume if matches, otherwise do nothing
--------------------------------------------------------------------------------

expectSymbol : Symbol -> Parser ()
expectSymbol expectedSymbol tokens =
  case tokens of
    (B (TokSym sym) symBounds :: rest) =>
      if sym == expectedSymbol
         then Right ((), rest)
         else Left (B (ParseExpected ("symbol " ++ show expectedSymbol)) symBounds)
    _ => failAtHead (ParseExpected ("symbol " ++ show expectedSymbol)) tokens

acceptSymbol : Symbol -> Parser Bool
acceptSymbol expectedSymbol tokens =
  case tokens of
    (B (TokSym sym) _ :: rest) =>
      if sym == expectedSymbol
         then Right (True, rest)
         else Right (False, tokens)
    _ => Right (False, tokens)

expectKeyword : Keyword -> Parser ()
expectKeyword expectedKeyword tokens =
  case tokens of
    (B (TokKw kw) kwBounds :: rest) =>
      if kw == expectedKeyword
         then Right ((), rest)
         else Left (B (ParseExpected ("keyword " ++ show expectedKeyword)) kwBounds)
    _ => failAtHead (ParseExpected ("keyword " ++ show expectedKeyword)) tokens

acceptKeyword : Keyword -> Parser Bool
acceptKeyword expectedKeyword tokens =
  case tokens of
    (B (TokKw kw) _ :: rest) =>
      if kw == expectedKeyword
         then Right (True, rest)
         else Right (False, tokens)
    _ => Right (False, tokens)

expectIdentName : Parser String
expectIdentName tokens =
  case tokens of
    (B (TokIdent identName) _ :: rest) => Right (identName, rest)
    _ => failAtHead (ParseExpected "identifier") tokens

--------------------------------------------------------------------------------
-- Small number helpers.
-- We keep integers/floats as RAW STRINGS in Literal, but we occasionally need a Nat:
--   * tuple indexing: t.0, t.1
--   * array repeat count: [0; 8] uses Nat in the AST
--   * size expressions: QReg[8] uses Nat in SizeExpr
--------------------------------------------------------------------------------

digitToNat : Char -> Maybe Nat
digitToNat c =
  if isDigit c then Just (cast (ord c - ord '0')) else Nothing

digitsToNat : String -> Maybe Nat
digitsToNat rawDigits =
  let chars = unpack rawDigits in
  case chars of
    [] => Nothing
    _  =>
      foldl
        (\acc, ch =>
            case acc of
              Nothing => Nothing
              Just n =>
                case digitToNat ch of
                  Nothing => Nothing
                  Just d  => Just (n * 10 + d)
        )
        (Just 0)
        chars

--------------------------------------------------------------------------------
-- Comma-separated list helper until a closing symbol.
-- Supports:
--   - empty list: ()
--   - trailing comma: (a, b, )
--------------------------------------------------------------------------------
mutual
  parseCommaSep0Until : (fuel : Nat) -> (closingSymbol : Symbol) -> Parser a -> Parser (List a)
  parseCommaSep0Until Z closingSymbol parseOne tokens =
    Left (outOfFuelErr tokens)

  parseCommaSep0Until (S fuel) closingSymbol parseOne tokens =
    case peekToken tokens of
      Just (TokSym s) =>
        if s == closingSymbol
          then Right ([], tokens)
          else parseCommaSep1Until fuel closingSymbol parseOne tokens
      _ =>
        parseCommaSep1Until fuel closingSymbol parseOne tokens

  parseCommaSep1Until : (fuel : Nat) -> (closingSymbol : Symbol) -> Parser a -> Parser (List a)
  parseCommaSep1Until Z closingSymbol parseOne tokens =
    Left (outOfFuelErr tokens)

  parseCommaSep1Until (S fuel) closingSymbol parseOne tokens =
    case parseOne tokens of
      Left err => Left err
      Right (firstValue, tokensAfterFirst) => go fuel [firstValue] tokensAfterFirst
    where
      go : (fuelGo : Nat)
        -> List a
        -> List (Bounded Token)
        -> Either (Bounded ParseErr) (List a, List (Bounded Token))
      go Z accumulatedValues currentTokens =
        Left (outOfFuelErr currentTokens)

      go (S fuelGo) accumulatedValues currentTokens =
        case peekToken currentTokens of
          Just (TokSym SymComma) =>
            case expectSymbol SymComma currentTokens of
              Left err => Left err
              Right ((), tokensAfterComma) =>
                -- Allow trailing comma: if next token is closing, stop.
                case peekToken tokensAfterComma of
                  Just (TokSym s) =>
                    if s == closingSymbol
                      then Right (accumulatedValues, tokensAfterComma)
                      else
                        case parseOne tokensAfterComma of
                          Left err => Left err
                          Right (nextValue, tokensAfterNext) =>
                            go fuelGo (accumulatedValues ++ [nextValue]) tokensAfterNext
                  _ =>
                    case parseOne tokensAfterComma of
                      Left err => Left err
                      Right (nextValue, tokensAfterNext) =>
                        go fuelGo (accumulatedValues ++ [nextValue]) tokensAfterNext
          _ =>
            Right (accumulatedValues, currentTokens)

--------------------------------------------------------------------------------
-- SIZE EXPRESSIONS (for symbolic `n` in types)
--   SizeExpr ::= Nat | Ident
-- Examples:
--   QReg[8]  => SizeNat 8
--   QReg[n]  => SizeVar "n"
--------------------------------------------------------------------------------
parseSizeExpr : Parser SizeExpr
parseSizeExpr tokens =
  case tokens of
    (B (TokIntLitRaw rawDigits) rawBounds :: rest) =>
      case digitsToNat rawDigits of
        Just n  => Right (SizeNat n, rest)
        Nothing => Left (B (ParseExpected "natural number for size (digits only)") rawBounds)

    (B (TokIdent name) _ :: rest) =>
      Right (SizeVar name, rest)

    _ =>
      failAtHead (ParseExpected "size expression (Nat literal or identifier)") tokens

--------------------------------------------------------------------------------
-- TYPE PARSING
--
-- TypExpr in your AST:
--   TypUnit
--   TypPrim TypPrimName
--   TypReg TypRegName (Maybe SizeExpr)
--   TypTuple (List TypExpr)
--   TypArrayFixed TypExpr SizeExpr
--
-- We implement internal "fuel" so the parser remains total even with recursion.
--------------------------------------------------------------------------------

mutual
  -- Internal fuel for type parsing (bounded by token length).
  -- If this hits 0, it means the input is pathological or our grammar is looping.
  public export
  parseTypExpr : Parser TypExpr
  parseTypExpr tokens =
    let typFuel : Nat = 2 * length tokens + 16 in
    parseTypExprFuel typFuel tokens

  parseTypExprFuel : Nat -> Parser TypExpr
  parseTypExprFuel Z tokens =
    failAtHead (ParseFuelExhausted "type expression") tokens

  parseTypExprFuel (S remainingFuel) tokens =
    case peekToken tokens of
      -- Parentheses: either unit type `()` or tuple type `(T1, T2, ...)`
      Just (TokSym SymLParen) =>
        case expectSymbol SymLParen tokens of
          Left err => Left err
          Right ((), tokens1) =>
            case peekToken tokens1 of
              -- Unit: ()
              Just (TokSym SymRParen) =>
                case expectSymbol SymRParen tokens1 of
                  Left err => Left err
                  Right ((), tokens2) => Right (TypUnit, tokens2)

              -- Otherwise parse first type, then decide tuple vs grouping
              _ =>
                case parseTypExprFuel remainingFuel tokens1 of
                  Left err => Left err
                  Right (firstTypExpr, tokens2) =>
                    case peekToken tokens2 of
                      -- Tuple type requires a comma
                      Just (TokSym SymComma) =>
                        case expectSymbol SymComma tokens2 of
                          Left err => Left err
                          Right ((), tokens3) =>
                            case parseCommaSep0Until remainingFuel SymRParen (parseTypExprFuel remainingFuel) tokens3 of
                              Left err => Left err
                              Right (moreTypes, tokens4) =>
                                case expectSymbol SymRParen tokens4 of
                                  Left err => Left err
                                  Right ((), tokens5) =>
                                    Right (TypTuple (firstTypExpr :: moreTypes), tokens5)

                      -- Grouping: (T) -> T
                      _ =>
                        case expectSymbol SymRParen tokens2 of
                          Left err => Left err
                          Right ((), tokens3) => Right (firstTypExpr, tokens3)

      -- Fixed array type: [T; n]
      Just (TokSym SymLBracket) =>
        parseTypArrayFixedFuel remainingFuel tokens

      -- Primitive type keyword token (already classified by lexer)
      Just (TokTypPrim typPrimName) =>
        case popToken tokens of
          Left err => Left err
          Right (_, remainingTokens) =>
            Right (TypPrim typPrimName, remainingTokens)

      -- Register type keyword token (already classified by lexer)
      -- Supports optional sizing: QReg[n], BReg[8]
      Just (TokTypReg typRegName) =>
        case popToken tokens of
          Left err => Left err
          Right (_, tokensAfterReg) =>
            case acceptSymbol SymLBracket tokensAfterReg of
              Left err => Left err
              Right (False, tokensNoBracket) =>
                Right (TypReg typRegName Nothing, tokensNoBracket)

              Right (True, tokensAfterLBracket) =>
                case parseSizeExpr tokensAfterLBracket of
                  Left err => Left err
                  Right (sizeExpr, tokensAfterSize) =>
                    case expectSymbol SymRBracket tokensAfterSize of
                      Left err => Left err
                      Right ((), tokensAfterRBracket) =>
                        Right (TypReg typRegName (Just sizeExpr), tokensAfterRBracket)

      _ =>
        failAtHead (ParseExpected "type expression") tokens

  --------------------------------------------------------------------------------
  -- Updated parseTypArrayFixed (as requested): [T; n] with SizeExpr
  --------------------------------------------------------------------------------
  public export
  parseTypArrayFixed : Parser TypExpr
  parseTypArrayFixed tokens =
    let typFuel : Nat = 2 * length tokens + 16 in
    parseTypArrayFixedFuel typFuel tokens

  parseTypArrayFixedFuel : Nat -> Parser TypExpr
  parseTypArrayFixedFuel Z tokens =
    failAtHead (ParseFuelExhausted "array type") tokens

  parseTypArrayFixedFuel (S remainingFuel) tokens =
    case expectSymbol SymLBracket tokens of
      Left err => Left err
      Right ((), tokens1) =>
        case parseTypExprFuel remainingFuel tokens1 of
          Left err => Left err
          Right (elementTypeExpr, tokens2) =>
            case expectSymbol SymSemi tokens2 of
              Left err => Left err
              Right ((), tokens3) =>
                case parseSizeExpr tokens3 of
                  Left err => Left err
                  Right (lengthSizeExpr, tokens4) =>
                    case expectSymbol SymRBracket tokens4 of
                      Left err => Left err
                      Right ((), tokens5) =>
                        Right (TypArrayFixed elementTypeExpr lengthSizeExpr, tokens5)

--------------------------------------------------------------------------------
-- LITERAL PARSING
--------------------------------------------------------------------------------
parseLiteral : Parser Literal
parseLiteral tokens =
  case tokens of
    (B (TokIntLitRaw rawInt) _ :: rest) =>
      Right (LitIntRaw rawInt, rest)

    (B (TokFloatLitRaw rawFloat) _ :: rest) =>
      Right (LitFloatRaw rawFloat, rest)

    (B (TokStringLit rawString) _ :: rest) =>
      Right (LitString rawString, rest)

    (B (TokKw KwTrue) _ :: rest) =>
      Right (LitBool True, rest)

    (B (TokKw KwFalse) _ :: rest) =>
      Right (LitBool False, rest)

    -- Unit literal: ()
    (B (TokSym SymLParen) _ :: _) =>
      case expectSymbol SymLParen tokens of
        Left err => Left err
        Right ((), tokens1) =>
          case expectSymbol SymRParen tokens1 of
            Left err => Left err
            Right ((), tokens2) =>
              Right (LitUnit, tokens2)

    _ =>
      failAtHead (ParseExpected "literal") tokens

--------------------------------------------------------------------------------
-- PATTERN PARSING (let bindings + match arms)
--------------------------------------------------------------------------------
parsePatternFuel : Nat -> Parser Pattern
parsePatternFuel Z tokens =
  -- If you have a better error constructor, use it; this keeps things simple.
  failAtHead (ParseExpected "pattern (out of fuel)") tokens

parsePatternFuel (S fuel) tokens =
  case tokens of
    -- Wildcard: _
    (B TokUnderscore _ :: rest) =>
      Right (PatWildcard, rest)

    -- Variable: x
    (B (TokIdent name) _ :: rest) =>
      Right (PatVarName name, rest)

    -- Literal patterns
    (B (TokIntLitRaw _) _ :: _) =>
      case parseLiteral tokens of
        Left err => Left err
        Right (lit, rest) => Right (PatLit lit, rest)

    (B (TokFloatLitRaw _) _ :: _) =>
      case parseLiteral tokens of
        Left err => Left err
        Right (lit, rest) => Right (PatLit lit, rest)

    (B (TokStringLit _) _ :: _) =>
      case parseLiteral tokens of
        Left err => Left err
        Right (lit, rest) => Right (PatLit lit, rest)

    (B (TokKw KwTrue) _ :: _) =>
      case parseLiteral tokens of
        Left err => Left err
        Right (lit, rest) => Right (PatLit lit, rest)

    (B (TokKw KwFalse) _ :: _) =>
      case parseLiteral tokens of
        Left err => Left err
        Right (lit, rest) => Right (PatLit lit, rest)

    -- Tuple pattern or unit: (...) / ()
    (B (TokSym SymLParen) _ :: _) =>
      case expectSymbol SymLParen tokens of
        Left err => Left err
        Right ((), tokens1) =>
          case peekToken tokens1 of
            Just (TokSym SymRParen) =>
              case expectSymbol SymRParen tokens1 of
                Left err => Left err
                Right ((), tokens2) => Right (PatUnit, tokens2)

            _ =>
              case parsePatternFuel fuel tokens1 of
                Left err => Left err
                Right (firstPat, tokens2) =>
                  case peekToken tokens2 of
                    Just (TokSym SymComma) =>
                      case expectSymbol SymComma tokens2 of
                        Left err => Left err
                        Right ((), tokens3) =>
                          -- Fuel for the comma-separated tail list.
                          let commaFuel : Nat = 2 * length tokens3 + 16 in
                          case parseCommaSep0Until commaFuel SymRParen (parsePatternFuel fuel) tokens3 of
                            Left err => Left err
                            Right (morePats, tokens4) =>
                              case expectSymbol SymRParen tokens4 of
                                Left err => Left err
                                Right ((), tokens5) =>
                                  Right (PatTuple (firstPat :: morePats), tokens5)

                    _ =>
                      -- Grouping parentheses for patterns: (x) -> x
                      case expectSymbol SymRParen tokens2 of
                        Left err => Left err
                        Right ((), tokens3) => Right (firstPat, tokens3)

    _ =>
      failAtHead (ParseExpected "pattern") tokens

parsePattern : Parser Pattern
parsePattern tokens =
  -- Big enough to cover recursive descent over the remaining input
  let patternFuel : Nat = 2 * length tokens + 16 in
  parsePatternFuel patternFuel tokens

--------------------------------------------------------------------------------
-- OPERATOR TABLES (BinaryOp + precedence)
--------------------------------------------------------------------------------
binaryOpFromSymbol : Symbol -> Maybe BinaryOp
binaryOpFromSymbol sym =
  case sym of
    SymPlus    => Just OpAdd
    SymMinus   => Just OpSub
    SymStar    => Just OpMul
    SymSlash   => Just OpDiv
    SymPercent => Just OpRem

    SymLt      => Just OpLt
    SymLe      => Just OpLe
    SymGt      => Just OpGt
    SymGe      => Just OpGe

    SymEqEq    => Just OpEqEq
    SymNotEq   => Just OpNotEq

    SymAndAnd  => Just OpAndAnd
    SymOrOr    => Just OpOrOr

    SymPipe    => Just OpBitOr
    SymCaret   => Just OpBitXor

    SymDotDot   => Just OpRangeExcl
    SymDotDotEq => Just OpRangeIncl

    _ => Nothing

binaryPrecedence : BinaryOp -> Nat
binaryPrecedence op =
  case op of
    OpRangeExcl => 1
    OpRangeIncl => 1

    OpOrOr      => 2
    OpAndAnd    => 3

    OpBitOr     => 4
    OpBitXor    => 5

    OpEqEq      => 6
    OpNotEq     => 6

    OpLt        => 7
    OpLe        => 7
    OpGt        => 7
    OpGe        => 7

    OpAdd       => 8
    OpSub       => 8

    OpMul       => 9
    OpDiv       => 9
    OpRem       => 9

