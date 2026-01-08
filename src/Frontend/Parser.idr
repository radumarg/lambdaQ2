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



