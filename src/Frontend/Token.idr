module Frontend.Token

import Derive.Prelude
import Language.Reflection

import Frontend.AST

%default total
%language ElabReflection

----------------------------------------------------------------------
-- Token is the output of lexing.
-- The lexer converts raw source text into a list of (Bounded Token).
-- "Bounded" comes from idris2-parser and attaches source span info.
----------------------------------------------------------------------

------------------------------------------------
-- Keywords: reserved words that affect syntax.
------------------------------------------------
public export
data Keyword
  = KwAs | KwBreak | KwCtrl | KwContinue | KwElse | KwFalse
  | KwFn | KwFor | KwIf | KwIn | KwLet | KwLoop
  | KwMatch | KwMeasr | KwNegCtrl | KwQAlloc | KwReset
  | KwReturn | KwTrue | KwWhile

---------------------------------------
-- Symbols: punctuation and operators.
----------------------------------------
public export
data Symbol
  = SymQuestion             -- ?
  | SymAmp                  -- &   (reserved; && exists too)
  | SymLParen | SymRParen   -- ( )
  | SymLBracket | SymRBracket -- [ ]
  | SymLBrace | SymRBrace   -- { }
  | SymComma | SymSemi | SymColon
  | SymDot                  -- .
  | SymBang                 -- !
  | SymEq                   -- =
  | SymPlus | SymMinus | SymStar | SymSlash | SymPercent
  | SymPlusEq | SymMinusEq | SymStarEq | SymSlashEq | SymPercentEq
  | SymGt | SymGe | SymLt | SymLe
  | SymEqEq | SymNotEq
  | SymAndAnd | SymOrOr
  | SymDotDot | SymDotDotEq -- .. and ..=
  | SymDoubleColon          -- ::
  | SymPipe | SymCaret      -- | and ^
  | SymArrow                -- ->
  | SymFatArrow             -- =>  (match arm separator)

------------------------------
-- Token:
--   TokIdent "x"
--   TokIntLitRaw "123"
--   TokFloatLitRaw "3.14"
--   TokStringLit "Hello"
--   TokKw KwLet
--   TokTypPrim TypPrimInt
--   TokTypReg TypRegQReg
--   TokGate GateH
--   TokSym SymPlusEq
--   TokUnderscore
-------------------------------
public export
data Token
  = TokIdent       String
  | TokIntLitRaw   String
  | TokFloatLitRaw String
  | TokStringLit   String
  | TokKw          Keyword
  | TokTypPrim     TypPrimName
  | TokTypReg      TypRegName
  | TokGate        GateName
  | TokSym         Symbol
  | TokUnderscore

-------------------------------------------------------------
-- Mappings used by lexer: identifier text -> token category
-------------------------------------------------------------
public export
keywordFromString : String -> Maybe Keyword
keywordFromString s =
  case s of
    "as"       => Just KwAs
    "break"    => Just KwBreak
    "ctrl"     => Just KwCtrl
    "continue" => Just KwContinue
    "else"     => Just KwElse
    "false"    => Just KwFalse
    "fn"       => Just KwFn
    "for"      => Just KwFor
    "if"       => Just KwIf
    "in"       => Just KwIn
    "let"      => Just KwLet
    "loop"     => Just KwLoop
    "match"    => Just KwMatch
    "measr"    => Just KwMeasr
    "negctrl"  => Just KwNegCtrl
    "qalloc"   => Just KwQAlloc
    "reset"    => Just KwReset
    "return"   => Just KwReturn
    "true"     => Just KwTrue
    "while"    => Just KwWhile
    _          => Nothing

public export
typeFromString : String -> Maybe (Either TypPrimName TypRegName)
typeFromString s =
  case s of
    "angle" => Just (Left TypPrimAngle)
    "Bit"   => Just (Left TypPrimBit)
    "bool"  => Just (Left TypPrimBool)
    "float" => Just (Left TypPrimFloat)
    "int"   => Just (Left TypPrimInt)
    "uint"  => Just (Left TypPrimUInt)
    "Qubit" => Just (Left TypPrimQubit)
    "QReg"  => Just (Right TypRegQReg)
    "BReg"  => Just (Right TypRegBReg)
    _       => Nothing

public export
gateFromString : String -> Maybe GateName
gateFromString s =
  case s of
    "Id"    => Just GateId
    "X"     => Just GateX
    "Y"     => Just GateY
    "Z"     => Just GateZ
    "H"     => Just GateH
    "S"     => Just GateS
    "SDG"   => Just GateSDG
    "T"     => Just GateT
    "TDG"   => Just GateTDG
    "SX"    => Just GateSX
    "SXDG"  => Just GateSXDG
    "RX"    => Just GateRX
    "RY"    => Just GateRY
    "RZ"    => Just GateRZ
    "U1"    => Just GateU1
    "U2"    => Just GateU2
    "U3"    => Just GateU3
    "CNOT"  => Just GateCNOT
    "CX"    => Just GateCX
    "CY"    => Just GateCY
    "CZ"    => Just GateCZ
    "CS"    => Just GateCS
    "CSDG"  => Just GateCSDG
    "CT"    => Just GateCT
    "CTDG"  => Just GateCTDG
    "CSX"   => Just GateCSX
    "CSXDG" => Just GateCSXDG
    "CRX"   => Just GateCRX
    "CRY"   => Just GateCRY
    "CRZ"   => Just GateCRZ
    "CU1"   => Just GateCU1
    "CU2"   => Just GateCU2
    "CU3"   => Just GateCU3
    "SWAP"  => Just GateSWAP
    "RXX"   => Just GateRXX
    "RYY"   => Just GateRYY
    "RZZ"   => Just GateRZZ
    "CCX"   => Just GateCCX
    "CSWAP" => Just GateCSWAP
    "GPI"   => Just GateGPI
    "GPI2"  => Just GateGPI2
    "MS"    => Just GateMS
    _       => Nothing

----------------------------------------
-- Derivations for debugging/testing
----------------------------------------
%runElab derive "Keyword" [Show, Eq]
%runElab derive "Symbol" [Show, Eq]
%runElab derive "Token" [Show, Eq]