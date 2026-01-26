module Test.ParserTests

import Frontend.AST
import Frontend.Lexer
import Frontend.Parser
import Frontend.Token
import Text.Bounds

%default total

sampleProgram : String
sampleProgram =
  """
fn main() {
  let q0: Qubit = qalloc();
  let q1: Qubit = qalloc();

  ctrl(q0) H(q1);
  CX(q0, q1);

  let (b0, q0) = measr(q0);
  if b0 { X(q0); }

  q0
}
"""

testParseSample : IO ()
testParseSample =
  case lexQuantum sampleProgram of
    Left err => putStrLn $ "Lexer error: " ++ show err
    Right tokens =>
      case parseProgramAll tokens of
        Left err => putStrLn $ "Parse error: " ++ show err
        Right program => putStrLn $ "Parsed program: " ++ show program

main : IO ()
main = do
  testParseSample