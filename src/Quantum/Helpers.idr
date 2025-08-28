module Quantum.Helpers

import Data.Fin
import Data.Nat

%default total

public export
finFromLiteral : {n : Nat} -> (i : Nat) -> {auto prf : LT i n} -> Fin n
-- LT i 0 is impossible
finFromLiteral {n=Z}   _ {prf} impossible
finFromLiteral {n=S k} i {prf} =
  case natToFin i (S k) of
    Just f  => f
    -- unreachable, but required for totality
    Nothing => FZ
