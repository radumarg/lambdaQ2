module Quantum.Helpers

import Data.Fin
import Data.Nat
import Decidable.Equality

%default total

public export
finFromLiteral : {n : Nat} -> (k : Nat) -> {auto 0 lt : LT k n} -> Fin n
finFromLiteral {n = S _} Z     = FZ
finFromLiteral {n = S n'} (S k) {lt = LTESucc ltk} = FS (finFromLiteral {n = n'} k {lt = ltk})

public export
mkNeq : {n : Nat} -> (i, j : Fin n) -> Maybe (Not (i = j))
mkNeq i j = case decEq i j of
  Yes Refl   => Nothing
  No contra  => Just contra