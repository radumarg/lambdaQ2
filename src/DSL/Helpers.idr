module DSL.Helpers

import Data.Fin
import Data.Nat
import Decidable.Equality

%default total

public export
fromLiteral : {n : Nat} -> (k : Nat) -> {auto 0 lt : LT k n} -> Fin n
fromLiteral {n = S _} Z     = FZ
fromLiteral {n = S n'} (S k) {lt = LTESucc ltk} = FS (fromLiteral {n = n'} k {lt = ltk})

public export
mkNeq : {n : Nat} -> (i, j : Fin n) -> Maybe (Not (i = j))
mkNeq i j = case decEq i j of
  Yes Refl   => Nothing
  No contra  => Just contra