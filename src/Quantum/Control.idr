module Quantum.Control

import Data.Vect
import Data.Fin
import Data.Nat
import Decidable.Equality

%default total

-- public export
-- data NotElem : (x : a) -> Vect n a -> Type where
--   NotHere  : NotElem x []
--   NotThere : (NotElem x xs) -> NotElem x (y :: xs)

-- public export
-- data AllDistinct : Vect n a -> Type where
--   ADNil  : AllDistinct []
--   ADCons : {xs : Vect n a} ->
--            NotElem x xs ->
--            AllDistinct xs ->
--            AllDistinct (x :: xs)

-- public export
-- Disjoint : Vect m a -> Vect n a -> Type
-- Disjoint xs ys = (All (\x => NotElem x ys) xs)