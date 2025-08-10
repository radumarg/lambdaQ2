module Quantum.Core

import Data.Vect
import Quantum.Gates

%default total

public export
Qubit : Type
Qubit = Nat     -- a wire label/index

public export
record Complex where
  constructor MkComplex
  re, im : Double

public export
data QubitState
  = Zero
  | One
  | Superposition Complex Complex  -- amplitudes α, β

-- a product-state register (cannot represent entanglement)
public export
Register : (n : Nat) -> Type
Register n = Vect n QubitState

-- Quantum circuits with n inputs and m outputs
public export
data Circuit : Nat -> Nat -> Type where
  -- Identity / “empty” circuit
  Id  : Circuit n n

  -- -- A single primitive gate
  -- GateStep : Gate n m -> Circuit n m

  -- Sequential composition
  Seq : Circuit n m -> Circuit m k -> Circuit n k

  -- Parallel composition
  Par : Circuit n1 m1 -> Circuit n2 m2 -> Circuit (n1 + n2) (m1 + m2)