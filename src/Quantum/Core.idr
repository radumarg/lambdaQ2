module Quantum.Core

%default total

public export
record Radians where
  constructor MkRad
  val : Double

-- public export
-- Qubit : Type
-- Qubit = Nat     -- wire label/index

-- public export
-- record Complex where
--   constructor MkComplex
--   re, im : Double

-- public export
-- data QubitState
--   = Zero
--   | One
--   | Superposition Complex Complex  -- amplitudes α, β
