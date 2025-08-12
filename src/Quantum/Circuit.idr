module Quantum.Circuit

import Quantum.Gates

%default total

-- Quantum circuits with n inputs and m outputs
public export
data Circuit : Nat -> Nat -> Type where
  -- Identity / “empty” circuit
  Id  : Circuit n n

  -- A single primitive gate
  GateApplication : Gate n -> Circuit n n

  -- Sequential composition
  Seq : Circuit n m -> Circuit m k -> Circuit n k

  -- Parallel composition
  Par : Circuit n1 m1 -> Circuit n2 m2 -> Circuit (n1 + n2) (m1 + m2)