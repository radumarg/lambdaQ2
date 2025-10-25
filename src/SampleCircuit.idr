
module SampleCircuit

import Data.Fin
import Quantum.Circuit
import Quantum.Core
import Quantum.Gates
import Quantum.GateHelpers
import Quantum.Helpers

public export
build : Circuit 5 5
build = c13
  where
    -- choose wires
    q0 = fromLiteral {n = 5} 0
    q1 = fromLiteral {n = 5} 1
    q2 = fromLiteral {n = 5} 2
    q3 = fromLiteral {n = 5} 3
    q4 = fromLiteral {n = 5} 4

    -- start empty
    c0  = emptyCircuit {n = 5}

    -- 1-qubit gates
    c1  = hadamard q0 c0
    c2  = s q1 c1
    c3  = rotY (MkRad 1.234) q2 c2

    -- 2-qubit, controlled rotations, and interactions
    c4  = case mkNeq q0 q1 of
      Just neq => cnot q0 q1 {neq = neq} c3
      Nothing  => c3  -- fallback (should be unreachable)
    c5  = case mkNeq q1 q2 of
      Just neq => ctrlRZ (MkRad 0.25) q1 q2 {neq = neq} c4
      Nothing  => c4  -- fallback (should be unreachable)
    c6  = case mkNeq q2 q3 of
      Just neq => rzx (MkRad 0.5) q2 q3 {neq = neq} c5
      Nothing  => c5  -- fallback (should be unreachable)
    c7  = case mkNeq q3 q4 of
      Just neq => swap q3 q4 {neq = neq} c6
      Nothing  => c6  -- fallback (should be unreachable)
    c8  = u3 (MkRad 0.7) (MkRad 0.1) (MkRad 0.2) q4 c7
    c9  = case mkNeq q0 q4 of
      Just neq => ctrlSX q0 q4 {neq = neq} c8
      Nothing  => c8  -- fallback (should be unreachable)

    -- measurement & reset (non-unitaries)
    c10 = measr q0 c9 
    c11 = reset q3 c10 

    -- continue with unitary ops on unmeasured lines
    c12 = case mkNeq q1 q2 of
      Just neq => rzz (MkRad 0.33) q1 q2 {neq = neq} c11
      Nothing  => c11  -- fallback (should be unreachable)
    c13 = tDag q2 c12
