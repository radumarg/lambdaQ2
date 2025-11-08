module Quantum.Gates

import Data.Fin
import Data.Vect
import Quantum.Core
import Quantum.Control

%default total

public export
data UnitaryGate : Nat -> Type where
  -- 1-qubit (Clifford + T and friends)
  Id    : (q : Fin n) -> UnitaryGate n
  X     : (q : Fin n) -> UnitaryGate n
  Y     : (q : Fin n) -> UnitaryGate n
  Z     : (q : Fin n) -> UnitaryGate n
  H     : (q : Fin n) -> UnitaryGate n
  S     : (q : Fin n) -> UnitaryGate n
  SDG   : (q : Fin n) -> UnitaryGate n
  T     : (q : Fin n) -> UnitaryGate n
  TDG   : (q : Fin n) -> UnitaryGate n
  SX    : (q : Fin n) -> UnitaryGate n
  SXDG  : (q : Fin n) -> UnitaryGate n

  -- Parametric 1-qubit rotations
  RX    : Radians -> (q : Fin n) -> UnitaryGate n
  RY    : Radians -> (q : Fin n) -> UnitaryGate n
  RZ    : Radians -> (q : Fin n) -> UnitaryGate n

  -- OpenQASM 2 primitives / U-family
  U     : Radians -> Radians -> Radians -> (q : Fin n) -> UnitaryGate n      -- U(θ, φ, λ)
  U1    : Radians -> (q : Fin n) -> UnitaryGate n                            -- U1(λ)   == U(0, 0, λ)
  U2    : Radians -> Radians -> (q : Fin n) -> UnitaryGate n                 -- U2(φ,λ) == U(π/2, φ, λ)
  U3    : Radians -> Radians -> Radians -> (q : Fin n) -> UnitaryGate n      -- U3(θ,φ,λ) == U(θ, φ, λ)

-- 2-qubit (with a proof that control ≠ target)
  CNOT : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
  CY    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
  CZ    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
  CH    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
  CS    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
  CSDG  : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
  CT    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
  CTDG  : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
  CSX   : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
  CSXDG : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n

  CRX   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
  CRY   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
  CRZ   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
  CU1   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
  CU2   : Radians -> Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
  CU3   : Radians -> Radians -> Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n

  SWAP  : (a,b : Fin n) -> {auto 0 neq : Not (a = b)} -> UnitaryGate n
  RXX   : Radians -> (a,b : Fin n) -> {auto 0 neq : Not (a = b)} -> UnitaryGate n
  RYY   : Radians -> (a,b : Fin n) -> {auto 0 neq : Not (a = b)} -> UnitaryGate n
  RZZ   : Radians -> (a,b : Fin n) -> {auto 0 neq : Not (a = b)} -> UnitaryGate n
  RZX   : Radians -> (a,b : Fin n) -> {auto 0 neq : Not (a = b)} -> UnitaryGate n

  -- 3-qubit (all distinct)
  CCX   : (c1,c2,t : Fin n)
        -> {auto 0 d12 : Not (c1 = c2)}
        -> {auto 0 d1t : Not (c1 = t)}
        -> {auto 0 d2t : Not (c2 = t)}
        -> UnitaryGate n
  CSWAP : (c,a,b : Fin n)
        -> {auto 0 cab : Not (a = b)}
        -> {auto 0 ca  : Not (c = a)}
        -> {auto 0 cb  : Not (c = b)}
        -> UnitaryGate n

  -- Generic controlled wrapper:
  --   cs = control wires,
  --   bs = their required polarities (True = |1>, False = |0>)
  --   inner = the original gate
  Controlled :
    {k : Nat} ->
    (cs : Vect k (Fin n)) ->
    (bs : Vect k Bool) -> 
    (inner : UnitaryGate n) ->
    {auto _ : AllDistinct cs} ->
    UnitaryGate n

public export
CX : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> UnitaryGate n
CX c t {neq} = CNOT c t {neq = neq}

public export
data Gate : Nat -> Type where
  UGate   : UnitaryGate n -> Gate n
  Measure : (q : Fin n) -> Gate n
  Reset   : (q : Fin n) -> Gate n

public export
targetsUnitary : UnitaryGate n -> (m ** Vect m (Fin n))
targetsUnitary (Id q)                    = (_ ** [q])
targetsUnitary (X q)                     = (_ ** [q])
targetsUnitary (Y q)                     = (_ ** [q])
targetsUnitary (Z q)                     = (_ ** [q])
targetsUnitary (H q)                     = (_ ** [q])
targetsUnitary (S q)                     = (_ ** [q])
targetsUnitary (SDG q)                   = (_ ** [q])
targetsUnitary (T q)                     = (_ ** [q])
targetsUnitary (TDG q)                   = (_ ** [q])
targetsUnitary (SX q)                    = (_ ** [q])
targetsUnitary (SXDG q)                  = (_ ** [q])
targetsUnitary (RX _ q)                  = (_ ** [q])
targetsUnitary (RY _ q)                  = (_ ** [q])
targetsUnitary (RZ _ q)                  = (_ ** [q])
targetsUnitary (U _ _ _ q)               = (_ ** [q])
targetsUnitary (U1 _ q)                  = (_ ** [q])
targetsUnitary (U2 _ _ q)                = (_ ** [q])
targetsUnitary (U3 _ _ _ q)              = (_ ** [q])
targetsUnitary (CNOT _ t)                = (_ ** [t])
targetsUnitary (CY _ t)                  = (_ ** [t])
targetsUnitary (CZ _ t)                  = (_ ** [t])
targetsUnitary (CH _ t)                  = (_ ** [t])
targetsUnitary (CS _ t)                  = (_ ** [t])
targetsUnitary (CSDG _ t)                = (_ ** [t])
targetsUnitary (CT _ t)                  = (_ ** [t])
targetsUnitary (CTDG _ t)                = (_ ** [t])
targetsUnitary (CSX _ t)                 = (_ ** [t])
targetsUnitary (CSXDG _ t)               = (_ ** [t])
targetsUnitary (CRX _ _ t)               = (_ ** [t])
targetsUnitary (CRY _ _ t)               = (_ ** [t])
targetsUnitary (CRZ _ _ t)               = (_ ** [t])
targetsUnitary (CU1 _ _ t)               = (_ ** [t])
targetsUnitary (CU2 _ _ _ t)             = (_ ** [t])
targetsUnitary (CU3 _ _ _ _ t)           = (_ ** [t])
targetsUnitary (SWAP a b)                = (_ ** [a, b])
targetsUnitary (RXX _ a b)               = (_ ** [a, b])
targetsUnitary (RYY _ a b)               = (_ ** [a, b])
targetsUnitary (RZZ _ a b)               = (_ ** [a, b])
targetsUnitary (RZX _ a b)               = (_ ** [a, b])
targetsUnitary (CCX _ _ t)               = (_ ** [t])
targetsUnitary (CSWAP _ a b)             = (_ ** [a, b])
targetsUnitary (Controlled _ _ inner)    = targetsUnitary inner

public export
targets : Gate n -> (m ** Vect m (Fin n))
targets (UGate u)    = targetsUnitary u
targets (Measure q)  = (_ ** [q])
targets (Reset q)    = (_ ** [q])

public export
mkControlled :
  {k : Nat} ->
  (cs : Vect k (Fin n)) ->
  (bs : Vect k Bool) ->
  (inner : UnitaryGate n) ->
  {auto distinct : AllDistinct cs} ->                                 -- keeps the control wires pairwise distinct
  {auto disjoint : Disjoint cs (snd (targetsUnitary inner))} ->       -- checks that none of those control wires overlap the targets
  UnitaryGate n
mkControlled cs bs inner = Controlled cs bs inner


public export
adjointUnitary : UnitaryGate n -> UnitaryGate n

-- 1-qubit Clifford + T
adjointUnitary (Id q)    = Id q
adjointUnitary (X q)     = X q
adjointUnitary (Y q)     = Y q
adjointUnitary (Z q)     = Z q
adjointUnitary (H q)     = H q
adjointUnitary (S q)     = SDG q
adjointUnitary (SDG q)   = S q
adjointUnitary (T q)     = TDG q
adjointUnitary (TDG q)   = T q
adjointUnitary (SX q)    = SXDG q
adjointUnitary (SXDG q)  = SX q

-- Parametric rotations (assuming Radians is a Num)
adjointUnitary (RX theta q) = RX (-theta) q
adjointUnitary (RY theta q) = RY (-theta) q
adjointUnitary (RZ theta q) = RZ (-theta) q

-- U-family
adjointUnitary (U  theta phi lambda q) =
  U (-theta) (-lambda) (-phi) q

adjointUnitary (U1 lambda q) =
  U1 (-lambda) q

-- For U2, we use the standard OpenQASM / Qiskit adjoint:
-- U2(φ, λ)† = U2(-λ - π, -φ + π), up to global phase
adjointUnitary (U2 phi lambda q) =
  U2 (-lambda - pi) ( -phi + pi ) q

adjointUnitary (U3 theta phi lambda q) =
  U3 (-theta) (-lambda) (-phi) q

-- 2-qubit + 3-qubit: many of these are self-adjoint
adjointUnitary (CNOT c t {neq})     = CNOT c t {neq = neq}
adjointUnitary (CY c t {neq})       = CY c t {neq = neq}
adjointUnitary (CZ c t {neq})       = CZ c t {neq = neq}
adjointUnitary (CH c t {neq})       = CH c t {neq = neq}
adjointUnitary (CS c t {neq})       = CSDG c t {neq = neq}
adjointUnitary (CSDG c t {neq})     = CS c t {neq = neq}
adjointUnitary (CT c t {neq})       = CTDG c t {neq = neq}
adjointUnitary (CTDG c t {neq})     = CT c t {neq = neq}
adjointUnitary (CSX c t {neq})      = CSXDG c t {neq = neq}
adjointUnitary (CSXDG c t {neq})    = CSX c t {neq = neq}

adjointUnitary (CRX theta c t {neq}) =
  CRX (-theta) c t {neq = neq}
adjointUnitary (CRY theta c t {neq}) =
  CRY (-theta) c t {neq = neq}
adjointUnitary (CRZ theta c t {neq}) =
  CRZ (-theta) c t {neq = neq}

adjointUnitary (CU1 lambda c t {neq}) =
  CU1 (-lambda) c t {neq = neq}
adjointUnitary (CU2 phi lambda c t {neq}) =
  CU2 (-lambda - pi) (-phi + pi) c t {neq = neq}
adjointUnitary (CU3 theta phi lambda c t {neq}) =
  CU3 (-theta) (-lambda) (-phi) c t {neq = neq}

adjointUnitary (SWAP a b {neq})     = SWAP a b {neq = neq}
adjointUnitary (RXX theta a b {neq}) =
  RXX (-theta) a b {neq = neq}
adjointUnitary (RYY theta a b {neq}) =
  RYY (-theta) a b {neq = neq}
adjointUnitary (RZZ theta a b {neq}) =
  RZZ (-theta) a b {neq = neq}
adjointUnitary (RZX theta a b {neq}) =
  RZX (-theta) a b {neq = neq}

adjointUnitary (CCX c1 c2 t {d12} {d1t} {d2t}) =
  CCX c1 c2 t {d12 = d12} {d1t = d1t} {d2t = d2t}

adjointUnitary (CSWAP c a b {cab} {ca} {cb}) =
  CSWAP c a b {cab = cab} {ca = ca} {cb = cb}

-- Controlled wrapper: adjoint just adjoints the inner gate
adjointUnitary (Controlled cs bs inner) =
  Controlled cs bs (adjointUnitary inner)

public export
adjointGate : Gate n -> Maybe (Gate n)
adjointGate (UGate u)   = Just (UGate (adjointUnitary u))
adjointGate (Measure _) = Nothing   -- not unitary
adjointGate (Reset   _) = Nothing   -- not unitary

  -- -- 1 control on |1⟩ (classic single control)
  -- let g1 : Gate n = mkControlled [c] [True] (X t)
  -- -- 1 control on |0⟩ (negative control)
  -- let g2 : Gate n = mkControlled [c] [False] (H t)
  -- -- 2 controls, mixed polarities
  -- let g3 : Gate n = mkControlled [c1, c2] [True, False] (RZ theta t)
  -- -- Add a control to a 2-qubit gate (e.g., controlled-SWAP)
  -- let g4 : Gate n = mkControlled [c] [True] (SWAP a b)
  -- -- Nesting: add another control later (e.g., build CCCX)
  -- let g5 : Gate n = mkControlled [d] [True] (mkControlled [c] [True] (X t))
  -- -- Controlled parametric gate (e.g., CU3)
  -- let g6 : Gate n = mkControlled [c] [True] (U3 th ph lam t)
