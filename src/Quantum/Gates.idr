module Quantum.Gates

import Data.Fin
import Data.Vect
import Quantum.Core
import Quantum.Control

%default total

public export
data Gate : Nat -> Type where
  -- 1-qubit (Clifford + T and friends)
  Id    : (q : Fin n) -> Gate n
  X     : (q : Fin n) -> Gate n
  Y     : (q : Fin n) -> Gate n
  Z     : (q : Fin n) -> Gate n
  H     : (q : Fin n) -> Gate n
  S     : (q : Fin n) -> Gate n
  SDG   : (q : Fin n) -> Gate n
  T     : (q : Fin n) -> Gate n
  TDG   : (q : Fin n) -> Gate n
  SX    : (q : Fin n) -> Gate n
  SXDG  : (q : Fin n) -> Gate n

  -- Parametric 1-qubit rotations
  RX    : Radians -> (q : Fin n) -> Gate n
  RY    : Radians -> (q : Fin n) -> Gate n
  RZ    : Radians -> (q : Fin n) -> Gate n

  -- OpenQASM 2 primitives / U-family
  U     : Radians -> Radians -> Radians -> (q : Fin n) -> Gate n      -- U(θ, φ, λ)
  U1    : Radians -> (q : Fin n) -> Gate n                            -- U1(λ)   == U(0, 0, λ)
  U2    : Radians -> Radians -> (q : Fin n) -> Gate n                 -- U2(φ,λ) == U(π/2, φ, λ)
  U3    : Radians -> Radians -> Radians -> (q : Fin n) -> Gate n      -- U3(θ,φ,λ) == U(θ, φ, λ)

  -- Additional operations
  Measure : (q : Fin n) -> Gate n
  Reset : (q : Fin n) -> Gate n

-- 2-qubit (with a proof that control ≠ target)
  CNOT : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CY    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CZ    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CH    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CS    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CSDG  : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CT    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CTDG  : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CSX   : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CSXDG : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n

  CRX   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CRY   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CRZ   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CU1   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CU2   : Radians -> Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CU3   : Radians -> Radians -> Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n

  SWAP  : (a,b : Fin n) -> {auto 0 neq : Not (a = b)} -> Gate n
  RXX   : Radians -> (a,b : Fin n) -> {auto 0 neq : Not (a = b)} -> Gate n
  RYY   : Radians -> (a,b : Fin n) -> {auto 0 neq : Not (a = b)} -> Gate n
  RZZ   : Radians -> (a,b : Fin n) -> {auto 0 neq : Not (a = b)} -> Gate n
  RZX   : Radians -> (a,b : Fin n) -> {auto 0 neq : Not (a = b)} -> Gate n

  -- 3-qubit (all distinct)
  CCX   : (c1,c2,t : Fin n)
        -> {auto 0 d12 : Not (c1 = c2)}
        -> {auto 0 d1t : Not (c1 = t)}
        -> {auto 0 d2t : Not (c2 = t)}
        -> Gate n
  CSWAP : (c,a,b : Fin n)
        -> {auto 0 cab : Not (a = b)}
        -> {auto 0 ca  : Not (c = a)}
        -> {auto 0 cb  : Not (c = b)}
        -> Gate n

  -- Generic controlled wrapper:
  --   cs = control wires,
  --   bs = their required polarities (True = |1>, False = |0>)
  --   inner = the original gate
  Controlled :
    {k : Nat} ->
    (cs : Vect k (Fin n)) ->
    (bs : Vect k Bool) -> 
    (inner : Gate n) ->
    {auto _ : AllDistinct cs} ->
    Gate n

public export
CX : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
CX c t {neq} = CNOT c t {neq = neq}

public export
targets : Gate n -> (m ** Vect m (Fin n))
targets (Id q)                    = (_ ** [q])
targets (X q)                     = (_ ** [q])
targets (Y q)                     = (_ ** [q])
targets (Z q)                     = (_ ** [q])
targets (H q)                     = (_ ** [q])
targets (S q)                     = (_ ** [q])
targets (SDG q)                   = (_ ** [q])
targets (T q)                     = (_ ** [q])
targets (TDG q)                   = (_ ** [q])
targets (SX q)                    = (_ ** [q])
targets (SXDG q)                  = (_ ** [q])
targets (RX _ q)                  = (_ ** [q])
targets (RY _ q)                  = (_ ** [q])
targets (RZ _ q)                  = (_ ** [q])
targets (U _ _ _ q)               = (_ ** [q])
targets (U1 _ q)                  = (_ ** [q])
targets (U2 _ _ q)                = (_ ** [q])
targets (U3 _ _ _ q)              = (_ ** [q])
targets (Measure q)               = (_ ** [q])
targets (Reset q)                 = (_ ** [q])
targets (CNOT _ t)                = (_ ** [t])
targets (CY _ t)                  = (_ ** [t])
targets (CZ _ t)                  = (_ ** [t])
targets (CH _ t)                  = (_ ** [t])
targets (CS _ t)                  = (_ ** [t])
targets (CSDG _ t)                = (_ ** [t])
targets (CT _ t)                  = (_ ** [t])
targets (CTDG _ t)                = (_ ** [t])
targets (CSX _ t)                 = (_ ** [t])
targets (CSXDG _ t)               = (_ ** [t])
targets (CRX _ _ t)               = (_ ** [t])
targets (CRY _ _ t)               = (_ ** [t])
targets (CRZ _ _ t)               = (_ ** [t])
targets (CU1 _ _ t)               = (_ ** [t])
targets (CU2 _ _ _ t)             = (_ ** [t])
targets (CU3 _ _ _ _ t)           = (_ ** [t])
targets (SWAP a b)                = (_ ** [a, b])
targets (RXX _ a b)               = (_ ** [a, b])
targets (RYY _ a b)               = (_ ** [a, b])
targets (RZZ _ a b)               = (_ ** [a, b])
targets (RZX _ a b)               = (_ ** [a, b])
targets (CCX _ _ t)               = (_ ** [t])
targets (CSWAP _ a b)             = (_ ** [a, b])
targets (Controlled _ _ inner)    = targets inner

mkControlled :
  {k : Nat} ->
  (cs : Vect k (Fin n)) ->
  (bs : Vect k Bool) ->
  (inner : Gate n) ->
  {auto distinct : AllDistinct cs} ->
  {auto disj : Disjoint cs (snd (targets inner))} ->
  Gate n
mkControlled cs bs inner = Controlled cs bs inner
