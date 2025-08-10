module Quantum.Gates

import Data.Fin 

%default total

public export
record Radians where
  constructor MkRad
  val : Double

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

-- 2-qubit (with a proof that control ≠ target)
  CNOT  : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CY    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CZ    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CH    : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n

  CRX   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CRY   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CRZ   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
  CU1   : Radians -> (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
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

public export
CX : (c,t : Fin n) -> {auto 0 neq : Not (c = t)} -> Gate n
CX = CNOT
