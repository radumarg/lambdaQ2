module Quantum.GateHelpers

import Data.Fin
import Decidable.Equality
import Quantum.Gates
import Quantum.Circuit
import Quantum.Core
import Quantum.LowLevelGateHelpers

%default total

public export
x : {n : Nat} -> (i : Nat) -> Circuit n n -> Circuit n n
x {n} i circ =
  case natToFin i n of
    Just q  => xFin q circ
    Nothing => circ

public export
z : {n : Nat} -> (i : Nat) -> Circuit n n -> Circuit n n
z {n} i circ =
  case natToFin i n of
    Just q  => zFin q circ
    Nothing => circ

public export
hadamard : {n : Nat} -> (i : Nat) -> Circuit n n -> Circuit n n
hadamard {n} i circ =
  case natToFin i n of
    Just q  => hadamardFin q circ
    Nothing => circ

public export
cnot : {n : Nat} -> (ic, it : Nat) -> Circuit n n -> Circuit n n
cnot {n} ic it circ =
  case (natToFin ic n, natToFin it n) of
    (Just c, Just t) =>
      case decEq c t of
        Yes _  => circ
        No neq => cnotFin c t {neq} circ
    _ => circ

public export
toffoli : {n : Nat} -> (ia, ib, it : Nat) -> Circuit n n -> Circuit n n
toffoli {n} ia ib it circ =
  case (natToFin ia n, natToFin ib n, natToFin it n) of
    (Just a, Just b, Just t) =>
      case (decEq a b, decEq a t, decEq b t) of
        (No ab, No at, No bt) => toffoliFin a b t {d12=ab} {d1t=at} {d2t=bt} circ
        _                     => circ
    _ => circ