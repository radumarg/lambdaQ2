module Quantum.GateHelpers

import Data.Fin
import Quantum.Gates
import Quantum.Circuit
import Quantum.Core

%default total

public export
emptyCircuit : {n : Nat} -> Circuit n n
emptyCircuit = Id

public export
x : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
x q circ = Seq circ (GateApplication (X q))

public export
y : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
y q circ = Seq circ (GateApplication (Y q))

public export
z : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
z q circ = Seq circ (GateApplication (Z q))

public export
hadamard : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
hadamard q circ = Seq circ (GateApplication (H q))

public export
s : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
s q circ = Seq circ (GateApplication (S q))

public export
t : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
t q circ = Seq circ (GateApplication (T q))

public export
sDag : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sDag q circ = Seq circ (GateApplication (SDG q))

public export
tDag : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
tDag q circ = Seq circ (GateApplication (TDG q))

public export
sx : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sx q circ = Seq circ (GateApplication (SX q))

public export
sxDag : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sxDag q circ = Seq circ (GateApplication (SXDG q))

-- Rotation gates
public export
rotX : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
rotX angle q circ = Seq circ (GateApplication (RX angle q))

public export
rotY : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
rotY angle q circ = Seq circ (GateApplication (RY angle q))

public export
rotZ : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
rotZ angle q circ = Seq circ (GateApplication (RZ angle q))

-- U-family gates
public export
u : {n : Nat} -> Radians -> Radians -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
u theta phi lambda q circ = Seq circ (GateApplication (U theta phi lambda q))

public export
u1 : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
u1 lambda q circ = Seq circ (GateApplication (U1 lambda q))

public export
u2 : {n : Nat} -> Radians -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
u2 phi lambda q circ = Seq circ (GateApplication (U2 phi lambda q))

public export
u3 : {n : Nat} -> Radians -> Radians -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
u3 theta phi lambda q circ = Seq circ (GateApplication (U3 theta phi lambda q))

-- Two-qubit gates
public export
cnot : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
cnot c t circ = Seq circ (GateApplication (CNOT c t))

public export
ctrlY : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlY c t circ = Seq circ (GateApplication (CY c t))

public export
ctrlZ : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlZ c t circ = Seq circ (GateApplication (CZ c t))

public export
swap : {n : Nat} -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
swap a b circ = Seq circ (GateApplication (SWAP a b))

public export
ctrlH : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlH c t circ = Seq circ (GateApplication (CH c t))

public export
ctrlS : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlS c t circ = Seq circ (GateApplication (CS c t))

public export
ctrlSDag : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlSDag c t circ = Seq circ (GateApplication (CSDG c t))

public export
ctrlT : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlT c t circ = Seq circ (GateApplication (CT c t))

public export
ctrlTDag : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlTDag c t circ = Seq circ (GateApplication (CTDG c t))

public export
ctrlSX : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlSX c t circ = Seq circ (GateApplication (CSX c t))

public export
measure : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
measure q circ = Seq circ (GateApplication (Measure q))

public export
reset : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
reset q circ = Seq circ (GateApplication (Reset q))

public export
ctrlSXDag : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlSXDag c t circ = Seq circ (GateApplication (CSXDG c t))

-- ctrl rotation gates
public export
ctrlRX : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlRX angle c t circ = Seq circ (GateApplication (CRX angle c t))

public export
ctrlRY : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlRY angle c t circ = Seq circ (GateApplication (CRY angle c t))

public export
ctrlRZ : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlRZ angle c t circ = Seq circ (GateApplication (CRZ angle c t))

-- ctrl U gates
public export
ctrlU1 : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlU1 lambda c t circ = Seq circ (GateApplication (CU1 lambda c t))

public export
ctrlU2 : {n : Nat} -> Radians -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlU2 phi lambda c t circ = Seq circ (GateApplication (CU2 phi lambda c t))

public export
ctrlU3 : {n : Nat} -> Radians -> Radians -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlU3 theta phi lambda c t circ = Seq circ (GateApplication (CU3 theta phi lambda c t))

-- Two-qubit interaction gates
public export
rxx : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
rxx angle a b circ = Seq circ (GateApplication (RXX angle a b))

public export
ryy : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
ryy angle a b circ = Seq circ (GateApplication (RYY angle a b))

public export
rzz : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
rzz angle a b circ = Seq circ (GateApplication (RZZ angle a b))

public export
rzx : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
rzx angle a b circ = Seq circ (GateApplication (RZX angle a b))

-- Three-qubit gates
public export
toffoli : {n : Nat} -> (c1, c2, t : Fin n) 
        -> {auto 0 d12 : Not (c1 = c2)}
        -> {auto 0 d1t : Not (c1 = t)}
        -> {auto 0 d2t : Not (c2 = t)}
        -> Circuit n n -> Circuit n n
toffoli c1 c2 t circ = Seq circ (GateApplication (CCX c1 c2 t))

public export
fredkin : {n : Nat} -> (c, a, b : Fin n) 
        -> {auto 0 cab : Not (a = b)}
        -> {auto 0 ca  : Not (c = a)}
        -> {auto 0 cb  : Not (c = b)}
        -> Circuit n n -> Circuit n n
fredkin c a b circ = Seq circ (GateApplication (CSWAP c a b))
