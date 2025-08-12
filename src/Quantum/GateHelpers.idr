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
x q c = Seq c (GateApplication (X q))

public export
y : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
y q c = Seq c (GateApplication (Y q))

public export
z : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
z q c = Seq c (GateApplication (Z q))

public export
hadamard : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
hadamard q c = Seq c (GateApplication (H q))

public export
s : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
s q c = Seq c (GateApplication (S q))

public export
t : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
t q c = Seq c (GateApplication (T q))

public export
sDag : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sDag q c = Seq c (GateApplication (SDG q))

public export
tDag : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
tDag q c = Seq c (GateApplication (TDG q))

public export
sx : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sx q c = Seq c (GateApplication (SX q))

public export
sxDag : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sxDag q c = Seq c (GateApplication (SXDG q))

-- Rotation gates
public export
rotX : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
rotX angle q c = Seq c (GateApplication (RX angle q))

public export
rotY : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
rotY angle q c = Seq c (GateApplication (RY angle q))

public export
rotZ : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
rotZ angle q c = Seq c (GateApplication (RZ angle q))

-- U-family gates
public export
u : {n : Nat} -> Radians -> Radians -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
u theta phi lambda q c = Seq c (GateApplication (U theta phi lambda q))

public export
u1 : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
u1 lambda q c = Seq c (GateApplication (U1 lambda q))

public export
u2 : {n : Nat} -> Radians -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
u2 phi lambda q c = Seq c (GateApplication (U2 phi lambda q))

public export
u3 : {n : Nat} -> Radians -> Radians -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
u3 theta phi lambda q c = Seq c (GateApplication (U3 theta phi lambda q))

-- Two-qubit gates
public export
cnot : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
cnot c t ckt = Seq ckt (GateApplication (CNOT c t))

public export
ctrlY : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlY c t ckt = Seq ckt (GateApplication (CY c t))

public export
ctrlZ : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlZ c t ckt = Seq ckt (GateApplication (CZ c t))

public export
swap : {n : Nat} -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
swap a b ckt = Seq ckt (GateApplication (SWAP a b))

public export
ctrlH : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlH c t ckt = Seq ckt (GateApplication (CH c t))

public export
ctrlS : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlS c t ckt = Seq ckt (GateApplication (CS c t))

public export
ctrlSDag : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlSDag c t ckt = Seq ckt (GateApplication (CSDG c t))

public export
ctrlT : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlT c t ckt = Seq ckt (GateApplication (CT c t))

public export
ctrlTDag : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlTDag c t ckt = Seq ckt (GateApplication (CTDG c t))

public export
ctrlSX : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlSX c t ckt = Seq ckt (GateApplication (CSX c t))

public export
ctrlSXDag : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlSXDag c t ckt = Seq ckt (GateApplication (CSXDG c t))

-- ctrl rotation gates
public export
ctrlRX : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlRX angle c t ckt = Seq ckt (GateApplication (CRX angle c t))

public export
ctrlRY : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlRY angle c t ckt = Seq ckt (GateApplication (CRY angle c t))

public export
ctrlRZ : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlRZ angle c t ckt = Seq ckt (GateApplication (CRZ angle c t))

-- ctrl U gates
public export
ctrlU1 : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlU1 lambda c t ckt = Seq ckt (GateApplication (CU1 lambda c t))

public export
ctrlU2 : {n : Nat} -> Radians -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlU2 phi lambda c t ckt = Seq ckt (GateApplication (CU2 phi lambda c t))

public export
ctrlU3 : {n : Nat} -> Radians -> Radians -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlU3 theta phi lambda c t ckt = Seq ckt (GateApplication (CU3 theta phi lambda c t))

-- Two-qubit interaction gates
public export
rxx : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
rxx angle a b ckt = Seq ckt (GateApplication (RXX angle a b))

public export
ryy : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
ryy angle a b ckt = Seq ckt (GateApplication (RYY angle a b))

public export
rzz : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
rzz angle a b ckt = Seq ckt (GateApplication (RZZ angle a b))

public export
rzx : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
rzx angle a b ckt = Seq ckt (GateApplication (RZX angle a b))

-- Three-qubit gates
public export
toffoli : {n : Nat} -> (c1, c2, t : Fin n) 
        -> {auto 0 d12 : Not (c1 = c2)}
        -> {auto 0 d1t : Not (c1 = t)}
        -> {auto 0 d2t : Not (c2 = t)}
        -> Circuit n n -> Circuit n n
toffoli c1 c2 t ckt = Seq ckt (GateApplication (CCX c1 c2 t))

public export
fredkin : {n : Nat} -> (c, a, b : Fin n) 
        -> {auto 0 cab : Not (a = b)}
        -> {auto 0 ca  : Not (c = a)}
        -> {auto 0 cb  : Not (c = b)}
        -> Circuit n n -> Circuit n n
fredkin c a b ckt = Seq ckt (GateApplication (CSWAP c a b))