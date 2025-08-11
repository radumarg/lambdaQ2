module Quantum.GateHelpers

import Data.Fin
import Quantum.Gates
import Quantum.Circuit
import Quantum.Core

%default total

public export
hadamard : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
hadamard q c = Seq c (GateApplication (H q))

public export
cnot : {n : Nat} -> (c, t : Fin n) -> Circuit n n -> Circuit n n
cnot c t ckt = Seq ckt (GateApplication (CNOT c t))

public export
pauliX : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
pauliX q c = Seq c (GateApplication (X q))

public export
pauliY : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
pauliY q c = Seq c (GateApplication (Y q))

public export
pauliZ : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
pauliZ q c = Seq c (GateApplication (Z q))

public export
sGate : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sGate q c = Seq c (GateApplication (S q))

public export
tGate : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
tGate q c = Seq c (GateApplication (T q))

public export
sDagger : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sDagger q c = Seq c (GateApplication (SDG q))

public export
tDagger : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
tDagger q c = Seq c (GateApplication (TDG q))

public export
sxGate : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sxGate q c = Seq c (GateApplication (SX q))

public export
sxDagger : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sxDagger q c = Seq c (GateApplication (SXDG q))

-- Rotation gates
public export
rotX : Radians -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
rotX angle q c = Seq c (GateApplication (RX angle q))

public export
rotY : Radians -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
rotY angle q c = Seq c (GateApplication (RY angle q))

public export
rotZ : Radians -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
rotZ angle q c = Seq c (GateApplication (RZ angle q))

-- U-family gates
public export
uGate : Radians -> Radians -> Radians -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
uGate theta phi lambda q c = Seq c (GateApplication (U theta phi lambda q))

public export
u1Gate : Radians -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
u1Gate lambda q c = Seq c (GateApplication (U1 lambda q))

public export
u2Gate : Radians -> Radians -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
u2Gate phi lambda q c = Seq c (GateApplication (U2 phi lambda q))

public export
u3Gate : Radians -> Radians -> Radians -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
u3Gate theta phi lambda q c = Seq c (GateApplication (U3 theta phi lambda q))

-- Two-qubit gates
public export
ctrlY : Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ctrlY c t ckt = Seq ckt (GateApplication (CY c t))

public export
ctrlZ : Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ctrlZ c t ckt = Seq ckt (GateApplication (CZ c t))

public export
swap : Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
swap a b ckt = Seq ckt (GateApplication (SWAP a b))

public export
ctrlH : Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ctrlH c t ckt = Seq ckt (GateApplication (CH c t))

public export
ctrlS : Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ctrlS c t ckt = Seq ckt (GateApplication (CS c t))

public export
ctrlSDG : Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ctrlSDG c t ckt = Seq ckt (GateApplication (CSDG c t))

public export
ctrlT : Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ctrlT c t ckt = Seq ckt (GateApplication (CT c t))

public export
ctrlTDG : Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ctrlTDG c t ckt = Seq ckt (GateApplication (CTDG c t))

public export
ctrlSX : Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ctrlSX c t ckt = Seq ckt (GateApplication (CSX c t))

public export
ctrlSXDG : Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ctrlSXDG c t ckt = Seq ckt (GateApplication (CSXDG c t))

-- ctrl rotation gates
public export
ctrlRX : Radians -> Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ctrlRX angle c t ckt = Seq ckt (GateApplication (CRX angle c t))

public export
ctrlRY : Radians -> Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ctrlRY angle c t ckt = Seq ckt (GateApplication (CRY angle c t))

public export
ctrlRZ : Radians -> Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ctrlRZ angle c t ckt = Seq ckt (GateApplication (CRZ angle c t))

-- ctrl U gates
public export
ctrlU1 : Radians -> Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ctrlU1 lambda c t ckt = Seq ckt (GateApplication (CU1 lambda c t))

public export
ctrlU2 : Radians -> Radians -> Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ctrlU2 phi lambda c t ckt = Seq ckt (GateApplication (CU2 phi lambda c t))

public export
ctrlU3 : Radians -> Radians -> Radians -> Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ctrlU3 theta phi lambda c t ckt = Seq ckt (GateApplication (CU3 theta phi lambda c t))

-- Two-qubit interaction gates
public export
rxx : Radians -> Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
rxx angle a b ckt = Seq ckt (GateApplication (RXX angle a b))

public export
ryy : Radians -> Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
ryy angle a b ckt = Seq ckt (GateApplication (RYY angle a b))

public export
rzz : Radians -> Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
rzz angle a b ckt = Seq ckt (GateApplication (RZZ angle a b))

public export
rzx : Radians -> Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
rzx angle a b ckt = Seq ckt (GateApplication (RZX angle a b))

-- Three-qubit gates
public export
toffoli : Qubit -> Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
toffoli c1 c2 t ckt = Seq ckt (GateApplication (CCX c1 c2 t))

public export
fredkin : Qubit -> Qubit -> Qubit -> {n : Nat} -> Circuit n n -> Circuit n n
fredkin c a b ckt = Seq ckt (GateApplication (CSWAP c a b))