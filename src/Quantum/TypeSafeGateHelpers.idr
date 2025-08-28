module Quantum.TypeSafeGateHelpers

import Data.Fin
import Quantum.Gates
import Quantum.Circuit
import Quantum.Core

%default total

public export
emptyCircuit : {n : Nat} -> Circuit n n
emptyCircuit = Id

public export
xFin : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
xFin q circ = Seq circ (GateApplication (X q))

public export
yFin : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
yFin q circ = Seq circ (GateApplication (Y q))

public export
zFin : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
zFin q circ = Seq circ (GateApplication (Z q))

public export
hadamardFin : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
hadamardFin q circ = Seq circ (GateApplication (H q))

public export
sFin : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sFin q circ = Seq circ (GateApplication (S q))

public export
tFin : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
tFin q circ = Seq circ (GateApplication (T q))

public export
sDagFin : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sDagFin q circ = Seq circ (GateApplication (SDG q))

public export
tDagFin : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
tDagFin q circ = Seq circ (GateApplication (TDG q))

public export
sxFin : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sxFin q circ = Seq circ (GateApplication (SX q))

public export
sxDagFin : {n : Nat} -> (q : Fin n) -> Circuit n n -> Circuit n n
sxDagFin q circ = Seq circ (GateApplication (SXDG q))

-- Rotation gates
public export
rotXFin : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
rotXFin angle q circ = Seq circ (GateApplication (RX angle q))

public export
rotYFin : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
rotYFin angle q circ = Seq circ (GateApplication (RY angle q))

public export
rotZFin : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
rotZFin angle q circ = Seq circ (GateApplication (RZ angle q))

-- U-family gates
public export
uFin : {n : Nat} -> Radians -> Radians -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
uFin theta phi lambda q circ = Seq circ (GateApplication (U theta phi lambda q))

public export
u1Fin : {n : Nat} -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
u1Fin lambda q circ = Seq circ (GateApplication (U1 lambda q))

public export
u2Fin : {n : Nat} -> Radians -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
u2Fin phi lambda q circ = Seq circ (GateApplication (U2 phi lambda q))

public export
u3Fin : {n : Nat} -> Radians -> Radians -> Radians -> (q : Fin n) -> Circuit n n -> Circuit n n
u3Fin theta phi lambda q circ = Seq circ (GateApplication (U3 theta phi lambda q))

-- Two-qubit gates
public export
cnotFin : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
cnotFin c t circ = Seq circ (GateApplication (CNOT c t))

public export
ctrlYFin : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlYFin c t circ = Seq circ (GateApplication (CY c t))

public export
ctrlZFin : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlZFin c t circ = Seq circ (GateApplication (CZ c t))

public export
swapFin : {n : Nat} -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
swapFin a b circ = Seq circ (GateApplication (SWAP a b))

public export
ctrlHFin : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlHFin c t circ = Seq circ (GateApplication (CH c t))

public export
ctrlSFin : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlSFin c t circ = Seq circ (GateApplication (CS c t))

public export
ctrlSDagFin : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlSDagFin c t circ = Seq circ (GateApplication (CSDG c t))

public export
ctrlTFin : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlTFin c t circ = Seq circ (GateApplication (CT c t))

public export
ctrlTDagFin : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlTDagFin c t circ = Seq circ (GateApplication (CTDG c t))

public export
ctrlSXFin : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlSXFin c t circ = Seq circ (GateApplication (CSX c t))

public export
ctrlSXDagFin : {n : Nat} -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlSXDagFin c t circ = Seq circ (GateApplication (CSXDG c t))

-- ctrl rotation gates
public export
ctrlRXFin : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlRXFin angle c t circ = Seq circ (GateApplication (CRX angle c t))

public export
ctrlRYFin : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlRYFin angle c t circ = Seq circ (GateApplication (CRY angle c t))

public export
ctrlRZFin : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlRZFin angle c t circ = Seq circ (GateApplication (CRZ angle c t))

-- ctrl U gates
public export
ctrlU1Fin : {n : Nat} -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlU1Fin lambda c t circ = Seq circ (GateApplication (CU1 lambda c t))

public export
ctrlU2Fin : {n : Nat} -> Radians -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlU2Fin phi lambda c t circ = Seq circ (GateApplication (CU2 phi lambda c t))

public export
ctrlU3Fin : {n : Nat} -> Radians -> Radians -> Radians -> (c, t : Fin n) -> {auto 0 neq : Not (c = t)} -> Circuit n n -> Circuit n n
ctrlU3Fin theta phi lambda c t circ = Seq circ (GateApplication (CU3 theta phi lambda c t))

-- Two-qubit interaction gates
public export
rxxFin : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
rxxFin angle a b circ = Seq circ (GateApplication (RXX angle a b))

public export
ryyFin : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
ryyFin angle a b circ = Seq circ (GateApplication (RYY angle a b))

public export
rzzFin : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
rzzFin angle a b circ = Seq circ (GateApplication (RZZ angle a b))

public export
rzxFin : {n : Nat} -> Radians -> (a, b : Fin n) -> {auto 0 neq : Not (a = b)} -> Circuit n n -> Circuit n n
rzxFin angle a b circ = Seq circ (GateApplication (RZX angle a b))

-- Three-qubit gates
public export
toffoliFin : {n : Nat} -> (c1, c2, t : Fin n) 
        -> {auto 0 d12 : Not (c1 = c2)}
        -> {auto 0 d1t : Not (c1 = t)}
        -> {auto 0 d2t : Not (c2 = t)}
        -> Circuit n n -> Circuit n n
toffoliFin c1 c2 t circ = Seq circ (GateApplication (CCX c1 c2 t))

public export
fredkinFin : {n : Nat} -> (c, a, b : Fin n) 
        -> {auto 0 cab : Not (a = b)}
        -> {auto 0 ca  : Not (c = a)}
        -> {auto 0 cb  : Not (c = b)}
        -> Circuit n n -> Circuit n n
fredkinFin c a b circ = Seq circ (GateApplication (CSWAP c a b))
