
module Examples

import Data.Fin
import Quantum.Circuit
import Quantum.Control
import Quantum.GateHelpers

%default total

q0 : Fin.Fin 5
q0 = Fin.FZ

q1 : Fin.Fin 5
q1 = Fin.FS Fin.FZ

q2 : Fin.Fin 5
q2 = Fin.FS (Fin.FS Fin.FZ)

q3 : Fin.Fin 5
q3 = Fin.FS (Fin.FS (Fin.FS Fin.FZ))

q4 : Fin.Fin 5
q4 = Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.FZ)))

neq_q0_q1 : Not (Fin.FZ = Fin.FS Fin.FZ)
neq_q0_q1 Refl impossible

neq_q0_q2 : Not (Fin.FZ = Fin.FS (Fin.FS Fin.FZ))
neq_q0_q2 Refl impossible

neq_q1_q2 : Not (Fin.FS Fin.FZ = Fin.FS (Fin.FS Fin.FZ))
neq_q1_q2 Refl impossible

build : Circuit 5 5
build =
  let c0 = emptyCircuit {n = 5}
      c1 = hadamard q0 c0
      c2 = x q1 c1
      c3 = cnot q0 q1 {neq = neq_q0_q1} c2
      c4 = toffoli q0 q1 q2
             { d12 = neq_q0_q1
             , d1t = neq_q0_q2
             , d2t = neq_q1_q2 } c3
   in z q2 c4