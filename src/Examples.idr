
module Examples

import Data.Fin
import Quantum.Circuit
import Quantum.Control
import Quantum.GateHelpers

%default total

q0 : Fin.Fin 3
q0 = Fin.FZ

q1 : Fin.Fin 3
q1 = Fin.FS Fin.FZ

q2 : Fin.Fin 3
q2 = Fin.FS (Fin.FS Fin.FZ)

neq_q0_q1 : Not (Fin.FZ = Fin.FS Fin.FZ)
neq_q0_q1 Refl impossible

build : Circuit 3 3
build =
  let c0 = emptyCircuit {n = 3}
      c1 = hadamard q0 c0
      c2 = x q1 c1
      c3 = cnot q0 q1 {neq = neq_q0_q1} c2
   in z q2 c3