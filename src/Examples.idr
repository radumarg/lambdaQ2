
module Examples

import Quantum.Circuit
import Quantum.Control
import Quantum.TypeSafeGateHelpers
import Quantum.GateHelpers

build : Circuit 5 5
build =
  let c0 = emptyCircuit {n = 5}
      c1 = hadamard 0 c0
      c2 = x        1 c1
      c3 = cnot     0 1 c2
      c4 = toffoli  0 1 2 c3
   in z 2 c4