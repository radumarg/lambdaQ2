
module Examples

import Data.Fin
import Quantum.Circuit
import Quantum.Control
import Quantum.GateHelpers

%default total

infixl 0 |>
(|>) : a -> (a -> b) -> b
x |> f = f x


-- bellCircuit : Circuit 2 2
-- bellCircuit =
--   cnot FZ (FS FZ) {neq = NotThere NotHere} (hadamard FZ Empty)

-- example : Circuit 2 2
-- example =
--   emptyCircuit
--     |> hadamard FZ       -- put qubit 0 in superposition
--     |> cnot FZ (FS FZ)   -- control = qubit 0, target = qubit 1

-- myCircuit : Circuit 2 2
-- myCircuit = hadamard FZ (cnot FZ (FS FZ) emptyCircuit)