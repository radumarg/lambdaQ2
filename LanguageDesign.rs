
// TYPES

true
false
Bit
Qubit
QReg
BReg

// KEYWORDS

let
ctrl
negctrl
&
measr
reset

// APLYING GATES

let q0 = new(true);
let q1 = new(false);

H(q0);
CX(q0, q1);

ctrl(q0) H(q1);
negctrl(q0) H(q1);

ctrl(q0, q1) H(q2);
 
let (q0, q1, q2) = ctrl(q0) negctrl(q1) H(q2);
let (q0, q1, q2) = ctrl(q0 = true, q1 = false) H(q2);

let (q0, q1) = CX(q0, q1);
let (q0, q1) = ctrl(q0) H(q1);

// introduce an explicit “borrow” marker for controls when controls are observed, not transformed, so they don’t need to be re-bound
let q1 = ctrl(&q0) H(q1);
H(q0); // q0 still available (read-only used as control)

// QUANTUM REGISTERS

// dynamic register (runtime-sized)
// lower into List + runtime checks
let qs: QReg = qalloc(n);

// static register (compile-time sized)
// lower into Vect n
let qs: QReg<8> = qalloc(8);