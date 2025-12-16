
// TYPES

bool
int
uint
angle
float
Bit
Qubit
QReg
BReg

// KEYWORDS

let
fn
true
false
while
loop
for
if
else
break
return
ctrl
negctrl
&
new
measr
reset
qalloc ?

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

// QUANTUM REGISTERS ..?

// dynamic register (runtime-sized)
// lower into List + runtime checks
let qs: QReg = qalloc(n);

// static register (compile-time sized)
// lower into Vect n
let qs: QReg<8> = qalloc(8);

// RUST-LIKE CONTROL FLOW

fn main() {
    //
}

// commnent
/*
   multi-line comment
*/

let my_num = 5;         // integer
let my_double = 5.99;   // float
let my_bool = true;     // boolean

// operators
let add = 5 + 3;
let sub = 10 - 4;
let mul = 6 * 2;
let div = 12 / 3;
let rem = 10 % 3;

let mut x = 10;
x += 5;
x -= 2;
x *= 2;
x /= 3;
x %= 4;

// booleans
let is_programming_fun: bool = true;

if 7 > 5 {
  // do something
} else {
  // do something else
}

// loops
let mut count = 1;
loop {
    if count == 3 {
        break;
    }
    count += 1;
}

// loops can return a value
let result = loop {
  println!("Hello!");

  if count == 3 {
    break count;
  }

  count += 1;
};

// while loop
let mut count = 1;
while count <= 5 {
  count += 1;
}

// for loop
for i in 1..6 {
  // do something
}

// functions
fn function_name() {
  // code to be executed
}

// variable scope
fn myFunction() {
  let message = "Hello!";
  println!("{}", message);  // You can access the message variable here but not outside this function
}

// tuples
let t = (1, 3.14, true);
let t: (int, float, bool) = (1, 3.14, true);