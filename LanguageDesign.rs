// (0) Code lines are terminated by ';' like this is currently done in Rust except for function return syntax which does not end with ';', again like is the convention in Rust. Paranthesis, square brakets and curly braces follow the same rules from Rust.

// (1) Types Reserved Keywords:  
  (), angle, bit, bool, float, int, qubit, uint

// (param?): bind value, get name let p:Param = param("theta1")

// (2) Reserved Keywords: 
  as, break, ctrl, continue, else, false, fn, for, if, in, let, loop, measr, negctrl, qalloc, reset, return, true, while

// (3) Operators Reserved Symbols and Keywords: 
  '?', '&', '(', ')', ',', ';', '=', '+', '-', '*', '/', '%', '+=', '-=', '*=', '/=', '%=', '>', '>=', '<', '<=', '..', '()', ':', '[', ']', '{', '}', '==', '!=', '&&', '||', '!', '.', '..=', '::', '|', '^', '->'

// (4) Quantum Gates Reserved Keywords: 
  Id, X, Y, Z, H, S, SDG, T, TDG, SX, SXDG, RX, RY, RZ, U1, U2, U3, CNOT, CY, CZ, CS, CSDG, CT, CTDG, CSX, CSXDG, CRX, CRY, CRZ, CU1, CU2, CU3, SWAP, RXX, RYY, RZZ, CCX, CSWAP, GPI, GPI2, MS


// (5) Apply simple quantum gates on some qubits:

H(q0);
CX(q0, q1);

// (6) Apply controlled gates:

ctrl(q0) H(q1);
negctrl(q0) H(q1);
ctrl(q0, q1) H(q2);

// (7) More complicated quantum gate patterns where resulting qubits are redeclared as fresh qubit variables:
// Also use use 'ctrl' and 'negtcrl' to apply controlled gates:
let (q0, q1, q2) = ctrl(q0) negctrl(q1) H(q2);
// Alternative syntax for declaring controlled gates using booleans arguments instead of 'ctrl' and 'negtcrl':
let (q0, q1, q2) = ctrl(q0 = true, q1 = false) H(q2);
// Control can apply to a block og gates:
ctrl(q0, q1) {
  H(q2);
  CX(q2, q3);
}

// (8) Comments syntax for the new language:

  // single line commnent

  /*
     multi-line comment
  */

// (9) Variable declaration and assigment:

  let my_var = 5;

  let x:int = 3;
  x = 2 + 5;

// (10) Types variable delaration:

  let my_var : int = 5;

// (11) Operators:

  let add = 5 + 3;
  let sub = 10 - 4;
  let mul = 6 * 2;
  let div = 12 / 3;
  let rem = 10 % 3;

// (12) More operators:

  x += 5;
  x -= 2;
  x *= 2;
  x /= 3;
  x %= 4;

// (13) Boolean variable:

  let my_var: bool = true;

// (14) If/Else syntax:

  if 7 > 5 {
    // do something
  } else {
    // do something else
  }

// (15) Syntax for declaring loops:

  loop {
      if count == 3 {
          break;
      }
      count += 1;
  }

// (16) Syntax for declaring loops that return a value:

  let result = loop {
    println!("Hello!");

    if count == 3 {
      break count;
    } else {
      continue;
    }

    count += 1;
  };

// (17) While loop syntax:

  while count <= 5 {
    count += 1;
  }
  
// (18) For loop syntax:

  for i in 1..6 {
    // do something
  }

// (19) Functions syntax:

  fn function_name() {
    // code to be executed
  }
  
  Function returning some variable:
  
  fn f(x: int) -> int {
  	x + 1
   }
  
// (20) Variable declared in the scope of a function:

  fn myFunction() {
    let message = "Hello!";
  }
  
// (21) Function syntax with typed arguments:

  fn f(x: (int, bool)) {
    let (n, flag) = x;
  }  
  
// (22) Function returning a value:
fn f() {
    let x = 2.0;
    x
}

// (23) Alternative syntax for function returning a value:
fn f() {
    let x = 2.0;
    return x
}
  
// (24) Declaring tuples:

  let t = (1, 3.14, true);
  let t: (int, float, bool) = (1, 3.14, true);
  
// (25) Tuples positional indexing:

  let x = t.0;
  let y = t.1;
  let z = t.2;

// (26) Extracting variables from tuples:
  
  let (a, b, c) = (1, 2, 3);
  let (x, _, z) = (1, 2, 3);
  let (q0, q1, q2) = (H(q0), H(q1), H(q2))
  
// (27) Unit type syntax:

  let u: () = ();
  
// (28) Declaring Arrays literal:

let a = [1, 2, 3];
let b: [int; 4] = [10, 20, 30, 40];

// (29) Arrays declared using a repeat syntax:

let zeros = [0; 8];         // [0, 0, 0, 0, 0, 0, 0, 0]
let flags = [true; 3];      // [true, true, true]

// (30) Array access and length:

let a = [1, 2, 3];
let first = a[0];
let n = a.len();

// (31) Other quantum specific constructs:

let q: qubit = qalloc();
let qs: [qubit; 8] = qalloc(8); 

let b: bit = measr(q);
let bs: [bit; 8] = measr(qs);

// (32) Bit can appear in conditions:

if b { X(q); }        

if b == 1 { X(q); }     


// (33) Ranges:
    a..b (exclusive)
    a..=b (inclusive)

// (34) Bitwise operations:

let and_ = a & b;
let or_  = a | b;
let xor_ = a ^ b;

// (35) Blocks as expressions:

  let x = if flag { 1 } else { 2 };
  
// (36) Pattern matching:

fn main() {
  let day = 4;

  match day {
    1 => { /* todo */ },
    2 => { /* todo */ },
    3 => { /* todo */ },
    4 => { /* todo */ },
    5 => { /* todo */ },
    6 => { /* todo */ },
    7 => { /* todo */ },
    _ => { /* todo */ },
  }
}

match b {
  true => { /* todo */ }
  false => { /* todo */ }
}

// (37) Type casting:
 
 let b:Bit = 1;
 let x = b as int;

// (38) Qubit allocation:

qalloc() -> Qubit
qalloc(n: uint) -> qubit[n]

// (39) Reset:

reset(q: Qubit) -> Qubit
reset(qs: [qubit; n]) -> [qubit; n]

// (40) Measure:

measr(q: qubit) -> (bit, qubit)
measr(qs: [qubit; n]) -> ([bit; n], [qubit; n])

// (41) An example of quantum flow:

fn bell_pair() -> (bit, bit) {
  let q0: qubit = qalloc();
  let q1: qubit = qalloc();

  H(q0);
  CX(q0, q1);

  let (b0, q0) = measr(q0);
  let (b1, q1) = measr(q1);

  // q0, q1 still exist (collapsed); can reset/discard later if you want
  (b0, b1)
}

// (42) Allocating quantum register, both notations should work: 

// dynamic length
let qs: [qubit] = qalloc(8);

// static length
let qs: [qubit; 8] = qalloc(8);

// static length alias
let qs: [qubit; 8] = qalloc(8);




