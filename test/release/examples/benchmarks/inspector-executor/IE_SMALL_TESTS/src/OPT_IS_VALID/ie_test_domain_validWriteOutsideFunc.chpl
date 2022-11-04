/*
    What this tests: Writes to A and B's domain outside of the function
    that contains the forall loop will turn on the inpector.

    
    Expected output on 2 locales:

        inspector on
        inspector on
        inspector on
        inspector on
        inspector on
        setHasOuterLoop for functionID=1
        1.0 1.0 1.0 1.0
        3.0 3.0 3.0 3.0
        6.0 6.0 6.0 6.0
        unsetHasOuterLoop for functionID=1
        inspector on
*/

use BlockDist;

proc func(A, B : [?D], C)
{
  forall i in B.domain {
      C[i] += A[B[i]];
  }
  writeln(C);
}

var dom = newBlockDom({0..#4});
var dom2 = newBlockDom({0..#4});

var A : [dom2] real;
var B : [dom] int;
var C = newBlockArr({0..#4}, real);

A = 1;

// Make remote accesses, assuming we're only on 2 locales
B[0] = 2;
B[1] = 3;
B[2] = 0;
B[3] = 1;

dom = newBlockDom({0..#4});

C = 0;
for j in 0..#3 {
    func(A, B, C);
    A += 1;
}

dom2 = newBlockDom({0..#4});
