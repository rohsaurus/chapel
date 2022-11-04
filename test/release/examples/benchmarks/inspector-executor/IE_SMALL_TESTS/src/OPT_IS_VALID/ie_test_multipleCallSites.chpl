/*
    What this tests: Tests that we can support multiple call sites
    to the same function that contains the forall loop being
    optimized.


    Expected output on 2 locales:

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
        inspector on
        inspector on
        inspector on
        1.0 1.0 1.0 1.0
*/

use BlockDist;

proc func(A : [?E], B : [?D], C)
{
  forall i in B.domain {
      C[i] += A[B[i]];
  }
  writeln(C);
}

var dom = newBlockDom({0..#4});
var dom2 = newBlockDom({0..#4});
var dom3 = newBlockDom({0..#4});

var A1 : [dom] real;
var B1 : [dom] int;
var C1 : [dom] real;

var A2 : [dom2] real;
var B2 : [dom2] int;
var C2 : [dom2] real;

var A3 : [dom2] real;
var B3 : [dom2] int;
var C3 : [dom2] real;

A1 = 1;
B1[0] = 2;
B1[1] = 3;
B1[2] = 0;
B1[3] = 1;
C1 = 0;
for j in 0..#3 {
    func(A1, B1, C1);
    A1 += 1;
}

// second call site, do more mods to make sure we are truly optimizing this separately
A2 = 1;
B2[0] = 2;
B2[1] = 3;
B2[2] = 0;
B2[3] = 1;
B2[0] = 2;
B2[1] = 3;
C2 = 0;
for j in 0..#3 {
    func(A2, B2, C2);
    A2 += 1;
}

// third call site that shouldn't be optimized/cloned
A3 = 1;
B3[0] = 2;
B3[1] = 3;
B3[2] = 0;
B3[3] = 1;
C3 = 0;
func(A3, B3, C3);
