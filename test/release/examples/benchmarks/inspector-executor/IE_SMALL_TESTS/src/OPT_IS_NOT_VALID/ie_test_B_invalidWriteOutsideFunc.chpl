/*
    What this tests: Cannot write to B outside of forall loop. This tests
    the case when the forall is in a function and the write is outside
    of that function.
*/

use BlockDist;

proc func(A:[?E], B:[?D], C)
{
  forall i in B.domain {
      C[i] += A[B[i]];
  }
  writeln(C);
}

var dom = newBlockDom({0..#4});

var A : [dom] real;
var B : [dom] int;
var C : [dom] real;

A = 1;

// Make remote accesses, assuming we're only on 2 locales
B[0] = 2;
B[1] = 3;
B[2] = 0;
B[3] = 1;

C = 0;
for j in 0..#3 {
    func(A, B, C);
    A += 1;
    B = j;
}
