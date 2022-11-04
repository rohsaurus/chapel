/*
    What this tests: We can optimize two forall loops that
    are in different functions. Also tests re-using arrays.
    func() is called with A and B, writing into C. func2()
    is called with C and B, writing into A.

    We'll see 2 inspector calls per write to B in the
    beginning, so 8 calls total. We'll then see another
    8 calls to the 2nd set of writes to B.


    Expected output on 2 locales:

        inspector on
        inspector on
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
        inspector on
        inspector on
        inspector on
        inspector on
        setHasOuterLoop for functionID=2
        1.0 1.0 1.0 1.0
        2.0 2.0 2.0 2.0
        3.0 3.0 3.0 3.0
        unsetHasOuterLoop for functionID=2
*/

use BlockDist;

proc func(A:[?E], B:[?D], C)
{
  forall i in B.domain {
      C[i] += A[B[i]];
  }
  writeln(C);
}

proc func2(X:[?E], Y:[?D], Z)
{
  forall i in Y.domain {
      Z[i] += X[Y[i]];
  }
  writeln(Z);
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
}

A = 1;
C = 0;
B[0] = 0;
B[1] = 2;
B[2] = 1;
B[3] = 3;
for j in 0..#3 {
    func2(C, B, A);
    A += 1;
}
