/*
    What this tests: Things work correctly when we have a function
    with the forall and a main(). It ensures we are finding things
    correctly when here are generic vs. concrete functions.


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
*/

use BlockDist;

proc func(A:[?E], B:[?D], C)
{
  forall i in B.domain {
      C[i] += A[B[i]];
  }
  writeln(C);
}

proc main() 
{
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
}
