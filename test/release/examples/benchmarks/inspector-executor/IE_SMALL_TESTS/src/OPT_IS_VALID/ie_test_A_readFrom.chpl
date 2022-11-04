/*
    What this tests: supporting reads from A within
    the forall loop.

    
    Expected output on 2 locales:

        inspector on
        inspector on
        inspector on
        inspector on
        1.0 1.0 1.0 1.0
        3.0 3.0 3.0 3.0
        6.0 6.0 6.0 6.0    
*/

use BlockDist;

var dom = newBlockDom({0..#4});

var A : [dom] real;
var B : [dom] int;

var C = newBlockArr({0..#4}, real);
var D = newBlockArr({0..#4}, real);

A = 1;

// Make remote accesses, assuming we're only on 2 locales
B[0] = 2;
B[1] = 3;
B[2] = 0;
B[3] = 1;

C = 0;
for j in 0..#3 {
    forall i in B.domain {
        var j = i;
        C[i] += A[B[i]];
        D = A;
    }
    A += 1;
    writeln(C);
}
