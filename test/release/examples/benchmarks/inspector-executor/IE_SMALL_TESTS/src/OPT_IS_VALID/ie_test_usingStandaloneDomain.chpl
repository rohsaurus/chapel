/*
    What this tests: We can use a stand-alone domain as
    the forall iterator/domain.


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

var D = newBlockDom({0..#4});

var A : [D] real;
var B : [D] int;
var C = newBlockArr({0..#4}, real);

A = 1;

// Make remote accesses, assuming we're only on 2 locales
B[0] = 2;
B[1] = 3;
B[2] = 0;
B[3] = 1;

C = 0;
for j in 0..#3 {
    forall i in D {
        C[i] += A[B[i]];
    }
    A += 1;
    writeln(C);
}
