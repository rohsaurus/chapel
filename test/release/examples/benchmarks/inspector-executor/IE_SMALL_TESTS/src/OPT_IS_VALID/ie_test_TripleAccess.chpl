/*
    What this tests: We only optimize the inner-most
    access B[C[i]].


    Expected output on 2 locales:

        inspector on
        inspector on
        inspector on
        inspector on
        2 3 0 1
        2 3 0 1
        2 3 0 1
*/

use BlockDist;

var dom = newBlockDom({0..#4});

var A : [dom] real;
var B : [dom] int;
var C : [dom] int;

var D = newBlockArr({0..#4}, real);

A = 1;
B = 1;

D = 0;

C[0] = 2;
C[1] = 3;
C[2] = 0;
C[3] = 1;

B[0] = 2;
B[1] = 3;
B[2] = 0;
B[3] = 1;

for it in 1..#3 {
    forall i in C.domain {
        D[i] += A[B[C[i]]];
    }
    A += 1;
    writeln(C);
}
