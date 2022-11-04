/*
    What this tests: Cannot modify the forall domain within the
    forall.
*/

use BlockDist;

var dom = newBlockDom({0..#4});

var A : [dom] real;
var B : [dom] int;
var C : [dom] real;

var dom2 = newBlockDom({0..#4});
var D : [dom2] int;

A = 1;

// Make remote accesses, assuming we're only on 2 locales
B[0] = 2;
B[1] = 3;
B[2] = 0;
B[3] = 1;

dom2 = newBlockDom({0..#4});

C = 0;
for j in 0..#3 {
    forall i in D.domain {
        for k in B.domain {
            C[i] += A[B[k]];
        }
    }
    A += 1;
    writeln(C);
    dom2 = newBlockDom({0..#4});
}

dom2 = newBlockDom({0..#4});
