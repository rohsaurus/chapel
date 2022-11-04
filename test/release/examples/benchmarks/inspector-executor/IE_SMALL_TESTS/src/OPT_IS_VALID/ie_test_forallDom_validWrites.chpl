/*
    What this tests: Writes to the domain that is iterated
    over in the forall cause the inspector to be turned on.

    
    Expected output on 2 locales:

        inspector on
        inspector on
        inspector on
        inspector on
        inspector on
        4.0 4.0 4.0 4.0
        12.0 12.0 12.0 12.0
        24.0 24.0 24.0 24.0
        inspector on
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
}

dom2 = newBlockDom({0..#4});
