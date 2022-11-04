/*
    What this tests: Having multiple/nested for-loops, where the
    inner most loop contains A[B[i]].


    Expected output on 2 locales:

        inspector on
        inspector on
        inspector on
        inspector on
        64.0 64.0 64.0 64.0
        192.0 192.0 192.0 192.0
        384.0 384.0 384.0 384.0
        640.0 640.0 640.0 640.0
*/

use BlockDist;

var D = newBlockDom({0..#4});

var A : [D] real;
var B : [D] int;
var C : [D] real;

A = 1;

// Make remote accesses, assuming we're only on 2 locales
B[0] = 2;
B[1] = 3;
B[2] = 0;
B[3] = 1;

C = 0;
for it in 0..#4 {
    forall i in A.domain {
        for j in B.domain {
            for k in A.domain {
                for l in B.domain {
                    C[i] += A[B[l]];
                }
            }
        }
    }
    A += 1;
    writeln(C);
}
