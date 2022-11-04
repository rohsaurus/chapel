/*
    What this tests: That we can write to B outside of the
    for-loop. We should see an inspectorOn call after these writes.

    
    Expected output on 2 locales:

        inspector on
        inspector on
        inspector on
        inspector on
        1.0 1.0 1.0 1.0
        3.0 3.0 3.0 3.0
        6.0 6.0 6.0 6.0
        inspector on
        10.0 10.0 10.0 10.0
        15.0 15.0 15.0 15.0
        21.0 21.0 21.0 21.0
        inspector on
        28.0 28.0 28.0 28.0
        36.0 36.0 36.0 36.0
        45.0 45.0 45.0 45.0
        inspector on
        55.0 55.0 55.0 55.0
        66.0 66.0 66.0 66.0
        78.0 78.0 78.0 78.0
        inspector on
*/

use BlockDist;

var dom = newBlockDom({0..#4});

var A : [dom] real;
var B : [dom] int;

var C = newBlockArr({0..#4}, real);

A = 1;

// Make remote accesses, assuming we're only on 2 locales
B[0] = 2;
B[1] = 3;
B[2] = 0;
B[3] = 1;

C = 0;
for it in 0..#4 {
    for j in 0..#3 {
        forall i in B.domain {
            C[i] += A[B[i]];
        }
        A += 1;
        writeln(C);
    }
    B[it] = it;
}
