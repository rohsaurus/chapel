/*
    What this tests: That we can write to B in a normal for-loop that is
    outside of the outer for-loop. We should have a single call to 
    inspectorOn after this loop.

    
    Expected output on 2 locales:
    
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
var C : [dom] real;

var D = newBlockArr({0..#4}, int);

A = 1;

// Make remote accesses, assuming we're only on 2 locales
D[0] = 2;
D[1] = 3;
D[2] = 0;
D[3] = 1;
for j in D.domain {
    B[j] = D[j];
}

C = 0;
for it in 0..#4 {
    for j in 0..#3 {
        forall i in B.domain {
            C[i] += A[B[i]];
        }
        A += 1;
        writeln(C);
    }
    for i in D.domain {
        B[i] = B[(i+1)%4];
    }
}
