/*
    What this tests: That we can write to B and an alias of B within a forall
    loop that is outside of the outer for-loop. We should see an inspectorOn call
    placed after this forall loop.

    
    Expected output on 2 locales:

        inspector on
        1.0 1.0 1.0 1.0 1.0 1.0 1.0 1.0 1.0 1.0 1.0 1.0 1.0 1.0 1.0 1.0
        3.0 3.0 3.0 3.0 3.0 3.0 3.0 3.0 3.0 3.0 3.0 3.0 3.0 3.0 3.0 3.0
        6.0 6.0 6.0 6.0 6.0 6.0 6.0 6.0 6.0 6.0 6.0 6.0 6.0 6.0 6.0 6.0
        inspector on
        10.0 10.0 10.0 10.0 10.0 10.0 10.0 10.0 10.0 10.0 10.0 10.0 10.0 10.0 10.0 10.0
        15.0 15.0 15.0 15.0 15.0 15.0 15.0 15.0 15.0 15.0 15.0 15.0 15.0 15.0 15.0 15.0
        21.0 21.0 21.0 21.0 21.0 21.0 21.0 21.0 21.0 21.0 21.0 21.0 21.0 21.0 21.0 21.0
        inspector on
        28.0 28.0 28.0 28.0 28.0 28.0 28.0 28.0 28.0 28.0 28.0 28.0 28.0 28.0 28.0 28.0
        36.0 36.0 36.0 36.0 36.0 36.0 36.0 36.0 36.0 36.0 36.0 36.0 36.0 36.0 36.0 36.0
        45.0 45.0 45.0 45.0 45.0 45.0 45.0 45.0 45.0 45.0 45.0 45.0 45.0 45.0 45.0 45.0
        inspector on
        55.0 55.0 55.0 55.0 55.0 55.0 55.0 55.0 55.0 55.0 55.0 55.0 55.0 55.0 55.0 55.0
        66.0 66.0 66.0 66.0 66.0 66.0 66.0 66.0 66.0 66.0 66.0 66.0 66.0 66.0 66.0 66.0
        78.0 78.0 78.0 78.0 78.0 78.0 78.0 78.0 78.0 78.0 78.0 78.0 78.0 78.0 78.0 78.0
        inspector on
*/


use BlockDist;

var dom = newBlockDom({0..#16});

var A : [dom] real;
var B : [dom] int;
var C : [dom] real;

var D = newBlockArr({0..#16}, int);

A = 1;

// Make remote accesses, assuming we're only on 2 locales
D = 1;
D[0] = 2;
D[1] = 3;
D[2] = 0;
D[3] = 1;
forall j in D.domain {
    ref FOO = B;
    FOO[j] = D[j];
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
    forall i in B.domain {
        ref BAR = B;
        BAR[i] = i;
        B[0] = i;
    }
}
