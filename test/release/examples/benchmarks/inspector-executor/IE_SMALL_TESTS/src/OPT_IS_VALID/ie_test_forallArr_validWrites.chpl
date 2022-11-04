/*
    What this tests: Writes to the array that the forall iterates
    over DOES NOT turn the inspector on. Only modifying its domain
    matters.

    
    Expected output on 2 locales:

        inspector on
        inspector on
        inspector on
        inspector on
        D = B
        D[0] = 1
        Starting loop
        4.0 4.0 4.0 4.0
        12.0 12.0 12.0 12.0
        24.0 24.0 24.0 24.0
        40.0 40.0 40.0 40.0
        60.0 60.0 60.0 60.0
        84.0 84.0 84.0 84.0
        112.0 112.0 112.0 112.0
        144.0 144.0 144.0 144.0
        180.0 180.0 180.0 180.0
*/


use BlockDist;

var dom = newBlockDom({0..#4});

var A : [dom] real;
var B : [dom] int;
var C : [dom] real;

var dom2 = newBlockDom({0..#4});
var D : [dom2] int;

A = 1;
D = 1;

// Make remote accesses, assuming we're only on 2 locales
B[0] = 2;
B[1] = 3;
B[2] = 0;
B[3] = 1;

writeln("D = B");
D = B;

writeln("D[0] = 1");
D[0] = 1;

C = 0;
writeln("Starting loop");
for z in 0..#3 {
    D = B;
    for j in 0..#3 {
        forall i in D.domain {
            for k in B.domain {
                C[i] += A[B[k]];
            }
        }
        A += 1;
        writeln(C);
    }
    D = B;
}

D = B;
