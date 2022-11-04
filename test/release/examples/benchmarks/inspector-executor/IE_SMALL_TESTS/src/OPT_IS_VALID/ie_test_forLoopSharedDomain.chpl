/*
    What this tests: We correctly track things when 
    the forall and inner for loop use the same domain

    
    Expected output on 2 locales:

        inspector on
        inspector on
        inspector on
        inspector on
        4.0 4.0 4.0 4.0
        12.0 12.0 12.0 12.0
        24.0 24.0 24.0 24.0
        40.0 40.0 40.0 40.0
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
        for j in A.domain {
            C[i] += A[B[j]];
        }
    }
    A += 1;
    writeln(C);
}
