/*
    What this tests: Optimize two different forall loops that
    are not in different functions.


    Expected output on 2 locales:

        inspector on
        inspector on
        inspector on
        inspector on
        inspector on
        inspector on
        inspector on
        inspector on
        1.0 1.0 1.0 1.0
        3.0 3.0 3.0 3.0
        6.0 6.0 6.0 6.0
        inspector on
        inspector on
        inspector on
        inspector on
        inspector on
        inspector on
        inspector on
        inspector on
        2.0 2.0 2.0 2.0
        3.0 3.0 3.0 3.0
        4.0 4.0 4.0 4.0    
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
for j in 0..#3 {
    forall i in B.domain {
        C[i] += A[B[i]];
    }
    A += 1;
    writeln(C);
}

B[0] = 1;
B[1] = 3;
B[2] = 0;
B[3] = 2;

A = 0;
C = 1;
for j in 0..#3 {
    forall i in B.domain {
        A[i] += C[B[i]];
    }
    C += 1;
    writeln(C);
}


