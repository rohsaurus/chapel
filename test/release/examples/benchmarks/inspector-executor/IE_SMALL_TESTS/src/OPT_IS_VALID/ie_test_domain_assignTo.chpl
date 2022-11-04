/*
    What this tests: Writing to the domain that B is declared
    over causing the inspector to be turned on.

    
    Expected output on 2 locales:

        inspector on
        inspector on
        inspector on
        inspector on
        inspector on
        1 1 1 1
        3 3 3 3
        6 6 6 6
*/

use BlockDist;

var ZZ = newBlockDom({0..#4});
var YY = newBlockDom({0..#4});
var DD = newBlockDom({0..#4});

var B : [DD] int;
var A : [ZZ] int;
var C : [YY] int;

A = 1;

// Make remote accesses, assuming we're only on 2 locales
B[0] = 2;
B[1] = 3;
B[2] = 0;
B[3] = 1;

DD = newBlockDom({0..#4});

C = 0;
for j in 0..#3 {
    forall i in B.domain {
        var j = i;
        C[i] += A[B[i]];
    }
    A += 1;
    writeln(C);
}
