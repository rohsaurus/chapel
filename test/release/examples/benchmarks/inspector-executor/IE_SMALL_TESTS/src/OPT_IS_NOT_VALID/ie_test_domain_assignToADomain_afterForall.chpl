/*
    What this tests: Cannot write to A's domain after forall
*/

use BlockDist;

var dom = newBlockDom({0..#4});
var dom2 = newBlockDom({0..#4});

var A : [dom2] real;
var B : [dom] int;
var C = newBlockArr({0..#4}, real);
var D = newBlockArr({0..#4}, real);

A = 1;

// Make remote accesses, assuming we're only on 2 locales
B[0] = 2;
B[1] = 3;
B[2] = 0;
B[3] = 1;

C = 0;
for j in 0..#3 {
    forall i in B.domain {
        var j = i;
        C[i] += A[B[i]];
    }
    A += 1; // valid, does not need to re-run inspector
    writeln(C);
    dom2 = newBlockDom({0..#4}); // invalid; would require inspector to be re ran
}
