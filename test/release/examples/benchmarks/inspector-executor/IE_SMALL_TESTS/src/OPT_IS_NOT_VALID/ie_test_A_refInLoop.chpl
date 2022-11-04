/*
    What this tests: A cannot be defined in the loop, even if it is a ref
    to something outside of the loop.
*/


use BlockDist;

var dom = newBlockDom({0..#4});

var A : [dom] real;
var B : [dom] int;
var C : [dom] real;

// Make remote accesses, assuming we're only on 2 locales
B[0] = 2;
B[1] = 3;
B[2] = 0;
B[3] = 1;

A = 1;

C = 0;
for j in 0..#3 {
    forall i in B.domain {
        var j = i;
        ref A2 = A;
        C[i] += A2[B[i]];
    }
    A = 1;
    writeln(C);
}
