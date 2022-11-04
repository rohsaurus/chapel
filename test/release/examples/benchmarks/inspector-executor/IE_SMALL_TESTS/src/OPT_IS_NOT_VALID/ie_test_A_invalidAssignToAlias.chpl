/*
    What this tests: We cannot assign to A in a loop, or an alias to A.
*/


use BlockDist;

var dom = newBlockDom({0..#4});

var A : [dom] real;
var B : [dom] int;
var C : [dom] real;

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
        ref FOO = A;
        FOO = 1;
    }
    A = 1;
    writeln(C);
}
