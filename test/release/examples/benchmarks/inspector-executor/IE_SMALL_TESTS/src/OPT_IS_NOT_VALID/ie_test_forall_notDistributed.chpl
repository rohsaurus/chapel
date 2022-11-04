/*
    What this tests: The forall must iterate over a distributed
    domain/array.
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

C = 0;
for j in 0..#3 {
    forall i in 0..#4 {
        var j = i;
        C[i] += A[B[i]];
    }
    writeln(C);
}

var Z : [{0..#4}] int;
for j in 0..#3 {
    forall i in Z {
        for j in B.domain {
            C[i] += A[B[j]];
        }
    }
    writeln(C);
}
