/*
    What this tests: B cannot be defined in the loop, even if it
    is an alias.
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
        for z in B.domain {
            ref foo = B;
            C[i] += A[foo[z]];
        }
    }
    A += 1;
    writeln(C);
}
