/*
    What this tests: B must be an array.
*/

use BlockDist;

var dom = newBlockDom({0..#4});

var A : [dom] real;
var B : [dom] (int,int);
var C : [dom] real;

A = 1;

// Make remote accesses, assuming we're only on 2 locales
B[0] = (2,0);
B[1] = (3,1);
B[2] = (0,2);
B[3] = (1,3);

C = 0;
for j in 0..#3 {
    forall coord in B {
        ref i = coord(1);
        C[i] += A[coord(0)];
    }
    A += 1;
    writeln(C);
}

