/*
    What this tests: supporting the case when the array A is
    2-D. The index into A is still a value from an array B,
    which is also a 2-D array. But the values in B are tuples.
    In other words, we still require that the index into
    A to a single index variable (i.e., not A[i,j].

    
    Expected output on 2 locales:
    
        inspector on
        inspector on
        inspector on
        inspector on
        1 1
        1 1
        3 3
        3 3
        6 6
        6 6
*/

use BlockDist;

var dom = newBlockDom({0..#2, 0..#2});

var A : [dom] int;
var B : [dom] (int,int);


var C = newBlockArr({0..#2,0..#2}, int);

A = 1;

C = 0;

B[0,0] = (1,0);
B[0,1] = (1,1);
B[1,0] = (0,0);
B[1,1] = (0,1);


for it in 0..#3 {
    forall (i,j) in B.domain {
        C[i,j] += A[B[i,j]];
    }
    A += 1;
    writeln(C);
}
