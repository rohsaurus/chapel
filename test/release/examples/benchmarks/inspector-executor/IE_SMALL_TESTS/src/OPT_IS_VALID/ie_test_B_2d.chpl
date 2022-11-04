/*
    What this tests: supporting the case where B is a 2-D array
    that stores single ints that are used to index into A, which
    is a 1-D array.

    
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

var dom = newBlockDom({0..#4});
var dom2 = newBlockDom({0..#2,0..#2});

var A : [dom] int;
var B : [dom2] int;

var C = newBlockArr({0..#2,0..#2}, int);

A = 1;

C = 0;

B[0,0] = 2;
B[0,1] = 3;
B[1,0] = 0;
B[1,1] = 1;

for it in 0..#3 {
    forall (i,j) in B.domain {
        C[i,j] += A[B[i,j]];
    }
    A += 1;
    writeln(C);
}
