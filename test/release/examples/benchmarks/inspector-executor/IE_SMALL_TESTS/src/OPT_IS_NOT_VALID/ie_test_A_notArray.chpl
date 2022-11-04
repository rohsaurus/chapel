/*
    What this tests: A must be an array. 
*/


use BlockDist;

var dom = newBlockDom({0..#4});

var B : [dom] int;

var A = (1,1,1,1);

var C = newBlockArr({0..#4}, int);

C = 0;

B[0] = 2;
B[1] = 3;
B[2] = 0;
B[3] = 1;

for it in 1..#3 {
    forall i in B.domain {
        C[i] += A(B[i]);
    }
    A = (it+1,it+1,it+1,it+1);
    writeln(C);
}
