/*
    What this tests: The forall cannot be nested in a coforall,
    forall, begin or cobegin.
*/


use BlockDist;

proc func(A : [?D], B : [?E], C : [?F])
{
    forall i in B.domain {
        C[i] += A[B[i]];
    }
}


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
    // invalid: A[B[i]] cannot be in an on-statement
    forall j in A.domain {
        forall i in B.domain {
            on Locales[1] {
                C[i] += A[B[i]];
            }

        }
        func(A,B,C);
    }
    A = 1;
    writeln(C);
}

C = 0;
for j in 0..#3 {
    // invalid: A[B[i]] cannot be nested in 2 foralls
    forall j in A.domain { 
        forall i in B.domain {
            C[i] += A[B[i]];
        }
        func(A,B,C);
    }
    A = 1;
    writeln(C);
}

for j in 0..#3 {
    // invalid: A[B[i]] cannot be nested in a coforall
    coforall loc in Locales do on loc {
        forall i in B.domain {
            C[i] += A[B[i]];
        }
        func(A,B,C);
    }
    A = 1;
    writeln(C);
}

for j in 0..#3 {
    // invalid: A[B[i]] cannot be nested in a cobegin
    cobegin {
        writeln("here\n"); 
        forall i in B.domain {
            C[i] += A[B[i]];
        }
        func(A,B,C);
    }
    A = 1;
    writeln(C);
}

for j in 0..#3 {
    // invalid: A[B[i]] cannot be nested in a begin.
    begin {
        forall i in B.domain {
            C[i] += A[B[i]];
        }
        func(A,B,C);
    }
    A = 1;
    writeln(C);
}
