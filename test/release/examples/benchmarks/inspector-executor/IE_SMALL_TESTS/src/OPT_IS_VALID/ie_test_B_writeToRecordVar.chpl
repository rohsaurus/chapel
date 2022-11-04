/*
    What this tests: When B a ref to a record field and we have
    a loop that writes to copies of those fields. We should not
    be turing on the inspector after those writes.

    
    Expected output on 2 locales:

        inspector on
        16.0 0.0 0.0 0.0
        16.0 32.0 0.0 0.0
        16.0 32.0 48.0 0.0
        16.0 32.0 48.0 64.0    
*/


use BlockDist;

record Foo {
    var dom : domain(1);
    var arr : [dom] int;
    proc init() {
        this.dom = {0..#4};
    }
}

var dom2 = newBlockDom({0..#4});

var A : [dom2] real;

var recs : [dom2] Foo;
var C = newBlockArr({0..#4}, real);

A = 1;

// Make remote accesses, assuming we're only on 2 locales
for r in recs {
    ref FOO = r.arr;
    FOO = 1;
    FOO[0] = 2;
    FOO[1] = 3;
    FOO[2] = 0;
    FOO[3] = 1;
}

for r in recs {
    var FOO = r.arr;
    FOO = 1;
    FOO[0] = 2;
    FOO[1] = 3;
    FOO[2] = 0;
    FOO[3] = 1;
}

C = 0;
ref B = recs[0].arr;
for j in 0..#4 {
    var temp : real = 0;
    forall r in recs with (+reduce temp) {
        for i in B.domain {
            temp += A[B[i]];
        }
    }
    C[j] += temp;
    A += 1;
    writeln(C);
}
