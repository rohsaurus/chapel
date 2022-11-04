/*
    What this tests: B is a reference an array that is the
    field of a record. Modifying the corresponding domain
    field of the record should trigger the inspector.

    
    Expected output on 2 locales:

        inspector on
        inspector on
        16.0 0.0 0.0 0.0
        16.0 32.0 0.0 0.0
        16.0 32.0 48.0 0.0
        16.0 32.0 48.0 64.0
*/

use BlockDist;

record Foo {
    var ZZZ : domain(1);
    var arr : [ZZZ] int;
    proc init() {
        this.ZZZ = {0..#4};
    }
}

var DD = newBlockDom({0..#4});

var A : [DD] real;
var recs : [DD] Foo;
var C = newBlockArr({0..#4}, real);

A = 1;

// Make remote accesses, assuming we're only on 2 locales
for r in recs {
    r.arr = 1;
    r.arr[0] = 2;
    r.arr[1] = 3;
    r.arr[2] = 0;
    r.arr[3] = 1;
}

for r in recs {
    r.ZZZ = {0..#4};
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
