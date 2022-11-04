/*
    What this tests: B cannot be defined in the forall. This
    case has B referencing the field of a record.
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
    r.arr = 1;
    r.arr[0] = 2;
    r.arr[1] = 3;
    r.arr[2] = 0;
    r.arr[3] = 1;
}

C = 0;
for j in 0..#4 {
    var temp : real = 0;
    forall r in recs with (+reduce temp) {
        ref B = r.arr;
        for i in B.domain {
            temp += A[B[i]];
        }
    }
    C[j] += temp;
    A += 1;
    writeln(C);
}
