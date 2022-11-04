/*
    What this tests: supporting A with records as element.
    We should only be aggregating the fields that are accessed
    in the forall, namely valueR and valueI. This test specifically
    looks at the case when A[B[i]] is pulled out as a var.

    
    Expected output on 2 locales:
   
        inspector on
        20.0 0.0 0.0 0.0
        20.0 40.0 0.0 0.0
        20.0 40.0 60.0 0.0
        20.0 40.0 60.0 80.0 

*/

use BlockDist;

record Foo {
    var dom : domain(1);
    var valueR : real;
    var valueI : int;
    var arr : [dom] int;
    proc init() {
        this.dom = {0..#4};
    }
}

var dom2 = newBlockDom({0..#4});

var A : [dom2] Foo;

var C = newBlockArr({0..#4}, real);

// Make remote accesses, assuming we're only on 2 locales
for r in A {
    r.valueR = 1.0;
    r.valueI = 1;
    r.arr = 1;
    r.arr[0] = 2;
    r.arr[1] = 3;
    r.arr[2] = 0;
    r.arr[3] = 1;
}

C = 0;
ref B = A[0].arr;
for j in 0..#4 {
    var tempR : real = 0;
    var tempI : int = 0;
    forall r in A with (+reduce tempR, +reduce tempI) {
        for i in B.domain {
            var t = A[B[i]];
            tempR += t.valueR;
            tempI = t.valueI;
        }
    }
    C[j] += tempR;
    C[j] += tempI:real;
    for r in A {
      r.valueR += 1.0;
      r.valueI += 1;
    }
    writeln(C);
}
