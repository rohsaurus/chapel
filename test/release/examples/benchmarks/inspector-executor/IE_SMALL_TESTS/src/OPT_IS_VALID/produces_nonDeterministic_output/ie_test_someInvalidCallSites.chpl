/*
    What this tests: Some call sites can be invalid, and they will call
    into cloned functions that are not optimized.

    Expected output:
    
        This will produce different output each time it runs,
        since the forall is executed by multiple tasks at the
        same time.

*/

use BlockDist;

proc func(A : [?E], B : [?D], C)
{
  forall i in B.domain {
      C[i] += A[B[i]];
  }
  writeln(C);
}

var dom = newBlockDom({0..#4});
var dom2 = newBlockDom({0..#4});
var dom3 = newBlockDom({0..#4});

var A1 : [dom] real;
var B1 : [dom] int;
var C1 : [dom] real;

var A2 : [dom2] real;
var B2 : [dom2] int;
var C2 : [dom2] real;

var A3 : [dom2] real;
var B3 : [dom2] int;
var C3 : [dom2] real;

var A4 : [dom2] real;
var B4 : [dom2] int;
var C4 : [dom2] real;

var A5 : [dom2] real;
var B5 : [dom2] int;
var C5 : [dom2] real;

var A6 : [dom2] real;
var B6 : [dom2] int;
var C6 : [dom2] real;


A1 = 1;
B1[0] = 2;
B1[1] = 3;
B1[2] = 0;
B1[3] = 1;
C1 = 0;

// Invall call site because there is no enclosing for-loop
func(A6, B6, C6);

// Invalid call site due to being enclosed in another forall
for j in 0..#3 {
    forall k in dom {
        func(A2, B2, C2);
    }
    A2 += 1;
}

// Invalid call site due to being enclosed in a coforall
for j in 0..#3 {
    coforall loc in Locales do on loc {
        func(A3, B3, C3);
    }
    A3 += 1;
}

// Invalid call site due to being enclosed in a cobegin
for j in 0..#3 {
    cobegin {
        writeln("here");
        func(A4, B4, C4);
    }
    A4 += 1;
}

// Invalid call site due to being enclosed in a begin
for j in 0..#3 {
    begin {
        func(A5, B5, C5);
    }
    A5 += 1;
}

// Valid call site
for j in 0..#3 {
    func(A1, B1, C1);
    A1 += 1;
}
