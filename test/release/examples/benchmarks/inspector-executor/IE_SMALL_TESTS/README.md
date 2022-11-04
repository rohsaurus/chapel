# Small IE Tests

The programs here test various features of the optimization, focusing mostly on correctness checks and other
static analysis features. We have programs that should be considered "valid" and be optimized, and programs that
should trigger some check and abort the optimization.

The directory `latest_good_results/` contains folders of the output from running these tests as well as the
compiler output. It represents that most recent execution of the tests that produced known-good results.

We will outline what each programs is designed to test and its expected output.

# Valid Tests

These are found in `src/OPT_IS_VALID` and are programs that should all "pass" the static checks and be optimized.

* ie\_test\_A\_2d: Tests the case when `A` is a 2-D array, whose indices are tuples.

* ie\_test\_A\_readFrom: Tests the case when `A` is read from within the forall loop.

* ie\_test\_A\_recordsRef: Tests the case when `A` stores records as elements.

* ie\_test\_A\_recordsVar: Same as above but `A[B[i]]` is pulled out as a `var` in the loop.

* ie\_test\_A\_recordsVarInFunc: Same as above but the `var` that corresponds to `A[B[i]]` is passed into a function and accessed (but not modified).

* ie\_test\_A\_writeToAlias: Tests that we can write to an alias of `A` outside of the forall loop.

* ie\_test\_A\_writeToCopy: Tests that we can write to a copy of `A` outside of the forall loop.

* ie\_test\_B\_2d: Tests the case where B is a 2-D array that stores single ints that are used to index into A, which is a 1-D array.

* ie\_test\_B\_validWritesAlias: Tests that we detect a valid write to an alias of `B` outside of the for-loop.

* ie\_test\_B\_validWrites: Tests that we detect a valid write to `B` outside of the for-loop.

* ie\_test\_B\_validWritesDoubleAlias: Tests that we detect a valid write to an alias of an alias to `B` outside of the for-loop.

* ie\_test\_B\_validWritesInForallAlias: Tests that we can detect a valid write to `B` and an alias of `B` that are within a forall
loop that is outside of the outer for-loop.

* ie\_test\_B\_validWritesInLoop: Same as above but without the alias to `B` and the writes are in a for loop.

* ie\_test\_B\_validWritesInWhileLoop: Same as above but the write is within a while loop.

* ie\_test\_B\_WriteOutsideFunc: Tests that we can write to `B` outside of the function that contains the forall loop of interest.

* ie\_test\_B\_writeToRecordVar: Tests when `B` a `ref` to a record field and we have a loop that writes to copies of those 
fields. We should not be turing on the inspector after those writes.

* ie\_test\_domain\_assignTo: Tests that when we write to the domain that `B` is declared over, we turn on the
inspector.

* ie\_test\_domain\_fieldOfRecord: Tests that when modifying the domain field of a record, where the corresponding array is
used for `B`, the inspector is turned on.

* ie\_test\_domain\_validWriteOutsideFunc: Tests that when the domaindsof `A` and `B` are written to outside of the function that 
contains the forall loop, the inspector is turned on.

* ie\_test\_doWhile: Tests that the `forall` can be within an outer do-while statement.

* ie\_test\_forallArr\_validWrites: Tests that writes to the array that the forall iterates over does not cause the inspector
to be turned on. Only writing to the domain of that array matters.

* ie\_test\_forallDom\_validWrites: Tests that when writing to the domain that the forall iterates over, the inspector is
turned on.

* ie\_test\_forallWithIf: Tests that we create the correct stripped down inspector loop when there is an if
statement in the loop, as well as some other constructs.

* ie\_test\_forLoopSharedDomain: Tests that the forall loop and inner for loop can use the same domain (makes sure we
track them correctly).

* ie\_test\_FUNC\_main: Tests that things work correctly when the forall is in a function and we have a `main`
function. We had issues initially with concrete vs. generic functions.

* ie\_test\_MULTI-FUNC" Tests that we can optimize two foralls in two different functions that use the same
`B` array but different `A` arrays.

* ie\_test\_MULTI-FUNC\_ints: Same as above but one of the `A` arrays stores ints and the other stores reals.

* ie\_test\_MULTI-FUNC\_sameArray: Tests that a given array can be used in multiple forall optimizations.

* ie\_test\_MULTI-NO-FUNC: Tests that we can optimize two different foralls that are not in different functions.

* ie\_test\_multipleCallSites: Tests that we can optimize a forall loop in a function that has multiple call sites, each
pass in different `A` and `B` arrays.

* ie\_test\_multipleCallSites2: Same as above but contains a unique pattern of `func(A,B,C); func(A,D,C); func(A,B,C);`.
In this case, it tests that `A` has multiple communication schedules that are uniquely associated with the call sites.

* ie\_test\_nestedForLoops: Tests that we can have nested for-loops in the forall, where `A[B[i]]` is in the inner most
loop.

* ie\_test\_NO-FUNC: Most basic test we have. Single forall with `A[B[i]]` that is not in a function.

* ie\_test\_TripleAccess: Tests that we will only optimize the inner must access in `A[B[C[i]]]`, namely `B[C[i]]`.

* ie\_test\_usingStandaloneDomain: Tests that the forall can iterate over a stand-alone domain `D`.

* ie\_test\_whileLoop: Tests that the `forall` can be enclosed in a `while` loop.

* ie\_test\_someInvalidCallSites: Tests that we invalidate some call sites but others are valid and
optimized. This produces non-deterministic output, so we don't test it with the rest of the tests.

# Not Valid Tests

These are found in `src/OPT_IS_NOT_VALID` and are programs that should all "fail" the 
static checks and not be optimized. As such, their output should match the original 
program's output.

* ie\_test\_AB\_writeTo: Tests that we cannot write to `A` and `B` within the forall.

* ie\_test\_accessOnLHS: Tests that `A[B[i]]` cannot be on the LHS of an operation.

* ie\_test\_A\_definedInLoop: Tests that `A` cannot be defined within the forall loop.

* ie\_test\_A\_invalidAssignToAlias: Tests that we cannot assign to an alias of `A` within the loop.

* ie\_test\_A\_invalidAssignTo: Tests that we cannot assing to `A` within the loop.

* ie\_test\_A\_notArray: Tests that `A` must be an array. **CURRENTLY NOT TESTING** this produces a compiler
error since when we call into our custom parallel iterator, we try to call `A.localSubdomain` which clearly
does not work in this case. We need to put a guard around with part of the optimization.

* ie\_test\_A\_recordsNonPODAccess: Tests that if `A` stores records, all accesses in the forall must be to the POD fields.

* ie\_test\_A\_recordsNonPODAccessInFunc: Same as above but tests the case when the non-POD field access is within a function that is
called from within the forall.

* ie\_test\_A\_refInLoop: Tests that `A` cannot be defined in the loop, even when it is an alias to something outside
of the loop.

* ie\_test\_B\_aliasInForLoop: Tests that `B` cannot be defined in the loop as an alias to something outside of the loop.
This particular case contains an inner for loop in the forall.

* ie\_test\_B\_assignAfterForall: Tests that `B` cannot be modified after the forall.

* ie\_test\_B\_assignBeforeForall: Tests that `B` cannot be modified before the forall.

* ie\_test\_B\_fieldOfRecordInLoop: Tests that `B` cannot be defined in the forall as an alias to the field of a record.

* ie\_test\_B\_invalidAssignToAlias: Tests that we cannot write to an alias of `B` within the forall.

* ie\_test\_B\_invalidAssignTo: Tests that we cannot write to `B` inside of the forall.

* ie\_test\_B\_invalidWriteOutsideFunc: Same as above but the forall is in a function and the write happens outside
of the function.

* ie\_test\_B\_notArray: Tests that `B` must be an array.

* ie\_test\_B\_with\_call: Tests that the index into `B` cannot be an expression other than `i` or a tuple like
`(i,j)`.

* ie\_test\_domain\_assignAfterForall: Tests that we cannot assign to a domain of interest after the forall.

* ie\_test\_domain\_assignBeforeForall: Same as above but the assignment is before the forall.

* ie\_test\_domain\_assignToADomain\_afterForall: Specific tests that we cannot assign to `A`'s domain after the forall.

* ie\_test\_domain\_invalidFieldOfRecordWriteAfterForall: Specific tests that we cannot write to a domain of interest after the forall
when the domain is the field of a record.

* ie\_test\_domain\_invalidFieldOfRecordWriteInForall: Same as above but the write happens within the forall.

* ie\_test\_domain\_invalidWriteOutsideFunc: Tests that we cannot write to a domain of interest when the forall is inside
of a function and the write is outside the function.

* ie\_test\_forallDom\_invalidWrites: Tests that we cannot write to the domain that the forall iterates over after the
forall.

* ie\_test\_forall\_notDistributed: Tests that the forall must iterate over a distributed domain/array.

* ie\_test\_NoForLoop: Tests that the forall must be enclosed inside of an outer for loop.

* ie\_test\_invalidStoreAsRef: Tests that `A[B[i]]` cannot be stored as a `ref`. It must be either
a `const ref` or `var`.

* ie\_test\_invalidedNestedStructures: Tests that the forall cannot be nested in another forall, coforall, cobegin or begin statement.
This produces non-deterministic output, so we don't run it as part of our test suite.

* ie\_test\_writeToSlice: Tests that we cannot get a `ref` to a slice of `B` and then write to it after the `forall`.
