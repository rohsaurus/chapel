/*
 * Copyright 2022 Hewlett Packard Enterprise Development LP
 * Other additional copyright holders may be indicated within.
 *
 * The entirety of this work is licensed under the Apache License,
 * Version 2.0 (the "License"); you may not use this file except
 * in compliance with the License.
 *
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
    File:   InspectorExecutor.chpl
    Date:   12/20/2021
    Author: Thomas Rolinger (tbrolin@cs.umd.edu)

    This is a module that contains various constructs and methods to
    carry out the inspector-executor (IE) optimization. The idea is
    that the actual optimizations (ex: selective data replication)
    will make use of this module, such as the inspector flag.

    As we implement more optimizations that require the IE technique,
    we imagine that this module will build up.
*/

pragma "inspector executor module"
module InspectorExecutor {

    private use ChapelStandard;
    private use BlockDist, CyclicDist, BlockCycDist, ReplicatedDist;

    /**************************************************************************
        Below are procedures that we call from within the compiler. They are
        here to make things easier for some of the checks we need to do.
    **************************************************************************/

    //###########################################################################
    //
    //              Utility Functions (uncategorized)
    //
    //###########################################################################
    // Rather than using a "if staticCheck == true" approach for IE optimization,
    // we will generate a "if staticCheckCallIE(id) == true" check. The ID refers to
    // the unique ID we give to each forall we optimize. During prefolding, if we
    // determine we are invalid, we will find the corresponding call to the below
    // function with the forall and replace it with gFalse. We do the same during
    // post resolution. During post resolution, if we determine we are valid, we
    // can replace the call with gTrue.
    //  
    // This is done to address a weird bug/crash that seems to happen in some cases
    // when we tried to invaliate the optimization during prefolding when we used the
    // variable staticCheck approach.
    proc staticCheckCallIE(id : int) { return true; }

    //###########################################################################
    //
    //              Call-site hashing for the inspector flag
    //
    //###########################################################################
    //
    // procedure to hash an array/domain. We use this when accessing an inspector
    // flag. We need to distinguish between different call sites of a function
    // that contains the forall of interest. This way, turning off B's flag in
    // one call to the function should not turn off "all" of B's flag. Another
    // call site needs to see that B has changed and needs to run the inspector,
    // since that call site may use a different A.
    //
    // To this end, each array/domain doesn't store a single flag. Instead, it
    // is an associative array of flags. We compute a hash of A, B, the forall
    // iterator symbol and the index iterator symbol and concatenate them into
    // a single hash (a tuple). That way, a different call site that has different
    // "values" for these symbols will hash to a different hash.
    //
    // If the thing we try to hash is not an array or domain, we just return -99. In
    // that case, we will abort the optimization during resolution. But we need the
    // code to compile up to that point.
    inline proc arrayIdentityHash(arr : [?D])
    {
        return chpl__defaultHashWrapper(if _isPrivatized(arr._instance) then arr._pid else arr._instance );
    }
    inline proc arrayIdentityHash(dom : domain)
    {
        return chpl__defaultHashWrapper(if _isPrivatized(dom._instance) then dom._pid else dom._instance );
    }
    inline proc arrayIdentityHash(obj)
    {
        return -99;
    }
    // There are two cases to consider: (1) we pass in all four relevant
    // symbols and hash them into the tuple, or (2) indexIter is not
    // applicable, so it isn't passed in. In the case of (2), we still
    // make the 4-element tuple but just set the last element to -1.
    inline proc computeHash(A, B, forallIter, indexIter)
    {
        var retval : (int,int,int,int);
        retval(0) = arrayIdentityHash(A);
        retval(1) = arrayIdentityHash(B);
        retval(2) = arrayIdentityHash(forallIter);
        retval(3) = arrayIdentityHash(indexIter);
        return retval;
    }
    inline proc computeHash(A, B, forallIter)
    {
        var retval : (int,int,int,int);
        retval(0) = arrayIdentityHash(A);
        retval(1) = arrayIdentityHash(B);
        retval(2) = arrayIdentityHash(forallIter);
        retval(3) = -1;
        return retval;
    }

    //###########################################################################
    //
    //              Custom parallel iterator for inspector loop
    //
    //###########################################################################
    //
    // Our optimized inspector loop does not use the standard forall iterator for
    // arrays/domains, where multiple tasks on the same locale may be used to
    // process that locale's elements. Instead, we want to use a coforall-like
    // approach where one task per locale processes the locale's elements. The
    // reason for this is so we can turn off parallel-safety for our replArrays,
    // which use associative domains/arrays. This generally provides us a performance
    // win for the inspector, despite reducing the amount of parallelism.
    //
    // So we define a custom parallel iterator that we use to replace the original
    // forall's iterator. We have the standard serial version that is required and
    // then the parallel version. Furthermore, we have two versions, one for arrays
    // and one for domains.
    //
    // Also note that this will only be applicable for arrays/domains that support
    // the localSubdomain query.
    //
    // If something we are trying to optimize is not an array or domain, we will get
    // a compiler error if we don't match the iterator to something "generic". Our
    // optimization will abort in this case anyways, so it doesn't matter what the
    // iterator does for the non-array/non-domain case.
    iter inspectorIter(obj) {
        yield obj;
    }
    iter inspectorIter(arr : [?D]) {
        for elem in arr{
            yield elem;
        }
    }
    iter inspectorIter(dom : domain) {
        for i in dom {
            yield i;
        }
    }
    iter inspectorIter(param tag : iterKind, const obj) {
        yield obj;
    }
    iter inspectorIter(param tag : iterKind, const arr : [?D]) ref
        where tag == iterKind.standalone {
        if arr.hasSingleLocalSubdomain() {
            coforall loc in Locales do on loc {
                const ref indices = arr.localSubdomain();
                for i in indices {
                    yield arr[i];
                }
            }
        }
        else {
            forall a in arr {
                yield a;
            }
        }
    }
    iter inspectorIter(param tag : iterKind, const dom : domain) ref
        where tag == iterKind.standalone {
        if dom.hasSingleLocalSubdomain() {
            coforall loc in Locales do on loc {
                const ref indices = dom.localSubdomain();
                for i in indices {
                    yield i;
                }
            }
        }
        else {
            forall i in dom {
                yield i;
            }
        }
    }

    //###########################################################################
    //
    //              Compile-time checks regarding arrays/domains
    //
    //###########################################################################
    //
    // Our optimization will insert checks during normalization that will be
    // resolved by the time we get to prefolding. These checks determine some
    // key information regarding the arrays/domains of interest that we need to
    // know to determine whether the optimization is valid to apply.
    //
    // (1) the array A in A[B[i]] must support the locaSubdomain query. This is
    //     also true for the array/domain iterated over by the forall if we are to
    //     use the optimized iterator for the inspector loop.
    //
    // (2) the array/domain iterated over by the forall must be distributed.
    proc chpl__hasSingleLocalSubdomainCheck(A) param
    {
        if isArray(A) || isDomain(A) {
            return A.hasSingleLocalSubdomain();
        }
        else {
            return false;
        }
    }
    // Various param-based procs to determine if a given domain is distributed.
    // We wrap them all up into a single isDistributed() proc that we will use
    // to ensure that the domain being iterated over in the forall is distributed.
    // One version is matched when we pass in an array; the other will match on
    // anything else.
    proc isBlock(D) param return false;
    proc isBlock(D: BlockDom) param return true;
    proc isCyclic(D) param return false;
    proc isCyclic(D: CyclicDom) param return true;
    proc isBlockCyclic(D) param return false;
    proc isBlockCyclic(D: BlockCyclicDom) param return true;
    proc isReplicated(D) param return false;
    proc isReplicated(D: ReplicatedDom) param return true;
    proc chpl__isDistributed(D) param
    {
        return isBlock(D._value)       ||
               isCyclic(D._value)      ||
               isBlockCyclic(D._value) ||
               isReplicated(D._value);
    }
    proc chpl__isDistributed(A : [?D]) param
    {
        return isBlock(D._value)       ||
               isCyclic(D._value)      ||
               isBlockCyclic(D._value) ||
               isReplicated(D._value);
    }


    //###########################################################################
    //
    //              Class to encapsulate the inspector flag
    //
    //###########################################################################
    //
    // For a given forall loop that is optimized via the inspector-executor
    // technique, we have an InspectorFlag object associated with it. Within
    // this object, we have an associative array of bools, where the keys
    // are hashes and the values represent a flag value (on or off). These
    // hashes correspond to information regarding the "parameters" of the
    // optimization. This is only relevant when the forall is in a function
    // with multiple call sites. Each call site with unique arguments should
    // have its own flag for the forall.
    //
    // We then have simple functions that turn the flags on/off and checks
    // the flag.
    var ieID : int = -99; // debugging only
    class InspectorFlag {
        var D : domain((int,int,int,int));
        var inspectorFlags : [D] bool;
    }

    // Compiler calls this during normalization to create the
    // flag object; easier than calling the "new" constructor.
    proc createInspectorFlag() { return new InspectorFlag(); }

    // For a given InspectorFlag object and hash, turn off the
    // flag
    proc inspectorOff(ieFlag : InspectorFlag, hash : (int,int,int,int))
    {
        ieFlag.inspectorFlags[hash] = false;
    }

    // For a given InspectorFlag object, turn off ALL of its flags.
    // This is called after a modification to an array/domain of
    // interest to the optimization. It doesn't matter which call-site
    // (hash) it is related to. A modification to it means any call-site
    // that uses it needs to re-run the inspector.
    //
    // We need to set this up a bit strangely so we can call it during
    // post-resolution. We need to specify the argument as owned and then
    // call inspectorOn one time on a "dummy" object. We added inspectorOn to
    // the well-known functions list. All of this does some "magic" to allow
    // us call insert the calls so late into the compilation process.
    pragma "inspector on"
    proc inspectorOn(ieFlag : owned InspectorFlag)
    {
        /*if ieID == -99 {
            ieID = 0;
        }
        else {
            writeln("inspector on");
        }*/
        ieFlag.inspectorFlags = true;
    }
    var dummyIEFlag123 = new InspectorFlag();
    inspectorOn(dummyIEFlag123);

    // For a given InspectorFlag object and hash, return its flag
    // value (true or false). If we haven't seen the hash yet, it means
    // this is the first time calling doInspector for that hash. If so,
    // we add it to the inspectorFlags.
    proc doInspector(ieFlag : InspectorFlag, hash : (int,int,int,int))
    {
        if !ieFlag.D.contains(hash) {
            ieFlag.D += hash;
            ieFlag.inspectorFlags[hash] = true;
            return true;
        }
        return ieFlag.inspectorFlags[hash];
    }


    //###########################################################################
    //
    //              Class to encapsulate the dyanmic call path flags
    //
    //###########################################################################
    //
    // We need a mechanism to "turn off" an optimized forall-loop at runtime,
    // defaulting to the original forall loop. This is the case when a call path
    // to a function that contains an optimized forall does not have an outer
    // serial loop, or is enclosed in an invalid structure like another forall,
    // coforall, etc. Multiple call paths may share the same call site to the
    // function with the forall, so we can't just eliminate the optimized forall
    // entirely. Instead, we will use two flags to incidate, at runtime, at on
    // the call path to the function we encountered an outer loop and we did not
    // encounter invalid structures. If both are true, we do the optimized forall.
    // If one is false, we do the original forall.
    //
    // These flags are tied to each unique function that has at least one valid
    // forall loop. For such a function, regardless of how many foralls are in
    // it, if the flags are true, then we can do the optimized version of those
    // foralls, and vice versa when the flags are false. The only exception is when
    // the forall in the function is directly nested in an outer loop. In that case,
    // the "has outer loop" check is also true. In any case, the compiler optimization
    // will handle such cases.
    //
    // Below is a class that encapsulates the two flags mentioned above. We store one
    // flag per function that has valid forall loops. We only need to create a single
    // global instance of this class, as it can be used across the entire program/compilation.
    // Similar to the inspectorOn() function, we need to do a few tricks so that we can
    // call the various set/unset methods during post-resolution.
    //
    class DynamicCallPathFlags {
        var numFuncs : int;
        var D : domain(1) = {0..#numFuncs};
        var hasOuterLoop : [D] bool;
        var hasInvalidEnclosingStructure : [D] bool;
    }

    // This is our global instance of DynamicCallPathFlags. All the set/unset methods
    // will explicitly work on this instance; there is no need to pass around a handle
    // to it. We give it a default/dummy value of 1 for numFuncs so we can call the
    // set/unset methods initially. Our compiler optimization will insert a call later
    // that properly set sthe number of functions.
    var gDynamicCallPathFlags = new DynamicCallPathFlags(numFuncs=1);

    // Below are the set/unset methods for the flags. We specify a unique function ID
    // to indicate which function's flags we are setting/unsetting.
    proc setHasOuterLoop(funcID : int)
    {
        /*if funcID != 0 {
            writeln("setHasOuterLoop for functionID=" +funcID:string);
        }*/
        gDynamicCallPathFlags.hasOuterLoop[funcID] = true;
    }
    proc unsetHasOuterLoop(funcID : int)
    {
        /*if funcID != 0 {
            writeln("unsetHasOuterLoop for functionID=" +funcID:string);
        }*/
        gDynamicCallPathFlags.hasOuterLoop[funcID] = false;
    }
    proc setHasInvalidEnclosingStructure(funcID : int)
    {
        /*if funcID != 0 {
            writeln("setHasInvalidEnclosingStructure for functionID=" +funcID:string);
        }*/
        gDynamicCallPathFlags.hasInvalidEnclosingStructure[funcID] = true;
    }
    proc unsetHasInvalidEnclosingStructure(funcID : int)
    {
        /*if funcID != 0 {
            writeln("unsetHasInvalidEnclosingStructure for functionID=" +funcID:string);
        }*/
        gDynamicCallPathFlags.hasInvalidEnclosingStructure[funcID] = false;
    }

    // Below are methods to get/return the flags for a given function ID. Since both
    // must be checked at the same time in all cases, we don't need individual methods
    // for each flag. Instead, we can have a single "isCallPathValid" method. A path is
    // valid if we found an outer loop and we did not find invalid enclosing structures
    inline proc isCallPathValid(funcID : int)
    {
        return gDynamicCallPathFlags.hasOuterLoop[funcID] &&
               !gDynamicCallPathFlags.hasInvalidEnclosingStructure[funcID];
    }

    // Here is the function that the compiler will generate a call to at the end of normalization
    // to properly set the number of functions. It reallocates the flag arrays and sets them to
    // their default values.
    proc setNumFuncsForDynamicCallPathFlags(numFuncs : int)
    {
        gDynamicCallPathFlags.numFuncs = numFuncs;
        gDynamicCallPathFlags.D = {0..#numFuncs};
        gDynamicCallPathFlags.hasOuterLoop = false;
        gDynamicCallPathFlags.hasInvalidEnclosingStructure = false;
    }

    // As mentioned, we need to make some initial calls to the set/unset methods now so
    // that they will be call-able by the compiler in post-resolution.
    setHasOuterLoop(0);
    unsetHasOuterLoop(0);
    setHasInvalidEnclosingStructure(0);
    unsetHasInvalidEnclosingStructure(0);

} /* end of InspectorExecutor module */
