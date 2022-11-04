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
    File:   AdaptiveRemoteCachePrefetching.chpl
    Date:   09/9/2022
    Author: Thomas Rolinger (tbrolin@cs.umd.edu)

    This module contains various utilities for performing
    adaptive prefetching for the remote cache, such as custom
    iterators that the compiler optimization will insert.
*/

module AdaptiveRemoteCachePrefetching {

    private use ChapelStandard;
    use Reflection;

    // The default prefetch distance that all distances start as.
    config const DEFAULT_PREFETCH_DISTANCE = 8; 

    // The default number of bytes to prefetch. Since all prefetches are
    // rounded by 64 byte cache lines, we can just leave this as some default
    // value. When we encounter record-field accesses, we issue separate prefetches
    // for each field, so we don't have to try to generate a single prefetch that
    // "captures" each field. Now, we could have a case where we are prefetching
    // a data type that is more than 64 bytes but we'll ignore that for now. We
    // are usually dealing with primitives (ints, reals, bool).
    config const DEFAULT_PREFETCH_SIZE = 4;

    // Some defaults associated with our approach to adjusting the prefetch distance.
    //
    //  MAX_PREFETCH_DISTANCE: the maximum value we will increase the distance to
    //
    //  MIN_PREFETCH_DISTANCE: the minimum value we will decrease the distance to
    //
    //  MAX_WINDOW: how many "windows" must elapse before we decrease the distance
    //
    //  PREFETCH_SAMPLE_RATIO: percentage of the loop iterations that must elapse
    //                         before we will attempt to adjust the distance.
    //
    //  LATE_PREFETCH_TOLERANCE: percentage of prefetches that are allowed to be
    //                           late. Default is 10%
    //
    //  TARGET_PREFETCHES: specifies which type of prefetches our adaptive
    //                     algorithm will focus on: late/waited-on (0), early/unused (1)
    //                     constant (2). This is a compile-time cosntant/param since
    //                     it is used to match on the adjustment procedure.
    //
    config const MAX_PREFETCH_DISTANCE = 256;
    config const MIN_PREFETCH_DISTANCE = 1;
    config const MAX_WINDOW = 16;
    config const PREFETCH_SAMPLE_RATIO = 0.1;
    config const LATE_PREFETCH_TOLERANCE = 10;
    config param TARGET_PREFETCHES = 0;

    //###########################################################################
    //
    //                            Prefetch Counters
    //
    //###########################################################################
    //
    // Below are various functions to interact with the per-cache prefetch 
    // counters that we added to the remote cache. These counters are part of the
    // C struct/code that implements Chapel's remote cache. Each core has its own
    // remote cache, and each remote cache has its own counters for the number of
    // prefetches issued, how many prefetches were unused and how many prefetches
    // had to be waited on. For our optimization, we'll want the following
    // functionality:
    //
    //      (1) reset counters across all caches
    //      (2) get counters for a given cache
    //      (3) get counters across all caches (sum reduce them)
    //
    // (1) and (2) are the most important for the optimization, while (3) is just
    // for debugging purposes. The tricky part is that when we are outside of
    // the forall being optimized, how do we "get" to the remote caches? The
    // easiest way is to just spawn a task on each core and then call the C
    // functions we created to access that core's remote cache counters.
    //
    // extern for the C functions we will call
    extern proc reset_per_cache_prefetch_counters();
    extern proc get_per_cache_num_prefetches() : int;
    extern proc get_per_cache_num_prefetches_unused() : int;
    extern proc get_per_cache_num_prefetches_waited() : int;
    
    inline proc reset_prefetch_counters()
    {
        coforall loc in Locales do on loc {
            coforall tid in 1..loc.maxTaskPar {
                reset_per_cache_prefetch_counters();
            }
        }   
    }
    inline proc get_cache_num_prefetches()
    {
        return get_per_cache_num_prefetches();
    }
    inline proc get_cache_num_prefetches_unused()
    {
        return get_per_cache_num_prefetches_unused();
    }
    inline proc get_cache_num_prefetches_waited()
    {
        return get_per_cache_num_prefetches_waited();
    }
    // For debugging: get counters across all caches
    inline proc get_all_cache_prefetch_counters()
    {
        var num_prefetches = 0;
        var num_prefetches_unused = 0;
        var num_prefetches_waited = 0;
        coforall loc in Locales with (+reduce num_prefetches,
                                      +reduce num_prefetches_unused,
                                      +reduce num_prefetches_waited)
        {
            on loc {
                coforall tid in 1..loc.maxTaskPar with (+reduce num_prefetches,
                                                        +reduce num_prefetches_unused,
                                                        +reduce num_prefetches_waited)
                {
                    num_prefetches += get_cache_num_prefetches();
                    num_prefetches_unused += get_cache_num_prefetches_unused();
                    num_prefetches_waited += get_cache_num_prefetches_waited();
                }
            }
        }
        return (num_prefetches, num_prefetches_unused, num_prefetches_waited);
    }

    //###########################################################################
    //
    //                            Custom iterators
    //
    //###########################################################################
    //
    // The loop that contains the access we are prefetching (call it A[B[i]]) needs
    // to be modified by the compiler. Specifically, we "look ahead" some number of
    // iterations of the loop. The amount of look ahead is the prefetch distance.
    // However, not all loops will yield index variables in the range 0,1,2,...,N.
    // If the loop is something like "for i in Array" and Array contains elements
    // like 1.4, -15.0, and 124.0, then we can't just say "prefetch A[B[i+prefetchDistance]]".
    // What we want to do is something like "for (i,idx) in zip(Array, Array.domain)" and then
    // use "idx" in our prefetch calculation. But it gets more tricky, as the array's domain
    // may have a stride that is NOT 1. So we want is "prefetch A[B[i+(prefetchDistance*stride)]]".
    //
    // That is the basic idea of why we are doing custom iterators: we want to expose the
    // loop stride and index variable when we are iterating over arrays. If we are iterating
    // over domains, it is pretty straightforward since we already have the loop index we need.
    //
    // Since we rely on having a stride, we DO NOT support prefetching if we are iterating over
    // an associative domain or array, or something that is not an array or domain at all.
    //
    // The basic idea of the iterators below is to match on non-associative arrays and domains
    // and perform the zippered iterator. If the loop iterates over an array, we will yield the
    // array element (which is what the loop was already yielding) and the corresponding index.
    // If the loop iterates over a domain, we will still yield a tuple but it will be redundant
    // (it will contain two copies of the index). We do this because when we apply this tranformation
    // within the compiler, we don't know whether "A" in "for i in A" is an array or domain yet.
    // So we need the transformation to work for both at this point. The same goes for the case when
    // "A" is not an array or domain; we will just yield (i,i) from A.
    //
    // We also have forall/parallel versions of these iterators when we are dealing with forall loops.
    // We also have versions that pass in a by-clause, where that version of the iterator will use
    // "by" in the loop. Note that a by-clause cannot be applied to an array, so we don't handle that.
    // If that was in the program, it is an error on the user for doing so. However, we will catch
    // it here and raise the error.
    //
    // We use the "_build_tuple_always_allow_ref" function when creating and returning the tuples
    // because we need to ensure that the original "thing" that was yielded by the loop can be
    // used as intended in the loop. For example, in "for elem in Arr", elem is a ref so it can
    // be modified in the loop. If we just returned (elem,idx) from the iterator, then the elem
    // that is now available is a copy. Note that just because we use this function doesn't mean
    // we all of the sudden allow for a domain index to be modified or something; that is still
    // not allowed.

    // this is matched when we are not iterating over an array or domain
    iter prefetchIter(obj) {
        for i in obj {
            yield _build_tuple_always_allow_ref(i,i);
        }
    }
    iter prefetchIter(obj, const byClause : int) {
        for i in obj by byClause {
            yield _build_tuple_always_allow_ref(i,i);
        }
    }
    // this is matched when we are iterating over a non-associative array
    iter prefetchIter(arr : [?D]) where !arr.domain.isAssociative() {
        for (elem,idx) in zip(arr, arr.domain) {
            yield _build_tuple_always_allow_ref(elem, idx);
        }
    }
    // if the original loop attempted to have a by-clause and iterate over an array,
    // that is a compiler error. To allow our optimization to continue on during
    // normalizaton, where we don't know if we have an array or not, we'll just raise
    // the compiler error here.
    iter prefetchIter(arr : [?D], const byClause : int) where !arr.domain.isAssociative() {
        compilerError("cannot apply 'by' to '", arr.type:string, "'");
    }
    // this is matched when we are iterating over a non-associative domain
    iter prefetchIter(dom : domain) where !dom.isAssociative() {
        for idx in dom {
            yield _build_tuple_always_allow_ref(idx,idx);
        }
    }
    iter prefetchIter(dom : domain, const byClause : int) where !dom.isAssociative() {
        for idx in dom by byClause {
            yield _build_tuple_always_allow_ref(idx,idx);
        }
    }
    // Here are the forall versions
    iter prefetchIter(param tag : iterKind, const obj) {
        forall i in obj {
            yield _build_tuple_always_allow_ref(i,i);
        }
    }
    iter prefetchIter(param tag : iterKind, const obj, const byClause : int) {
        forall i in obj by byClause {
            yield _build_tuple_always_allow_ref(i,i);
        }
    }
    iter prefetchIter(param tag : iterKind, const arr : [?D]) where tag == iterKind.standalone
                                                                    && !arr.domain.isAssociative() {
        forall (elem,idx) in zip(arr, arr.domain) {
            yield _build_tuple_always_allow_ref(elem,idx);
        }
    }
    iter prefetchIter(param tag : iterKind, const arr : [?D], const byClause : int) where tag == iterKind.standalone
                                                                                    && !arr.domain.isAssociative() {
        compilerError("cannot apply 'by' to '", arr.type:string, "'");
    }
    iter prefetchIter(param tag : iterKind, const dom : domain) where tag == iterKind.standalone
                                                                      && !dom.isAssociative() {
        forall idx in dom {
            yield _build_tuple_always_allow_ref(idx,idx);
        }
    }
    iter prefetchIter(param tag : iterKind, const dom : domain, const byClause : int) where tag == iterKind.standalone
                                                                                      && !dom.isAssociative() {
        forall idx in dom by byClause{
            yield _build_tuple_always_allow_ref(idx,idx);
        }
    }


    //###########################################################################
    //
    //                            Prefetch Parameter Calculation
    //
    //###########################################################################
    //
    // These functions are a utility that compute some useful prefetching parameters
    // for us. The compiler inserts call to them right before the loop that contains
    // the prefetch access. That way, the compiler can use them in various calculations,
    // such offseting the index by the prefetch distance and knowing the last valid index
    // in the loop.
    //

    // ##################### Extracting the stride of the loop #######################
    //
    // This is called when the loop did not have an explicit stride but was iterating
    // over an array/domain. In that case, the stride is whatever the stride is of
    // the underlying domain for the array, or just the stride of the domain if we
    // had a domain rather than an array. We match on the different possibilities.
    inline proc getLoopStride(const arr : [?D]) const where !arr.domain.isAssociative()
    {
        return arr.domain.stride;
    }
    inline proc getLoopStride(const dom : domain) const where !dom.isAssociative()
    {
        return dom.stride;
    }
    // This is called in the same cases above but when there was an explicit stride via a
    // "by" clause. In this case, the ultimate stride of the loop is equal to the array/domain
    // stride multiplied by the "by" clause stride. We assume that the byStride is an int.
    inline proc getLoopStride(const arr : [?D], const byStride : int) const where !arr.domain.isAssociative()
    {
        return arr.domain.stride * byStride;   
    }
    inline proc getLoopStride(const dom : domain, const byStride : int) const where !dom.isAssociative()
    {
        return dom.stride * byStride;
    }
    // This is called when we iterated over ranges without an explicit by-stride. So we
    // just return 1.
    inline proc getLoopStride() const
    {
        return 1;
    }
    // Same as above but when the range did have a by-stride
    inline proc getLoopStride(const byStride : int) const 
    {
        return byStride;
    }
    // Finally, catch-call for things we won't end up optimizing because we didn't have an
    // array or domain (or they were associative arrays/domains). So just return 1.
    inline proc getLoopStride(obj) const { return -1; }
    inline proc getLoopStride(obj, byStride) const { return -1; }

    // ##################### Computing the last index of the loop #######################
    //
    // When iterating over an array or domain, the last valid index of the loop is
    // the "high" field of the underlying domain.
    inline proc getLastLoopIndex(const arr : [?D]) const where !arr.domain.isAssociative()
    {
        return arr.domain.high;
    }
    inline proc getLastLoopIndex(const dom : domain) const where !dom.isAssociative()
    {
        return dom.high;
    }
    // These compute the last valid index of the range when the loop iterates over
    // something like 0..N. We pass in whatever "N" was and return that. The compiler
    // already has the expression for N, but this is just a way for us to get it stored
    // in a variable that matches what all the other cases will have, so the rest of the
    // code transformations will be more alike.
    inline proc getLastLoopIndexSimpleRange(const rangeEnd) const
    {
        return rangeEnd;
    }   
    // Same as above but the case when we have 0..<N. In this case, the end of the range is
    // N-1. What we pass in here via the compiler is the CallExpr to chpl__nudgeHighBound,
    // which will do the -1 for us.
    inline proc getLastLoopIndexNudgeHigh(const rangeEnd) const
    {
        return rangeEnd;
    }
    // Finally, this handles the case for start..#end. The generalized formula for the end of
    // the range is "start + end - 1". For example, if we had 10..#5, the loop will yield the
    // values "10, 11, 12, 13, 14".
    inline proc getLastLoopIndexCountOp(const rangeStart, const rangeEnd) const
    {
        return rangeStart + rangeEnd - 1;
    }
    // Catch all for when we didn't have a valid array/domain
    inline proc getLastLoopIndex(obj) 
    {
        return -1;
    }
    // ##################### Computing the first index of the loop #######################
    // We only need to do this when iterating over an array/domain, and we just return
    // domain.low. When we have ranges, we already extracted the Expr that represents the
    // start of the loop.
    inline proc getFirstLoopIndex(const arr : [?D]) const where !arr.domain.isAssociative()
    {
        return arr.domain.low;
    }
    inline proc getFirstLoopIndex(const dom : domain) const where !dom.isAssociative()
    {
        return dom.low;
    }
    inline proc getFirstLoopIndex(obj)
    {
        return -1;
    }

    //###########################################################################
    //
    //                           Adjusting Prefetch Distance
    //
    //###########################################################################
    //
    // This procedure determines the sample size for when we do prefetch distance
    // adjustment. We want to adjust the distance every so many iterations of the
    // loop that contains the prefetched access. In general, we want the sample
    // size to be PREFETCH_SAMPLE_RATIO of the number of iterations assigned to 
    // a task. When we have a forall with an inner for-loop which contains the access, 
    // we compute this relative to the for-loop's iterations. Since only one task 
    // executes this for-loop, we don't have to do anything too complicated. However, 
    // if we have a forall only, then we want to determine how many iterations are given 
    // to each task, and use that for the calculation. We also need to consider things like
    // the loop stride when determining how many iterations it has.
    //
    // "end" here refers to lastValidIndex from getLastLoopIndex().
    // The assumption is that the loop is [start,...,end], so the bounds
    // are inclusive. So the number of iterations is equal to (end-start)+1.
    // When factoring in the stride, we divide that by the stride.
    inline proc getPrefetchSampleSizeForLoop(const start : int, const end : int, const stride : int)
    {
        const numIters = ((end - start)+1) / stride;
        const sampleSize = (numIters * PREFETCH_SAMPLE_RATIO):int;
        // If we don't have enough iterations to get a sample size that is at least 1,
        // just return numIters; this ensures we'll never do prefetch adjustments.
        if sampleSize == 0 {
            return numIters;
        }
        else {
            return sampleSize;
        }
    }
    // version when we have a forall
    inline proc getPrefetchSampleSizeForall(const start : int, const end : int, const stride : int)
    {
        const totalNumIters = ((end - start)+1) / stride;
        // totalNumIters is total number of iterations of the forall. We care about the number of
        // iterations that will be given to a task. So we need to factor in how many locales
        // we are running on, and how many tasks per locale. We assume that maxTaskPar is the 
        // same across all locales. It may be the case that numTasks is greater than totalNumIters,
        // which can happen when we have a very small loop (or running on LOTS of locales with many
        // cores). In such a case, we can assume that prefetching is not of interest, so just return
        // totalNumIters, which means we'll never do the adjustment since the count we keep incrementing
        // will never reach totalNumIters within the check we do.
        const numTasks = if dataParTasksPerLocale == 0 then numLocales * here.maxTaskPar
                                                       else numLocales * dataParTasksPerLocale;
        const numItersPerTask = totalNumIters / numTasks;
        if numItersPerTask == 0 {
            return totalNumIters;
        }
        else {
            return (numItersPerTask * PREFETCH_SAMPLE_RATIO):int;
        }
    }

    // This procedure performs the adjustment of a given prefetch distance. It is
    // the version that favors increasing the distance to reduce waited-on prefetches.
    // The compiler will insert a call to this function within the loop that contains 
    // the prefetch. Specifically, the compiler will generate an if-check that has a 
    // call to this procedure in the then-block. The if-check looks at a task-private 
    // variable "count" and sees whether it greater than the number of sample iterations. 
    // If it is, we call this procedure. Else, we increment it. So something like:
    //
    //      if (count < numSampleIterations) {
    //          count += 1;
    //      }
    //      else {
    //          adjustPrefetchDistance(dist, window);
    //          count = 0;
    //      }
    //  
    // The "numSampleIterations" value is determined by the number of iterations of
    // the loop that contains the prefetched access (see getPrefetchSampleSize()).
    //
    // This approach is adapted/taken from the following paper:
    //  " Near-Side Prefetch Throttling: Adpative Prefetching for High-Performance Many-Core Processors"
    //
    inline proc adjustPrefetchDistance(ref dist : int, ref window : int) where TARGET_PREFETCHES == 0
    {
        // 1.) Get the current counters
        const numPrefetches = get_per_cache_num_prefetches();
        const numLatePrefetches = get_per_cache_num_prefetches_waited();
        
        // 2.) Compute the percentage of late prefetches
        const latePrefetchPercent = ((numLatePrefetches:real / numPrefetches)*100):int;

        // 3.) We want latePrefetchPercent to be 10% or less (default). If it is larger,
        //     then we increase the distance by 1. If it is less, and the value
        //     of "window" is less than MAX_WINDOW, then keep the distance constant
        //     until "window" hits MAX_WINDOW. If "window" is greater than or equal
        //     to MAX_WINDOW, then we decrement the distance. This continues until
        //     we hit MIN_PREFETCH_DISTANCE or the percentage of late prefetches
        //     exceeds 10%.
        if (latePrefetchPercent > LATE_PREFETCH_TOLERANCE) {
            dist = min(dist+1, MAX_PREFETCH_DISTANCE);
            window = 0;
        }
        else {
            if (window < MAX_WINDOW) {
                window += 1;
            }
            else {
                dist = max(dist-1, MIN_PREFETCH_DISTANCE);
            }
        }

        // 4.) Reset the counters
        reset_per_cache_prefetch_counters();
    }
   
    // This is the same procedure as above but instead favors decreasing the distance to
    // "optimize" prefetches that are unused (kicked out of cache before we could use them).
    //
    // This approach is adapted/taken from the following paper:
    //  "Improving the Effectiveness of Software Prefetching with Adaptive Execution"
    inline proc adjustPrefetchDistance(ref dist : int, ref window : int) where TARGET_PREFETCHES == 1
    {
        // TODO: implement the algorithm to favor unused prefetches
        return;
    }

    // This is a version we use for testing that keeps the distance constant
    inline proc adjustPrefetchDistance(ref dist : int, ref window : int) where TARGET_PREFETCHES == 2
    {
        return;
    }

    //###########################################################################
    //
    //                           Utilities
    //
    //###########################################################################
    //
    // These are functions that are not worth categorizing in any particular way.
    
    // Initialized the task-private prefetch distance to the initial value
    inline proc initPrefetchDistance()
    {
        return DEFAULT_PREFETCH_DISTANCE;
    }

    // Used to initialize the task-private count/window variables (just sets them
    // to 0).
    inline proc initCounts()
    {
        return 0;
    }

    // Param/static check used to ensure that the prefetch is supported.
    // We can do prefetching as long as the loop that contains the access
    // to prefetch iterates over a non-associative array or domain. We also
    // ensure that A and B from A[B[i]] are arrays
    proc chpl__isPrefetchSupported(loopIter : [?D], A : [?F], B : [?E]) param
    {
        return !loopIter.domain.isAssociative();
    }
    proc chpl__isPrefetchSupported(loopIter : domain, A : [?F], B : [?E]) param
    {
        return !loopIter.isAssociative();
    }
    // Matched when the loop iterates over a range, so there is no
    // loop iterator Symbol
    proc chpl__isPrefetchSupported(A, B) param
    {
        return isArray(A) && isArray(B);
    }
    proc chpl__isPrefetchSupported(obj1, obj2, obj3) param
    {
        return false;
    }

    // Simple wrapper around the primitive that actually
    // performs the prefetch. Here, "x" is the address of
    // where we start the prefetch from.
    pragma "remote cache prefetch"
    inline proc prefetch(const id : int, const ref x)
    {
        __primitive("chpl_comm_remote_prefetch", x.locale.id, x, DEFAULT_PREFETCH_SIZE);
    }
    // Verison of prefetching when we are dealing with records.
    // We specify the index/position of the field to access.
    // For some reason, we get a compiler error if we specify the formal "x"
    // as a const ref. Seems to be that what we pass into here is not a const
    // ref, or something. It bugs out on the call to getFieldRef.
    pragma "remote cache prefetch"
    inline proc prefetch(const id : int, ref x, param fieldPos : int)
    {
        __primitive("chpl_comm_remote_prefetch", x.locale.id, getFieldRef(x, fieldPos), DEFAULT_PREFETCH_SIZE);
    }

} /* end of AdaptiveRemoteCachePrefetching module */
