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
    private use ChplConfig;
    use Reflection;
    private use BlockDist, CyclicDist, BlockCycDist, ReplicatedDist;

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

    // Some defaults associated with our approach to adjusting the prefetch distance. In
    // all cases where we refer to the prefetch distance, we are talking about some task's
    // distance. The same logic/operations are performed for every task's distance independently
    // from the others.
    //
    // MAX_PREFETCH_DISTANCE: the maximum value we will increase the distance to
    //
    // MIN_PREFETCH_DISTANCE: the minimum value we will decrease the distance to
    //
    // LATE_WINDOW: how many "windows" must elapse before we decrease the distance if
    //              we've been below the late prefetch tolerance each time. The logic here is
    //              that if we are not waiting for prefetches, we run the risk of prefetching too
    //              early and that could lead to unused prefetches (data evicted before it could be
    //              used). So if we've consistently NOT late, then decrease the distance by 1. This
    //              has the effect of trying to make our prefetches come in right on time. The
    //              "windows" here refer to each time we make a call to adjustment distance, which is
    //              determined by PREFETCH_SAMPLE (see below). So if PREFETCH_SAMPLE is 10 and LATE_WINDOW
    //              is 8, then we will decreasr the distance if we've been NOT late for 10*8 = 80 loop
    //              iterations.
    //
    // PREFETCH_SAMPLE: number of loop iterations that must elapse before we
    //                  will attempt to adjust the distance. By "loop" we mean the
    //                  the loop that contains the prefetch call
    //
    // LATE_PREFETCH_TOLERANCE: percentage of prefetches that are allowed to be
    //                          late. A prefetch is late if the task had to wait
    //                          for the prefetch to arrive. The late prefetch percentage
    //                          is computed per adjustment interval (so it resets after each
    //                          attempt to adjust the distance).
    //
    // USELESS_PREFETCH_TOLERANCE: percentage of prefetches that are allowed to be useless. A
    //                             prefetch is useless if the data we tried to prefetch was already
    //                             in the cache (so we didn't need to issue the prefetch to begin with).
    //                             The data may be there from an earlier prefetch or just the normal
    //                             read-ahead feature of the remote cache. So a value of 80% here says
    //                             that if 80% or more of the prefetches are useless, then we should do
    //                             something (see PREFETCH_TIMEOUT). Like with late prefetch percentages,
    //                             we calculate the useless prefetch percentages per adjustment window.
    //
    // PREFETCH_TIMEOUT: the number of adjustment intervals (windows) that elapse before we will quit
    //                   prefetching if we've been above the useless prefetch tolerance. The logic here is
    //                   that if we're consistently issuing useless prefetches, we're better off not prefetching
    //                   because we're clearly in some sort of dense/regular memory access pattern region. Prefetching
    //                   can resume once we observe a X% miss rate, where X is specified by MISS_TOLERANCE.
    //
    // MISS_TOLERANCE: the percentage of GETs to the cache that are allowed to be misses before we decide to restart
    //                 prefetching. We use this threshold once we've stopped prefetching due to too many useless
    //                 prefetches. We still stop at each adjustment interval/window, but we'll now check the miss rate
    //                 of that window and see if it is above MISS_TOLERANCE. If it is, we'll resume prefetching again using
    //                 the last value of the distance before we stopped. The logic here is that we stopped prefetching because 
    //                 we were hitting in the cache for data we wanted to prefetch. But if we see that we start missing a lot then
    //                 we'll want to begin prefetching again.
    //
    // CONSTANT_PREFETCHES: If this is set true, then we will not adjust the
    //                      prefetch distance. Default is false so
    //                      we use our heuristic. This is a compile-time variable,
    //                      so it must be set when compiling.
    //
    config const MAX_PREFETCH_DISTANCE = 256;
    config const MIN_PREFETCH_DISTANCE = 1;
    config const LATE_WINDOW = 8;
    config const PREFETCH_SAMPLE = 100;
    config const LATE_PREFETCH_TOLERANCE = 10;
    config const USELESS_PREFETCH_TOLERANCE = 80;
    config const PREFETCH_TIMEOUT = 32;
    config const MISS_TOLERANCE = 50;
    config param CONSTANT_PREFETCHES = false;

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
    extern proc reset_per_cache_get_counters();
    extern proc get_per_cache_num_prefetches() : int;
    extern proc get_per_cache_num_prefetches_waited() : int;
    extern proc get_per_cache_num_prefetches_useless() : int;
    extern proc get_per_cache_num_prefetches_completed() : int;
    extern proc get_per_cache_num_get_hits() : int;
    extern proc get_per_cache_num_get_misses() : int;
    
    // Not directly related to prefetches but useful to see how prefetches
    // are helping us.
    inline proc per_cache_num_get_hits()
    {
        return get_per_cache_num_get_hits();
    }
    inline proc per_cache_num_get_misses()
    {
        return get_per_cache_num_get_misses();
    }
    inline proc reset_get_counters()
    {
        coforall loc in Locales do on loc {
            coforall tid in 1..loc.maxTaskPar {
                reset_per_cache_get_counters();
            }
        }
    }
    inline proc get_total_get_hits()
    {
        var totalHits = 0;
        coforall loc in Locales with (+reduce totalHits) do on loc {
            coforall tid in 1..loc.maxTaskPar with (+reduce totalHits) {
                totalHits += per_cache_num_get_hits();
            }
        }
        return totalHits;
    }
    inline proc get_total_get_misses()
    {
        var totalMisses = 0;
        coforall loc in Locales with (+reduce totalMisses) do on loc {
            coforall tid in 1..loc.maxTaskPar with (+reduce totalMisses) {
                totalMisses += per_cache_num_get_misses();
            }
        }
        return totalMisses;
    }
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
    inline proc get_cache_num_prefetches_waited()
    {
        return get_per_cache_num_prefetches_waited();
    }
    inline proc get_cache_num_prefetches_useless()
    {
        return get_per_cache_num_prefetches_useless();
    }
    inline proc get_cache_num_prefetches_completed()
    {
        return get_per_cache_num_prefetches_completed();
    }
    // For debugging: get counters across all caches
    inline proc get_all_cache_prefetch_counters()
    {
        var num_prefetches = 0;
        var num_prefetches_waited = 0;
        var num_prefetches_useless = 0;
        var num_prefetches_completed = 0;
        coforall loc in Locales with (+reduce num_prefetches,
                                      +reduce num_prefetches_waited,
                                      +reduce num_prefetches_useless,
                                      +reduce num_prefetches_completed)
        {
            on loc {
                coforall tid in 1..loc.maxTaskPar with (+reduce num_prefetches,
                                                        +reduce num_prefetches_waited,
                                                        +reduce num_prefetches_useless,
                                                        +reduce num_prefetches_completed)
                {
                    num_prefetches += get_cache_num_prefetches();
                    num_prefetches_waited += get_cache_num_prefetches_waited();
                    num_prefetches_useless += get_cache_num_prefetches_useless();
                    num_prefetches_completed += get_cache_num_prefetches_completed();
                }
            }
        }
        return (num_prefetches, num_prefetches_waited, num_prefetches_useless, num_prefetches_completed);
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

    // ##################### Getting prefetch sample size #######################
    // This is simply a wrapper to get the value of PREFETCH_SAMPLE
    inline proc getPrefetchSampleSize()
    {
        return PREFETCH_SAMPLE;
    }

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
    // Here is the heuristic that is called to attempt to adjust the prefetch
    // distance for some task.
    //
    //      dist: the prefetch distance to adjust. This is passed in as a ref since we can modify it
    //  
    //      windowLate: keeps track of how many windows have elapsed where we were below the late tolerance. Also
    //                  passed in as a ref since we modify it.
    //
    //      windowUseless: keeps track of how many windows have elapsed where we were above the useless tolerance.
    //                     Passed in as a ref since we modify it.
    //
    //      stoppedPrefetching: is this is true, it means we have not been prefetching, so we do something
    //                          different in the heuristic. This is passed in as a ref because this procedure
    //                          is what actually sets this parameter to true or false.
    //
    // When this is called, there are two scenarios to consider:
    //      1.) We had stopped prefetching
    //      2.) We have been prefetching up to this point
    //
    // For (1), we haven't been prefetching because we stopped due to too many useless prefetches. 
    // So what we do now is look at our miss rate and see if we need to restart prefetching.
    // For (2), we will look at how many prefetches were late and use that to determine whether we
    // modify the prefetch distance (and factor in windowLate, see code-comments below). We also look
    // at useless prefetches and see whether we need to stop prefetching.
    //
    // We know that we had stopped prefetching because the argument stoppedPrefetching is set to true.
    // If we are in case (2) but find that we meet the criteria to stop prefetching, then we will set
    // stoppedPrefetching to true. If we are in case (1) and find that we meet the critera to restart
    // prefetching, we will set stoppedPrefetching to false.
    inline proc adjustPrefetchDistance(ref dist : int, 
                                       ref windowLate : int, 
                                       ref windowUseless : int,
                                       ref stoppedPrefetching : bool) where CONSTANT_PREFETCHES == false
    {
        //###################################################################################
        // 1.) If we have not been prefetching, calculate the miss rate by looking at
        // the number of misses and hits. Then, if the miss rate is above MISS_TOLERANCE,
        // set stoppedPrefetching to false to indicate that we will start prefetching
        // again. We reset the windows, and keep dist as it is (so we will start with
        // the distance we used last).
        if (stoppedPrefetching == true) {
            const numMisses = per_cache_num_get_misses();
            const numHits = per_cache_num_get_hits();
            const missRate = ((numMisses:real)/(numMisses+numHits))*100:int;
            const tmp = ((numMisses:real)/(numMisses+numHits))*100;
            if (missRate > MISS_TOLERANCE) {
                stoppedPrefetching = false;
                windowLate = 0;
                windowUseless = 0;
            }
            // Reset counters for next window
            reset_per_cache_prefetch_counters();
            reset_per_cache_get_counters();
            return;
        }

        //###################################################################################
        // 2.) If we have been prefetching up to this point, calculate the late prefetch
        // and useless prefetch percentages. We differeniate between the total number of
        // prefetches (numPrefetches) and the number of completed prefetches (numPrefetchesComp).
        // A completed prefetch is one where we actually issued the prefetch (i.e., it wasn't
        // a useless prefetch). We can calculate that by just substracting off the number of
        // useless prefetches from the total number of prefetches
        const numPrefetches = get_per_cache_num_prefetches();
        const numUselessPrefetches = get_per_cache_num_prefetches_useless();
        const numPrefetchesComp = numPrefetches - numUselessPrefetches;
        const numLatePrefetches = get_per_cache_num_prefetches_waited();
        const latePrefetchPercent = ((numLatePrefetches:real / numPrefetchesComp)*100):int;
        const uselessPrefetchPercent = ((numUselessPrefetches:real / numPrefetches)*100):int; 
            
        // If the amount of useless prefetches is too high, and has been too high for PREFETCH_TIMEOUT
        // consecutive windows, then set stoppedPrefetching to true and return. This means we are
        // likely not getting a benefit from prefetching so we should stop for now.
        if (uselessPrefetchPercent > USELESS_PREFETCH_TOLERANCE) {
            if (windowUseless < PREFETCH_TIMEOUT) {
                // Haven't reach the timeout yet, so increment the window
                windowUseless += 1;
            }
            else {
                // We've been above the threshold too many times in a row, so
                // quite prefetching for now.
                stoppedPrefetching = true;
                windowUseless = 0;
                windowLate = 0;
                // Reset counters for next window
                reset_per_cache_prefetch_counters();
                reset_per_cache_get_counters();
                return;
            }
        }
        else {
            // We're below the threshold, so reset the window count
            windowUseless = 0;
        }

        // If we're here, we are either below the useless prefetch tolerance, or
        // we are above it but haven't been above it for too long. In either case,
        // we need to consider the late prefetches now, which can actually affect the
        // value of the prefetch distance. If the late prefetch percentage is above
        // the tolerance, we increase the distance (effectively giving future prefetches
        // more time to complete so we don't have to wait for them). If we are below the
        // tolerance, and we have been below for LATE_WINDOW intervals, then increase the
        // distance so we are not too early.
        if (latePrefetchPercent > LATE_PREFETCH_TOLERANCE) {
            dist = min(dist+1, MAX_PREFETCH_DISTANCE);
            windowLate = 0;
        }
        else {
            if (windowLate < LATE_WINDOW) {
                windowLate += 1;
            }
            else {
                dist = max(dist-1, MIN_PREFETCH_DISTANCE);
            }
        }

        // Last thing we do is reset the cache counters for the next window/interval.
        reset_per_cache_prefetch_counters();
        reset_per_cache_get_counters();
    } 


    // This is a version that keeps the distance constant (i.e., does nothing
    inline proc adjustPrefetchDistance(ref dist : int, ref window : int) where CONSTANT_PREFETCHES == true
    {
        return;
    }


    //###########################################################################
    //
    //                           Utilities
    //
    //###########################################################################
    //
    // These are functions that are not worth categorizing in any particular way

    // Utility code to monitor the prefetch distance. When we want to do this, we'll uncomment out
    // some compiler code that sets thing up when the optimization is applied. Specifically, each
    // task in the forall gets its own array with MAX_PREFETCH_DISTANCE elements. This array keeps
    // track of how many times a given distance i is used for a prefetch. This is done by simply
    // incrementing the array at index i.
    //
    use BlockDist;
    var numArrays = numLocales * here.maxTaskPar;
    var arrDom = {1..MAX_PREFETCH_DISTANCE};
    var distArrays = Block.createArray({0..#numArrays}, [arrDom] int);
    forall arr in distArrays {
        arr = 0;
        arr[initPrefetchDistance()] = 1;
    }
    // A given task will be assigned an array from distArrays, but we need to ensure it is co-located
    // on the locale that the task is on. So we make another array of indices that will be atomically
    // "given" to each task
    var indexArray = Block.createArray(LocaleSpace, atomic int);
    forall elem in indexArray {
        elem.write(0);
    }
    // This is called within the forall with's clause. It gives a task its own array to
    // keep track of the distances. We ensure it is co-located on the locale where that task is.
    inline proc getDistArray() ref
    {
        const taskID = indexArray[here.id].fetchAdd(1) + (here.id * here.maxTaskPar);
        return distArrays[taskID];
    }
    // This is called right before we do a prefetch.
    inline proc logDistance(const dist, ref distArr)
    {
        distArr[dist] += 1;
    }
    // For apps like SSSP where we need to run multiple iterations, we need
    // to reset the task IDs each time; otherwise they increment past the max value.
    inline proc resetTaskIDs()
    {
        forall elem in indexArray {
            elem.write(0);
        }
    }
    // Print the stats
    inline proc printDistanceStats()
    {
        writef("$$$ Prefetch Distance Statistics (how many times each distance was used)\n");
        for (idx, arr) in zip(distArrays.domain, distArrays) {
            writef("+ Task %i on Locale %i:\n", idx, arr.locale.id);
            for (dist, count) in zip(arr.domain, arr) {
                writef("\t[%i] = %i\n", dist, count);
            }
            writef("\n");
        }
    }
    
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
    
    // Used to initialize the task-private stoppedPrefetching variable
    inline proc initBool()
    {
        return false;
    }

    // Various param-based procs to determine if a given domain is distributed.
    // We wrap them all up into a single isDistributed() proc that we will use
    // to ensure that the domain being iterated over in the forall is distributed.
    // One version is matched when we pass in an array; the other will match on
    // anything else.
    proc isBlock(D) param do return false;
    proc isBlock(D: BlockDom) param do return true;
    proc isCyclic(D) param do return false;
    proc isCyclic(D: CyclicDom) param do return true;
    proc isBlockCyclic(D) param do return false;
    proc isBlockCyclic(D: BlockCyclicDom) param do return true;
    proc isReplicated(D) param do return false;
    proc isReplicated(D: ReplicatedDom) param do return true;
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

    // Param/static check used to ensure that the prefetch is supported.
    // We can do prefetching as long as the loop that contains the access
    // to prefetch iterates over a non-associative array or domain. We also
    // ensure that A and B from A[B[i]] are arrays. Finally, DO NOT do prefetching
    // if CHPL_COMM == "ugni"; there are no non-blocking reads in that case, so
    // prefetching is useless.
    proc chpl__isPrefetchSupported(loopIter : [?D], A : [?F], B : [?E]) param
    {
        return !loopIter.domain.isAssociative() && chpl__isDistributed(A) && CHPL_COMM != "ugni";
    }
    proc chpl__isPrefetchSupported(loopIter : domain, A : [?F], B : [?E]) param
    {
        return !loopIter.isAssociative() && chpl__isDistributed(A) && CHPL_COMM != "ugni";
    }
    // Matched when the loop iterates over a range, so there is no
    // loop iterator Symbol
    proc chpl__isPrefetchSupported(A, B) param
    {
        return isArray(A) && isArray(B) && chpl__isDistributed(A) && CHPL_COMM != "ugni";
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
