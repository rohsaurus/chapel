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
    File:   AutoRemoteWriteAggregation.chpl
    Date:   05/24/2022
    Author: Thomas Rolinger (tbrolin@cs.umd.edu)

    This module is similar to ChapelAutoAggregation but specifically
    for the RemoteWriteAggregation module that we will use for our
    irregular access optimizations. Down the road it'll probably make
    more sense to roll all of this into the existing aggregation code
    but I prefer to keep it separate for now.

    The main purpose of this module is to provide some helper routines
    to use during the optimization (i.e., procedures that the compiler
    can generate calls to, which reduces the complexity of what the
    compiler needs to generate itself).
*/
module AutoRemoteWriteAggregation {
  private use RemoteWriteAggregation;
  private use ChplConfig;
  private use InspectorExecutor;

  // Similar to what is done in AutoAggregation. This is what the
  // compiler generates calls to to create/return the aggregator object.
  // We'll keep the pragma here though I'm not sure if it will be used.
  //
  // The first argument to the aggregator constructor is the type of the
  // source (i.e., RHS). The second argument is the type of the destination
  // (i.e., LHS, A from A[B[i]]). This is different from the existing auto-aggregation
  // since it assumed that the types for the source and destintation were the same.
  // That is true for assignment (A[i] = B[i]). But when we have something like
  // A[B[i]] += val and A contains associative domains, that is no longer true,
  // as the element type of A is an associative domain, not whatever the type of
  // val is.
  //
  // The third argument to the constructor is a type. Specifically, it is the type
  // of a Record that was generated to have a single procedure that performs the
  // aggregated operation. This procedure is a Type method. So when the aggregator
  // flushes, it will call opRec.op(lhs,rhs). It is the job of the compiler optimization
  // to generate this Record.

  //####################################################################
  //                                                                  //
  //        "General" aggregator where we specify the operation to    //
  //        perform when the buffers are flushed. The operation is    //
  //        passed in as a record type with a type method.            //
  //                                                                  //
  //####################################################################
  //
  // We can only do aggregation if the element type of the array is POD.
  // But there are a couple other cases that can work, such as when the
  // element type is an associative domain or atomic. Those are not POD but
  // we can do aggregation on them (i.e., += for associative domains, .add()
  // for atomics). The assumption is that if the compiler is generating calls
  // to this, we have determined we have a "valid" operator. Note that we do
  // not support aggregator on atomics when CHPL_COMM is ugni. This is because
  // ugni/Aries has network atomics which have a lot of overhead when performed
  // locally (which is what aggregation will do).
  pragma "aggregator generator"
  proc chpl__irregWriteAggregatorGeneral(arr: [] ?eltType, type opRec) where isPODType(eltType) ||
                                                                             (isDomainType(arr.eltType) &&
                                                                             arr[arr.domain.low].isAssociative() &&
                                                                             arr[arr.domain.low].parSafe) ||
                                                                             (isAtomic(eltType) && CHPL_COMM != "ugni")

  {
    // If we're dealing with an array of atomics, we get the destType in a different
    // way.
    if (isAtomic(eltType) && CHPL_COMM != "ugni") {
      type srcType = eltType.T;
      type destType = eltType;
      return new RemoteWriteAggregator(srcType, destType, opRec);
    }
    // If we're dealing with an array of associative domains, we need to get the
    // srcType in a different way
    else if (isDomainType(eltType) && arr[arr.domain.low].isAssociative()) {
      if (arr[arr.domain.low].parSafe) {
        type srcType = arr[arr.domain.low].idxType;
        type destType = eltType;
        return new RemoteWriteAggregator(srcType, destType, opRec);
      }
    }
    // Else, we just have POD types
    else {
      type srcType = eltType;
      type destType = eltType;
      return new RemoteWriteAggregator(srcType, destType, opRec);
    }
  }

  // If nothing is matched above, we return nil and will abort the optimization
  // during prefolding. This also happens if we don't pass in an array.
  pragma "aggregator generator"
  proc chpl__irregWriteAggregatorGeneral(x, type opRec) { return nil; }

  // Param check that the array A is distributed and the aggregator isn't nil.
  // The idea is that this will be resolved to true or false after normalization.
  // If we use it to guard to aggregator call, then when we get to prefolding
  // we'll either still have the aggregator call or it will be eliminated.
  proc chpl__isAggregationSupported(arr : [?D], agg : RemoteWriteAggregator) param 
  {
    return chpl__isDistributed(arr);
  }
  // Matched when we don't have an array
  proc chpl__isAggregationSupported(obj, agg : RemoteWriteAggregator) param
  {
    return false;
  }
  // Matched when agg is nil
  proc chpl__isAggregationSupported(arr : [?D], agg) param
  {
    return false;
  }
  // Matched when we don't have an array and agg is nil
  proc chpl__isAggregationSupported(obj, agg) param
  {
    return false;
  }  
} /* end of AutoRemoteWriteAggregation module */
