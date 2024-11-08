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
    File:   SelectiveDataReplication.chpl
    Date:   12/28/2021
    Author: Thomas Rolinger (tbrolin@cs.umd.edu)

    This is a module that contains the inner workings of the
    Selective Data Replication (SDR) optimization. In short,
    this optimization uses the inspector-executor technique to
    determine which elements of an array-of-interest are accessed
    remotely during a kernel. Those remotely accesses elements are
    replicated on the locale that issued the accesses, so they can
    be used locally the next time the kernel is executed.

    The purpose of this module is to provide methods to perform
    the inspect/execute routines for the memory accesses, as well
    as other utility methods.

    It is worth explaining the organization of the replicated arrays.
    A given distributed array A (BlockDist or CyclicDist) contains a
    field called "commSchedules". This is an array of CommunicationSchedule
    records, where each element corresponds to a specific forall that is
    being optimized where A is used in the loop as part of a A[B[i]]
    access. The compiler generates a unique ID for the forall and uses
    that as an index into this array. Within each CommunicationSchedule
    record is an associative array of ReplicatedElems records, which
    actually store the replicated arrays. This associative array is
    indexed by a hash so we can handle multiple call sites of the
    function that contains the forall, if applicable. Finally, the
    distributed array A stores one commSchedules array on each locale.
    Meaning, A.commSchedules will access the commSchedules on whatever
    locale we issue the access from. This means that A.commSchedules on
    locale 4 holds all the communication schedule data for A as it pertains
    to locale 4.

    In the below procedures, "id" refers to the forall ID we are passing in
    and "hash" refers to the call-site hash we are passing in. This allows
    us to grab the correct replicated array data.

    Most procedures take in the array A, the ID and the hash and then
    do something with the corresponding ReplicatedElems record. But
    the inspectAccess and executeAccess procedure directly take in
    fields of a ReplicatedElems record. This is because these calls
    happen within the forall, so we need to avoid all that indirection.
*/

pragma "selective data replication"
module SelectiveDataReplication {

    private use ChapelStandard;
    use Reflection;
    use ChapelAutoAggregation.CopyAggregation;
    private use RemoteWriteAggregation;

    //###################################################################
    // getArrDom: Given an array A, return the corresponding arrDom field
    // in the ReplicatedElems record for the given ID and hash.
    //
    // A: the array of interest with ReplicatedElems records
    // id: ID of the forall we are dealing with
    // hash: call-site hash that we are dealing with
    //###################################################################
    inline proc getArrDom(A : [?D], id : int, hash : (int,int,int,int)) ref
    {
        return A.commSchedules[id].scheds[hash].arrDom;
    }

    //###################################################################
    // getReplArr: Given an array A, return A.replArray.replArr for the
    // specified id and hash.
    //
    // A: the array of interest with ReplicatedElems records
    // id: ID of the forall we are dealing with
    // hash: call-site hash that we are dealing with
    //###################################################################
    inline proc getReplArr(A : [?D], id : int, hash : (int,int,int,int)) ref
    {
        return A.commSchedules[id].scheds[hash].replArr;
    }

    //###################################################################
    // getReplD: Given an array A, return A.replArray.replD for the
    // specified id and hash.
    //
    // A: the array of interest with ReplicatedElems records
    // id: ID of the forall we are dealing with
    // hash: call-site hash that we are dealing with
    //###################################################################
    inline proc getReplD(A : [?D], id : int, hash : (int,int,int,int)) ref
    {
        return A.commSchedules[id].scheds[hash].replD;
    }

    //###################################################################
    // Same as above but matches on arguments that are not arrays. This
    // needs to be handled since we insert these calls during normalization,
    // before we know if we have an array or not. We just need to return
    // something that will compile, as the optimization will abort once
    // we get to resolution.
    //###################################################################
    var replArrayDummy : ReplicatedElems(int, int, 1);
    inline proc getArrDom(obj, id : int, hash : (int,int,int,int)) ref
    {
        return replArrayDummy.arrDom;
    }
    inline proc getReplArr(obj, id : int, hash : (int,int,int,int)) ref
    {
        return replArrayDummy.replArr;
    }
    inline proc getReplD(obj, id : int, hash : (int,int,int,int)) ref
    {
        return replArrayDummy.replD;
    }

    //###################################################################
    // sortReplIndices: simply calls sortIndices() on each ReplicatedElems
    // record in A for the given ID and hash. We have one version that
    // matches on arrays and does the sorting, and one version that matches
    // on anything else and just returns.
    //
    // A: the array of interest with ReplicatedElems records
    // id: ID of the forall we are dealing with
    // hash: call-site hash that we are dealing with
    //###################################################################
    inline proc sortReplIndices(A : [?D], id : int, hash : (int,int,int,int))
    {
        coforall loc in Locales do on loc {
            sortIndices(A.commSchedules[id].scheds[hash]);
        }
    } /* end of sortReplIndices */
    inline proc sortReplIndices(obj, id : int, hash : (int,int,int,int))
    {
        return;
    }

    //###################################################################
    // executorPreamble: this is the code that runs prior to the kernel
    // (executor) running. We need to do the replicated element update
    // phase for the given id and hash.
    //
    // This version is called when the elements we are dealing with are
    // primitive types (int, real, etc.)
    //
    // A: the array of interest with ReplicatedElems records
    // id: ID of the forall we are dealing with
    // hash: call-site hash that we are dealing with
    //###################################################################
    pragma "executor preamble"
    inline proc executorPreamble(A, id : int, const hash : (int,int,int,int))
    {
        coforall loc in Locales do on loc {
            update(A.commSchedules[id].scheds[hash], A);
        }
    } /* end of executorPreamble */

    //###################################################################
    // executorPreamble: another version of the executor preamble but for
    // records. It contains information about which fields in the record to
    // update.
    //
    // Note that we do the actual updating in this procedure, rather
    // than calling out to the CommunicationSchedule module. This is because
    // this procedure takes in a variable number of arguments for the field
    // locations. I'm not sure how to pass such arguments to another
    // procedure.
    //
    // A: the array of interest with ReplicatedElems records
    // id: ID of the forall we are dealing with
    // hash: call-site hash that we are dealing with
    // fieldPositions: field indices of the record fields of interest
    //###################################################################
    inline proc executorPreambleRecords(A, id : int, hash : (int,int,int,int), fieldPositions ...?numPositions)
    {
        coforall loc in Locales do on loc {
            ref replRec = A.commSchedules[id].scheds[hash];
            ref replArr = replRec.replArr;
            const ref indices = replRec.indices;
            if indices.size > 0 {
                for fieldPos in fieldPositions {
                    param nFields = numFields(replRec.elemType);
                    for param i in 0..#nFields {
                        if (i == fieldPos) {
                            type fieldType = getFieldRef(A[0], i).type;
                            if isPODType(fieldType) {
                                forall idx in indices with (var agg = new SrcAggregator(fieldType)) {
                                    ref src = getFieldRef(A[idx], i);
                                    ref dst = getFieldRef(replArr[idx], i);
                                    agg.copy(dst, src);
                                }
                            }
                            else if isAtomic(fieldType) {
                                forall idx in indices with (var agg = new AtomicCopyDstAggregator(fieldType.T)) {
                                    ref src = getFieldRef(A[idx], i);
                                    ref dst = getFieldRef(replArr[idx], i);
                                    agg.write(dst, src.read());
                                }               
                            }
                        }
                    }
                }
            }
        }
    } /* end of executorPreambleRecords */

    //###################################################################
    // executorPreamble: same as above but a micro-optimization when a
    // field we are updating is atomic and it is written to within the loop.
    // This means the write is something like .add(), and we only support this
    // case if the elements are set to 0 (the identity of the + operator in terms
    // of reductions). It is faster to just set the element to 0 vs doing atomic
    // reads from A.
    //
    // A: the array of interest with ReplicatedElems records
    // id: ID of the forall we are dealing with
    // hash: call-site hash that we are dealing with
    // fieldPositions: field indices of the record fields of interest
    //###################################################################
    inline proc executorPreambleRecordsAtomicAdd(A, id : int, hash : (int,int,int,int), fieldPositions ...?numPositions)
    {
        coforall loc in Locales do on loc {
            ref replRec = A.commSchedules[id].scheds[hash];
            ref replArr = replRec.replArr;
            const ref indices = replRec.indices;
            if indices.size > 0 {
                for fieldPos in fieldPositions {
                    param nFields = numFields(replRec.elemType);
                    for param i in 0..#nFields {
                        if (i == fieldPos) {
                            type fieldType = getFieldRef(A[0], i).type;
                            if isPODType(fieldType) {
                                forall idx in indices with (var agg = new SrcAggregator(fieldType)) {
                                    ref src = getFieldRef(A[idx], i);
                                    ref dst = getFieldRef(replArr[idx], i);
                                    agg.copy(dst, src);
                                }
                            }
                            else if isAtomic(fieldType) {
                                forall idx in indices {
                                    ref dst = getFieldRef(replArr[idx], i);
                                    dst.write(0, memoryOrder.relaxed);
                                }
                            }
                        }
                    }
                }
            }
        }   
    } /* end executorPreambleRecordsAtomicAdd */

    //###################################################################
    // executorPostambleRecords: runs right after the executor to "reduce"
    // replicated elements back to the original array. We only do this
    // in the case of record fields that are atomics, and the writes in
    // the forall are in the form of atomic adds (.add()). We could generalize
    // this in the future to allow for writes to atomics that are not record fields
    // but we don't have a use-case for that right now.
    //
    // A: the array of interest with ReplicatedElems records
    // id: ID of the forall we are dealing with
    // hash: call-site hash that we are dealing with
    // fieldPositions: field indices of the record fields of interest
    //###################################################################
    inline proc executorPostambleRecords(A, id : int, hash : (int,int,int,int), fieldPositions ...?numPositions)
    {
        coforall loc in Locales do on loc {
            ref replRec = A.commSchedules[id].scheds[hash];
            ref replArr = replRec.replArr;
            const ref indices = replRec.indices;
            if indices.size > 0 {
                for fieldPos in fieldPositions {
                    param nFields = numFields(replRec.elemType);
                    for param i in 0..#nFields {
                        if (i == fieldPos) {
                            type fieldType = getFieldRef(A[0], i).type;
                            if isAtomic(fieldType) {
                                forall idx in indices with (var agg = new AtomicAddAggregator(fieldType.T)) {
                                    ref src = getFieldRef(A[idx], i);
                                    ref dst = getFieldRef(replArr[idx], i);
                                    agg.bufferOp(dst, src.read());
                                }
                            }
                        }
                    }
                }
            }
        }
    } /* end of executorPostambleRecords */

    //###################################################################
    // fieldsHaveAddIdentity: given an array that is assumed to hold 
    // records as elements, ensure that specified fields are set to 0,
    // which is the identity for addition. If any field is not 0, return
    // false. Otherwise, return true.
    //
    // We insert this procedure call during prefolding, where we know if
    // A stores records and everything else checks out.
    //
    // A: the array of interest
    // fieldPositions: field indices of the record fields of interest
    //###################################################################
    inline proc fieldsHaveAddIdentity(ref A : [?D], fieldPositions ...?numPositions) : bool
    {
        var isValid : bool = true;
        forall i in A.domain with (ref isValid) {
            for fieldPos in fieldPositions {
                param nFields = numFields(A.eltType);
                for param j in 0..#nFields {
                    if (j == fieldPos) {
                        ref field = getFieldRef(A[i], j);
                        if (isAtomic(field)) {
                            if (field.read(memoryOrder.relaxed) != 0) {
                                isValid = false;
                                break;
                            }
                        }
                    }
                }
            }
        }
        return isValid;
    }
    proc dummyCallIE(id : int) { return true; }

    //###################################################################
    // inspectorPreamble: this is the code that runs prior to the inspector
    // running. We need to extract A's local subdomains. We have one version
    // that matches on arrays and does the preamble, and one version that
    // matches on anything else and just returns. Again, we do this for
    // a specified ID and hash. If this is the first time we've called
    // the preamble for this ID/hash, we need to add the hash to the
    // schedule.
    //
    // A: the array of interest with ReplicatedElems records
    // id: ID of the forall we are dealing with
    // hash: call-site hash that we are dealing with
    //###################################################################
    pragma "inspector preamble"
    inline proc inspectorPreamble(A : [?D], id : int, hash : (int,int,int,int))
    {
        coforall loc in Locales do on loc {
            // "create" the schedule for this hash if we haven't seen it before
            ref schedD = A.commSchedules[id].D;
            if !schedD.contains(hash) {
                schedD += hash;
            }
            ref replArray = A.commSchedules[id].scheds[hash];
            replArray.replD.clear();
            replArray.idxD.clear();
            replArray.arrDom = A.localSubdomain();
        }
    } /* end of inspectorPreamble */
    pragma "inspector preamble"
    inline proc inspectorPreamble(obj, id : int, hash : (int,int,int,int))
    {
        return;
    }

    //###################################################################
    // inspectAccess: given an index that is assumed to be to the
    // array of interest, check whether the index would be a remote access.
    // This is done by looking at the local subdomain we have extracted
    // earlier (arrDom). If the index would lead to a remote access, add
    // it to the assocative domain (replD).
    //
    // replD:   the associative domain
    // arrDom:  the local subdomain
    // idx:     index to query
    //
    // returns: None
    //###################################################################
    pragma "inspect access"
    inline proc inspectAccess(ref replD, ref arrDom, idx)
    {
        local do if(!arrDom.contains(idx)) {
            replD += idx;
        }
    } /* end of inspectAccess */

    //###################################################################
    // executeAccess: given an index and the array of interest, determine
    // whether the access should be redirected to the replicated elements
    // we have or simply issued to the original array. This is ran during
    // the executor, with the assumption that the inspector has already
    // completed.
    //
    // arrDom:  A's local subdomain for this locale
    // replArr: associative array associated with this locale
    // A:        original array-of-interest
    // idx:     index used in access
    //
    // returns: reference to A[idx] if the access is remote;
    //          else reference to the replicated element in replRec
    //          that corresponds to idx.
    //
    //##################################################################
    pragma "execute access"
    inline proc executeAccess(arrDom, replArr, A, idx) ref
    {
        local do if(!arrDom.contains(idx)) {
            return replArr[idx];
        }

        else {
            return A[idx];
        }
    } /* end of executeAccess */

} /* end of SelectiveDataReplication module */
