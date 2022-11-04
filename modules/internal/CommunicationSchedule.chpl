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
    File:   CommunicationSchedule.chpl
    Date:   12/28/2021
    Author: Thomas Rolinger (tbrolin@cs.umd.edu)

    This is a module that defines the ReplicatedElems record
    and CommunicationSchedule records, as well as various
    various methods associated with them. This is used as
    part of the Selective Data Replication optimization.
    Specifically, these records store information as it
    relates to elements that are replicated on a locale.
*/

module CommunicationSchedule {

    private use ChapelStandard;
    use ChapelAutoAggregation.CopyAggregation;

    /**************************************************************************

        ReplicatedElems record

        This is the record that each locale will use to replicate remotely
        accessed data as part of the selective data replication optimization.
        At its core, this record contains an associative array that maps the
        the array-of-interest's indices to their corresponding values. The
        index/value pairs refer specifically to elements of the array-of-interest
        that are accessed remotely from a given locale within a kernel of interest.

        We also have a separate default array of the associative array's indices
        that are sorted. This provides much faster accesses during the update()
        routine.

        This record is parameterized on the array-of-interest's element type,
        index type and its rank.

        elemType:   The type of element that is to be replicated
        idxType:    The type of the index used to access the replicated elements
        rank:       The rank of the array (1-D, 2-D, etc).
        replD:      Associative domain used to represent replicated elements
        replArr:    Associative array used to store replicated elements
        idxD:       Domain used to create an array of sorted keys from replD
        indices:    Sorted array of keys (indices) from replD
        arrDom:     local subdomain of the original array-of-interest that
                    corresponds to the locale associated with this reocrd.

    **************************************************************************/
    record ReplicatedElems {
        type elemType;
        type idxType;
        param rank;
        var replD : domain(idxType, parSafe=false);
        var replArr : [replD] elemType;
        var idxD : domain(1) = {1..0};
        var indices : [idxD] idxType;
        var arrDom : domain(rank);

        //###################################################################
        // init: Assigns the element and index types and the rank
        //###################################################################
        proc init(type elemType, type idxType, param rank)
        {
            this.elemType = elemType;
            this.idxType = idxType;
            this.rank = rank;
        } /* end of init */
    } /* end of ReplicatedElems */

    /**************************************************************************

        CommunicationSchedule record

        This is an encapsulation of a set of ReplicatedElems records. The
        motivation is as follows: for a given forall that is being optimized,
        it could be within a function, where A and B are passed in arguments.
        It is necessary to associate separate replicated arrays for each call
        site. Consider

                func(A,B); func(A,C); func(A,B);

        In this example, the first call will run the inspector and populate
        A's ReplicatedElems record(s). The next call will also run the inspector,
        since our inspector flag is associated with a call-site hashing, and C is
        different from B. This will "wipe out" A's replicated arrays and re-populate
        them based on C. When we get to the last call to func(), we do not re-run
        the inspector since nothing has changed from the first call site that
        would cause it to be re-run. However, A no longer has a schedule w.r.t. B.

        So a CommunicationSchedule will contain an associative array of
        ReplicatedElems records, where the keys will be call-site hashes
        like we did for the inspector flag. The array-of-interest will store
        an array of these CommunicationSchedule records, one for each forall
        loop that is being optimized and the array is used in.

        elemType:   element type of the array of interest
        idxType:    index type of the array of interest
        rank:       rank of the array of interest
        D:          associative domain of hashes (4 element tuples)
        scheds:     associative array of ReplicatedElems records

    **************************************************************************/
    record CommunicationSchedule {
        type elemType;
        type idxType;
        param rank;
        var D : domain((int,int,int,int)); // hash is a 4 element tuple
        var scheds : [D] ReplicatedElems(elemType, idxType, rank);

        //###################################################################
        // init: Assigns the element and index types and the rank
        //###################################################################
        proc init(type elemType, type idxType, param rank)
        {
            this.elemType = elemType;
            this.idxType = idxType;
            this.rank = rank;
        } /* end of init */

        //###################################################################
        // TODO: This copy-init seems to be required when we have distributed arrays
        // of certain element types, like lists. In that case, we get compiler
        // errors about not being able to copy-initialize. Adding this works,
        // since we omit copying over the scheds field. See issue
        // https://github.com/thomasrolinger/chapel/issues/18 for more details.
        //###################################################################
        proc init=(other : CommunicationSchedule)
        {
            this.elemType = other.elemType;
            this.idxType = other.idxType;
            this.rank = other.rank;
            this.D = other.D;
        } /* end of init= */

    } /* end of CommunicationSchedule record */

    /***********************************************************************
        Below are procedures that operate on ReplicatedElems records
    ************************************************************************/

    //###################################################################
    // Index sorting: assumption is that this is called once
    // replD has been populated
    //
    // replRec: A ReplicatedElems record
    //###################################################################
    inline proc sortIndices(ref replRec)
    {
        local {
            replRec.idxD = {0..#replRec.replD.size};
            replRec.indices = for x in replRec.replD.sorted() do x;
        }
    } /* end of sortIndices */

    //###################################################################
    // Update: iterate through indices and grap the corresponding value
    // from the original array origArr. This uses src aggregation for
    // optimizing the remote reads.
    //
    // This routine will be used when the element type of the arrays
    // are primitives (int, real, etc.).
    //
    // replRec: A ReplicatedElems record
    // origArr: original array of interest
    //###################################################################
    inline proc update(ref replRec, origArr)
    {
        ref replArr = replRec.replArr;
        const ref indices = replRec.indices;
        forall idx in indices with (var agg = new SrcAggregator(replRec.elemType)) {
            agg.copy(replArr[idx], origArr[idx]);
        }
    } /* end of update */

} /* end of CommunicationSchedule module */
