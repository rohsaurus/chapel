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
    File:   RemoteWriteAggregation.chpl
    Date:   05/20/2022
    Author: Thomas Rolinger (tbrolin@cs.umd.edu)

    This is a module that we will use to perform aggregation
    specifically for remote writes as part of our irregular
    memory access optimizations.

    Ideally, we would pass in a FCF that represents the operation
    we want to aggregate. As of now, the support for FCFs is limited,
    so we can't do that. An alternative is to do something similar to
    how the Sort module uses comparators. The user/compiler creates a
    record that has a procedure that does the operation. We pass in the
    type of this record to the aggregator, and the aggregator will call
    that type's method (this needs to be a type method).
*/

module RemoteWriteAggregation
{
    use AggregationPrimitives;
    use CTypes;
    use ChplConfig;

    /*
        Copy/paste from CopyAggregation.chpl

        Sets up some internal parameters to use for aggregation. For our
        purposes, it seems a smaller buffer size is better than what it used
        in CopyAggregation.chpl. Also, we'll use different env variables so we
        don't conflict with the existing ones.

        TODO: test our apps on swan to see how the buffer size for ugni is
        reacting.
    */
    private param defaultBuffSize = if CHPL_COMM == "ugni" then 128 else 128;
    private const yieldFrequency = getEnvInt("CHPL_IRREG_AGGREGATION_YIELD_FREQUENCY", 1024);
    private const dstBuffSize = getEnvInt("CHPL_IRREG_AGGREGATION_DST_BUFF_SIZE", defaultBuffSize);


    //#########################################################################//
    //                                                                         //
    //              The RemoteWriteAggregator record                           //
    //                                                                         //
    //#########################################################################//
    /*
        srcValType: the type of the value we are writing
        dstType:    the type of the destination we are writing to
        opRecType:  the type of the record that defines the operation to aggregate
    */
    record RemoteWriteAggregator
    {
        type srcValType;
        type dstType;
        type opRecType;
        type aggType = (c_ptr(dstType), srcValType);
        var bufferSize = dstBuffSize;
        const myLocaleSpace = 0..<numLocales;
        var opsUntilYield = yieldFrequency;
        var lBuffers : c_ptr(c_ptr(aggType));
        var rBuffers : [myLocaleSpace] remoteBuffer(aggType);
        var bufferIdxs : c_ptr(int);

        proc init(type srcValType, type dstType, type opRecType)
        {
            this.srcValType = srcValType;
            this.dstType = dstType;
            this.opRecType = opRecType;
        }

        /*
            Post initialization: allocates buffers, etc.
        */
        proc postinit()
        {
            lBuffers = c_malloc(c_ptr(aggType), numLocales);
            bufferIdxs = bufferIdxAlloc();
            for loc in myLocaleSpace {
                lBuffers[loc] = c_malloc(aggType, bufferSize);
                bufferIdxs[loc] = 0;
                rBuffers[loc] = new remoteBuffer(aggType, bufferSize, loc);
            }
        }

        /*
            Destructor: flushes what is left in the buffers and then
            frees them.
        */
        proc deinit()
        {
            flush();
            for loc in myLocaleSpace {
                c_free(lBuffers[loc]);
            }
            c_free(lBuffers);
            c_free(bufferIdxs);
        }

        /*
            Flush: this is explictly called upon deinit(). It goes through
            each locale's buffer and flushes it, freeing the data along
            the way.
        */
        proc flush()
        {
            for loc in myLocaleSpace {
                _flushBuffer(loc, bufferIdxs[loc], freeData=true);
            }
        }

        /*
            Buffers an operation: this is what is called in place of
            the original operation. It takes in a destination address
            (i.e., A[B[i]]) and the value to write to that address.
            It will buffer those two as a tuple into a buffer for
            the locale that "dst" is located on. If that buffer is
            full upon adding it, we flush that buffer.
        */
        inline proc bufferOp(ref dst : dstType, const in srcVal : srcValType)
        {
            // Get the locale where dst is, and its local address on
            // that locale. getAddr() is defined in the AggregationPrimitives
            // module that is in CopyAggregation.chpl
            const loc = dst.locale.id;
            const dstAddr = getAddr(dst);

            // Get the current buffer index where we can add (dstAddr, srcVal) for
            // dst's locale
            ref bufferIdx = bufferIdxs[loc];

            lBuffers[loc][bufferIdx] = (dstAddr, srcVal);
            bufferIdx += 1;

            // If we are full, flush. The yielding stuff is to allow
            // other tasks to run if we have been running for a while.
            // This prevents us from blocking remote tasks from flushing.
            if bufferIdx == bufferSize {
                _flushBuffer(loc, bufferIdx, freeData=false);
                opsUntilYield = yieldFrequency;
            }
            else if opsUntilYield == 0 {
                chpl_task_yield();
                opsUntilYield = yieldFrequency;
            }
            else {
                opsUntilYield -= 1;
            }
        } /* end of bufferOp */

        /*
            Flushes a given locale's buffer.
        */
        proc _flushBuffer(const loc : int, ref bufferIdx, freeData)
        {
            // Store off bufferIdx into a const for the reads we'll
            // do. It is passed in as a ref because we will set it to
            // 0 after the flush.
            const myBufferIdx = bufferIdx;

            // Don't flush if there isn't anything to flush. This is
            // important for the flush() we do during deinit. If we
            // didn't do this check, it would still work but we'd waste
            // a lot of time.
            if myBufferIdx == 0 then return;

            // Allocate a remote buffer
            ref rBuffer = rBuffers[loc];
            const remBufferPtr = rBuffer.cachedAlloc();

            // Do a bulk copy of our local buffered data to
            // the remote buffer.
            rBuffer.PUT(lBuffers[loc], myBufferIdx);

            // On the destination local, process the remote buffer. It stores
            // tuples of destination addresses and the value to write to them.
            // For each tuple, we call opRecType.op().
            on Locales[loc] {
                for (dstAddr, srcVal) in rBuffer.localIter(remBufferPtr, myBufferIdx) {
                    opRecType.op(dstAddr.deref(), srcVal);
                }
                if freeData {
                    rBuffer.localFree(remBufferPtr);
                }
            }
            if freeData {
                rBuffer.markFreed();
            }
            bufferIdx = 0;
        } /* end of _flushBuffer */
    } /* end of RemoteWriteAggregator record*/

} /* end of RemoteWriteAggregation module */
