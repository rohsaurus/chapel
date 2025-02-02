/*
 * Copyright 2020-2024 Hewlett Packard Enterprise Development LP
 * Copyright 2004-2019 Cray Inc.
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

#ifndef _FORALL_STMT_H_
#define _FORALL_STMT_H_

#include "stmt.h"
#include "LoopWithShadowVarsInterface.h"

// added by tbrolin
#include <tuple>

enum ForallAutoLocalAccessCloneType {
  NOT_CLONE,
  NO_OPTIMIZATION,
  STATIC_ONLY,
  STATIC_AND_DYNAMIC
};

// Support for reporting calls that are not optimized for different reasons
enum CallRejectReason {
  CRR_ACCEPT,
  CRR_NOT_ARRAY_ACCESS_LIKE,
  CRR_NO_CLEAN_INDEX_MATCH,
  CRR_ACCESS_BASE_IS_LOOP_INDEX,
  CRR_ACCESS_BASE_IS_NOT_OUTER_VAR,
  CRR_ACCESS_BASE_IS_COMPLEX_SHADOW_VAR,
  CRR_ACCESS_BASE_IS_REDUCE_SHADOW_VAR,
  CRR_TIGHTER_LOCALITY_DOMINATOR,
  CRR_UNKNOWN,
};

class ALACandidate {
  public:
    ALACandidate() = delete;
    ALACandidate(CallExpr *call, ForallStmt *forall, bool checkArgs=false);
    inline CallExpr* getCall() const { return call_; }

    inline int getIterandIdx() const { return iterandIdx_; }
    inline void setIterandIdx(int iterandIdx) { iterandIdx_ = iterandIdx; }

    inline CallRejectReason getReason() const { return reason_; }
    inline void setReasonIfNeeded(CallRejectReason reason) {
      if (!hasReason() || reason_ == CRR_ACCEPT) reason_ = reason;
    }

    inline bool hasReason() const { return reason_ != CRR_UNKNOWN; }
    inline bool shouldReport() const {
      return reason_ != CRR_UNKNOWN && reason_ != CRR_NOT_ARRAY_ACCESS_LIKE;
    }
    inline bool isRejected() const { return reason_ != CRR_ACCEPT; }

    inline std::vector<Expr*>& offsetExprs() { return offsetExprs_; }
    void addOffset(Expr* e);

    inline bool hasOffset() const { return hasOffset_; }

    Symbol* getCallBase() const;

  private:
    CallExpr *call_;
    int iterandIdx_;
    CallRejectReason reason_;
    std::vector<Expr*> offsetExprs_;
    bool hasOffset_;

    bool argsSupported(const std::vector<Symbol *> &syms);

    // the following are helpers to extract information from +/- operators
    // (unary or binary) in the context of ALA. They don't read or modify
    // ALACandidate instances.
    static bool isCallPlusOrMinus(CallExpr* call);
    static SymExpr* getSymFromValidUnaryOp(Expr* e);
    static bool getIdxAndOffsetFromPlusMinus(CallExpr* call,
                                             Symbol* loopIdx,
                                             SymExpr*& accIdxExpr,
                                             Expr*& offsetExpr);
    static int findLoopIdxInPlusMinus(CallExpr* call, Symbol* loopIdx);
};

// added by tbrolin
enum ForallIrregAccessCloneType {
  ORIGINAL,
  CLONED,
  PENDING_OPTIMIZATION,
  INSPECTOR,
  EXECUTOR,
  AGGREGATED,
  INVALID_OPT,
};
enum ieIndexIteratorType {
  NORMAL,               // for i in foo
  NORMAL_REC_FIELD,     // for i in foo where foo is ref foo = rec.field
  DOT_DOMAIN,           // for i in foo.domain
  DOT_DOMAIN_REC_FIELD  // for i in foo.domain where foo is ref foo = rec.field
};
enum IrregWriteAggrOp {
  INVALID,      // indicates that the operation is not valid for aggregation
  GENERAL,      // general operation (A[B[i]] op val)
  ASSIGNMENT,   // A[B[i]] = val
  PLUSEQ,       // A[B[i]] += val
  ATOMIC_ADD    // A[B[i]].add(val)
};
enum PrefetchLoopIteratorType {
  INVALID_LOOP_TYPE,
  ARRAY_OR_DOMAIN,
  EXPLICIT_DOMAIN,
  RANGE
};
enum LoopRangeOperatorType {
  COUNT_OPERATOR,
  NUDGE_HIGH_BOUND,
  NO_OPERATOR,
  NOT_A_RANGE
};

// added by tbrolin 09/14/2022
// struct to encapsulate a prefetch candidate
typedef struct AdaptiveRemotePrefetchingCandidate {
  // if the candidate is in a ForLoop, record that
  // so we can get anything we need from it later.
  // If it is not in a for loop, this is NULL.
  ForLoop *forloop;

  // the stride of the loop/access as specified via
  // a "by" clause. This is NULL if there is no by clause.
  // Note that this can be a literal (a SymExpr) or an
  // expression (CallExpr).
  Expr *byClauseStride;

  // the type of the loop iterator. We allow the loop
  // the iterate over an array or domain object, a "dot domain",
  // or a range.
  PrefetchLoopIteratorType loopIteratorType;

  // the loop iterator if we are iterating over an array or domain.
  // If the loopIteratorType is ARRAY_OR_DOMAIN, than this is "foo"
  // from "for i in foo". If the type is EXPLICIT_DOMAIN, than this
  // is "bar" from "for i in bar.domain". If the type is RANGE, then
  // this is NULL;
  Symbol *loopIteratorSym;

  // The A[expr(B[expr])] call expression. In other words,
  // the entire access of interest.
  CallExpr *parentCall;

  // The B[expr] portion of parentCall.
  CallExpr *call;

  // Set of Symbols used in parentCall. So for something like
  // A[B[i+j+k] * m] we will extract the Symbols for i,j,k,m.
  // The purpose is to keep these around so when/if we get to
  // post resolution, we can do some analysis. Specifically,
  // all of these Symbols must be read-only in the loop that
  // contains the prefetch candidate.
  std::set<Symbol *>prefetchIndexSymbols;

  // The range operator (#, < or nothing), if there is a range.
  // We need to know this to effectively compute the bounds of
  // the loop
  LoopRangeOperatorType loopRangeOperator;

  // The start of the range, if we're iterating over a range.
  // NULL otherwise
  Expr *rangeStart;

  // The end of the range, if we're iterating oer a range.
  // NULL otherwise
  Expr *rangeEnd;

  // The index variable now yielded by the custom iterator, if
  // we applied one. This is NULL if we did not need to apply it
  VarSymbol *prefetchIter_idx;

  // The original loop index variable yielded by the iterator.
  // We will probably want access to this when we create the
  // prefetch call. 
  Symbol *originalIter_idx;

  // The prefetch distance Symbol for this candidate. It is a shadow
  // variable as part of the forall. We also have shadow variables for
  // the iteration count and windows, etc.
  ShadowVarSymbol *prefetchDistance;
  ShadowVarSymbol *iterCount;
  ShadowVarSymbol *windowLate;
  ShadowVarSymbol *windowUseless;
  ShadowVarSymbol *stopPrefetching;
  ShadowVarSymbol *distArr;
  ShadowVarSymbol *countArr;

  // Unique ID given to the candidate
  int ID;

  // VarSymbols for the loopStride and lastValidIndex. We'll
  // refer to these when inserting calls to Chapel functions to
  // support the optimization.
  VarSymbol *loopStride;
  VarSymbol *lastValidIndex;
  VarSymbol *numSamples;

  // The static check variable used to "control" whether the
  // optimization will be performed or not. We also have the
  // CondStmt it is used in
  VarSymbol *staticCheck;
  CondStmt *staticCond;

  // CondStmt for the out-of-bounds check
  CondStmt *outOfBoundsCond;

  // CondStmt for isArray() check when we had
  // an iterator type of ARRAY_OR_DOMAIN
  CondStmt *isArrayCond;

} AdaptiveRemotePrefetchingCandidate;

class ForallOptimizationInfo {
  public:
    bool infoGathered;

    std::vector<Symbol *> iterSym;
    std::vector<Expr *> dotDomIterExpr;
    std::vector<Symbol *> dotDomIterSym;
    std::vector<Symbol *> dotDomIterSymDom;

    std::vector<CallExpr *> iterCall;  // refers to the original CallExpr
    std::vector<Symbol *> iterCallTmp; // this is the symbol to use for checks

    // even if there is a single index we store them in a vector
    std::vector< std::vector<Symbol *> > multiDIndices;

    // calls in the loop that are candidates for ALA optimization
    std::vector<ALACandidate> staticCandidates;
    std::vector<ALACandidate> dynamicCandidates;

    // added by tbrolin
    // Flag that says whether the forall has been checked by the
    // adaptive remote prefetching optimization
    bool adaptiveRemotePrefetchingChecked;
    int arpID;
    // Holds candidates for prefetching optimization; since we support more than 1
    // prefetch candidate per forall, it is cleaner to store candidates in a vector,
    // encapsulating their info into a struct.
    std::vector<AdaptiveRemotePrefetchingCandidate> adaptiveRemotePrefetchingCandidates;

    // added by tbrolin
    // For the IE optimization, we only allow 1 candidate per forall, so not much sense
    // in storing a vector of candidates like we do above for prefetching. But our existing
    // code assumed we had a vector, so might as well keep it.
    std::vector< std::pair<CallExpr *, CallExpr *> > ieCandidates;
    std::vector< std::pair<Symbol *, Symbol *> > ieCandidatesResolved;
    // unique ID given to the forall for the inspector-executor
    // optimizaton
    int ieID;
    VarSymbol *ieIDVar;
    // the call-site hash we compute and pass into various procedures
    // to access the replicated arrays
    VarSymbol *ieHash;
    // Global inspector flag used by the forall.
    VarSymbol *inspectorFlag;
    // holds the forall iterator Symbol found during normalization.
    // In the case of "forall a in foo" this will hold "foo". In the
    // case of "forall a in foo.domain", it also holds "foo". Later on,
    // we'll find its domain, which is what we really care about.
    Symbol *ieForallIteratorSym;
    // Holds the Symbol that yields "i" in A[B[i]]. We find this
    // during normalization. In the case of "... i in foo" we get
    // foo. In the case of "... i in foo.domain" we also get foo.
    // If foo is defined inside the forall as a ref to something
    // outside, we will get that outside alias. The special case is
    // when we have something like "ref foo = rec.field". In that case,
    // we get foo but mark it as special.
    Symbol *ieIndexIterator;
    // will be NORMAL if we had something like "i in foo"
    // and foo is defined outside of the loop or is an alias
    // to something outside of the loop. It will be DOT_DOMAIN
    // if we had something like "i in foo.domain". It will be
    // REC_FIELD if we had something like "ref foo = rec.field"
    ieIndexIteratorType indexIteratorType;
    // Flag that says if the loop has been processed for the IE
    // optimization, and the clone type.
    bool inspectorExecutorChecked;
    ForallIrregAccessCloneType cloneTypeIE;
    // Map of all relevant loop iterator symbols for the IE optimization.
    // These are iterators that yield symbols used in the irregular access.
    // We have a map of pairs since we could have the same Symbol used in two
    // different loop iterators but one as "foo" and the other as "foo.domain".
    // In that way, they are different based on their index iterator type.
    std::map<std::pair<Symbol *, ieIndexIteratorType>, bool> ieLoopIteratorSyms;
    // Map of all the relevant variables used in an IE candidate access.
    // We ensure they are yielded by loops over arrays/domains and track
    // changes to those array/domains. But we also need to ensure that the
    // index variables themselves are not changed within the forall. This is
    // allowed if the variable is yielded by an array
    std::set<Symbol *> ieIndexSymbols;
    // Keeps track of the function ID that this forall is nested in.
    // We only count the function if it isn't the module init function.
    // We use this for our call path analysis. During normalization, we
    // set this field to a unqiue ID, and any forall in the same function
    // gets the same ID.
    int functionID;
    // Determined during normalization whether we had something like
    // "ref t = A[B[i]]". We want to know this during prefolding so we
    // can make some additional checks.
    bool nonConstRefIE;
    
    // added by tbrolin
    // Stuff for remote write aggregation. We don't need to store much, just LHS and RHS
    bool irregWriteAggregationChecked;
    // what we need to store is the LHS (A[B[i]]), the RHS and
    // operation type (+=, =, .add(), or GENERAL).
    std::vector< std::tuple<Expr *, Expr *, IrregWriteAggrOp> > irregWriteAggrCandidates;
    

    // the static check control symbol added for symbol
    std::map<Symbol *, Symbol *> staticCheckSymForSymMap;
    std::map<Symbol *, Symbol *> staticCheckWOffSymForSymMap;

    // the dynamic check call added for symbol
    std::map<Symbol *, CallExpr *> dynamicCheckForSymMap;

    std::vector<Symbol *> staticCheckSymsForDynamicCandidates;

    bool autoLocalAccessChecked;
    bool hasAlignedFollowers;

    ForallAutoLocalAccessCloneType cloneType;

    ForallOptimizationInfo();

    Expr* getIterand(int idx);
    Expr* getLoopDomainExpr();
};

///////////////////////////////////
// forall loop statement         //
///////////////////////////////////

class ForallStmt final : public Stmt, public LoopWithShadowVarsInterface
{
public:
  Expr* asExpr() override { return this; }

  bool       zippered()       const; // 'zip' keyword used and >1 index var
  AList&     inductionVariables();   // DefExprs, one per iterated expr
  const AList& constInductionVariables() const; // const counterpart
  AList&     iteratedExpressions();  // Exprs, one per iterated expr
  const AList& constIteratedExpressions() const;  // const counterpart
  AList&     shadowVariables() override;      // DefExprs of ShadowVarSymbols
  BlockStmt* loopBody()       const override; // the body of the forall loop
  std::vector<BlockStmt*> loopBodies() const; // body or bodies of followers
  LabelSymbol* continueLabel();      // create it if not already
  CallExpr* zipCall() const;

  // when originating from a ForLoop or a reduce expression
  bool createdFromForLoop()     const;  // is converted from a for-loop
  bool needToHandleOuterVars()  const override;  // yes, convert to shadow vars
  bool needsInitialAccumulate() const override;  // for a reduce intent
  bool fromReduce()             const;  // for a Chapel reduce expression
  bool overTupleExpand()        const;  // contains (...tuple) iterable(s)
  bool allowSerialIterator()    const;  // ok to loop over a serial iterator?
  bool requireSerialIterator()  const;  // do not seek standalone or leader

  DECLARE_COPY(ForallStmt);
  ForallStmt* copyInner(SymbolMap* map) override;


  void        verify() override;
  void        accept(AstVisitor* visitor) override;
  GenRet      codegen() override;

  void        replaceChild(Expr* oldAst, Expr* newAst) override;
  Expr*       getFirstExpr() override;
  Expr*       getNextExpr(Expr* expr) override;
  void        setZipCall(CallExpr *call);

  static ForallStmt* buildHelper(Expr* indices, Expr* iterator,
                                 CallExpr* intents, BlockStmt* body,
                                 bool zippered, bool fromForLoop);

  static BlockStmt*  build(Expr* indices, Expr* iterator, CallExpr* intents,
                           BlockStmt* body, bool zippered, bool serialOK);

  static ForallStmt* fromForLoop(ForLoop* forLoop);

  static ForallStmt* fromReduceExpr(VarSymbol* idx, SymExpr* dataExpr,
                                    ShadowVarSymbol* svar,
                                    bool zippered, bool requireSerial);

  // helpers

  int numInductionVars()  const;
  int numIteratedExprs()  const;
  int numShadowVars()     const;

  DefExpr* firstInductionVarDef() const;
  Expr*    firstIteratedExpr()    const;
  void setNotZippered();
  bool isReduceIntent(Symbol* var) const;
  bool hasVectorizationHazard() const;
  void setHasVectorizationHazard(bool v);

  // indicates a forall expression (vs a forall statement)
  bool isForallExpr() const;

  ForallOptimizationInfo optInfo;

  void insertZipSym(Symbol *sym);

  bool isInductionVar(Symbol* sym) override;

  bool isForallStmt() final override { return true; }
  ForallStmt *forallStmt() final override { return this; }

private:
  AList          fIterVars;    // DefExprs of the induction vars
  AList          fIterExprs;
  AList          fShadowVars;  // may be empty
  BlockStmt*     fLoopBody;    // always present
  bool           fZippered;
  CallExpr*      fZipCall;
  bool           fFromForLoop; // see comment below
  bool           fFromReduce;
  bool           fOverTupleExpand;
  bool           fAllowSerialIterator;
  bool           fRequireSerialIterator;
  bool           fVectorizationHazard;
  bool           fIsForallExpr;

  // constructor
  ForallStmt(BlockStmt* body);

public:
  LabelSymbol*            fContinueLabel;
  LabelSymbol*            fErrorHandlerLabel;

  // for recursive iterators during lowerIterators
  DefExpr*       fRecIterIRdef;
  DefExpr*       fRecIterICdef;
  CallExpr*      fRecIterGetIterator;
  CallExpr*      fRecIterFreeIterator;
};

/*
fFromForLoop and its accessors

These support handling of some ForLoops by converting them to ForallStmts.
They cause skipping certain actions for these "conversion" ForallStmt nodes.

Why not just have a single accessor to fFromForLoop? This is to emphasize
that the three accessors check different properties. These properties could
potentially be independent of each other.

fFromReduce and its accessors

These support handling of reduce exprs by converting them to ForallStmts.
Same idea as fFromForLoop.
*/

/// accessor implementations ///

inline bool   ForallStmt::zippered()         const { return fZippered;   }
inline AList& ForallStmt::inductionVariables()     { return fIterVars;   }
inline const AList& ForallStmt::constInductionVariables() const {
  return fIterVars;
}
inline AList& ForallStmt::iteratedExpressions()    { return fIterExprs;  }
inline const AList& ForallStmt::constIteratedExpressions() const {
  return fIterExprs;
}
inline AList& ForallStmt::shadowVariables()        { return fShadowVars; }
inline BlockStmt* ForallStmt::loopBody()     const { return fLoopBody;   }

inline CallExpr* ForallStmt::zipCall()       const { return fZipCall;    }

inline bool ForallStmt::needToHandleOuterVars() const { return !fFromForLoop; }
inline bool ForallStmt::createdFromForLoop()    const { return  fFromForLoop; }
inline bool ForallStmt::needsInitialAccumulate()const { return !fFromReduce;  }
inline bool ForallStmt::fromReduce()            const { return  fFromReduce;  }
inline bool ForallStmt::overTupleExpand()       const { return fOverTupleExpand;       }
inline bool ForallStmt::allowSerialIterator()   const { return fAllowSerialIterator;   }
inline bool ForallStmt::requireSerialIterator() const { return fRequireSerialIterator; }
/// conveniences ///

inline int   ForallStmt::numInductionVars()  const { return fIterVars.length; }
inline int   ForallStmt::numIteratedExprs()  const { return fIterExprs.length;}
inline int   ForallStmt::numShadowVars()     const { return fShadowVars.length;}
inline Expr* ForallStmt::firstIteratedExpr() const { return fIterExprs.head;  }
inline DefExpr* ForallStmt::firstInductionVarDef() const { return toDefExpr(fIterVars.head); }

#define for_shadow_var_defs(SVD,TEMP,FS)    \
  for_alist(TEMP,(FS)->shadowVariables())   \
    if (DefExpr* SVD = toDefExpr(TEMP))

#define for_shadow_vars_and_defs(SV,DEF,TEMP,FS)           \
  for_shadow_var_defs(DEF,TEMP,FS)                         \
    if (ShadowVarSymbol* SV = toShadowVarSymbol(DEF->sym))

#define for_shadow_vars(SV,TEMP,FS)         \
  for_shadow_vars_and_defs(SV,SVD,TEMP,FS)

/// helpers ///

ForallStmt* enclosingForallStmt(Expr* expr);
ForallStmt* isForallIterVarDef(Expr* expr);
ForallStmt* isForallIterExpr(Expr* expr);
ForallStmt* isForallRecIterHelper(Expr* expr);
ForallStmt* isForallLoopBody(Expr* expr);
const ForallStmt* isConstForallLoopBody(const Expr* expr);
VarSymbol*  parIdxVar(ForallStmt* fs);

QualifiedType fsIterYieldType(Expr* ref, FnSymbol* iterFn);
bool fsGotFollower(Expr* anchor, Symbol* followThis, Symbol* iterSym);
void fsCheckNumIdxVarsVsIterables(ForallStmt* fs, int numIdx, int numIter);

/// done ///

#endif
