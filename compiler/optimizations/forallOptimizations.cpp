/*
 * Copyright 2020-2022 Hewlett Packard Enterprise Development LP
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

#include <algorithm>

#include "astutil.h"
#include "build.h"
#include "ForallStmt.h"
#include "LoopExpr.h"
#include "LoopStmt.h"
#include "passes.h"
#include "preFold.h"
#include "forallOptimizations.h"
#include "optimizations.h"
#include "resolution.h"
#include "stlUtil.h"
#include "stringutil.h"
#include "view.h"

#include "global-ast-vecs.h"

// This file contains analysis and transformation logic that need to happen
// before normalization. These transformations help the following optimizations:
//
// - symbolic fast follower check: Avoids dynamic costs for checking for fast
//                                followers in cases where the follower can be
//                                proven to be aligned with the leader. e.g.
//                                `zip(A, A.domain)`
// - automatic local access: Use `localAccess` instead of `this` for array
//                           accesses that can be proven to be local
//
// - automatic aggregation: Use aggregation instead of regular assignments for
//                          applicable last statements within `forall` bodies
//
// - inspector executor: Look for accesses of the form A[B[i]] where A and B
//                       are arrays. Idea is to use an inspector to determine
//                       the remote values of A needed by each locale and
//                       replicate them.
//
// - irreg write aggregation: Looks for A[B[i]] on the LHS of a write that can
//                            be aggregated. Similar to existing auto aggregation
//                            but a bit more general in what can be aggregated, but
//                            also restricted to writes to A[B[i]].
//
// - adaptive remote prefetching: Looks for less-restrictive cases of A[B[i]] reads when
//                                compared to the inspector executor. The optimization inserts
//                                calls to prefetch data into the remote cache. It is called
//                                "adaptive" because the amount of look-ahead (i.e., prefetch distance)
//                                is adjusted as the forall loop runs.

static int curLogDepth = 0;
static bool LOG_ALA(int depth, const char *msg, BaseAST *node);
static void LOGLN_ALA(BaseAST *node);

static bool LOG_AA(int depth, const char *msg, BaseAST *node);
static void LOGLN_AA(BaseAST *node);

// Support for reporting calls that are not optimized for different reasons
enum CallRejectReason {
  CRR_ACCEPT,
  CRR_NOT_ARRAY_ACCESS_LIKE,
  CRR_NO_CLEAN_INDEX_MATCH,
  CRR_ACCESS_BASE_IS_LOOP_INDEX,
  CRR_ACCESS_BASE_IS_NOT_OUTER_VAR,
  CRR_ACCESS_BASE_IS_SHADOW_VAR,
  CRR_TIGHTER_LOCALITY_DOMINATOR,
  CRR_UNKNOWN,
};

// we store all the locations where we have added these primitives. When we
// report finalizing an optimization (either positively or negatively) we remove
// those locations from the set. Towards the end of resolution, if there are
// still items left in these sets, those indicate that we reverted the
// optimization by completely removing the block that those primitives are in.
std::set<astlocT> primMaybeLocalThisLocations;
std::set<astlocT> primMaybeAggregateAssignLocations;


static bool callHasSymArguments(CallExpr *ce, const std::vector<Symbol *> &syms);
static Symbol *getDotDomBaseSym(Expr *expr);
static Expr *getDomExprFromTypeExprOrQuery(Expr *e);
static Symbol *getDomSym(Symbol *arrSym);
static Symbol *getDomSymFromDomExpr(Expr *domExpr, bool allowQuery);
static Expr *getLocalityDominator(CallExpr* ce);
static bool isSubIndexAssignment(Expr *expr,
                                 Symbol *subIndex,
                                 int indexIndex,
                                 Symbol *indexBundle);
static std::vector<Symbol *> getLoopIndexSymbols(ForallStmt *forall,
                                                 Symbol *baseSym);
static void gatherForallInfo(ForallStmt *forall);
static bool loopHasValidInductionVariables(ForallStmt *forall);
static Symbol *canDetermineLoopDomainStatically(ForallStmt *forall);
static Symbol *getCallBaseSymIfSuitable(CallExpr *call, ForallStmt *forall,
                                        bool checkArgs, int *argIdx,
                                        CallRejectReason *reason=NULL);
static Symbol *getCallBase(CallExpr *call);
static void generateDynamicCheckForAccess(CallExpr *access,
                                          ForallStmt *forall,
                                          int iterandIdx,
                                          CallExpr *&allChecks);
static Symbol *generateStaticCheckForAccess(CallExpr *access,
                                            ForallStmt *forall,
                                            int iterandIdx,
                                            Expr *&allChecks);
static CallExpr *replaceCandidate(CallExpr *candidate,
                                  Symbol *staticCheckSym,
                                  bool doStatic);
static void optimizeLoop(ForallStmt *forall,
                         Expr *&staticCond, CallExpr *&dynamicCond,
                         bool doStatic);
static CallExpr *addStaticCheckSymsToDynamicCond(ForallStmt *forall,
                                     CallExpr *dynamicCond,
                                     std::vector<Symbol *> &staticCheckSyms);
static ForallStmt *cloneLoop(ForallStmt *forall);
static void constructCondStmtFromLoops(Expr *condExpr,
                                       ForallStmt *optimized,
                                       ForallStmt *unoptimized);

static void generateOptimizedLoops(ForallStmt *forall);
static void autoLocalAccess(ForallStmt *forall);
static CallExpr *revertAccess(CallExpr *call);
static CallExpr *confirmAccess(CallExpr *call);

static void symbolicFastFollowerAnalysis(ForallStmt *forall);

static bool canBeLocalAccess(CallExpr *call);
static bool isLocalAccess(CallExpr *call);
static const char *getForallCloneTypeStr(Symbol *aggMarker);
static CallExpr *getAggGenCallForChild(Expr *child, bool srcAggregation);
static bool assignmentSuitableForAggregation(CallExpr *call, ForallStmt *forall);
static void insertAggCandidate(CallExpr *call, ForallStmt *forall);
static bool handleYieldedArrayElementsInAssignment(CallExpr *call,
                                                   ForallStmt *forall);
static void findAndUpdateMaybeAggAssign(CallExpr *call, bool confirmed);
static CallExpr *findMaybeAggAssignInBlock(BlockStmt *block);
static void removeAggregatorFromMaybeAggAssign(CallExpr *call, int argIndex);
static void removeAggregatorFromFunction(Symbol *aggregator, FnSymbol *parent);
static void removeAggregationFromRecursiveForallHelp(BlockStmt *block);
static void autoAggregation(ForallStmt *forall);

////////////////////////////////////////////
//                                        //
//  Added by tbrolin 1/11/2022 - present  //
//                                        //
////////////////////////////////////////////
#include "ForLoop.h"
#include "WhileStmt.h"
#include "wellknown.h"
#include "resolveFunction.h"
#include "DeferStmt.h"

//////////////////////////////////////////////////////////
//                                                      //
//  Inspector-executor Normalization Related Functions  //
//                                                      //
//////////////////////////////////////////////////////////
static void inspectorExecutor(ForallStmt *forall);
static void findCandidatesIE(ForallStmt* forall);
static bool doesCallHaveNestedCallBaseIE(CallExpr *call);
static void analyzeCandidateIE(CallExpr *call,
                               CallExpr *parentCall,
                               ForallStmt *forall);
static void setForallFunctionIdIE(ForallStmt *forall);
static void generateOptimizedLoopsIE(ForallStmt* forall);
static void createPrimitiveIE(int accessType,
                              int ID,
                              VarSymbol *hasSingleLocalSubdomain,
                              VarSymbol *isForallDistributed,
                              Symbol *forallIterSym,
                              Symbol *indexIterator,
                              std::map<std::pair<Symbol *, ieIndexIteratorType>, bool> loopIteratorSyms,
                              Expr *parentCall,
                              Expr *call);
static void generateInspectorExecutorLoops(ForallStmt *forall);
static void createStrippedInspectorLoop(ForallStmt *inspectorLoop,
                                        std::vector<CallExpr *>primitives);
static bool stripInspectorLoop(BlockStmt *block,
                               CallExpr *prim,
                               std::vector<Expr *> &exprsToRemove,
                               std::map<Symbol *, bool> &symbolsToTrack);
static void replaceIteratorWithInspectorIterator(ForallStmt *inspectorLoop);

////////////////////////////////////////////////////////
//                                                    //
//  Inspector-executor Pre-folding Related Functions  //
//                                                    //
////////////////////////////////////////////////////////
static void printIEPreFoldHeader(CallExpr *call);
static void printIEPreFoldFooter(CallExpr *call);
static bool isIEOptimizationValid(CallExpr *call);
static bool fieldAccessesAreValidIE(CallExpr *call);
static CallExpr *processInspectorAccess(CallExpr *call);
static CallExpr *processExecutorAccess(CallExpr *call);
static CallExpr *revertPrimitiveIE(CallExpr *call);

////////////////////////////////////////////////////////////
//                                                        //
//  Inspector-executor Post-resolution Related Functions  //
//                                                        //
////////////////////////////////////////////////////////////
static void detectCyclesInCallGraphIE(CallExpr *call,
                                      std::map<int, bool> &executorProcessed);
static bool depthFirstSearchIE(FnSymbol *fn,
                               std::set<FnSymbol *> &visitedFunctions);
static void executeAccessCallPostAnalysis(CallExpr *call,
                                          std::map<int, bool> &inspectorProcessed);
static Symbol *domainSymbolForArray(Symbol *arr,
                                    Expr *expr,
                                    bool &isRecordField,
                                    std::map<Symbol *, bool> &aliasesAnalyzed,
                                    AggregateType *&at);
static void findAllModificationsToSymbol(Symbol *sym,
                                         Expr *expr,
                                         std::map<Symbol *, std::map<CallExpr *, bool>> &modifications,
                                         std::map<Symbol *, bool> &aliasesAnalyzed,
                                         std::map<Symbol *, std::set<Symbol *>> &aliasSymbols,
                                         bool isRecordField,
                                         AggregateType *at);
static Symbol *detectAliasesInCall(CallExpr *call,
                                   SymExpr *symexpr,
                                   bool checkCase4);
static FnSymbol *isSymbolRecordField(Symbol *sym,
                                     Symbol *&fieldSym,
                                     AggregateType *&at);
/*static void cleanUpAliasSymbols(std::map<Symbol *, std::set<Symbol *>> &origAliases,
                                std::map<Symbol *, std::set<Symbol *>> &newAliases);*/
static bool isSymbolModifiedInForall(ForallStmt *forall,
                                     std::map<Symbol *, std::map<CallExpr *, bool>> &modifications,
                                     bool allowWrites);
static bool isSymbolModifiedBeforeForall(ForallStmt *forall,
                                         std::map<Symbol *, std::map<CallExpr *, bool>> &modifications);
static void turnInspectorOnAfterModifcations(ForallStmt *forall,
                                             std::map<Symbol *, std::map<CallExpr *, bool>> &modifications);
static void insertCallToInspectorOn(VarSymbol *ieFlag,
                                    CallExpr *mod,
                                    ForallStmt *forall);
static int insertInspectorOnAfterLoop(Expr *loop,
                                      ForallStmt *forall,
                                      BlockStmt *dummyBlock,
                                      VarSymbol *ieFlag);
static bool isInspectorOnCall(Expr *expr,
                              VarSymbol *ieFlag);
static void dynamicCallPathAnalysisIE(CallExpr *call,
                                      std::map<int, bool> &forallProcessed);
static void findLocationsForCallPathFlagsIE(FnSymbol *fn,
                                            FnSymbol *modInitFn,
                                            std::set<Expr *> &hasOuterLoopLocs,
                                            std::set<Expr *> &hasInvalidEnclosingStructureLocs,
                                            Expr *lastOuterLoop,
                                            Expr *lastInvalidStructure);

////////////////////////////////////////////////////
//                                                //
//  Inspector-executor Utility Related Functions  //
//                                                //
////////////////////////////////////////////////////
static void removeOptimizationIE(int ID,
                                 FnSymbol *fn);
static void mapArrayFieldsToDomainFields();
static bool detectFieldAccesses(Symbol * sym,
                                AggregateType *at,
                                int64_t ID);
static Symbol *isFieldAccess(CallExpr *call,
                             AggregateType *at);
static FnSymbol *getEnclosingFunction(Expr *expr);
static ForLoop *findEnclosingForLoop(Expr *expr);
static void gatherForLoopInfo(ForLoop *f);
static void getForLoopIndexVars(ForLoop *f);
static std::vector<Symbol *> getForLoopIndexSymbols(ForLoop *f,
                                                    Symbol *baseSym);
static void getForLoopDomainInfo(ForLoop *f,
                                 Expr *expr);
static bool extractAllLoopSyms(CallExpr *call,
                               std::vector<Symbol *> &loopIndexSyms,
                               std::vector<std::pair<Symbol *, ieIndexIteratorType>> &loopIteratorSyms);
static bool isLoopDomainValidIE(CallExpr *call,
                                CallExpr *parentCall,
                                std::vector<Symbol *> loopIndexSyms,
                                std::vector<std::pair<Symbol *, ieIndexIteratorType>> loopIteratorSyms,
                                BlockStmt *loopBody,
                                std::vector< std::vector<Symbol *> > multiDIndices,
                                std::vector<Symbol *> iterSym,
                                std::vector<Symbol *> dotDomIterSym,
                                ForallOptimizationInfo &optInfo,
                                std::map<std::pair<Symbol *, ieIndexIteratorType>, bool> &loopIterSymsUsed);
static bool callHasValidExpression(CallExpr *ce,
                                   CallExpr *ignore,
                                   const std::vector<Symbol *> &syms,
                                   std::vector<int> &loopIndexSymsUsed);
static bool isCallExprBinaryOperator(CallExpr *call);
static Symbol *isSymbolDefinedInBlock(Symbol *sym,
                                      BlockStmt *blckStmt,
                                      bool &isRecField);
static ForallStmt *findEnclosingForallLoop(Expr *expr);
static bool isCallExprValid(CallExpr *call);
static bool doesExprContainExpr(Expr *expr,
                                Expr *matchExpr);
static Expr *findEnclosingLoop(Expr *expr);
static Expr *findEnclosingSerialLoop(Expr *expr);
static Symbol *getFuncFirstArg(SymExpr *symexpr,
                               PrimitiveTag prim);
static Symbol *getFuncFirstArg(SymExpr *symexpr,
                               const char *funcName,
                               bool *isSplitInit);
static bool checkForInvalidEnclosingConstructs(Expr *expr,
                                               ForallStmt *forall);
static bool isCallSiteInvalid(Expr *callSite);
static bool isAssignment(CallExpr *call);

/////////////////////////////////////////////////////////////////////////
//                                                                     //
//  Adaptive Remote Prefetching (ARP) Normalization Related Functions  //
//                                                                     //
/////////////////////////////////////////////////////////////////////////
void adaptiveRemotePrefetching(ForallStmt *forall);
static void findCandidatesARP(ForallStmt* forall);
static void analyzeCandidateARP(CallExpr *call,
                                CallExpr *parentCall,
                                ForallStmt *forall);
static void analyzeLoopStructureARP(CallExpr *parentCall,
                                    CallExpr *call,
                                    std::vector< std::vector<Symbol *> > multiDIndices,
                                    std::vector<Symbol *> iterSym,
                                    std::vector<Symbol *> dotDomIterSym,
                                    ForallStmt *forall,
                                    ForLoop *forloop,
                                    std::vector<AdaptiveRemotePrefetchingCandidate> &candidates);
static void loopIteratesOverRangeOrUsesByClause(CallExpr *parentCall,
                                                CallExpr *call,
                                                ForallStmt *forall,
                                                ForLoop *forloop,
                                                Symbol *loopIndexSym,
                                                std::vector<AdaptiveRemotePrefetchingCandidate> &candidates);
static void optimizeLoopARP(ForallStmt *forall);
static void updateLoopIteratorARP(ForallStmt *forall,
                                  AdaptiveRemotePrefetchingCandidate &candidate,
                                  bool &updatedForallIterator,
                                  std::set<ForLoop *> &updatedForLoopIterator);
static void updateLoopIndexVariableARP(ForallStmt *forall,
                                       AdaptiveRemotePrefetchingCandidate &candidate,
                                       bool &updatedForallIndexVar,
                                       std::set<ForLoop *> &updatedForLoopIndexVar);
static void createConstVariablesARP(ForallStmt *forall,
                                    AdaptiveRemotePrefetchingCandidate &candidate,
                                    bool &addedVarsForall,
                                    std::set<ForLoop *> &addedVarsForLoop);
static void addTaskPrivateVariablesToForallARP(ForallStmt *forall,
                                               AdaptiveRemotePrefetchingCandidate &candidate);
static void createStaticCheckARP(ForallStmt *forall,
                                 AdaptiveRemotePrefetchingCandidate &candidate);
static void createOutOfBoundsCheckARP(ForallStmt *forall,
                                      AdaptiveRemotePrefetchingCandidate &candidate);
static void createPrefetchAdjustmentCheck(ForallStmt *forall,
                                          AdaptiveRemotePrefetchingCandidate &candidate);
static void createPrefetchCallARP(ForallStmt *forall,
                                  AdaptiveRemotePrefetchingCandidate &candidate);
static void createPrimitiveARP(ForallStmt *forall,
                               AdaptiveRemotePrefetchingCandidate &candidate);

//////////////////////////////////////////////////////////////////////
//                                                                  //
//  Adaptive Remote Prefetching (ARP) Pre-folding Related Functions //
//                                                                  //
//////////////////////////////////////////////////////////////////////
static void fieldAccessAnalysisARP(CallExpr *call,
                                   bool doPrints);
static void findFieldAccessesARP(Symbol *sym,
                                 AggregateType *at,
                                 std::map<const char *, int> &fieldInfo);

//////////////////////////////////////////////////////////////////////////
//                                                                      //
//  Adaptive Remote Prefetching (ARP) Post Resolution Related Functions //
//                                                                      //
//////////////////////////////////////////////////////////////////////////
static bool postAnalyzePrefetchCandidate(CallExpr *call);

/////////////////////////////////////////////////////////////////////////
//                                                                     //
//  Irregular write aggregation (IWA) Normalization Related Functions  //
//                                                                     //
/////////////////////////////////////////////////////////////////////////
void irregularWriteAggregation(ForallStmt *forall);
static void findCandidatesIWA(ForallStmt* forall);
static void analyzeCandidateIWA(CallExpr *call,
                                CallExpr *parentCall,
                                ForallStmt *forall);
static IrregWriteAggrOp isOperationAggregatable(CallExpr *call);
static bool aggregatedStmtHasDataDependencies(ForallStmt *forall,
                                              CallExpr *aggrCall,
                                              CallExpr *call);
static void findAliasesForSymbol(Symbol *sym,
                                 std::set<Symbol *> &aliases,
                                 FnSymbol *fn);
static void areSymbolsUsedInBlock(BlockStmt * block,
                                  CallExpr *matchCall,
                                  bool *doDependencyChecks,
                                  bool *foundDependency,
                                  std::set<Symbol *> symbols,
                                  std::set<FnSymbol *> &fnProcessed);
static void optimizeLoopIWA(ForallStmt *forall);
static TypeSymbol *generateAggregationRecord(ForallStmt *forall,
                                             int ID,
                                             IrregWriteAggrOp op);
static CallExpr * createPrimitiveIWA(Expr *LHS,
                                     Expr *RHS,
                                     IrregWriteAggrOp op,
                                     ShadowVarSymbol *aggregator,
                                     int ID);

/////////////////////////////////////
//                                 //
//  Utility vectors/maps/#defines  //
//                                 //
/////////////////////////////////////
#define INSPECTOR_ACCESS 0
#define EXECUTOR_ACCESS 1
#define NOT_INSERTED 0
#define INSERTED 1
#define ALREADY_INSERTED 2
#define NOT_IN_FUNCTION -1
#define FUNCTION_ID_UNSET -2
int gIEForallID = 0;
int gARPForallID = 0;
// gArrFieldsToDomFields is defined in compiler/include/passes.h as
// extern
std::map<AggregateType *, std::map<int, int>> gArrFieldsToDomFields;
std::map<int64_t, bool> gInspectorLoopProcessed;
std::map<int64_t, bool> gExecutorLoopProcessed;
std::map<int64_t, bool> gDoOptimizationIE;
std::map<int64_t, std::vector<int>> gFieldPositionsIE;
std::set<CallExpr *> gDeadCodeToRemoveIE;
std::map<int64_t, bool> gIrregWriteAggLoopProcessed;
std::map<int64_t, std::set<int64_t>> gPrefetchCallProcessed;
std::set<const char *> gCandidatesAnalyzedIE;
std::set<const char *> gCandidatesAnalyzedIWA;
std::set<const char *> gCandidatesAnalyzedARP;
std::map<FnSymbol *, int> gFnsWithCandidatesIE;
int gFnWithCandidateID = 1;
int gIWACandidateID = 0;

///////////////////////////////////
//                               //
//  End of additions by tbrolin  //
//                               //
///////////////////////////////////



void doPreNormalizeArrayOptimizations() {
  const bool anyAnalysisNeeded = fAutoLocalAccess ||
                                 fAutoAggregation ||
                                 !fNoFastFollowers ||
                                 fOptimizeIrregularArrayAccesses;
  if (anyAnalysisNeeded) {
    // Added by tbrolin; things we do prior to applying the IE optimization.
    //
    // 1.) generate a mapping of arrays-to-domains for record fields
    if (fOptimizeIrregularArrayAccesses) {
      mapArrayFieldsToDomainFields();
    }
    forv_expanding_Vec(ForallStmt, forall, gForallStmts) {
      // Added by tbrolin 1/11/2022
      // Let's only focus on user modules
      if (fOptimizeIrregularArrayAccesses) {
        if (forall->getModule()->modTag == MOD_USER) {
          inspectorExecutor(forall);
          adaptiveRemotePrefetching(forall);
          irregularWriteAggregation(forall);
        }
      }
      if (!fNoFastFollowers) {
        symbolicFastFollowerAnalysis(forall);
      }

      if (fAutoLocalAccess) {
        autoLocalAccess(forall);
      }

      if (fAutoAggregation) {
        autoAggregation(forall);
      }
    }
    // Added by tbrolin; things we do after applying the IE optimization.
    //
    // 1.) Count the number of unique functions we found that contain at
    //     least one potential candidate forall. Using that number, insert
    //     a call to setNumFuncsForDynamicCallPathFlags() at the very end of
    //     the InspectorExecutor module. Note that we add 1 to it when inserting
    //     the call because we using 1-based indexing into our flags. This is
    //     only because we reserve index 0 for an initial call to the set/unset
    //     routines that are required so the functions are available after resolution.
    int numFuncsWithCandidates = gFnsWithCandidatesIE.size();
    if (numFuncsWithCandidates > 0) {
      CallExpr *setFuncsCall = new CallExpr("setNumFuncsForDynamicCallPathFlags",
                                            new_IntSymbol(numFuncsWithCandidates+1));
      bool addedCall = false;
      forv_Vec(ModuleSymbol, mod, gModuleSymbols) {
        if (mod->hasFlag(FLAG_IE_MOD_MARKER)) {
          FnSymbol *modInitFn = mod->initFn;
          modInitFn->insertAtTail(setFuncsCall);
          addedCall = true;
          break;
        }
      }
      INT_ASSERT(addedCall == true);
    }
  }
}

Expr *preFoldMaybeLocalArrElem(CallExpr *call) {

  // This primitive is created with 4 arguments:
  // (call "may be local arr elem": elem, arr, paramFlag, fastFollowerControl)
  //
  // But we remove the second argument right after using it, because it can be
  // an expression with side effects

  SymExpr *maybeArrElemSymExpr = toSymExpr(call->get(1));
  INT_ASSERT(maybeArrElemSymExpr);

  SymExpr *controlSymExpr = toSymExpr(call->get(2));
  INT_ASSERT(controlSymExpr);
  bool iterableTypeSuitable = (controlSymExpr->symbol() == gTrue);

  SymExpr *ffControlSymExpr = toSymExpr(call->get(3));
  INT_ASSERT(ffControlSymExpr);
  bool fastFollowerSuitable = (ffControlSymExpr->symbol() == gTrue);

  bool confirmed = (iterableTypeSuitable && fastFollowerSuitable);

  if (confirmed) {
    LOG_AA(0, "Confirmed that this symbol is a local array element", call);
  }
  else {
    if (!iterableTypeSuitable) {
      LOG_AA(0, "Iterable type not suitable for aggregation", call);
    }
    else if (!fastFollowerSuitable) {
      LOG_AA(0, "Could not prove locality outside of a fast follower body", call);
    }
    else {
      INT_FATAL("Unexpected failure");
    }
  }

  if (fAutoAggregation) {
    findAndUpdateMaybeAggAssign(call, confirmed);
  }

  return maybeArrElemSymExpr->remove();
}

Expr *preFoldMaybeLocalThis(CallExpr *call) {
  Expr *ret = NULL;
  bool confirmed = false;

  // PRIM_MAYBE_LOCAL_THIS looks like
  //
  //  (call "may be local access" arrSymbol, idxSym0, ... ,idxSymN,
  //                              paramControlFlag, paramStaticallyDetermined)
  //
  // we need to check the second argument from last to determine whether we
  // are confirming this to be a local access or not
  if (SymExpr *controlSE = toSymExpr(call->get(call->argList.length-1))) {
    if (controlSE->symbol() == gTrue) {
      confirmed = true;
    }
  }
  else {
    INT_FATAL("Misconfigured PRIM_MAYBE_LOCAL_THIS");
  }

  if (fAutoLocalAccess) {
    ret = confirmed ? confirmAccess(call) : revertAccess(call);
  }
  else {
    // maybe we have automatic aggregation but no automatic local access? In
    // that case we may have generated one of this primitive, for aggregation
    // detection, now we just remove it silently
    ret = revertAccess(call);
  }

  INT_ASSERT(ret);

  if (fAutoAggregation) {
    findAndUpdateMaybeAggAssign(call, confirmed);
  }

  primMaybeLocalThisLocations.erase(call->astloc);

  return ret;
}

// we record the aggregators that we actually end up being used, so that we can
// avoid removing their declarations/destructions
std::set<Symbol *> usedAggregators;

// called during LICM to restructure a conditional aggregation to direct
// aggregation
void transformConditionalAggregation(CondStmt *cond) {

  // move the aggregation call before the conditional (at this point in
  // compilation it must be inlined)
  bool foundAggregator = false;
  for_alist(expr, cond->elseStmt->body) {
    if (!foundAggregator) {
      std::vector<SymExpr *> symExprs;
      collectSymExprs(expr, symExprs);
      for_vector(SymExpr, symExpr, symExprs) {
        if (symExpr->symbol()->hasFlag(FLAG_COMPILER_ADDED_AGGREGATOR)) {
          usedAggregators.insert(symExpr->symbol());
          foundAggregator = true;
        }
      }
    }
    cond->insertBefore(expr->remove());
  }

  // remove the defpoint of the aggregation marker
  SymExpr *condExpr = toSymExpr(cond->condExpr);
  INT_ASSERT(condExpr);

  if (fReportAutoAggregation) {
    std::stringstream message;
    message << "Replaced assignment with aggregation";
    if (condExpr->symbol()->hasFlag(FLAG_AGG_IN_STATIC_AND_DYNAMIC_CLONE)) {
      message << " [static and dynamic ALA clone] ";
    }
    else if (condExpr->symbol()->hasFlag(FLAG_AGG_IN_STATIC_ONLY_CLONE)) {
      message << " [static only ALA clone] ";
    }
    LOG_AA(0, message.str().c_str(), condExpr);
  }

  condExpr->symbol()->defPoint->remove();

  // remove the conditional
  cond->remove();
}

// called during forall lowering to remove aggregation where the forall leader
// is recursive. Foralls with recursive iterators can only have ref shadow
// variables, and aggregators are non-ref (task-private)
void removeAggregationFromRecursiveForall(ForallStmt *forall) {
  LOG_ALA(0, "Reverting aggregation: forall leader is recursive", forall);
  removeAggregationFromRecursiveForallHelp(forall->loopBody());
}

// called after unordered forall optimization to remove aggregation code (by
// choosing non-aggregated version)
void cleanupRemainingAggCondStmts() {
  forv_Vec(FnSymbol, fn, gFnSymbols) {
    if (fn->hasFlag(FLAG_COBEGIN_OR_COFORALL)) {
      std::vector<Expr *> stmts;
      collect_stmts(fn->body, stmts);

      // With the initial implementation of aggregators, I doubt we can have
      // more than 1 aggregator in this set. But we can have that, when we don't
      // limit aggregation to the last statement in the forall body.
      std::set<Symbol *> aggregatorsToRemove;

      for_vector(Expr, stmt, stmts) {
        if (CondStmt *condStmt = toCondStmt(stmt)) {
          if (condStmt->inTree()) {
            if (SymExpr *condSymExpr = toSymExpr(condStmt->condExpr)) {
              if (condSymExpr->symbol()->hasFlag(FLAG_AGG_MARKER)) {
                // this is a conditional that wasn't modified by the unordered
                // optimization, so we need to remove the effects of the
                // forall intent adding the aggregator

                // find the aggregator symbol within the else block:
                // note that the else block will be inlined and will be a big mess, we
                // need to find the compiler-generated aggregator in that mess
                std::vector<SymExpr *> symExprs;
                collectSymExprs(condStmt->elseStmt, symExprs);

                Symbol *aggregatorToRemove = NULL;
                FnSymbol *parentFn = NULL;
                for_vector(SymExpr, symExpr, symExprs) {
                  Symbol *sym = symExpr->symbol();
                  if(sym->hasFlag(FLAG_COMPILER_ADDED_AGGREGATOR)) {
                    aggregatorToRemove = sym;
                    parentFn = toFnSymbol(symExpr->parentSymbol);
                    break;
                  }
                }

                INT_ASSERT(aggregatorToRemove != NULL);
                INT_ASSERT(parentFn != NULL);

                // put the nodes in the then block right before the conditional
                for_alist(expr, condStmt->thenStmt->body) {
                  condStmt->insertBefore(expr->remove());
                }

                // remove the remaining conditional
                condStmt->remove();

                if (usedAggregators.count(aggregatorToRemove) == 0) {
                  aggregatorsToRemove.insert(aggregatorToRemove);
                }
              }
            }
          }
        }
      }

      for_set(Symbol, aggregatorToRemove, aggregatorsToRemove) {
        // remove the defPoint of the aggregator
        aggregatorToRemove->defPoint->remove();

        // search for the aggregator in the parent function and scrub it clean.
        // We expect 3 occurrences of the symbol after the else block is gone
        std::vector<SymExpr *> symExprs;
        collectSymExprs(fn->body, symExprs);

        for_vector(SymExpr, symExpr, symExprs) {
          Symbol *sym = symExpr->symbol();
          if (sym == aggregatorToRemove) {
            CallExpr *parentCall = toCallExpr(symExpr->parentExpr);
            INT_ASSERT(parentCall != NULL);

            if (parentCall->isPrimitive(PRIM_MOVE)) {
              /* Here's what we expect to see in the AST with associated
                 variable names in the following snippet

                (def aggregator)
                (def rhsSym)
                (def prevRhsSym)
                (call chpl_srcAggregatorForArr someArrSym, prevRhsSym)  `aggGenCall`
                (call move call_tmp prevRhsSym)      `prevCall`
                (call move aggregator rhsSym)   `parentCall`

                At this point we only have a handle on the last expression. We
                walk back up from that.
              */
              INT_ASSERT(toSymExpr(parentCall->get(1))->symbol() == aggregatorToRemove);

              Symbol *rhsSym = toSymExpr(parentCall->get(2))->symbol();
              CallExpr *prevCall = toCallExpr(parentCall->prev);
              INT_ASSERT(prevCall);
              INT_ASSERT(toSymExpr(prevCall->get(1))->symbol() == rhsSym);

              Symbol *prevRhsSym = toSymExpr(prevCall->get(2))->symbol();
              CallExpr *aggGenCall = toCallExpr(prevCall->prev);
              INT_ASSERT(aggGenCall);
              INT_ASSERT(aggGenCall->theFnSymbol()->hasFlag(FLAG_AGG_GENERATOR));
              INT_ASSERT(toSymExpr(aggGenCall->get(2))->symbol() == prevRhsSym);

              parentCall->remove();
              prevCall->remove();
              aggGenCall->remove();
              rhsSym->defPoint->remove();
              prevRhsSym->defPoint->remove();
            }
            else if (parentCall->isPrimitive(PRIM_SET_REFERENCE)) {
              /* Here's what we expect to see in the AST with associated
                 variable names in the following snippet

                 (def lhsSym)
                 (move lhsSym (`set reference` aggregator))  `moveCall`
                 (deinit lhsSym)

                At this point we only have a handle on the `set reference` call.
                We detect other expressions starting from that.
              */
              CallExpr *moveCall = toCallExpr(parentCall->parentExpr);
              INT_ASSERT(moveCall);
              INT_ASSERT(moveCall->isPrimitive(PRIM_MOVE));

              Symbol *lhsSym = toSymExpr(moveCall->get(1))->symbol();
              INT_ASSERT(lhsSym->defPoint == moveCall->prev);

              CallExpr *deinitCall = toCallExpr(moveCall->next);
              INT_ASSERT(deinitCall);
              INT_ASSERT(deinitCall->theFnSymbol()->hasFlag(FLAG_DESTRUCTOR));
              INT_ASSERT(toSymExpr(deinitCall->get(1))->symbol() == lhsSym);

              moveCall->remove();
              lhsSym->defPoint->remove();
              deinitCall->remove();
            }
            else if (parentCall->resolvedFunction()->hasFlag(FLAG_AUTO_DESTROY_FN)) {
              // we bump into this case when inlining is disabled, we only
              // need to remove the call
              parentCall->remove();
            }
            else {
              INT_FATAL("Auto-aggregator is in an unexpected expression");
            }
          }
        }
      }
    }
  }
}

void finalizeForallOptimizationsResolution() {
  if (fVerify) {
    for_alive_in_Vec (CallExpr, callExpr, gCallExprs) {
      if (callExpr->isPrimitive(PRIM_MAYBE_LOCAL_THIS) ||
          callExpr->isPrimitive(PRIM_MAYBE_LOCAL_ARR_ELEM) ||
          callExpr->isPrimitive(PRIM_MAYBE_AGGREGATE_ASSIGN) ||
          callExpr->isPrimitive(PRIM_MAYBE_IRREG_ACCESS)) {
        INT_FATAL(callExpr, "This primitive should have disappeared by now");
      }
    }
  }

  // the following chunks can be refactored into a helper, but there are slight
  // differences, and it may be dirtier if we do that.
  if (fReportAutoLocalAccess) {
    std::set<astlocT>::iterator it;
    for (it = primMaybeLocalThisLocations.begin() ;
         it != primMaybeLocalThisLocations.end();
         ++it) {
      std::stringstream message;
      message << "Local access attempt reverted. All static checks failed or code is unreachable.";
      message << "(" << it->stringLoc() << ")";
      LOG_ALA(0, message.str().c_str(), NULL);
    }
  }
  primMaybeLocalThisLocations.clear();

  if (fAutoAggregation) {
    std::set<astlocT>::iterator it;
    for (it = primMaybeAggregateAssignLocations.begin() ;
         it != primMaybeAggregateAssignLocations.end();
         ++it) {
      std::stringstream message;
      message << "Aggregation attempt reverted. Could not prove that exactly one side of the assignment is local.";
      message << "(" << it->stringLoc() << ")";
      LOG_AA(0, message.str().c_str(), NULL);
    }
  }
  primMaybeAggregateAssignLocations.clear();
}

//
// logging support for --report-auto-local-access and --report-auto-aggregation
// during the first analysis phase depth is used roughly in the following way
// 0: entering/exiting forall
// 1: information about the forall
// 2: entering/exiting call
// 3: information about call
//
// during resolution, the output is much more straightforward, and depth 0 is
// used always
static bool LOG_help(int depth, const char *msg, BaseAST *node,
                     ForallAutoLocalAccessCloneType cloneType, bool flag) {

  bool reportedLoc = false;
  if (flag) {
    bool verbose = node == NULL ||  // to support wholesale reversion reporting
                   (node->getModule()->modTag != MOD_INTERNAL &&
                    node->getModule()->modTag != MOD_STANDARD);

    const bool veryVerbose = false;
    if (verbose) {
      curLogDepth = depth;
      if (curLogDepth > 0) {
        std::cout << "|";
      }

      for (int i = 0 ; i < depth; i++) {
        std::cout << " ";
      }
      std::cout << msg;
      switch (cloneType) {
        case STATIC_AND_DYNAMIC:
          std::cout << " [static and dynamic ALA clone] ";
          break;
        case STATIC_ONLY:
          std::cout << " [static only ALA clone] ";
          break;
        case NO_OPTIMIZATION:
          std::cout << " [no ALA clone] ";
          break;
        default:
          break;
      }
      if (node != NULL) {
        std::cout << " (" << node->stringLoc() << ")";
        if (veryVerbose) {
          nprint_view(node);
        }
        reportedLoc = true;
      }
      std::cout << std::endl;
    }
  }
  return reportedLoc;
}

static void LOGLN_help(BaseAST *node, bool flag) {
  if (flag) {
    bool verbose = (node->getModule()->modTag != MOD_INTERNAL &&
                    node->getModule()->modTag != MOD_STANDARD);
    if (verbose) {
      if (curLogDepth > 0) {
        std::cout << "|";
      }
      std::cout << std::endl;
    }
  }
}

static bool LOG_AA(int depth, const char *msg, BaseAST *node) {
  ForallAutoLocalAccessCloneType cloneType = NOT_CLONE;
  if (ForallStmt *forall = toForallStmt(node)) {
    cloneType = forall->optInfo.cloneType;
  }
  return LOG_help(depth, msg, node, cloneType,
                  fAutoAggregation && fReportAutoAggregation);
}

static void LOGLN_AA(BaseAST *node) {
  LOGLN_help(node, fAutoAggregation && fReportAutoAggregation);
}

static bool LOG_ALA(int depth, const char *msg, BaseAST *node,
                    bool forallDetails) {
  ForallAutoLocalAccessCloneType cloneType = NOT_CLONE;

  if (forallDetails) {
    CallExpr *call = toCallExpr(node);
    INT_ASSERT(call);

    ForallStmt *forall = enclosingForallStmt(call);
    INT_ASSERT(forall);

    cloneType = forall->optInfo.cloneType;
  }
  return LOG_help(depth, msg, node, cloneType,
           fAutoLocalAccess && fReportAutoLocalAccess);
}

static bool LOG_ALA(int depth, const char *msg, BaseAST *node) {
  ForallAutoLocalAccessCloneType cloneType = NOT_CLONE;
  return LOG_help(depth, msg, node, cloneType,
           fAutoLocalAccess && fReportAutoLocalAccess);
}

static void LOGLN_ALA(BaseAST *node) {
  LOGLN_help(node, fAutoLocalAccess && fReportAutoLocalAccess);
}

//
// Normalize support for --auto-local-access
//

// Return true if `ce`'s arguments are exactly identical to `syms`
static bool callHasSymArguments(CallExpr *ce, const std::vector<Symbol *> &syms) {
  if (((std::size_t)ce->argList.length) != syms.size()) return false;
  for (int i = 0 ; i < ce->argList.length ; i++) {
    if (SymExpr *arg = toSymExpr(ce->get(i+1))) {
      if (arg->symbol() != syms[i]) {
        return false;
      }
    }
    else {
      return false;
    }
  }
  return true;
}

// Return the symbol `A` from an expression if it is in the form `A.domain`
static Symbol *getDotDomBaseSym(Expr *expr) {
  if (CallExpr *ce = toCallExpr(expr)) {
    if (ce->isNamedAstr(astrSdot)) {
      if (SymExpr *se = toSymExpr(ce->get(2))) {
        if (VarSymbol *var = toVarSymbol(se->symbol())) {
          if (var->immediate->const_kind == CONST_KIND_STRING) {
            if (strcmp(var->immediate->v_string.c_str(), "_dom") == 0) {
              if (SymExpr *se = toSymExpr(ce->get(1))) {
                return se->symbol();
              }
            }
          }
        }
      }
    }
  }
  return NULL;
}

static Expr *getDomainExprFromArrayType(CallExpr* ceInner){
  if (ceInner->isNamed("chpl__ensureDomainExpr")) {
    return ceInner->get(1);
  }
  return NULL;
}

// get the domain part of the expression from `[D] int` or `[?D] int`
static Expr *getDomExprFromTypeExprOrQuery(Expr *e) {
  if (CallExpr *ce = toCallExpr(e)) {
    if (ce->isNamed("chpl__buildArrayRuntimeType")) {
      if (CallExpr *ceInner = toCallExpr(ce->get(1))) {
        if (Expr* e = getDomainExprFromArrayType(ceInner)){
          return e;
        }
      } else if (DefExpr *queryDef = toDefExpr(ce->get(1))) {
        return queryDef;
      }
    }
  } else if (SymExpr* se = toSymExpr(e)) {
    if(se->symbol()->hasFlag(FLAG_TYPE_VARIABLE) &&
        se->symbol()->hasFlag(FLAG_TEMP)) {
      //if type var then check type expression
      if(DefExpr* defExpr = toDefExpr(se->symbol()->defPoint)){
        if (CallExpr *ce = toCallExpr(defExpr->init)) {
          if (ce->isNamed("chpl__buildArrayRuntimeType")) {
            if (CallExpr *ceInner = toCallExpr(ce->get(1))) {
              if (Expr* e = getDomainExprFromArrayType(ceInner)){
                return e;
              }
            }
          }
        }
      }
    }
  }
  return NULL;
}

static Symbol *getDomSym(Symbol *arrSym);

// get the domain symbol from `Dom`, `?Dom` (if allowQuery) or `arr.domain`
static Symbol *getDomSymFromDomExpr(Expr *domExpr, bool allowQuery) {
  // we try the following cases one by one:

  if (SymExpr *domSE = toSymExpr(domExpr)) {
    return domSE->symbol();
  }

  if (allowQuery) {
    if (DefExpr *domSE = toDefExpr(domExpr)) {
      return domSE->sym;
    }
  }

  if (Symbol *dotDomBaseSym = getDotDomBaseSym(domExpr)) {
    return getDomSym(dotDomBaseSym); // recurse
  }
  return NULL;
}

// If `arrSym` is an array symbol, try to return its domain's symbol. return
// NULL if we can't find a domain symbol statically
static Symbol *getDomSym(Symbol *arrSym) {

  Symbol *ret = NULL;

  // try to get the domain of arrays that are defined in this scope
  if(DefExpr *def = arrSym->defPoint) {
    if (def->exprType != NULL) {
      // check for pattern `var A: [D] int;`
      if (Expr *arg = getDomExprFromTypeExprOrQuery(def->exprType)) {
        ret = getDomSymFromDomExpr(arg, /* allowQuery= */ false);
      }
      // check for `B` in `var A, B: [D] int;`
      else if (CallExpr *ceOuter = toCallExpr(def->exprType)) {
        if (ceOuter->isPrimitive(PRIM_TYPEOF)) {
          if (SymExpr *typeOfSymExpr = toSymExpr(ceOuter->get(1))) {
            ret = getDomSym(typeOfSymExpr->symbol()); // recurse
          }
        }
      }
    }
  }

  if (ret == NULL) {
    // try to get the domain if the symbol was an argument
    // e.g. `a: [d] int`, `a: [?d] int`, `a: [x.domain] int`
    if (ArgSymbol *arrArgSym = toArgSymbol(arrSym)) {
      if (BlockStmt *typeBlock = toBlockStmt(arrArgSym->typeExpr)) {
        Expr *firstExpr = typeBlock->body.head;
        Expr *domExpr = getDomExprFromTypeExprOrQuery(firstExpr);

        ret = getDomSymFromDomExpr(domExpr, /* allowQuery= */ true);

      }
    }
  }
  return ret;
}

// Return the closest parent of `ce` that can impact locality (forall or on)
static Expr *getLocalityDominator(CallExpr* ce) {
  Expr *cur = ce->parentExpr;
  while (cur != NULL) {
    if (BlockStmt *block = toBlockStmt(cur)) {
      if (!block->isRealBlockStmt()) { // check for on statement
        return block;
      }
    }

    if (LoopExpr *loop = toLoopExpr(cur)) {
      if (loop->forall) {
        return loop;
      }
    }

    if (ForallStmt *forall = toForallStmt(cur)) {
      return forall;
    }
    cur = cur->parentExpr;
  }
  return NULL;
}

// check whether an expression is used to assign a subindex. e.g.
//
//   forall (i, j) in D
//
// will have in the beginning of its body assignments to i and j from an
// "indexOfInterest" that represents that tuple in a single symbol
static bool isSubIndexAssignment(Expr *expr,
                                 Symbol *subIndex,
                                 int indexIndex,
                                 Symbol *indexBundle) {
  if (CallExpr *moveCE = toCallExpr(expr)) {
    if (moveCE->isPrimitive(PRIM_MOVE)) {
      if (SymExpr *moveDstSE = toSymExpr(moveCE->get(1))) {
        if (CallExpr *moveSrcCE = toCallExpr(moveCE->get(2))) {
          if (SymExpr *moveSrcBaseSE = toSymExpr(moveSrcCE->baseExpr)) {
            if (SymExpr *moveSrcIdxSE = toSymExpr(moveSrcCE->get(1))) {
              if (VarSymbol *moveSrcIdxVS = toVarSymbol(moveSrcIdxSE->symbol())) {
                return (moveDstSE->symbol() == subIndex) &&
                       ( moveSrcBaseSE->symbol() == indexBundle &&
                         moveSrcIdxVS->immediate->int_value() == indexIndex );
              }
            }
          }
        }
      }
    }
  }
  return false;
}

// baseSym must be the tuple tmp that represents `(i,j)` in `forall (i,j) in D`
static std::vector<Symbol *> getLoopIndexSymbols(ForallStmt *forall,
                                                 Symbol *baseSym) {
  std::vector<Symbol *> indexSymbols;
  int indexVarCount = -1;
  int bodyExprCount = 1;

  AList &bodyExprs = forall->loopBody()->body;

  // find the check_tuple_var_decl and get the size of the tuple
  if (CallExpr *firstCall = toCallExpr(bodyExprs.get(bodyExprCount++))) {
    if (firstCall->isNamed("_check_tuple_var_decl")) {
      if (SymExpr *firstArgSE = toSymExpr(firstCall->get(1))) {
        if (firstArgSE->symbol() == baseSym) {
          if (SymExpr *secondArgSE = toSymExpr(firstCall->get(2))) {
            if (VarSymbol *vs = toVarSymbol(secondArgSE->symbol())) {
              indexVarCount = vs->immediate->int_value();
            }
          }
        }
      }
    }
  }

  if (indexVarCount != -1) {
    INT_ASSERT(indexVarCount > 0);

    // push every element (subindex) of the index tuple to the vector
    for (int i = 0 ; i < indexVarCount ; i++) {
      if (DefExpr *indexDE = toDefExpr(bodyExprs.get(bodyExprCount++))) {
        Symbol *indexSym = indexDE->sym;
        if(isSubIndexAssignment(bodyExprs.get(bodyExprCount++),
                                indexSym, i, baseSym)) {
          indexSymbols.push_back(indexSym);
        }
      }
    }
  }

  // we must have pushed the same number of indexes to the vector as we
  // initially found. Otherwise, clear the vector, which denotes an unknown
  // pattern.
  if (indexVarCount == -1 ||
      ((std::size_t)indexVarCount) != indexSymbols.size()) {
    LOG_ALA(1, "Can't recognize loop's index symbols", baseSym);
    indexSymbols.clear();
  }

  return indexSymbols;
}

static void gatherForallInfo(ForallStmt *forall) {


  AList &iterExprs = forall->iteratedExpressions();
  AList &indexVars = forall->inductionVariables();


  for(int i = 1 ; i <= iterExprs.length ; i++ ) {

    Expr *curIterExpr = iterExprs.get(i);
    Expr *curIndexVar = indexVars.get(i);

    Symbol *loopIdxSym = NULL;
    Symbol *iterSym = NULL;
    Expr *dotDomIterExpr = NULL;
    Symbol *dotDomIterSym = NULL;
    Symbol *dotDomIterSymDom = NULL;

    CallExpr *iterCall = NULL;
    Symbol *iterCallTmp = NULL;

    std::vector<Symbol *> multiDIndices;

    if (isUnresolvedSymExpr(curIterExpr) || isSymExpr(curIterExpr)) {
      if (SymExpr *iterSE = toSymExpr(curIterExpr)) {
        iterSym = iterSE->symbol();
      }
    }
    // it might be in the form `A.domain` where A is used in the loop body
    else if (Symbol *dotDomBaseSym = getDotDomBaseSym(curIterExpr)) {
      dotDomIterExpr = curIterExpr;
      dotDomIterSym = dotDomBaseSym;
      dotDomIterSymDom = getDomSym(dotDomIterSym);
    }
    else if (CallExpr *curIterCall = toCallExpr(curIterExpr)) {
      // not sure how or why we should support forall i in zip((...tup))
      if (!curIterCall->isPrimitive(PRIM_TUPLE_EXPAND)) {
        if(Symbol *curIterCallTmp = earlyNormalizeForallIterand(curIterCall, forall)) {
          iterCall = curIterCall;
          iterCallTmp = curIterCallTmp;
        }
      }
    }

    forall->optInfo.iterSym.push_back(iterSym);

    forall->optInfo.dotDomIterExpr.push_back(dotDomIterExpr);
    forall->optInfo.dotDomIterSym.push_back(dotDomIterSym);
    forall->optInfo.dotDomIterSymDom .push_back(dotDomIterSymDom);

    forall->optInfo.iterCall.push_back(iterCall);
    forall->optInfo.iterCallTmp.push_back(iterCallTmp);

    if (iterSym != NULL ||
        dotDomIterSym != NULL ||
        iterCall != NULL) {
      // the iterator is something we can optimize
      // now check the induction variables
      if (SymExpr* se = toSymExpr(curIndexVar)) {
        loopIdxSym = se->symbol();
      }
      else if (DefExpr* de = toDefExpr(curIndexVar)) {
        loopIdxSym = de->sym;
      }
      else {
        INT_FATAL("Loop index cannot be extracted");
      }

      if (loopIdxSym->hasFlag(FLAG_INDEX_OF_INTEREST)) {
        multiDIndices = getLoopIndexSymbols(forall, loopIdxSym);
      }
      else {
        multiDIndices.push_back(loopIdxSym);
      }

      forall->optInfo.multiDIndices.push_back(multiDIndices);
    }
  }

  forall->optInfo.infoGathered = true;
}

static bool loopHasValidInductionVariables(ForallStmt *forall) {
  // if we understand the induction variables, then we can still take a look at
  // the loop body for some calls that we can optimize dynamically
  return forall->optInfo.multiDIndices.size() > 0;
}

static Symbol *canDetermineLoopDomainStatically(ForallStmt *forall) {
  // a forall is suitable for static optimization only if it iterates over a
  // symbol (with the hopes that that symbol is a domain), or a foo.domain
  if (forall->optInfo.iterSym.size() > 0){
    Symbol *ret = forall->optInfo.iterSym[0];
    if (ret != NULL) {
      return ret;
    }
  }

  if (forall->optInfo.dotDomIterSym.size() > 0) {
    Symbol *ret = forall->optInfo.dotDomIterSym[0];
    if (ret != NULL) {
      return ret;
    }
  }
  return NULL;
}

static const char *getCallRejectReasonStr(CallRejectReason reason) {
  switch (reason) {
    case CRR_NO_CLEAN_INDEX_MATCH:
      return "call arguments don't match loop indices cleanly";
      break;
    case CRR_NOT_ARRAY_ACCESS_LIKE:
      return "call doesn't look like array access";
      break;
    case CRR_ACCESS_BASE_IS_LOOP_INDEX:
      return "call base is yielded by forall iterator";
      break;
    case CRR_ACCESS_BASE_IS_NOT_OUTER_VAR:
      return "call base is defined within the loop body";
      break;
    case CRR_ACCESS_BASE_IS_SHADOW_VAR:
      return "call base is a defined in a forall intent";
      break;
    case CRR_TIGHTER_LOCALITY_DOMINATOR:
      return "call base is in a nested on and/or forall";
      break;
    default:
      return "";
      break;
  }

  return "";
}

// Bunch of checks to see if `call` is a candidate for optimization within
// `forall`. Returns the symbol of the `baseExpr` of the `call` if it is
// suitable. NULL otherwise
static Symbol *getCallBaseSymIfSuitable(CallExpr *call, ForallStmt *forall,
                                        bool checkArgs, int *argIdx,
                                        CallRejectReason *reason) {

  // TODO see if you can use getCallBase
  SymExpr *baseSE = toSymExpr(call->baseExpr);

  if (baseSE != NULL) {
    Symbol *accBaseSym = baseSE->symbol();

    // Prevent making changes to `new C[i]`
    if (CallExpr *parentCall = toCallExpr(call->parentExpr)) {
      if (parentCall->isPrimitive(PRIM_NEW)) { return NULL; }
    }

    // don't analyze further if the call base is a yielded symbol
    if (accBaseSym->hasFlag(FLAG_INDEX_VAR)) {
      if (!accBaseSym->hasFlag(FLAG_TEMP) && reason != NULL) {
        *reason = CRR_ACCESS_BASE_IS_LOOP_INDEX;
      }
      return NULL;
    }

    // give up if the access uses a different symbol than the symbols yielded by
    // one of the iterators
    if (checkArgs) {
      int idx = -1;
      bool found = false;

      std::vector< std::vector<Symbol *> >::iterator it;
      for (it = forall->optInfo.multiDIndices.begin();
           it != forall->optInfo.multiDIndices.end();
           it++) {
        idx++;
        if (callHasSymArguments(call, *it)) {
          *argIdx = idx;
          found = true;
        }
      }

      if (!found) {
        if (reason != NULL) *reason = CRR_NO_CLEAN_INDEX_MATCH;
        return NULL;
      }
    }

    // (i,j) in forall (i,j) in bla is a tuple that is index-by-index accessed
    // in loop body that throw off this analysis
    if (accBaseSym->hasFlag(FLAG_INDEX_OF_INTEREST)) { return NULL; }

    // give up if the symbol we are looking to optimize is defined inside the
    // loop itself
    if (forall->loopBody()->contains(accBaseSym->defPoint)) {
      if (reason != NULL) *reason = CRR_ACCESS_BASE_IS_NOT_OUTER_VAR;
      return NULL;
    }

    // similarly, give up if the base symbol is a shadow variable
    if (isShadowVarSymbol(accBaseSym)) {
      if (reason != NULL) *reason = CRR_ACCESS_BASE_IS_SHADOW_VAR;
      return NULL;
    }

    // this call has another tighter-enclosing stmt that may change locality,
    // don't optimize
    if (forall != getLocalityDominator(call)) {
      if (reason != NULL) *reason = CRR_TIGHTER_LOCALITY_DOMINATOR;
      return NULL;
    }

    return accBaseSym;
  }

  if (reason != NULL) *reason = CRR_NOT_ARRAY_ACCESS_LIKE;
  return NULL;
}

static Symbol *getCallBase(CallExpr *call) {
  SymExpr *baseSE = toSymExpr(call->baseExpr);
  if (baseSE != NULL) {
    return baseSE->symbol();
  }
  return NULL;
}

// for a call like `A[i]`, this will create something like
//
// chpl_dynamicAutoLocalCheck(A, loopDomain)
//
// right before the `forall`. Multiple dynamic checks are &&'ed. `allChecks` is
// that "&&" call, or NULL if this was the first time we are adding a
// dynamic check
static void generateDynamicCheckForAccess(CallExpr *access,
                                          ForallStmt *forall,
                                          int iterandIdx,
                                          CallExpr *&allChecks) {
  ForallOptimizationInfo &optInfo = forall->optInfo;
  Symbol *baseSym = getCallBase(access);
  INT_ASSERT(baseSym);

  SET_LINENO(forall);

  CallExpr *currentCheck = NULL;
  if (optInfo.dynamicCheckForSymMap.count(baseSym) == 0) {
    currentCheck = new CallExpr("chpl__dynamicAutoLocalCheck");
    optInfo.dynamicCheckForSymMap[baseSym] = currentCheck;
  }
  else {
    return;
  }
  currentCheck->insertAtTail(baseSym);

  if (optInfo.iterSym[iterandIdx] != NULL) {
    currentCheck->insertAtTail(new SymExpr(optInfo.iterSym[iterandIdx]));
  }
  else if (optInfo.dotDomIterExpr[iterandIdx] != NULL) {
    currentCheck->insertAtTail(optInfo.dotDomIterExpr[iterandIdx]->copy());
  }
  else if (optInfo.iterCallTmp[iterandIdx] != NULL) {
    currentCheck->insertAtTail(new SymExpr(optInfo.iterCallTmp[iterandIdx]));
  }
  else {
    INT_FATAL("optInfo didn't have enough information");
  }

  CallExpr *staticOverride = new CallExpr(PRIM_UNARY_LNOT,
      new SymExpr(forall->optInfo.staticCheckSymForSymMap[baseSym]));
  currentCheck = new CallExpr("||", staticOverride, currentCheck);

  if (allChecks == NULL) {
    allChecks = currentCheck;
  }
  else {
    allChecks = new CallExpr("&&", currentCheck, allChecks);
  }
}

// for a call like `A[i]`, this will create something like
//
// param staticAutoLocalCheckSym = chpl_staticAutoLocalCheck(A, loopDomain)
//
// right before the `forall` and will return the symbol declared. If a check was
// added for `A` before, it'll just return the symbol (that was created before)
static Symbol *generateStaticCheckForAccess(CallExpr *access,
                                            ForallStmt *forall,
                                            int iterandIdx,
                                            Expr *&allChecks) {

  ForallOptimizationInfo &optInfo = forall->optInfo;
  Symbol *baseSym = getCallBase(access);
  INT_ASSERT(baseSym);

  if (optInfo.staticCheckSymForSymMap.count(baseSym) == 0) {
    SET_LINENO(forall);

    VarSymbol *checkSym = new VarSymbol("chpl__staticAutoLocalCheckSym");
    checkSym->addFlag(FLAG_PARAM);
    optInfo.staticCheckSymForSymMap[baseSym] = checkSym;

    CallExpr *checkCall = new CallExpr("chpl__staticAutoLocalCheck");
    checkCall->insertAtTail(baseSym);

    if (optInfo.iterSym[iterandIdx] != NULL) {
      checkCall->insertAtTail(new SymExpr(optInfo.iterSym[iterandIdx]));
    }
    else if (optInfo.dotDomIterExpr[iterandIdx] != NULL) {
      checkCall->insertAtTail(optInfo.dotDomIterExpr[iterandIdx]->copy());
    }
    else if (optInfo.iterCallTmp[iterandIdx] != NULL) {
      checkCall->insertAtTail(new SymExpr(optInfo.iterCallTmp[iterandIdx]));
    }
    else {
      INT_FATAL("optInfo didn't have enough information");
    }

    if (allChecks == NULL) {
      allChecks = new SymExpr(checkSym);
    }
    else {
      allChecks = new CallExpr("||", new SymExpr(checkSym), allChecks);
    }

    DefExpr *checkSymDef = new DefExpr(checkSym, checkCall);
    forall->insertBefore(checkSymDef);
    return checkSym;
  }
  else {
    return optInfo.staticCheckSymForSymMap[baseSym];
  }
}

// replace a candidate CallExpr with the corresponding PRIM_MAYBE_LOCAL_THIS
static CallExpr* replaceCandidate(CallExpr *candidate,
                                  Symbol *staticCheckSym,
                                  bool doStatic) {
  SET_LINENO(candidate);

  Symbol *callBase = getCallBase(candidate);
  CallExpr *repl = new CallExpr(PRIM_MAYBE_LOCAL_THIS, new SymExpr(callBase));
  for (int i = 1 ; i <= candidate->argList.length ; i++) {
    Symbol *argSym = toSymExpr(candidate->get(i))->symbol();
    INT_ASSERT(argSym);

    repl->insertAtTail(new SymExpr(argSym));
  }
  repl->insertAtTail(new SymExpr(staticCheckSym));

  // mark if this access is a static candidate. Today, this is only used for
  // accurate logging
  repl->insertAtTail(new SymExpr(doStatic?gTrue:gFalse));

  candidate->replace(repl);

  return repl;
}

// replace all the candidates in the loop with PRIM_MAYBE_LOCAL_THIS
// while doing that, also builds up static and dynamic conditions
static void optimizeLoop(ForallStmt *forall,
                         Expr *&staticCond, CallExpr *&dynamicCond,
                         bool doStatic) {

  std::vector< std::pair<CallExpr *, int> > candidates = doStatic ?
      forall->optInfo.staticCandidates :
      forall->optInfo.dynamicCandidates;

  std::vector< std::pair<CallExpr *, int> >::iterator it;
  for(it = candidates.begin() ; it != candidates.end() ; it++) {
    CallExpr *candidate = it->first;
    int iterandIdx = it->second;

    Symbol *checkSym = generateStaticCheckForAccess(candidate,
                                                    forall,
                                                    iterandIdx,
                                                    staticCond);
    if (!doStatic) {
      forall->optInfo.staticCheckSymsForDynamicCandidates.push_back(checkSym);

      generateDynamicCheckForAccess(candidate,
                                    forall,
                                    iterandIdx,
                                    dynamicCond);
    }

    replaceCandidate(candidate, checkSym, doStatic);
  }
}

// add the param part of the dynamicCond
static CallExpr *addStaticCheckSymsToDynamicCond(ForallStmt *forall,
                                                 CallExpr *dynamicCond,
                                                 std::vector<Symbol *> &staticCheckSyms) {
  CallExpr *ret = dynamicCond;

  if (staticCheckSyms.size() > 0) {
    SET_LINENO(forall);

    if (staticCheckSyms.size() == 1) {
      ret = new CallExpr("&&", staticCheckSyms[0], dynamicCond);
    }
    else {
      CallExpr *allChecks = new CallExpr("||", staticCheckSyms[0],
                                               staticCheckSyms[1]);

      for (size_t i = 2 ; i < staticCheckSyms.size() ; i++) {
        allChecks = new CallExpr("||", staticCheckSyms[i], allChecks);
      }
      ret = new CallExpr("&&", allChecks, dynamicCond);
    }
  }

  return ret;
}

static ForallStmt *cloneLoop(ForallStmt *forall) {
  SET_LINENO(forall);

  ForallStmt *clone = forall->copy();
  clone->optInfo.autoLocalAccessChecked = forall->optInfo.autoLocalAccessChecked;
  clone->optInfo.hasAlignedFollowers = forall->optInfo.hasAlignedFollowers;
  // added by tbrolin 01/21/2022
  clone->optInfo.inspectorExecutorChecked = forall->optInfo.inspectorExecutorChecked;
  clone->optInfo.cloneTypeIE = forall->optInfo.cloneTypeIE;
  clone->optInfo.indexIteratorType = forall->optInfo.indexIteratorType;
  clone->optInfo.inspectorFlag = forall->optInfo.inspectorFlag;
  clone->optInfo.ieID = forall->optInfo.ieID;
  clone->optInfo.ieHash = forall->optInfo.ieHash;
  // added by tbrolin 08/23/2022
  clone->optInfo.functionID = forall->optInfo.functionID;
  // added by tbrolin 06/30/2022
  clone->optInfo.irregWriteAggregationChecked = forall->optInfo.irregWriteAggregationChecked;
  // added by tbrolin 09/13/2022
  clone->optInfo.adaptiveRemotePrefetchingChecked = forall->optInfo.adaptiveRemotePrefetchingChecked;
  clone->optInfo.arpID = forall->optInfo.arpID;
  return clone;
}

// expects `optimized` to be in the AST, `unoptimized` to be not
//
// turns
//
//   optimized
//
// into
//
//   if condExpr then
//     optimized
//   else
//     unoptimized
static void constructCondStmtFromLoops(Expr *condExpr,
                                       ForallStmt *optimized,
                                       ForallStmt *unoptimized) {
  SET_LINENO(optimized);

  BlockStmt *thenBlock = new BlockStmt();
  BlockStmt *elseBlock = new BlockStmt();
  CondStmt *cond = new CondStmt(condExpr, thenBlock, elseBlock);

  optimized->insertAfter(cond);
  thenBlock->insertAtTail(optimized->remove());
  elseBlock->insertAtTail(unoptimized);
}

// Takes a forall statement and generates the following structure:
//
// param staticCheck1 = staticCheck(arr1, loopDomain)
// param staticCheck2 = staticCheck(arr2, loopDomain)
// ...
// param staticCheckN = staticCheck(arrN, loopDomain)
//
// if (staticCheck1 || staticCheck2 || ... || staticCheckN) {
//
//   const dynamicCheck = (!staticCheckX || dynamicCheck(arrX, loopDomain)) &&
//                        (!staticCheckY || dynamicCheck(arrY, loopDomain)) &&
//                        ...
//                        (!staticCheckZ || dynamicCheck(arrZ, loopDomain));
//
//   if (staticCheckX || .. || staticCheckZ) && dynamicCheck {
//     loop2
//   }
//   else {
//     loop1
//   }
// }
// else {
//   loop0
// }
//
// loop0: This'll be the copy of the unoptimized forall loop
// loop1: This'll contain optimizations that can be decided at the compile time
//        only. If there is no such optimizations but there are some that can be
//        determined at runtime, we still create this and it'll be identical to
//        loop0. This'll be the "backup" loop for potential dynamic check
//        failure
// loop2: Optional. This is only created if there are some dynamic candidates
//        and dynamic optimizations are enabled with the
//        `--dynamic-auto-local-access` flag.
//
// staticCheckX and staticCheckZ are static checks added for dynamic
// candidates. OR'ed static checks in two `if`s are added so that we can fold
// out unnecessary loops during resolution.
//
// Note that the static checks are param flags and during resolution we'll
// definitely lose either loop0 or the bigger branch. In other words, there can
// be duplicate loops at the end of normalize, but after resolution we expect
// them to go away.
static void generateOptimizedLoops(ForallStmt *forall) {
  std::vector< std::pair<CallExpr *, int> > &sOptCandidates = forall->optInfo.staticCandidates;
  std::vector< std::pair<CallExpr *, int> > &dOptCandidates = forall->optInfo.dynamicCandidates;

  const int totalNumCandidates = sOptCandidates.size() + dOptCandidates.size();
  if (totalNumCandidates == 0) return;

  ForallStmt *noOpt = NULL;
  ForallStmt *noDyn = NULL;
  Expr *staticCond = NULL;
  CallExpr *dynamicCond = NULL;

  // copy the forall to have: `noOpt` == loop0, `forall` == loop1
  noOpt = cloneLoop(forall);
  noOpt->optInfo.cloneType = NO_OPTIMIZATION;

  if (sOptCandidates.size() > 0) {
    // change potential static accesses in loop1
    optimizeLoop(forall, staticCond, dynamicCond, /* isStatic= */ true);
    forall->optInfo.cloneType = STATIC_ONLY;
  }

  if (dOptCandidates.size() > 0) {
    // copy the forall to have: `noDyn` == loop1, `forall` == loop2
    noDyn = cloneLoop(forall);
    noDyn->optInfo.cloneType = STATIC_ONLY;

    // change potential dynamic accesses in loop2
    optimizeLoop(forall, staticCond, dynamicCond, /* isStatic= */ false);
    forall->optInfo.cloneType = STATIC_AND_DYNAMIC;
  }

  // add `(staticChecksX || .. || staticChecksZ)` part
  dynamicCond = addStaticCheckSymsToDynamicCond(forall, dynamicCond,
          forall->optInfo.staticCheckSymsForDynamicCandidates);

  // we have all the parts needed, now build the structure
  if (staticCond != NULL) {  // this must be true at this point
    constructCondStmtFromLoops(staticCond, forall, noOpt);
  }

  if (dynamicCond != NULL) {
    constructCondStmtFromLoops(dynamicCond, forall, noDyn);
  }
}

static void autoLocalAccess(ForallStmt *forall) {

  if (forall->optInfo.autoLocalAccessChecked) {
    return;
  }
  forall->optInfo.autoLocalAccessChecked = true;

  LOGLN_ALA(forall);
  LOG_ALA(0, "Start analyzing forall", forall);

  if (!forall->optInfo.infoGathered) {
    gatherForallInfo(forall);
  }

  if (!loopHasValidInductionVariables(forall)) {
    LOG_ALA(1, "Can't optimize this forall: invalid induction variables", forall);
    return;
  }

  Symbol *loopDomain = canDetermineLoopDomainStatically(forall);
  bool staticLoopDomain = loopDomain != NULL;
  if (staticLoopDomain) {
    LOG_ALA(1, "Found loop domain", loopDomain);
    LOG_ALA(1, "Will attempt static and dynamic optimizations", forall);
    LOGLN_ALA(forall);
  }
  else {
    LOG_ALA(1, "Couldn't determine loop domain: will attempt dynamic optimizations only", forall);
    LOGLN_ALA(forall);
  }

  std::vector<CallExpr *> allCallExprs;
  collectCallExprs(forall->loopBody(), allCallExprs);

  for_vector(CallExpr, call, allCallExprs) {
    int iterandIdx = -1;
    CallRejectReason reason = CRR_UNKNOWN;
    Symbol *accBaseSym = getCallBaseSymIfSuitable(call, forall,
                                                  /*checkArgs=*/true,
                                                  &iterandIdx,
                                                  &reason);

    if (accBaseSym == NULL) {
      if (reason != CRR_UNKNOWN &&
          reason != CRR_NOT_ARRAY_ACCESS_LIKE) {
        LOG_ALA(2, "Start analyzing call", call);

        std::stringstream message;
        message << "Cannot optimize: ";
        message << getCallRejectReasonStr(reason);

        LOG_ALA(3, message.str().c_str(), call);
      }
      continue;
    }

    LOG_ALA(2, "Start analyzing call", call);

    INT_ASSERT(iterandIdx >= 0);

    bool canOptimizeStatically = false;

    if (staticLoopDomain) {

      // forall i in A.domain do ... A[i] ...
      if (forall->optInfo.dotDomIterSym[iterandIdx] == accBaseSym) {
        canOptimizeStatically = true;

        LOG_ALA(3, "Can optimize: Access base is the iterator's base", call);
      }
      else {
        Symbol *domSym = getDomSym(accBaseSym);

        if (domSym != NULL) {  //  I can find the domain of the array
          LOG_ALA(3, "Found the domain of the access base", domSym);

          // forall i in A.domain do ... B[i] ... where B and A share domain
          if (forall->optInfo.dotDomIterSymDom[iterandIdx] == domSym) {
            canOptimizeStatically = true;

            LOG_ALA(3, "Can optimize: Access base has the same domain as iterator's base", call);
          }

          // forall i in D do ... A[i] ... where D is A's domain
          else if (forall->optInfo.iterSym[iterandIdx] == domSym) {
            canOptimizeStatically = true;

            LOG_ALA(3, "Can optimize: Access base's domain is the iterator", call);
          }
        }
        else {
          LOG_ALA(3, "Can't determine the domain of access base", accBaseSym);
        }
      }

      if (canOptimizeStatically) {
        bool reportedLoc = LOG_ALA(2,
                                   "This call is a static optimization candidate",
                                   call);
        LOGLN_ALA(call);

        if (reportedLoc) {
          primMaybeLocalThisLocations.insert(call->astloc);
        }

        std::pair<CallExpr *, int> candidate;
        candidate.first = call;
        candidate.second = iterandIdx;
        forall->optInfo.staticCandidates.push_back(candidate);
      }
    }

    if (fDynamicAutoLocalAccess && !canOptimizeStatically) {
      // two things might have happened:
      //
      // (1) I couldn't find a domain symbol for this array, but it can
      // still be a candidate for optimization based on analysis at
      // runtime
      //
      // (2) the loop wasn't suitable for static optimization (i.e. I can't
      // determine the symbol of the loop domain. But this call that I am
      // looking at still has potential because it is `A(i)` where `i` is
      // the loop index. So, add this call to dynamic candidates
      bool reportedLoc = LOG_ALA(2,
                                 "This call is a dynamic optimization candidate",
                                 call);
      LOGLN_ALA(call);

      if (reportedLoc) {
        primMaybeLocalThisLocations.insert(call->astloc);
      }

      std::pair<CallExpr *, int> candidate;
      candidate.first = call;
      candidate.second = iterandIdx;
      forall->optInfo.dynamicCandidates.push_back(candidate);
    }
  }

  generateOptimizedLoops(forall);

  LOG_ALA(0, "End analyzing forall", forall);
  LOGLN_ALA(forall);
}



//
// Resolution support for auto-local-access
//
static CallExpr *revertAccess(CallExpr *call) {
  LOG_ALA(0, "Static check failed. Reverting optimization", call,
          /*forallDetails=*/true);

  CallExpr *repl = new CallExpr(new UnresolvedSymExpr("this"),
                                gMethodToken);

  // Don't take the last two args; they are the static control symbol, and flag
  // that tells whether this is a statically-determined access
  for (int i = 1 ; i < call->argList.length-1 ; i++) {
    Symbol *argSym = toSymExpr(call->get(i))->symbol();
    repl->insertAtTail(new SymExpr(argSym));
  }

  return repl;
}

static CallExpr *confirmAccess(CallExpr *call) {
  if (toSymExpr(call->get(call->argList.length))->symbol() == gTrue) {
    LOG_ALA(0, "Static check successful. Using localAccess", call,
            /*forallDetails=*/true);
  }
  else {
    LOG_ALA(0, "Static check successful. Using localAccess with dynamic check", call);
  }

  CallExpr *repl = new CallExpr(new UnresolvedSymExpr("localAccess"),
                                gMethodToken);

  // Don't take the last two args; they are the static control symbol, and flag
  // that tells whether this is a statically-determined access
  for (int i = 1 ; i < call->argList.length-1 ; i++) {
    Symbol *argSym = toSymExpr(call->get(i))->symbol();
    repl->insertAtTail(new SymExpr(argSym));
  }

  return repl;
}

//
// An analysis to enable overriding dynamic checks for fast followers
//
static void symbolicFastFollowerAnalysis(ForallStmt *forall) {
  AList &iterExprs = forall->iteratedExpressions();

  if (iterExprs.length < 2) {
    return;
  }

  Symbol *commonDomSym = NULL;
  bool confirm = true;

  for_alist(iterExpr, forall->iteratedExpressions()) {
    Symbol *iterBaseSym = NULL;
    Symbol *iterBaseDomSym = NULL;

    // record it if it is a symbol
    if (isUnresolvedSymExpr(iterExpr) || isSymExpr(iterExpr)) {
      if (SymExpr *iterSE = toSymExpr(iterExpr)) {
        iterBaseSym = iterSE->symbol();
      }
    }
    // it might be in the form `A.domain`
    else if (Symbol *dotDomBaseSym = getDotDomBaseSym(iterExpr)) {
      iterBaseSym = dotDomBaseSym;
    }

    // break if we couldn't get a symbol that we can analyze further
    if (iterBaseSym == NULL) {
      confirm = false;
      break;
    }

    if (Symbol *domainSymbol = getDomSym(iterBaseSym)) {
      // found a symbol through a definition that I can recognize
      iterBaseDomSym = domainSymbol;
    }
    else {
      // for now, just roll the dice and hope that it was a domain
      iterBaseDomSym = iterBaseSym;
    }

    if (commonDomSym == NULL) {
      commonDomSym = iterBaseDomSym;
    }
    else {
      // this iterator's symbol is different then what I assumed to be the
      // common domain for all iterators. Not much I can do with this loop
      if (commonDomSym != iterBaseDomSym) {
        confirm = false;
        break;
      }
    }
  }
  forall->optInfo.hasAlignedFollowers = confirm;
}

//
// Support for automatic aggregation

static void autoAggregation(ForallStmt *forall) {

  // if auto-local-access was on (that's the default case), we don't need to
  // look into the loop in detail, but if that optimization was off, we still
  // need to check what is local and what is not for aggregation.
  if (forall->optInfo.autoLocalAccessChecked == false) {
    autoLocalAccess(forall);
  }

  if (!forall->optInfo.infoGathered) {
    gatherForallInfo(forall);
  }

  LOG_AA(0, "Start analyzing forall for automatic aggregation", forall);

  if (loopHasValidInductionVariables(forall)) {
    std::vector<Expr *> lastStmts = getLastStmtsForForallUnorderedOps(forall);

    for_vector(Expr, lastStmt, lastStmts) {
      if (CallExpr *lastCall = toCallExpr(lastStmt)) {
        bool reportedLoc = false;
        if (lastCall->isNamedAstr(astrSassign)) {
          // no need to do anything if it is array access
          if (assignmentSuitableForAggregation(lastCall, forall)) {
            reportedLoc = LOG_AA(1, "Found an aggregation candidate", lastCall);

            insertAggCandidate(lastCall, forall);
          }
          // we need special handling if it is a symbol that is an array element
          else if (handleYieldedArrayElementsInAssignment(lastCall, forall)) {
            reportedLoc = LOG_AA(1, "Found an aggregation candidate", lastCall);

            insertAggCandidate(lastCall, forall);
          }
        }

        if (reportedLoc) {
          primMaybeAggregateAssignLocations.insert(lastCall->astloc);
        }
      }
    }
  }
  else {
    LOG_AA(1, "Can't optimize this forall: invalid induction variables", forall);
  }

  LOG_AA(0, "End analyzing forall for automatic aggregation", forall);
  LOGLN_AA(forall);
}

AggregationCandidateInfo::AggregationCandidateInfo(CallExpr *candidate,
                                                   ForallStmt *forall):
  candidate(candidate),
  forall(forall),
  lhsLocalityInfo(UNKNOWN),
  rhsLocalityInfo(UNKNOWN),
  lhsLogicalChild(NULL),
  rhsLogicalChild(NULL),
  srcAggregator(NULL),
  dstAggregator(NULL) { }

static CondStmt *createAggCond(CallExpr *noOptAssign, Symbol *aggregator, SymExpr *aggMarkerSE) {
  INT_ASSERT(aggregator);
  INT_ASSERT(aggMarkerSE);

  // the candidate assignment must have been normalized, so, we expect symexpr
  // on both sides
  SymExpr *lhsSE = toSymExpr(noOptAssign->get(1));
  SymExpr *rhsSE = toSymExpr(noOptAssign->get(2));
  INT_ASSERT(lhsSE != NULL && rhsSE != NULL);

  SET_LINENO(noOptAssign);

  // generate the aggregated call
  Expr *callBase = buildDotExpr(aggregator, "copy");
  CallExpr *aggCall = new CallExpr(callBase, lhsSE->copy(), rhsSE->copy());

  // create the conditional with regular assignment on the then block
  // and the aggregated call is on the else block
  BlockStmt *thenBlock = new BlockStmt();
  BlockStmt *elseBlock = new BlockStmt();

  CondStmt *aggCond = new CondStmt(aggMarkerSE, thenBlock, elseBlock);

  thenBlock->insertAtTail(noOptAssign);
  elseBlock->insertAtTail(aggCall);

  return aggCond;
}

// PRIM_MAYBE_LOCAL_ARR_ELEM has a 2nd argument that is a copy of the expression
// that we iterate. We add it there when we create the primitive, so that we can
// generate some checks outside the forall. However, keeping that expression
// inside the forall body can have bunch of side effects. In some cases we
// remove it when we use it, but we can also leave some untouched. This
// function removes that argument if the primitive still has 3 arguments
void AggregationCandidateInfo::removeSideEffectsFromPrimitive() {
  INT_ASSERT(this->candidate->isNamed("="));

  if (CallExpr *childCall = toCallExpr(this->candidate->get(1))) {
    if (childCall->isPrimitive(PRIM_MAYBE_LOCAL_ARR_ELEM)) {
      if (childCall->numActuals() == 4) {
        childCall->get(2)->remove();
      }
    }
  }

  if (CallExpr *childCall = toCallExpr(this->candidate->get(2))) {
    if (childCall->isPrimitive(PRIM_MAYBE_LOCAL_ARR_ELEM)) {
      if (childCall->numActuals() == 4) {
        childCall->get(2)->remove();
      }
    }
  }

}

// currently we only support one aggregator at normalize time, however, we
// should relax that limitation a bit. Normalize should be able to add both
// aggregators for
//
// forall i in a.domain {
//   a[i] = b[i];
// }
//
// Because: b[i] is a local access candidate, and both sides of = will be
// visited as such. Currently, that's not handled properly
void AggregationCandidateInfo::addAggregators() {
  if (srcAggregator != NULL && dstAggregator != NULL) { // assert?
    return; // we have already enough
  }

  // we have a lhs that waits analysis or local, and a rhs that we can't know
  // about
  if (srcAggregator == NULL &&
      (lhsLocalityInfo == PENDING || lhsLocalityInfo == LOCAL) &&
      rhsLogicalChild != NULL) {
    if (CallExpr *genCall = getAggGenCallForChild(rhsLogicalChild, true)) {
      SET_LINENO(this->forall);

      UnresolvedSymExpr *aggTmp = new UnresolvedSymExpr("chpl_src_auto_agg");
      ShadowVarSymbol *aggregator = ShadowVarSymbol::buildForPrefix(SVP_VAR,
                                                                    aggTmp,
                                                                    NULL, //type
                                                                    genCall);
      aggregator->addFlag(FLAG_COMPILER_ADDED_AGGREGATOR);
      forall->shadowVariables().insertAtTail(aggregator->defPoint);

      LOG_AA(2, "Potential source aggregation", this->candidate);

      this->srcAggregator = aggregator;
    }
  }

  // we have a rhs that waits analysis or local
  if (dstAggregator == NULL &&
      (rhsLocalityInfo == PENDING || rhsLocalityInfo == LOCAL) &&
      lhsLogicalChild != NULL) {
    if (CallExpr *genCall = getAggGenCallForChild(lhsLogicalChild, false)) {
      SET_LINENO(this->forall);

      UnresolvedSymExpr *aggTmp = new UnresolvedSymExpr("chpl_dst_auto_agg");
      ShadowVarSymbol *aggregator = ShadowVarSymbol::buildForPrefix(SVP_VAR,
                                                                    aggTmp,
                                                                    NULL, //type
                                                                    genCall);
      aggregator->addFlag(FLAG_COMPILER_ADDED_AGGREGATOR);
      forall->shadowVariables().insertAtTail(aggregator->defPoint);

      LOG_AA(2, "Potential destination aggregation", this->candidate);

      this->dstAggregator = aggregator;
    }
  }

}

static const char *getForallCloneTypeStr(Symbol *aggMarker) {
  if (aggMarker->hasFlag(FLAG_AGG_IN_STATIC_AND_DYNAMIC_CLONE)) {
    return "[static and dynamic ALA clone]";
  }
  if (aggMarker->hasFlag(FLAG_AGG_IN_STATIC_ONLY_CLONE)) {
    return "[static only ALA clone]";
  }
  return "";
}

static CallExpr *getAggGenCallForChild(Expr *child, bool srcAggregation) {
  SET_LINENO(child);

  if (CallExpr *childCall = toCallExpr(child)) {
    const char *aggFnName = srcAggregation ? "chpl_srcAggregatorFor" :
                                             "chpl_dstAggregatorFor";
    if (canBeLocalAccess(childCall)) {
      if (SymExpr *arrSymExpr = toSymExpr(childCall->get(1))) {
        return new CallExpr(aggFnName, new SymExpr(arrSymExpr->symbol()));
      }
    }
    else if (childCall->isPrimitive(PRIM_MAYBE_LOCAL_ARR_ELEM)) {
      return new CallExpr(aggFnName, childCall->get(2)->remove());
    }
    else if (SymExpr *arrSymExpr = toSymExpr(childCall->baseExpr)) {
      return new CallExpr(aggFnName, new SymExpr(arrSymExpr->symbol()));
    }
  }

  return NULL;
}

// currently we want both sides to be calls, but we need to relax these to
// accept symexprs to support foralls over arrays
static bool assignmentSuitableForAggregation(CallExpr *call, ForallStmt *forall) {
  INT_ASSERT(call->isNamed("="));

  if (CallExpr *leftCall = toCallExpr(call->get(1))) {
    if (CallExpr *rightCall = toCallExpr(call->get(2))) {
      // we want either side to be PRIM_MAYBE_LOCAL_THIS
      if (canBeLocalAccess(leftCall) ||
          canBeLocalAccess(rightCall)) {
        // we want the side that's not to have a baseExpr that's a SymExpr
        // this avoid function calls
        if (!canBeLocalAccess(leftCall)) {
          return getCallBaseSymIfSuitable(leftCall, forall,
                                          /*checkArgs=*/false,
                                          NULL) != NULL;
        }
        else if (!canBeLocalAccess(rightCall)) {
          return getCallBaseSymIfSuitable(rightCall, forall,
                                          /*checkArgs=*/false,
                                          NULL) != NULL;
        }
      }
    }
    else if (SymExpr *rightSymExpr = toSymExpr(call->get(2)))  {
      if (rightSymExpr->symbol()->isImmediate() ||
          rightSymExpr->symbol()->isParameter()) {
        if (!canBeLocalAccess(leftCall)) {
          return getCallBaseSymIfSuitable(leftCall, forall,
                                          /*checkArgs=*/false,
                                          NULL) != NULL;
        }
      }
    }
  }
  return false;
}

Expr *preFoldMaybeAggregateAssign(CallExpr *call) {
  INT_ASSERT(call->isPrimitive(PRIM_MAYBE_AGGREGATE_ASSIGN));

  Expr *rhs = call->get(2)->remove();
  Expr *lhs = call->get(1)->remove();

  CallExpr *assign = new CallExpr("=", lhs, rhs);

  SymExpr *srcAggregatorSE = toSymExpr(call->get(2)->remove());
  INT_ASSERT(srcAggregatorSE);
  SymExpr *dstAggregatorSE = toSymExpr(call->get(1)->remove());
  INT_ASSERT(dstAggregatorSE);

  Symbol *srcAggregator = srcAggregatorSE->symbol();
  Symbol *dstAggregator = dstAggregatorSE->symbol();

  SymExpr *rhsLocalSE = toSymExpr(call->get(2)->remove());
  INT_ASSERT(rhsLocalSE);
  SymExpr *lhsLocalSE = toSymExpr(call->get(1)->remove());
  INT_ASSERT(lhsLocalSE);

  bool rhsLocal = (rhsLocalSE->symbol() == gTrue);
  bool lhsLocal = (lhsLocalSE->symbol() == gTrue);

  SymExpr *aggMarkerSE = toSymExpr(call->get(1)->remove());
  INT_ASSERT(aggMarkerSE);

  Expr *replacement = NULL;

  std::stringstream message;

  // either side is local, but not both
  if (lhsLocal != rhsLocal) {
    Symbol *aggregator = NULL;

    // aggregator can be nil in two cases:
    // (1) we couldn't determine what the code looks like statically on one side of
    //     the assignment, in which case we set this argument to `gNil`.
    // (2) we may have called an aggregator generator on an unsupported type,
    //     which returns `nil` in the module code.
    if (lhsLocal && (srcAggregator->type != dtNil)) {
      if (fReportAutoAggregation) {
        message << "LHS is local, RHS is nonlocal. Will use source aggregation ";
      }
      aggregator = srcAggregator;
    }
    else if (rhsLocal && (dstAggregator->type != dtNil)) {
      if (fReportAutoAggregation) {
        message << "LHS is nonlocal, RHS is local. Will use destination aggregation ";
      }
      aggregator = dstAggregator;
    }

    if (aggregator != NULL) {
      replacement = createAggCond(assign, aggregator, aggMarkerSE);
    }
  }

  if (replacement == NULL) {
    if (fReportAutoAggregation) {
      if (lhsLocal && rhsLocal) {
        message << "Both sides of the assignment looks local. Will not use aggregation";
      }
      else if (!lhsLocal && !rhsLocal) {
        message << "Could not prove the locality of either side. Will not use aggregation";
      }
      else {
        message << "Will not use aggregation for unknown reasons. Type doesn't support aggregation?";
      }
    }
    aggMarkerSE->symbol()->defPoint->remove();

    FnSymbol *parentFn = toFnSymbol(call->parentSymbol);
    INT_ASSERT(parentFn);

    if (srcAggregator != gNil) {
      removeAggregatorFromFunction(srcAggregator, parentFn);
    }
    if (dstAggregator != gNil) {
      removeAggregatorFromFunction(dstAggregator, parentFn);
    }
    replacement = assign;
  }

  if (fReportAutoAggregation) {
    message << getForallCloneTypeStr(aggMarkerSE->symbol());
    LOG_AA(0, message.str().c_str(), call);
  }

  primMaybeAggregateAssignLocations.erase(call->astloc);

  return replacement;
}

// 3rd argument of PRIM_MAYBE_LOCAL_ARR_ELEM controls the optimization and it is
// initially set to `false` if the optimization can be done only in a fast
// follower body.  This function takes that body as an argument, and adjusts
// such primitives' 3rd arguments to enable optimization
void adjustPrimsInFastFollowerBody(BlockStmt *body) {
  std::vector<CallExpr *> calls;
  collectCallExprs(body, calls);

  for_vector(CallExpr, call, calls) {
    if (call->isPrimitive(PRIM_MAYBE_LOCAL_ARR_ELEM)) {
      call->get(3)->replace(new SymExpr(gTrue));
    }
  }
}

void AggregationCandidateInfo::transformCandidate() {
  SET_LINENO(this->candidate);
  Expr *rhs = this->candidate->get(2)->remove();
  Expr *lhs = this->candidate->get(1)->remove();
  CallExpr *repl = new CallExpr(PRIM_MAYBE_AGGREGATE_ASSIGN,
                                lhs,
                                rhs);

  repl->insertAtTail(this->dstAggregator ? this->dstAggregator : gNil);
  repl->insertAtTail(this->srcAggregator ? this->srcAggregator : gNil);

  // add bool flags that denote whether one side of the assignment is local.
  // This is happening before normalization, so the only way we can know whether
  // something is local at this point is if that thing is a literal. And that
  // can only happen on RHS. However, I am checking for both sides for
  // completeness
  repl->insertAtTail(new SymExpr(lhsLocalityInfo == LOCAL ? gTrue : gFalse));
  repl->insertAtTail(new SymExpr(rhsLocalityInfo == LOCAL ? gTrue : gFalse));

  Symbol *aggMarker = newTemp("aggMarker", dtBool);
  aggMarker->addFlag(FLAG_AGG_MARKER);
  switch (this->forall->optInfo.cloneType) {
    case STATIC_AND_DYNAMIC:
      aggMarker->addFlag(FLAG_AGG_IN_STATIC_AND_DYNAMIC_CLONE);
      break;
    case STATIC_ONLY:
      aggMarker->addFlag(FLAG_AGG_IN_STATIC_ONLY_CLONE);
      break;
    default:
      break;
  }
  this->candidate->insertBefore(new DefExpr(aggMarker));

  repl->insertAtTail(new SymExpr(aggMarker));

  this->candidate->replace(repl);
}

static void insertAggCandidate(CallExpr *call, ForallStmt *forall) {
  AggregationCandidateInfo *info = new AggregationCandidateInfo(call, forall);

  // establish connection between PRIM_MAYBE_LOCAL_THIS and their parent
  CallExpr *lhsCall = toCallExpr(call->get(1));
  INT_ASSERT(lhsCall); // enforced by callSuitableForAggregation
  if (lhsCall->isPrimitive(PRIM_MAYBE_LOCAL_THIS) ||
      lhsCall->isPrimitive(PRIM_MAYBE_LOCAL_ARR_ELEM)) {
    info->lhsLocalityInfo = PENDING;
  }
  else if (isLocalAccess(lhsCall)) {
    info->lhsLocalityInfo = LOCAL;
  }
  info->lhsLogicalChild = lhsCall;

  if (CallExpr *rhsCall = toCallExpr(call->get(2))) {
    if (rhsCall->isPrimitive(PRIM_MAYBE_LOCAL_THIS) ||
        rhsCall->isPrimitive(PRIM_MAYBE_LOCAL_ARR_ELEM)) {
      info->rhsLocalityInfo = PENDING;
    }
    else if (isLocalAccess(rhsCall)) {
      info->rhsLocalityInfo = LOCAL;
    }
    info->rhsLogicalChild = rhsCall;
  }
  else if (SymExpr *rhsSymExpr = toSymExpr(call->get(2))) {
    info->rhsLocalityInfo = LOCAL;
    info->rhsLogicalChild = rhsSymExpr;
  }

  info->addAggregators();

  info->removeSideEffectsFromPrimitive();

  info->transformCandidate();
}

static Expr *getAlignedIterandForTheYieldedSym(Symbol *sym, ForallStmt *forall,
                                               bool *onlyIfFastFollower) {
  AList &iterExprs = forall->iteratedExpressions();
  AList &indexVars = forall->inductionVariables();

  if (!forall->optInfo.hasAlignedFollowers) {
    // either not zippered, or followers are not statically aligned:
    // we set `onlyIfFastFollower` to true only if the iterand is a follower.
    // We can argue about this symbols locality only dynamically if it is in a
    // fast follower body.
    for (int i = 1 ; i <= indexVars.length ; i++){
      if (DefExpr *idxDef = toDefExpr(indexVars.get(i))) {
        if (sym == idxDef->sym) {
          *onlyIfFastFollower = (i>1);
          return iterExprs.get(i);
        }
      }
    }
  }
  else {
    // forall is zippered over what seems to be aligned followers (they have the
    // same domain that we can prove just by looking at symbols)
    for (int i = 1 ; i <= indexVars.length ; i++){
      if (DefExpr *idxDef = toDefExpr(indexVars.get(i))) {
        if (sym == idxDef->sym) {
          return iterExprs.get(i);
        }
      }
    }
  }

  return NULL;
}

static bool handleYieldedArrayElementsInAssignment(CallExpr *call,
                                                   ForallStmt *forall) {
  SET_LINENO(call);

  INT_ASSERT(call->isNamed("="));

  if (!forall->optInfo.infoGathered) {
    gatherForallInfo(forall);
  }

  Symbol *maybeArrElemSym = NULL;
  Expr *maybeArrExpr = NULL;

  bool lhsMaybeArrSym = false;
  bool rhsMaybeArrSym = false;

  SymExpr *lhsSymExpr = toSymExpr(call->get(1));
  SymExpr *rhsSymExpr = toSymExpr(call->get(2));

  bool onlyIfFastFollower = false;

  // note that if we hit both inner if's below, that would mean we have
  // something like `a=a`. We check for this case right after and don't continue
  // with the optimization
  if (lhsSymExpr) {
    Symbol *tmpSym = lhsSymExpr->symbol();
    maybeArrExpr = getAlignedIterandForTheYieldedSym(tmpSym, forall,
                                                     &onlyIfFastFollower);
    if (maybeArrExpr != NULL) {
      lhsMaybeArrSym = true;
      maybeArrElemSym = tmpSym;
    }
  }
  if (rhsSymExpr) {
    Symbol *tmpSym = rhsSymExpr->symbol();
    maybeArrExpr = getAlignedIterandForTheYieldedSym(tmpSym, forall,
                                                     &onlyIfFastFollower);
    if (maybeArrExpr != NULL) {
      rhsMaybeArrSym = true;
      maybeArrElemSym = tmpSym;
    }
  }

  // stop if neither can be an array element symbol
  if (!lhsMaybeArrSym && !rhsMaybeArrSym) return false;

  // just to be sure, stop if someone's doing `a=a`;
  if (lhsMaybeArrSym && rhsMaybeArrSym) return false;

  Expr *otherChild = lhsMaybeArrSym ? call->get(2) : call->get(1);

  bool otherChildIsSuitable = false;
  if (CallExpr *otherCall = toCallExpr(otherChild)) {
    if (canBeLocalAccess(otherCall)) {
      otherChildIsSuitable = true;
    }
    else {
      otherChildIsSuitable = (getCallBaseSymIfSuitable(otherCall,
                                                       forall,
                                                       /*checkArgs=*/false,
                                                       NULL) != NULL);
    }
  }

  if (!otherChildIsSuitable) return false;

  SymExpr *symExprToReplace = lhsMaybeArrSym ? lhsSymExpr : rhsSymExpr;

  // add the check symbol
  VarSymbol *checkSym = new VarSymbol("chpl__yieldedArrayElemIsAligned");
  checkSym->addFlag(FLAG_PARAM);

  // this call is a param call, the copy expression will be removed
  CallExpr *checkCall = new CallExpr("chpl__arrayIteratorYieldsLocalElements");
  checkCall->insertAtTail(maybeArrExpr->copy());

  DefExpr *checkSymDef = new DefExpr(checkSym, checkCall);
  forall->insertBefore(checkSymDef);

  // We want the `fastFollowerControl` flag to be false for the non-fast
  // follower, and true elsewhere. So, if `onlyIfFastFollower` is set, we
  // initially set `fastFollowerControl` to be `false`. We will switch it to
  // `true` when we copy the fast follower body, later on.
  //
  // If `onlyIfFastFollower` is unset, this flag shouldn't hinder the
  // optimization, so we set it to `true`.
  SymExpr *fastFollowerControl = new SymExpr(onlyIfFastFollower ? gFalse:gTrue);

  // replace the call with PRIM_MAYBE_LOCAL_ARR_ELEM
  // we are adding `maybeArrExpr` that may have side effects, but we'll remove
  // it before we start normalization
  CallExpr *primCall = new CallExpr(PRIM_MAYBE_LOCAL_ARR_ELEM,
                                    new SymExpr(maybeArrElemSym),
                                    maybeArrExpr->copy(),
                                    new SymExpr(checkSym),
                                    fastFollowerControl);

  symExprToReplace->replace(primCall);

  return true;
}

static CallExpr *findMaybeAggAssignInBlock(BlockStmt *block) {
  Expr *cur = block->body.last();

  // at this point, only skippable call seems like PRIM_END_OF_STATEMENT, so
  // just skip that and give up after.
  if (CallExpr *curCall = toCallExpr(cur)) {
    if (curCall->isPrimitive(PRIM_END_OF_STATEMENT)) {
      cur = cur->prev;
    }
  }

  if (CallExpr *curCall = toCallExpr(cur)) {
    if (curCall->isPrimitive(PRIM_MAYBE_AGGREGATE_ASSIGN)) {
      return curCall;
    }
  }

  return NULL;
}

// called during resolution when we revert an aggregation
static void removeAggregatorFromFunction(Symbol *aggregator, FnSymbol *parent) {

  // find other SymExprs within the function and remove the aggregator if it is
  // not being used by other primitives, or its `copy` function.

  std::vector<SymExpr *> symExprsToCheck;
  collectSymExprsFor(parent, aggregator, symExprsToCheck);

  std::vector<SymExpr *> symExprsToRemove;
  bool shouldRemove = true;

  for_vector(SymExpr, se, symExprsToCheck) {
    if (CallExpr *parentCall = toCallExpr(se->parentExpr)) {
      // is `aggregator used in another `PRIM_MAYBE_AGGREGATE_ASSIGN`?
      if (parentCall->isPrimitive(PRIM_MAYBE_AGGREGATE_ASSIGN)) {
        shouldRemove = false;
        break;
      }

      // is `aggregator` receiver of a `copy` call?
      if (parentCall->isNamed("copy")) {
        // this check should be enough to make sure that this is an aggregated
        // copy call. The following asserts make sure of that:
        INT_ASSERT(toSymExpr(parentCall->get(2))->symbol() == aggregator);
        INT_ASSERT(parentCall->resolvedFunction()->_this->getValType() ==
                   aggregator->getValType());
        shouldRemove = false;
        break;
      }
    }

    symExprsToRemove.push_back(se);
  }

  if (shouldRemove) {
    // remove the definition
    aggregator->defPoint->remove();

    for_vector(SymExpr, se, symExprsToRemove) {
      se->remove();
    }
  }
}

static void removeAggregatorFromMaybeAggAssign(CallExpr *call, int argIndex) {
  INT_ASSERT(call->isPrimitive(PRIM_MAYBE_AGGREGATE_ASSIGN));

  SymExpr *aggregatorSE = toSymExpr(call->get(argIndex));
  INT_ASSERT(aggregatorSE);
  Symbol *aggregator = aggregatorSE->symbol();
  if (aggregator != gNil) {
    // replace the SymExpr in call
    aggregatorSE->replace(new SymExpr(gNil));

    FnSymbol *parentFn = toFnSymbol(call->parentSymbol);
    INT_ASSERT(parentFn);

    removeAggregatorFromFunction(aggregator, parentFn);
  }
}

static void findAndUpdateMaybeAggAssign(CallExpr *call, bool confirmed) {
  bool unaggregatable = false;
  if (call->isPrimitive(PRIM_MAYBE_LOCAL_ARR_ELEM)) {
    if (!confirmed) {
      unaggregatable = true;
    }
  }

  bool lhsOfMaybeAggAssign = false;
  bool rhsOfMaybeAggAssign = false;
  Symbol *tmpSym = NULL;
  if (CallExpr *parentCall = toCallExpr(call->parentExpr)) {
    if (parentCall->isPrimitive(PRIM_MOVE)) {
      SymExpr *lhsSE = toSymExpr(parentCall->get(1));
      INT_ASSERT(lhsSE);

      Symbol *lhsSym = lhsSE->symbol();
      if (lhsSym->hasFlag(FLAG_EXPR_TEMP)) {
        tmpSym = lhsSym;
      }
    }
  }

  if (tmpSym) {
    if (CallExpr *maybeAggAssign = findMaybeAggAssignInBlock(call->getScopeBlock())) {


      if (fReportAutoAggregation) {
        std::stringstream message;

        SymExpr *aggMarkerSE = toSymExpr(maybeAggAssign->get(7));
        INT_ASSERT(aggMarkerSE);

        message << "Aggregation candidate ";
        message << "has ";
        message << (confirmed ? "confirmed" : "reverted");
        message << " local child ";
        message << getForallCloneTypeStr(aggMarkerSE->symbol());
        LOG_AA(0, message.str().c_str(), call);
      }

      if (unaggregatable) {
        removeAggregatorFromMaybeAggAssign(maybeAggAssign, 3);
        removeAggregatorFromMaybeAggAssign(maybeAggAssign, 4);
      }
      else {
        SymExpr *lhsSE = toSymExpr(maybeAggAssign->get(1));
        INT_ASSERT(lhsSE);

        SymExpr *rhsSE = toSymExpr(maybeAggAssign->get(2));
        INT_ASSERT(rhsSE);

        lhsOfMaybeAggAssign = (lhsSE->symbol() == tmpSym);
        rhsOfMaybeAggAssign = (rhsSE->symbol() == tmpSym);

        if (lhsOfMaybeAggAssign || rhsOfMaybeAggAssign) {
          // at most one can be true
          INT_ASSERT(lhsOfMaybeAggAssign != rhsOfMaybeAggAssign);

          int flagIndex = lhsOfMaybeAggAssign ? 5 : 6;
          SymExpr *controlFlag = new SymExpr(confirmed ? gTrue : gFalse);
          maybeAggAssign->get(flagIndex)->replace(controlFlag);

          int aggToRemoveIndex = lhsOfMaybeAggAssign ? 3 : 4;
          removeAggregatorFromMaybeAggAssign(maybeAggAssign, aggToRemoveIndex);
        }
      }
    }
  }
}

// the logic here is applicable for lowerForalls
static void removeAggregationFromRecursiveForallHelp(BlockStmt *block) {
  for_alist(stmt, block->body) {
    if (CondStmt *condStmt = toCondStmt(stmt)) {
      SymExpr *condExpr = toSymExpr(condStmt->condExpr);
      if (condExpr == nullptr)
        if (CallExpr* call = toCallExpr(condStmt->condExpr))
          if (call->isPrimitive(PRIM_CHECK_ERROR))
            continue; // error check blocks should not have aggregation code
      INT_ASSERT(condExpr);

      Symbol *aggMarkerSym = condExpr->symbol();

      if (aggMarkerSym->hasFlag(FLAG_AGG_MARKER)) {

        CallExpr *assignCall = toCallExpr(condStmt->thenStmt->getFirstExpr()->parentExpr);
        INT_ASSERT(assignCall);
        INT_ASSERT(assignCall->isNamed("="));

        CallExpr *aggCall = toCallExpr(condStmt->elseStmt->getFirstExpr()->parentExpr);
        INT_ASSERT(aggCall);
        INT_ASSERT(aggCall->isNamed("copy"));

        SymExpr *aggregatorSE = toSymExpr(aggCall->get(1));
        INT_ASSERT(aggregatorSE);

        Symbol *aggSym = aggregatorSE->symbol();
        INT_ASSERT(aggSym->hasFlag(FLAG_COMPILER_ADDED_AGGREGATOR));

        condStmt->insertBefore(assignCall->remove());
        condStmt->remove();
        aggMarkerSym->defPoint->remove();
        aggSym->defPoint->remove();

      }
    }
    else if (BlockStmt *blockStmt = toBlockStmt(stmt)) {
      removeAggregationFromRecursiveForallHelp(blockStmt);
    }
  }
}

static bool canBeLocalAccess(CallExpr *call) {
  return call->isPrimitive(PRIM_MAYBE_LOCAL_THIS) ||
         isLocalAccess(call);
}

static bool isLocalAccess(CallExpr *call) {
  if (CallExpr *baseCall = toCallExpr(call->baseExpr)) {
    if (baseCall->isNamedAstr(astrSdot)) {
      if (SymExpr *secondArgSE = toSymExpr(baseCall->get(2))) {
        if (VarSymbol *secondArgSym = toVarSymbol(secondArgSE->symbol())) {
          if (Immediate *imm = secondArgSym->immediate) {
            if(strcmp(imm->string_value(), "localAccess") == 0) {
              return true;
            }
          }
        }
      }
    }
  }

  return false;
}


// Added by tbrolin 1/11/2022 - present
//
// Support for inspector-executor to apply selective data replication
//

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                      Normalization Related Functions                      //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
/*
    The following functions perform the normalization-related tasks for the
    inspector-executor optimization. These functions mostly perform loop
    cloning and conditional construction. A majority of the static analysis
    to determine whether the optimization is valid/applicable is performed
    during pre-folding and post-resolution.

    By the end of normalization, a given forall loop with a candidate
    access will be transformed into:

        ....
        if isCallPathValid(funcID) {
            if staticCheckCall(forallID) == true {
                if doInspector(..) {
                    do inspector loop
                    sort indices
                    turn off inspector flags
                }
                do executor forall
            }
            else {
                do original forall
            }
        }
        else {
            do original forall
        }

    A candidate access is of the form A[expr(B[expr])], where "expr"
    must be a binary operation between immediates or variables that
    are yielded by loops that iterate over arrays/domains. For
    simplicity, we commonly just use A[B[i]] to refer to a candidate
    access. But we cannot know until prefolding whether A and B are arrays.
    But we can enforce some requirenents on various other structures during
    normalization.

    TODO: As of now (02/09/22), we will only optimize for one
    candidate access in the loop. We'll just assume the first one
    we find is the one we optimize.

    Arguments:
    forall -> The forall loop to be optimized

    Return:
    None (forall is modified)
*/
static void inspectorExecutor(ForallStmt *forall)
{
  // If this loop has already been checked for this optimization,
  // return. This happens when we make a clone of the forall via
  // this very same optimization. This prevents an infinite loop.
  // Looking at inspectorExecutorChecked should be sufficient but just
  // in case, also look at the cloneTypeIE field.
  if (forall->optInfo.inspectorExecutorChecked || forall->optInfo.cloneTypeIE == CLONED) {
    return;
  }
  forall->optInfo.inspectorExecutorChecked = true;

  // Quit if we have optimized too many loops. We can adjust this as
  // necessary but just set it to 32 for now.
  if (gIEForallID >= 32) {
    return;
  }

  // Gather forall info. This gets us some information regarding the
  // loop's domain.
  if (!forall->optInfo.infoGathered) {
    gatherForallInfo(forall);
  }

  // Do not proceed if we can't determine the loop's domain statically.
  Symbol *loopDomain = canDetermineLoopDomainStatically(forall);
  if (loopDomain == NULL) {
    return;
  }

  // Iterate through all call expressions in the forall loop
  // and add potential candidates to an internal vector that is
  // stored within the forall.
  findCandidatesIE(forall);

  // If we did not find any potential candidates, then we're done
  if (forall->optInfo.ieCandidates.size() == 0) return;

  // If we're here, then we'll optimize the loop. Assign it a unique
  // ID
  forall->optInfo.ieID = gIEForallID++;

  // See whether the forall is in a function that isn't the module init.
  // If it is, see if we've seen this function before w.r.t. another forall.
  // In either case, set the forall->optInfo.functionID field to be associated
  // with this function.
  setForallFunctionIdIE(forall);

  // Generates the optimized loop(s), replacing the candidates we found
  // above with the MAYBE_IRREG_ACCESS primitive.
  generateOptimizedLoopsIE(forall);

} /* end of inspectorExecutor */

//##################################################################################
/*
    For a given forall loop, find all potential candidates for the inspector-executor
    optimization.

    A candidate is of the form A[expr(B[expr])], where "expr" must be a binary operation
    between immediates or variables that are yielded by loops that iterate over arrays/domains.
    These loops can be enclosed in the forall, or they can enclose the forall itself.

    For each candidate we find, we add it to the ieCandidates vector stored within
    forall. See analyzeCandidateIE() for more details.

    TODO: while we can find multiple candidates in the forall, we only perform the
    optimization on the first one we find.

    Arguments:
    forall -> The forall loop to analyze for candidates

    Return:
    None
*/
static void findCandidatesIE(ForallStmt* forall)
{
  std::vector<CallExpr *> callExprs;
  collectCallExprs(forall->loopBody(), callExprs);

  for_vector(CallExpr, call, callExprs) {
    // 1.) Ensure that we can get the call base for call. This
    //     means it is a B[expr]
    if (getCallBase(call)) {
      // If we have something like A[B[C[i]]], we will first find
      // call=C[i] and then find parentCall=B[C[i]]. That is ok, and
      // that is what we'll optimize. But the next candidate we'd see
      // would be call=B[C[i]] and parentCall=A[B[C[i]]]; that is not
      // good, as we don't want to try to optimize both candidates.
      // To avoid this, look at call's arguments and if any are things we
      // can get callbases for, then skip this candidate.
      if (doesCallHaveNestedCallBaseIE(call)) {
        continue;
      }

      // 2.) From call, look up at the parentExprs. As long as we see
      //     CallExprs that are valid binary operators, keep going. We
      //     stop if we have a CallExpr with a call base OR we have a
      //     CallExpr that isn't a valid binary operator (like =,+=,etc).
      //     Also stop/fail if we're inside of a primitive
      CallExpr *parentCall = NULL;
      CallExpr *curr = call;
      bool isValid = true;
      while (isValid) {
        if ((curr = toCallExpr(curr->parentExpr))) {
          if (curr->isPrimitive(PRIM_MAYBE_IRREG_ACCESS) || 
              curr->isPrimitive(PRIM_MAYBE_IRREG_AGGREGATE_WRITE) ||
              curr->isPrimitive(PRIM_MAYBE_PREFETCH_CANDIDATE)) {
            isValid = false;
          }
          else if(getCallBase(curr)) {
            parentCall = curr;
            break;
          }
          else if (!isCallExprBinaryOperator(curr)) {
            isValid = false;
          }
        }
        else {
          isValid = false;
        }
      }
      if (isValid == false) { continue; }
      INT_ASSERT(parentCall);
      // Ensure we're not nested in a primitive
      CallExpr *tmp = parentCall;
      while (tmp != NULL && tmp->parentExpr != NULL) {
        if (tmp->isPrimitive(PRIM_MAYBE_IRREG_ACCESS) ||
            tmp->isPrimitive(PRIM_MAYBE_IRREG_AGGREGATE_WRITE) ||
            tmp->isPrimitive(PRIM_MAYBE_PREFETCH_CANDIDATE)) {

          isValid = false;
          break;
        }
        else if (tmp->isNamed("prefetch")) {
          isValid = false;
          break;
        }
        tmp = toCallExpr(tmp->parentExpr);
      }
      if (isValid == false) { continue; }

      // 3.) If we're here, then we found a valid parentCall.
      //     So we can pass off call and parentCall to analyzeCandidateIE
      //     for a more in-depth analysis
      analyzeCandidateIE(call, parentCall, forall);
    } /* end of if getCallBase(call) */

  } /* end for_vector */

} /* end of findCandidatesIE */

//##################################################################################
/*
    Given a CallExpr call, look at each of its arguments. If they are CallExprs,
    see whether we can get its call base. If we can, return true. If we can't,
    call this function recursively and look at that call's arguments.

    The first call to this function is given call = B[expr] when we are looking
    for IE candidates. We want to ensure that "expr" does not contain any other
    potential array accesses. That is why we look for CallExprs that we can get
    the call base for.

    This avoids the problem of trying to optimize something like A[B[C[i]]].
    We will optimixe B[C[i]] but we don't want to try to optimize the
    outer-most access. So we'd pass in B[C[i]] here and find that we can get
    the call base for C[i] and return true. That will skip over the candidate.

    Arguments:
    call -> the CallExpr to analyze

    Return:
    true if call contains a nested CallExpr with a call base; false otherwise
*/
static bool doesCallHaveNestedCallBaseIE(CallExpr *call)
{
  bool retval = false;
  for (int i = 1; i <= call->argList.length; i++) {
    if (CallExpr *callArg = toCallExpr(call->get(i))) {
      if (getCallBase(callArg)) {
        return true;
      }
      else {
        retval |= doesCallHaveNestedCallBaseIE(callArg);
      }
    }
  }
  return retval;
} /* end of doesCallHaveNestedCallBaseIE */

//##################################################################################
/*
    This is called from findCandidatesIE once we have determined that we have
    something like A[B[i]]. We don't know whether they are arrays (we do that
    check during prefolding), but we can do some checks here to eliminate
    a candidate.

    This function mostly does some analysis regarding the loop iterators/
    domains. The forall must iterate over an array or domain. Later on,
    we ensure that that array/domain is distributed and supports the
    localSubdomain query.

    For any variables used in the access, like i,j,k in A[B[i+j]*k], they
    must come from loops iterating over domains/arrays. We do checks later
    in prefolding to see if they are truely arrays/domains. This is required
    so we know what to "track" to detect changes to the access pattern, and
    thus rerun the inspector.

    We also require that A and B are defined outside of the forall.

    If everything passes, we add the candidate to forall->optInfo.

    One thing we do here is to extract the symbol that the forall loop
    is iterating over. We use this in later checks. This is either
    iterSym (i.e., "foo" in forall i in foo) or dotDomIterSym
    (i.e., "foo" in forall i in foo.domain). We note whether we got the
    symbol from a "dot domain" expression, as that is useful info for
    later on.

    We also extract the Symbols that yield any of the indices. This could be
    "foo" from "for/forall i in foo" and "for/forall i in foo.domain".
    If "foo" is defined as a ref to something outside of the loop, we
    will extract that outside alias rather than foo. The special case
    is when "foo" is defined as "ref foo = rec.arr". We note this as
    a record-field case and handle it differently later on.


    Arguments:
    call ->  CallExpr that represents B[i]
    parentCall -> CallExpr that represents A[B[i]]
    forall -> forall loop that contains A[B[i]]

    Return:
    None; we modify forall->optInfo
*/
static void analyzeCandidateIE(CallExpr *call,
                               CallExpr *parentCall,
                               ForallStmt *forall)
{
  bool isCandidate = true;
  Symbol *callBase = getCallBase(call);
  Symbol *parentCallBase = getCallBase(parentCall);

  // If we've already looked at this candidate, don't do any printing. Other
  // optimizations can clone this forall loop, which can lead us to print out duplicate info.
  // We still need to do the analyzing, but we don't need to print twice.
  bool oldFReport = fReportIrregArrayAccesses;
  if (gCandidatesAnalyzedIE.count(parentCall->stringLoc()) != 0) {
    fReportIrregArrayAccesses = false;
  }
  else {
    gCandidatesAnalyzedIE.insert(parentCall->stringLoc());
  }

  if (fReportIrregArrayAccesses) {
    printf("+ [INSPECTOR-EXECUTOR] Considering candidate irregular access at %s (forall at %s)\n", parentCall->stringLoc(),
                                                                                forall->stringLoc());
    printf("\t- Parent: %s, Call: %s\n", parentCallBase->name, callBase->name);
  }

  // Ensure that the candidate is not nested in a call to prefetch(), which is part of the
  // prefetch optimization. Don't think this should happen since we do the IE optimization
  // before prefetching, but worth checking anyways.
  CallExpr *tmp = parentCall;
  while (tmp != NULL && tmp->parentExpr != NULL) {
    if (tmp->isNamed("prefetch")) {
      if (fReportIrregArrayAccesses) {
        printf("\t\t !!! irregular access cannot be an argument to prefetch()\n");
      }
      fReportIrregArrayAccesses = oldFReport;
      return;
    }
    tmp = toCallExpr(tmp->parentExpr);
  }

  // A[B[i]] cannot be on the LHS of an operation. We can check for this
  // be seeing if parentCall's parent is an assignment, and if parentCall is
  // the first argument to the assignment. We also check for something like
  // A[B[i]].foo(), which we will assume could write to A[B[i]]
  if (CallExpr *opCall = toCallExpr(parentCall->parentExpr)) {
    if (isAssignment(opCall)) {
      if (parentCall == toCallExpr(opCall->get(1))) {
        if (fReportIrregArrayAccesses) {
          printf("\t\t !!! irregular access cannot be on LHS on assignment for inspector-executor\n");
        }
        fReportIrregArrayAccesses = oldFReport;
        return;
      }
    }
    else if (opCall->isNamed(".")  == true) {
      // If here, then we have something like A[B[i]].foo or
      // A[B[i]].func(). If func() takes in an argument, we could tell that
      // and abort. But if it does not take in an argument, it looks the same
      // as A[B[i]].foo, where foo would be a field. That would be allowed but
      // since we can't really tell the difference at this point, we don't allow
      // any "." expressions here.
      if (fReportIrregArrayAccesses) {
        printf("\t\t !!! irregular access cannot be on LHS on assignment for inspector-executor\n");
      }
      fReportIrregArrayAccesses = oldFReport;
      return;
    }
  }

  // If we have something like "ref t = A[B[i]]", we do not allow that.
  // It can only be "const ref t = A[B[i]]". What we see at this point is
  // that parentCall's parent will be a DefExpr, so we if it is "ref var"
  // and does not have the "const" flag, then we abort.
  if (DefExpr *def = toDefExpr(parentCall->parentExpr)) {
    if (def->sym->hasFlag(FLAG_REF_VAR) && !def->sym->hasFlag(FLAG_CONST)) {
      if (fReportIrregArrayAccesses) {
        printf("\t\t !!! irregular access is on RHS (stored in %s) but it must be a const ref or var\n", def->name());
      }
      fReportIrregArrayAccesses = oldFReport;
      return;
    }
  }

  // A cannot be defined inside of the loop body.
  if (forall->loopBody()->contains(parentCallBase->defPoint)) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t !!! %s cannot be defined inside of the forall\n", parentCallBase->name);
    }
    fReportIrregArrayAccesses = oldFReport;
    return;
  }
  // Same as above but for B
  if (forall->loopBody()->contains(callBase->defPoint)) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t !!! %s cannot be defined inside of the forall\n", callBase->name);
    }
    fReportIrregArrayAccesses = oldFReport;
    return;
  }

  // A[B[i]] cannot be nested within two foralls, and the forall it is in
  // cannot be nested in a coforall, begin or cobegin. This is to prevent
  // the chance for multiple tasks to be executing the entire forall, which
  // would lead to data races when running the inspector. Note that this check
  // does not go across call sites if forall is in a function; we do such checks
  // during post-resolution when the call graph is fully available. We also do not
  // allow for A[B[i]] to be within an on-statement, as that could change the
  // source/destination of the remote accesses.
  if (checkForInvalidEnclosingConstructs(call, forall)) {
   if (fReportIrregArrayAccesses) {
      printf("\t\t !!! detected invalid enclosing construct (another forall, on, coforall, cobegin, or begin)\n");
    }
    fReportIrregArrayAccesses = oldFReport;
    return;
  }

  // Extract the forall's iterator symbol so we can use it later.
  // TODO: assumes 1 iterator for the forall.
  if (forall->optInfo.iterSym[0]) {
    // this could be an array or domain; we'll find out in prefolding.
    forall->optInfo.ieForallIteratorSym = forall->optInfo.iterSym[0];
  }
  else {
    // we have something like forall i in foo.domain. Still grab foo.
    forall->optInfo.ieForallIteratorSym = forall->optInfo.dotDomIterSym[0];
    INT_ASSERT(forall->optInfo.ieForallIteratorSym != NULL);
  }

  // We support any non-affine access of the form A[expr(B(expr))], as long
  // as the "exprs" only contain binary operations between immediates and
  // loop index variables "above" the access of interest. In prefolding, we will
  // determine whether these symbols are yielded from arrays/domains. So here, we
  // extract all loop index and iterator symbols that could be used in a valid way
  // in A[expr(B[expr])]. We will pass these on to the primitive we make later, but
  // only the loop iterator symbols that correspond to loop index symbols that were
  // actually used in the expression(s); we store only those in the loopIterSymsUsed
  // map, which is populated via isLoopDomainValidIE().
  //
  // We also log what type of iterators we have, as either NORMAL or DOT_DOMAIN.
  std::vector<Symbol *> loopIndexSyms;
  std::vector<std::pair<Symbol *, ieIndexIteratorType>> loopIteratorSyms;
  std::map<std::pair<Symbol *, ieIndexIteratorType>, bool> loopIterSymsUsed;
  bool retval = extractAllLoopSyms(call,
                                   loopIndexSyms,
                                   loopIteratorSyms);
  if (retval == false) {
    fReportIrregArrayAccesses = oldFReport;
    return;
  }

  // If A[B[i]] is inside of a for-loop that is nested in the forall, then we
  // want to do some checks regarding the for-loop's domain. Specifically,
  // it must yield "i" and it must iterate a domain or array that is defined
  // outside of the loop, or is a ref to something outside of the loop. We
  // do a few checks regarding the symbol and mark it accordingly so it can
  // be handled correctly later. Note that we do not look across function calls
  // for the for-loop. The fact that we found A[B[i]] in a forall suggest that
  // we must be looking for a for-loop in the current function scope.
  //
  // Otherwise, if A[B[i]] is directly inside of the forall, we do the
  // same checks for the forall's loop domain.
  ForLoop *f = findEnclosingForLoop(call);
  compute_call_sites(); // needed by doesExprContainExpr
  if (f != NULL && doesExprContainExpr(f, forall)) {
    // f is a for-loop that contains A[B[i]] and f is within
    // the forall.
    if (fReportIrregArrayAccesses) {
      printf("\t\t- Candidate access is in a for-loop (%s) that is nested in the forall\n", f->stringLoc());
    }
    if (!f->forLoopInfoGathered) {
      gatherForLoopInfo(f);
    }
    isCandidate = isLoopDomainValidIE(call,
                                      parentCall,
                                      loopIndexSyms,
                                      loopIteratorSyms,
                                      forall->loopBody(),
                                      f->multiDIndices,
                                      f->iterSym,
                                      f->dotDomIterSym,
                                      forall->optInfo,
                                      loopIterSymsUsed);
  }
  else {
    isCandidate = isLoopDomainValidIE(call,
                                      parentCall,
                                      loopIndexSyms,
                                      loopIteratorSyms,
                                      forall->loopBody(),
                                      forall->optInfo.multiDIndices,
                                      forall->optInfo.iterSym,
                                      forall->optInfo.dotDomIterSym,
                                      forall->optInfo,
                                      loopIterSymsUsed);
  }

  if (isCandidate) {
    std::pair<CallExpr *, CallExpr *> candidate;
    candidate.first = parentCall;
    candidate.second = call;
    forall->optInfo.ieCandidates.push_back(candidate);
    forall->optInfo.ieLoopIteratorSyms = loopIterSymsUsed;
    if (fReportIrregArrayAccesses) {
      printf("\t\t- Candidate is valid thus far\n");
    }
  }
  else {
    if (fReportIrregArrayAccesses) {
      printf("\t\t- !!! invalid loop domain or access detected\n");
    }
  }

  fReportIrregArrayAccesses = oldFReport;
} /* end of analyzeCandidateIE */

//##################################################################################
/*
    For a given forall, set its optInfo->functionID field. We only call this if the
    forall was deemed to have at least 1 potential candidate.

    If the forall is in a function that isn't the module init, then see if we've
    processed that function before. If we haven't, assign it a new ID. Otherwise,
    look-up the ID. If the function is the module init, give the forall an ID of
    NOT_IN_FUNCTION to indicate that it is not relevant for our purposes.

    Arguments:
    forall -> the forall to analyze

    Return:
    None; we modify forall->optInfo
*/
static void setForallFunctionIdIE(ForallStmt *forall)
{
  int ID = NOT_IN_FUNCTION;

  // Get the forall's module init function
  FnSymbol *modInitFn = forall->getModule()->initFn;

  // Look at the forall's parentSymbol. If it is modInitFn, give
  // an ID of -1. Otherwise, look it up in the gFnsWithCandidatesIE map.
  FnSymbol *forallFn = toFnSymbol(forall->parentSymbol);
  INT_ASSERT(forallFn != NULL);
  if (forallFn != modInitFn) {
    if (gFnsWithCandidatesIE.count(forallFn) == 0) {
      gFnsWithCandidatesIE[forallFn] = gFnWithCandidateID;
      gFnWithCandidateID++;
    }
    ID = gFnsWithCandidatesIE[forallFn];
  }
  forall->optInfo.functionID = ID;
} /* end of setForallFunctionIdIE */

//##################################################################################
/*
    This is called after findCandidatesIE(). This function generates the following
    if-then-else structure:

        if isCallPathValid {
            if staticCheckCall(forallID) == true {
                optimized forall loop
            }
            else {
                original forall loop
            }
        }
        else {
            original forall loop
        }
    
    the "staticCheckCall" always returns true. Its purpose is a placeholder for
    later on in prefolding and post resolution, where we know whether the optimization
    is valid. If we find it is invalid, we replace staticCheckCall with false, so
    the if turns into "if false == true", resulting in the else branch always being
    taken. Note that this staticCheckCall is parameterized by the forall ID. This
    is so we can find the corresponding call for a given forall that is invalid.

    There are some additional checks that we insert here that will be resolved
    by the time we get to prefolding. Specifically, we check that A supports
    the localSubdomain() query and that the array/domain that the forall is
    iterating over is distributed.

    This function will also replace each candidate previously found with the
    MAYBE_IRREG_ACCESS primitive.

    The outer if-then-else is used to dynamically handle invalid call-paths to
    the function that contains the forall. We only do this if forall->optInfo.functionID
    is not NOT_IN_FUNCTION; a value of NOT_IN_FUNCTION indicates it is not in
    a function, so we don't need to check for call paths.

    At the end of this function, we call generateInspectorExecutorLoops().
    That will turn "optimized forall loop" into the inspector loop and
    executor loop.

    Arguments:
    forall -> The forall loop to optimize

    Return:
    None (forall is modified)
*/
static void generateOptimizedLoopsIE(ForallStmt* forall)
{
  SET_LINENO(forall);
  std::vector< std::pair<CallExpr *, CallExpr *> > &ieCandidates = forall->optInfo.ieCandidates;

  // 1.) Clone the forall loop. Now noOpt is the original and forall will be our
  //     optimized version (we do more cloning later). At this point, noOpt is
  //     NOT in the AST and forall is.
  ForallStmt *noOpt = NULL;
  noOpt = cloneLoop(forall);
  noOpt->optInfo.cloneTypeIE = ORIGINAL;
  forall->optInfo.cloneTypeIE = PENDING_OPTIMIZATION;

  // 2.) Generate the call/code for "staticCheckCall(id) == true"
  CallExpr *staticCheckCall = new CallExpr("staticCheckCallIE",
                                           new_IntSymbol(forall->optInfo.ieID));
  Expr *staticCond = new CallExpr("==", staticCheckCall, gTrue);

  // 3.) Later on in prefolding, we need to keep track of whether we processed
  //     a given loop or not. ALA and other optimizations will clone the forall
  //     we are processing now. In other words, it'll make clones of our clones.
  //     Some things we do in prefolding do not need to happen to every clone we
  //     come across. So we use a map to keep track of when we processed one. We
  //     use staticCheck as the unique ID to associate with our loop(s).
  gInspectorLoopProcessed[forall->optInfo.ieID] = false;
  gExecutorLoopProcessed[forall->optInfo.ieID] = false;

  // Pull out the candidate.
  // TODO: assuming 1 candidate per forall right now
  std::pair<CallExpr *, CallExpr *> candidate = ieCandidates[0];
  CallExpr *parentCall = candidate.first;
  CallExpr *call = candidate.second;

  // 4.) Insert some param/compile-time calls before the forall. These are
  //     things that will resolve to true or false and help us with our
  //     static analysis later on. First, we want to be sure that A supports
  //     the localSubdomain() query, since that is needed in the optimization.
  //     Second, we want to ensure that the array/domain of the forall is distributed.
  //     This is important as it ensures we can reason about the locality of the
  //     forall. What we pass into isDistributed() needs to be the domain of whatever
  //     the forall iterates over or the (assumed) array symbol. We already checked
  //     that the forall is iterating over something like A.domain or just A; we
  //     quit if we didn't find such a pattern.
  VarSymbol *hasSingleLocalSubdomain = new VarSymbol("hasSingleLocalSubdomain");
  hasSingleLocalSubdomain->addFlag(FLAG_PARAM);
  CallExpr *localSubCall = new CallExpr("chpl__hasSingleLocalSubdomainCheck", getCallBase(parentCall));
  forall->insertBefore(new DefExpr(hasSingleLocalSubdomain,
                           localSubCall));

  INT_ASSERT(forall->optInfo.ieForallIteratorSym != NULL);
  VarSymbol *isForallDistributed = new VarSymbol("isDistributed");
  isForallDistributed->addFlag(FLAG_PARAM);
  CallExpr *distCall = new CallExpr("chpl__isDistributed", forall->optInfo.ieForallIteratorSym);
  forall->insertBefore(new DefExpr(isForallDistributed,
                           distCall));

  // 5.) Replace the candidate with the MAYBE_IRREG_ACCESS primitive.
  //     Set access type to EXECUTOR_ACCESS; when we clone to create the
  //     inspector loop, we'll go through and change the access type.
  createPrimitiveIE(EXECUTOR_ACCESS,
                    forall->optInfo.ieID,
                    hasSingleLocalSubdomain,
                    isForallDistributed,
                    forall->optInfo.ieForallIteratorSym,
                    forall->optInfo.ieIndexIterator,
                    forall->optInfo.ieLoopIteratorSyms,
                    (Expr*)parentCall,
                    (Expr*)call);


  // 6.) Construct the if-then-else structure that will do the optimization
  //     iff the call path is valid. Otherwise, it does the original loop.
  //     We only need to do this if the forall is in a function.
  if (forall->optInfo.functionID != NOT_IN_FUNCTION) {
    // Create call to isCallPathInvalid == true.
    CallExpr *isCallPathValid = new CallExpr("isCallPathValid",
                                             new_IntSymbol(forall->optInfo.functionID));
    Expr *isCallPathCond = new CallExpr("==",
                                        isCallPathValid,
                                        gTrue);
    // Create the if-then-else structure
    BlockStmt *thenBlock = new BlockStmt();
    BlockStmt *elseBlock = new BlockStmt();
    CondStmt *cond = new CondStmt(isCallPathCond, thenBlock, elseBlock);
    forall->insertAfter(cond);
    thenBlock->insertAtTail(forall->remove());
    elseBlock->insertAtTail(noOpt);
  }
  // Now create the if-then-else for staticCheckCall == true conditional.
  // If functionID wasn't NOT_IN_FUNCTION, this if-then-else is placed within the
  // then-block we created above.
  BlockStmt *thenBlock = new BlockStmt();
  BlockStmt *elseBlock = new BlockStmt();
  CondStmt *cond = new CondStmt(staticCond, thenBlock, elseBlock);
  forall->insertAfter(cond);
  thenBlock->insertAtTail(forall->remove());
  // If the forall isn't in a function, we haven't inserted noOpt into
  // the AST yet, so we can do that now. Otherwise, we already put noOpt
  // into the else-branch of the outer if-then-else. So make another clone
  // and insert that.
  if (forall->optInfo.functionID == NOT_IN_FUNCTION) {
    elseBlock->insertAtTail(noOpt);
  }
  else {
    ForallStmt *noOpt2 = cloneLoop(noOpt);
    noOpt2->optInfo.cloneTypeIE = CLONED;
    elseBlock->insertAtTail(noOpt2);
  }

  // 7.) Finally, create the inspector and executor loops from
  //     forall.
  generateInspectorExecutorLoops(forall);

} /* end of generateOptimizedLoopsIE */


//##################################################################################
/*
    Creates the MAYBE_IRREG_ACCESS primitive for the IE optimization. The point
    of this primitive is to "flag" this access so it is caught during prefolding.
    At that point, A and B will have been resolved so we'll be able to reason
    further about the optimization (i.e., we'll know whether A and B are arrays).

    The primitive has the following structure for A[B[i]]:

        (call "maybe irreg access",
         accessType,
         forall ID,
         hasSingleLocalSubdomain,
         isForallDistributed,
         forallIterSym,
         indexIterator,
         A,
         B,
         B[i],
         numLoopIteratorSyms,
         ieLoopIteratorSym_1,
         ieLoopIteratorSym_2,
         ...
         ieLoopIteratorSym_N,
         ieLoopIteratorType_1,
         ieLoopIteratorType_2,
         ...
         ieLoopIteratorType_N
        )

    (NOTE: we add additional arguments to the primitive later on)

    where accessType is used to distinguish between an access that is part of the
    inspector loop or executor loop.

    The hasSingleLocalSubdomain argument is something that will be resolved by the time
    we process this primitive in prefolding; it will be true is A supports the locaSubdomain
    query and false otherwise. Likewise, isForallDistributed will be resolved to true or false
    when we get to prefolding. It checks whether the domain being iterated over by the forall
    is distributed. We also pass in the Symbol used in the forall iterator, since we need it
    during post-resolution and many things in forall->optInfo do not carry over. Similarly,
    we pass in the symbol that yields "i" in A[B[i]] so we can do checks on it during
    prefolding.

    Finally, we add all relevant loop iterator symbols and types at the end. These are any iterator
    symbols related to the irregular access (i.e., the symbol that yields i, j and k from
    A[B[i+j]*k]. We need to ensure that each of these symbols are arrays or domains. Their types
    are ieIndexIteratorType, which dentoes whether they are "normal", "dot domain", etc.

    Once the primitive is created, we replace parentCall (A[B[i]]) with the primitive.

    Arguments:
    accessType  -> either EXECUTOR_ACCESS or INSPECTOR_ACCESS
    ID -> the unique forall ID for the forall that contains the access
    hasSingleLocalSubdomain -> resolved later to be true if A supports localSubdomain(), false otherwise
    isForallDistributed -> resolved later to be true if the forall iterates over a distributed array/domain
    forallIterSym -> the Symbol used in the forall iterator
    indexIterator -> the Symbol that yields i in A[B[i]]
    loopIteratorSyms -> map of all iterator symbols that are relevant to the irregular access
    parentCall  -> expression for A[B[i]]
    call        -> expression for B[i]

    Return:
    None (parentCall is modified)
*/
static void createPrimitiveIE(int accessType,
                              int ID,
                              VarSymbol *hasSingleLocalSubdomain,
                              VarSymbol *isForallDistributed,
                              Symbol *forallIterSym,
                              Symbol *indexIterator,
                              std::map<std::pair<Symbol *, ieIndexIteratorType>, bool> loopIteratorSyms,
                              Expr* parentCall,
                              Expr* call)
{
  Symbol *A = getCallBase((CallExpr*)parentCall);
  Symbol *B = getCallBase((CallExpr*)call);
  INT_ASSERT(A);
  INT_ASSERT(B);

  CallExpr *repl = new CallExpr(PRIM_MAYBE_IRREG_ACCESS, new_IntSymbol(accessType));
  repl->insertAtTail(new_IntSymbol(ID));
  repl->insertAtTail(hasSingleLocalSubdomain);
  repl->insertAtTail(isForallDistributed);
  repl->insertAtTail(forallIterSym);
  repl->insertAtTail(indexIterator);
  repl->insertAtTail(A);
  repl->insertAtTail(B);
  // In the simple case of A[B[i]], we want to add B[i] so we can use it
  // in our calls to inspect/execute access. However, we also allow for 
  // something like A[B[i] + j]. In that case, the index we want to pass
  // into inspect/execute access is B[i]+j. So instead of just adding "call"
  // to the primitive, we add the first argument to parentCall, which will be
  // all the "stuff" used to index into A.
  CallExpr *tempParent = toCallExpr(parentCall);
  repl->insertAtTail(tempParent->get(1)->copy());
  repl->insertAtTail(new_IntSymbol(loopIteratorSyms.size()));
  for (auto &elem : loopIteratorSyms) {
    Symbol *sym = elem.first.first;
    repl->insertAtTail(sym);
  }
  for (auto &elem : loopIteratorSyms) {
    ieIndexIteratorType iterType = elem.first.second;
    repl->insertAtTail(new_IntSymbol(iterType));
  }
  parentCall->replace(repl);

} /* end of createPrimitive */

//##################################################################################
/*
    This is called from generateOptimizedLoopsIE(). It takes the
    forall that is assumed to be the optimized version and further
    clones it into an inspector loop and an executor loop. For the
    inspector loop, we go through and update each of the candidates
    (primitives) to have access type set to INSPECTOR_ACCESS. The
    inspector loop is a stripped down version of the original loop,
    in that the only statements it contains are the primitive and
    any DefExprs.

    We then generate the following structure:

        if doInspector(..) {
            inspector preamble
            inspector loop
            inspectorOff(..)
            sort indices
        }
        executor loop

    We also create the forall's InspectorFlag object, which is used in
    calls to doInspector, inspectorOff and later during post-resolution,
    inspectorOn(). This object is created in the global scope so we can
    call it anywhere.

    Arguments:
    forall -> the forall loop to clone/optimize

    Return:
    None
*/
static void generateInspectorExecutorLoops(ForallStmt* forall)
{
  // Pull out the candidate we're dealing with. As mentioned
  // before, we're only dealing with 1 right now.
  std::pair<CallExpr *, CallExpr *> candidate = forall->optInfo.ieCandidates[0];

  // We'll let forall be the executor loop (in the AST).
  // We'll construct the if-then structure to insert the
  // inspector loop in a few steps.
  ForallStmt *inspectorLoop = NULL;
  inspectorLoop = cloneLoop(forall);
  inspectorLoop->optInfo.cloneTypeIE = INSPECTOR;
  forall->optInfo.cloneTypeIE = EXECUTOR;

  // Create the global InspectorFlag object
  VarSymbol *ieFlag = NULL;
  forv_Vec(ModuleSymbol, mod, gModuleSymbols) {
    if (mod->hasFlag(FLAG_SDR_MOD_MARKER)) {
      ieFlag = new VarSymbol("ieFlag");
      FnSymbol *modInitFn = mod->initFn;
      modInitFn->insertAtHead(new DefExpr(ieFlag,
                              new CallExpr("createInspectorFlag")));
      forall->optInfo.inspectorFlag = ieFlag;
      inspectorLoop->optInfo.inspectorFlag = ieFlag;
      break;
    }
  }
  INT_ASSERT(ieFlag);

  // We want to create a hash of all the symbols that are related to
  // the optimization. This will be unique per call-site if the forall
  // is in a function and if any of the symbols are passed in as arguments.
  // We do not hash the indexIterSym if its type is NORMAL_REC_FIELD or DOT_DOMAIN_REC_FIELD,
  // as we may not have a "valid" Symbol to pass into computeHash().
  Symbol *A = getCallBase(candidate.first);
  Symbol *B = getCallBase(candidate.second);
  Symbol *forallIterSym = forall->optInfo.ieForallIteratorSym;
  Symbol *indexIterSym = forall->optInfo.ieIndexIterator;
  ieIndexIteratorType indexIteratorType = forall->optInfo.indexIteratorType;
  CallExpr *computeHash = NULL;
  if (indexIteratorType == NORMAL_REC_FIELD || indexIteratorType == DOT_DOMAIN_REC_FIELD) {
    computeHash = new CallExpr("computeHash", A, B, forallIterSym);
  }
  else {
    computeHash = new CallExpr("computeHash", A, B, forallIterSym, indexIterSym);
  }
  VarSymbol *ieHash = new VarSymbol("ieHash");
  ieHash->addFlag(FLAG_IE_IRREG_PRIMITIVE_ARG);
  forall->insertBefore(new DefExpr(ieHash, computeHash));
  forall->optInfo.ieHash = ieHash;

  // We also want to insert the forall ID that we'll pass into various calls to get the
  // corresponding communication schedule for this loop.
  VarSymbol *ieID = new VarSymbol("ieID");
  ieID->addFlag(FLAG_IE_IRREG_PRIMITIVE_ARG);
  forall->insertBefore(new DefExpr(ieID, new_IntSymbol(forall->optInfo.ieID)));
  forall->optInfo.ieIDVar = ieID;

  // Create the if doInspector conditional. This is simply:
  //      if doInspector(ieFlag, ieHash) == true
  CallExpr *doInspectorCall = new CallExpr("doInspector", ieFlag, ieHash);
  Expr *inspectorCheck = new CallExpr("==", doInspectorCall, gTrue);

  // Construct the if-then structure
  BlockStmt *thenBlock = new BlockStmt();
  CondStmt *cond = new CondStmt(inspectorCheck, thenBlock);
  forall->insertBefore(cond);
  thenBlock->insertAtTail(inspectorLoop);

  // We want to add a call right after the inspector loop to turn off
  // the inspector flag: inspectorOff(ieFlag, ieHash)
  inspectorLoop->insertAfter(new CallExpr("inspectorOff", ieFlag, ieHash));

  // Call sortReplIndices for A
  CallExpr *sortIndices = new CallExpr("sortReplIndices", A, ieID, ieHash);
  inspectorLoop->insertAfter(sortIndices);

  // Call the inspector preamble
  CallExpr *inspectorPreamble = new CallExpr("inspectorPreamble", A, ieID, ieHash);
  inspectorLoop->insertBefore(inspectorPreamble);

  // Shadow variables for executor loop:
  // ref arrDom = x.replArray.arrDom, ref replArr = x.replArray.replArr
  CallExpr *arrDomCallExecutor = new CallExpr("getArrDom", A, ieID, ieHash);
  CallExpr *replArrCallExecutor = new CallExpr("getReplArr", A, ieID, ieHash);
  ShadowVarSymbol *arrDomExecutor = ShadowVarSymbol::buildForPrefix(SVP_REF,
                                                                    new UnresolvedSymExpr("arrDom"),
                                                                    NULL,
                                                                    arrDomCallExecutor);
  ShadowVarSymbol *replArrExecutor = ShadowVarSymbol::buildForPrefix(SVP_REF,
                                                                     new UnresolvedSymExpr("replArr"),
                                                                     NULL,
                                                                     replArrCallExecutor);
  forall->shadowVariables().insertAtTail(arrDomExecutor->defPoint);
  forall->shadowVariables().insertAtTail(replArrExecutor->defPoint);

  // Shadow variables for inspector loop:
  // ref replD = x.replArray.replD, ref arrDom = x.replArray.arrDom
  CallExpr *replDCallInspector = new CallExpr("getReplD", A, ieID, ieHash);
  CallExpr *arrDomCallInspector = new CallExpr("getArrDom", A, ieID, ieHash);
  ShadowVarSymbol *replDInspector = ShadowVarSymbol::buildForPrefix(SVP_REF,
                                                                    new UnresolvedSymExpr("replD"),
                                                                    NULL,
                                                                    replDCallInspector);
  ShadowVarSymbol *arrDomInspector = ShadowVarSymbol::buildForPrefix(SVP_REF,
                                                                     new UnresolvedSymExpr("arrDom"),
                                                                     NULL,
                                                                     arrDomCallInspector);
  inspectorLoop->shadowVariables().insertAtTail(replDInspector->defPoint);
  inspectorLoop->shadowVariables().insertAtTail(arrDomInspector->defPoint);

  // We need to change the access type of the primitives in the
  // inspector loop to be INSPECTOR_ACCESS. We also add the replD
  // and arrDom vars that we'll need to call the inspectAccess function,
  // as well as the ieHash and ieIDVar.
  std::vector<CallExpr *> callExprs;
  std::vector<CallExpr *> primitives;
  collectCallExprs(inspectorLoop->loopBody(), callExprs);
  for_vector(CallExpr, call, callExprs) {
    if (call->isPrimitive(PRIM_MAYBE_IRREG_ACCESS)) {
      // Update the first argument
      call->get(1)->remove();
      call->insertAtHead(new_IntSymbol(INSPECTOR_ACCESS));
      // Add other arguments
      call->insertAtHead(ieHash);
      call->insertAtHead(ieID);
      call->insertAtHead(arrDomInspector);
      call->insertAtHead(replDInspector);
      primitives.push_back(call);
    }
  }
  // Do the same for the executor to add the shadow vars.
  // Also, during post resolution we want to do some analysis on the variables
  // used within the A[B[i]] access. So extract those from the parentCall expr
  // within the primitive.
  std::vector<CallExpr *> callExprs2;
  collectCallExprs(forall->loopBody(), callExprs2);
  for_vector(CallExpr, call, callExprs2) {
    if (call->isPrimitive(PRIM_MAYBE_IRREG_ACCESS)) {
      // extract symbols in parentCall
      std::vector<SymExpr *> symexprs;
      CallExpr *thisParentCall = toCallExpr(call->get(9));
      collectSymExprs(thisParentCall, symexprs);
      for (auto &symexpr : symexprs) {
        if (Symbol *sym = symexpr->symbol()) {
          // Ignore literals
          if (sym != A && sym != B && !sym->isImmediate()) {
            forall->optInfo.ieIndexSymbols.insert(sym);
          }
        }
      }
      // Add the shadow vars and hash/ID to the head
      call->insertAtHead(ieHash);
      call->insertAtHead(ieID);
      call->insertAtHead(arrDomExecutor);
      call->insertAtHead(replArrExecutor);
      // Add the loop index syms to the tail
      int numSyms = forall->optInfo.ieIndexSymbols.size();
      call->insertAtTail(new_IntSymbol(numSyms));
      for (auto &sym : forall->optInfo.ieIndexSymbols) {
        call->insertAtTail(sym);
      }
    }
  }

  // Generate the stripped down inspector loop that only contains
  // the MAYBE_IRREG_ACCESS primitive
  createStrippedInspectorLoop(inspectorLoop,
                              primitives);

  // Replace the inspector's forall iterator with our own custom
  // inspector iterator. It only creates one task per locale to
  // process a given locale's chunk of the array/domain that the
  // forall iterates over.
  // TODO: for now, assume we can always do this. But later we'll
  // want to add a "if forallIterSym has localSubdomain" check around this. If
  // we can't do it, then use the original inspectorLoop.
  replaceIteratorWithInspectorIterator(inspectorLoop);

} /*end of generateInspectorExecutorLoops*/


//##################################################################################
/*
    This function creates the stripped down inspector loop. By stripped down, we
    mean the loop contains the bare minimum to properly inspect the access
    A[B[i]]. For more details of what we keep and don't keep in the loop,
    see stripInspectorLoop().

    Arguments:
    inspectorLoop -> the forall loop to modify
    primitives -> vector of MAYBE_IRREG_ACCESS primitives in the loop

    Return:
    None; inspectorLoop is modified in-place.
*/
static void createStrippedInspectorLoop(ForallStmt *inspectorLoop,
                                        std::vector<CallExpr *>primitives)
{

  std::vector<Expr *> exprsToRemove;
  std::map<Symbol *, bool> symbolsToTrack;
  // TODO: assumes one candidate per loop
  CallExpr *prim = primitives[0];
  stripInspectorLoop(inspectorLoop->loopBody(),
                     prim,
                     exprsToRemove,
                     symbolsToTrack);

  // Now iterate through the Exprs in exprsToRemove and remove them.
  for(auto &expr : exprsToRemove) {
    expr->remove();
  }

} /* end of createStrippedInspectorLoop */


//##################################################################################
/*
    Given a BlockStmt block, iterate through its statements and add any that should
    be removed to the vector exprsToRemove. We pass in the MAYBE_IRREG_ACCESS
    primitive as we do certain things when we detect it.

    This is initially called with the inspector loop's body. However, it is a recursive
    function that we will call with other BlockStmts as we encounter them. Below is a
    brief outline of the criteria we use to decide whether we keep or remove a statement,
    where we refer to the statement as "node"

    1.) If node is a DefExpr, we keep node. However, if prim is part of this DefExpr,
        such as "ref t = A[B[i]]", then replace node with the primitive.
    2.) If node is a PRIM_MOVE where the RHS is a call to _getIterator or
        iteratorIndex, then we keep node. These relate to for-loops contained within
        the block. But if the RHS is a call that accesses a Symbol we are tracking,
        we keep node. For now, this specifically relates to the Symbol that was
        associated with _check_tuple_var_decl.
    3.) If node is a call to _freeIterator, we keep node (another piece of a for-loop).
    4.) If node is a call to _check_tuple_var_decl, we keep node. Also, we log the
        Symbol related to it (the 1st arg), as it will be used later to get something
        like (i,j) from forall (i,j) in ...
    5.) If node is the primitive, we keep node. This is not likely to happen, as A[B[i]]
        would be part of some other call, like a move, +=, etc. Nevertheless, we check
        for it.
    6.) If node is a CallExpr that contains the primitive as an argument, we replace
        node with the primitive.
    7.) If node is a CondStmt that contains the primitive, we replace node with the
        primitive.
    8.) If node is a DeferStmt, then we call this function on its body. If we ended
        up keeping anything within its body, we keep node.
    9.) If node is a ForLoop, we call this function on its body. If we ended up
        keeping anything within the body, we keep node.
    10.) If node is a BlockStmt, we call this function on it. If we ended up keeping
        anything within the block, we keep node. Note that a ForLoop will also be
        considered a BlockStmt via toBlockStmt(), so we only process this step if
        node was NOT a ForLoop.

    Arguments:
    block -> the current block to analyze
    prim -> our primitive MAYBE_IRREG_ACCESS
    exprsToRemove -> vector of Exprs we will remove
    symbolsToTrack -> map of Symbols we explicitly look for

    Return:
    true if we kept a node within block, false otherwise
*/
static bool stripInspectorLoop(BlockStmt *block,
                               CallExpr *prim,
                               std::vector<Expr *> &exprsToRemove,
                               std::map<Symbol *, bool> &symbolsToTrack)
{
  bool keptNode = false;
  for_alist(node, block->body) {
    bool remove = true;
    // Keep any defExprs. Special case if if the prim is contained in the defExpr.
    // This happens when we have something like "ref t = A[B[i]]". In that case,
    // replace the defExpr with prim.
    if (DefExpr* def = toDefExpr(node)) {
      remove = false;
      keptNode = true;
      if (doesExprContainExpr(prim, def)) {
        def->replace(prim->remove());
      }
      continue;
    }

    // Keep any calls to _freeIterator, _getIterator, iteratorIndex, _check_tuple_var_decl
    if (CallExpr *call = toCallExpr(node)) {
      if (call->isPrimitive(PRIM_MOVE)) {
        // this could be a call to _getIterator or iteratorIndex.
        // it could also be a use of a Symbol we tracked from _check_tuple_var_decl
        if (CallExpr *RHS = toCallExpr(call->get(2))) {
          if (RHS->isNamed("_getIterator") || RHS->isNamed("iteratorIndex")) {
            remove = false;
            keptNode = true;
            continue;
          }
          else if (Symbol *sym = (toSymExpr(RHS->baseExpr))->symbol()) {
            if (symbolsToTrack.count(sym) > 0) {
              remove = false;
              keptNode = true;
              continue;
            }
          }
        }
      }
      else if (call->isNamed("_freeIterator")) {
        remove = false;
        keptNode = true;
        continue;
      }
      else if (call->isNamed("_check_tuple_var_decl")) {
        remove = false;
        keptNode = true;
        Symbol *sym = (toSymExpr(call->get(1)))->symbol();
        INT_ASSERT(sym != NULL);
        symbolsToTrack[sym] = true;
        continue;
      }
    }

    // If node is PRIM_MAYBE_IRREG_ACCESS or is a CallExpr that
    // contains PRIM_MAYBE_IRREG_ACCESS as an argument, replace
    // node with the primitive
    if (CallExpr *call = toCallExpr(node)) {
      // I don't think this case can happen, since any A[B[i]] would be part
      // of some other CallExpr, like a move, +=, etc. But check for it anyways
      if (call->isPrimitive(PRIM_MAYBE_IRREG_ACCESS)) {
        remove = false;
        keptNode = true;
        continue;
      }
      else {
        // The more sensible case where the primitive is part of call as an argument.
        // But the prim could be the argument to an argument to call, etc. So let's
        // simply check that call "contains" prim.
        if (doesExprContainExpr(prim, call)) {
          call->replace(prim->remove());
          remove = false;
          keptNode = true;
          continue;
        }
      }
    }

    // if node is a Cond stmt, see if prim is contained in the
    // then or else block. If it is, just replace node with prim.
    // We don't want to reason about when the conditional will be true,
    // since we are just logging A[B[i]] accesses. So if we log some that
    // would not happen due to the conditional, it doesn't break anything.
    if (CondStmt *c = toCondStmt(node)) {
      if (doesExprContainExpr(prim, c)) {
        c->replace(prim->remove());
        remove = false;
        keptNode = true;
        continue;
      }
    }

    // if node is a Defer stmt, get its body and look at it
    if (DeferStmt *d = toDeferStmt(node)) {
      BlockStmt *b = d->body();
      bool retval = stripInspectorLoop(b, prim, exprsToRemove, symbolsToTrack);
      // retval indicates whether we kept something during the recursive
      // call. If it is true, then we DO NOT remove node
      if (retval == true) {
        remove = false;
        keptNode = true;
        continue;
      }
    }

    // If node is a ForLoop and prim is contained in the loop,
    // we get everything before its body.
    ForLoop *f = toForLoop(node);
    if (f != NULL) {
      if (doesExprContainExpr(prim, f)) {
        BlockStmt *b = NULL;
        for_alist(fnode, f->body) {
          if (isBlockStmt(fnode)) {
            b = toBlockStmt(fnode);
            break;
          }
        }
        INT_ASSERT(b != NULL);
        bool retval = stripInspectorLoop(b, prim, exprsToRemove, symbolsToTrack);
        if (retval == true) {
          remove = false;
          keptNode = true;
          continue;
        }
      }
    }

    // Apparently toBlockStmt() on a node that is a ForLoop will
    // work here. Let's ensure that what we have is NOT a ForLoop
    if (BlockStmt *b = toBlockStmt(node)) {
      if (f == NULL) {
        bool retval = stripInspectorLoop(b, prim, exprsToRemove, symbolsToTrack);
         if (retval == true) {
          remove = false;
          keptNode = true;
          continue;
        }
      }
    }

    if (remove == true) {
      exprsToRemove.push_back(node);
    }
  } /* end of for_alist */

  return keptNode;

} /* end of stripInspectorLoop */

//##################################################################################
/*
    Given the inspectorLoop, transform it into a coforall-like structure. Specifically,
    it will be of the form:

        coforall loc in Locales do on loc {
            const ref indices = A.localSubdomain();
            for i in indices {
                ...
            }
        }

    The point of doing this is so we can turn off parallel-safety for the Chapel
    associative domains used in our optimization. With the above loop structure,
    a given locale will process its portion of the forall in serial.

    The way we do this is by simply replacing/adding our own custom parallel
    iterator to the inspector loop: inspectorIter(). Behind the scenes, the
    iterator performs the coforall above and yields the correct element back
    to the loop.

    Arguments:
    inspectorLoop -> the forall loop to modify

    Return:
    None; inspectorLoop is modified in-place.
*/

static void replaceIteratorWithInspectorIterator(ForallStmt *inspectorLoop)
{

  // origIterExpr will be the "B.domain" in "forall i in B.domain".
  // We want to stick that into our inspectorIter() call
  // TODO: assuming forall->numIteratedExprs() == 1. Should add checks
  //       later
  Expr *origIterExpr = inspectorLoop->firstIteratedExpr();
  CallExpr *inspectorIter = new CallExpr("inspectorIter");
  origIterExpr->insertBefore(inspectorIter);
  inspectorIter->insertAtTail(origIterExpr->remove());

} /* end of replaceIteratorWithInspectorIterator */

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                      Pre-folding Related Functions                        //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
/*
    The following functions perform further analysis/code-transformation for the
    inspector-executor optimization during pre-folding.

    The main task is to check whether the optimization can be, and should be,
    applied. We know much more about A and B (from A[B[i]]) at this point, so
    we can perform this analysis. If all the checks pass, we replace A[B[i]]
    with special calls to inspectAccess() or executeAccess(), depending on
    which forall loop we are dealing with.
*/

//##################################################################################
/*
    This gets called during prefolding when we come across PRIM_MAYBE_IRREG_ACCESS.
    It is declared in forallOptimizations.h because it is called from preFold.cpp.

    The purpose here is to determine that we have something like A[B[i]].
    As of 4/14/2022, PRIM_MAYBE_IRREG_ACCESS looks like this for A[B[i]]:

        (call "maybe irreg access",
         1: replArrExecutorShadow or replDInspectorShadow
         2: arrDomExecutorShadow or arrDomInspectorShadow
         3: ieIDVar,
         4: ieHash,
         5: accessType,
         6: forall ID (not the var but just the int),
         7: hasSingleLocalSubdomain,
         8: isForallDistributed,
         9: forallIterSym,
         10: indexIterator,
         11: A,
         12: B,
         13: B[i],
         14:numLoopIteratorSyms,
         15:loopIteratorSym_1,
         16:loopIteratorSym_2,
         17: loopIterType_1,
         18: loopIterType_2,
         19:numLoopIndexSyms,
         20:loopIndexSym_1,
         21:loopIndexSym_2)

    (we can have any number of loop iteraor symbols/types, but only 2 are shown above for
     example).

    The following steps are performed:

    1.) Check whether the optimization is valid/applicable. This involves things
        like checking whether A and B are both arrays, that the forall is in an
        enclosing for-loop, etc. The inpsector-loop only needs to do this.

    2.) If step (1) tells us the optimization is invalid, we need to go back
        and set staticCheckCall() to false. This effectively removes the optimization.
        We also then need to change the PRIM_MAYBE_IRREG_ACCESS back to A[B[i]]. We
        have the symbol A in the primitive, and we have the index used to access A
        (#12 above, B[i] in the simple case but it could be something like B[i]+j).

    3.) If step (1) tells us the optimizaiton is valid, we process the primitive
        based on whether it is part of the inspector or executor loop. The end
        result in either case is that PRIM_MAYBE_IRREG_ACCESS is changed into
        inspectAccess() or executeAccess(), depending on the loop.

    We make use of the maps gInspectorLoopProcessed, gDoOptimizationIE, etc.
    Their keys are the forall IDs. The purpose of the maps is to
    prevent us from doing repeated work for various clones of the
    inspector/executor foralls, which are created during ALA. Once we process
    a loop for the first time, the entry corresponding to its forall ID
    is marked in the map.

    Arguments:
    call -> The MAYBE_IRREG_ACCESS primitive

    Return:
    CallExpr* -> we either replace call with a special function call or
                 we revert it back to the original A[B[i]]
*/
CallExpr *preFoldMaybeIrregAccess(CallExpr *call)
{
  CallExpr *repl = NULL;

  printIEPreFoldHeader(call);

  // Pull out the access type from the primitive and the
  // ID
  int64_t accessType, forallID;
  get_int(toSymExpr(call->get(5)), &accessType);
  get_int(toSymExpr(call->get(6)), &forallID);

  // Performs a series of checks to determine whether we can
  // and should do the optimization. We only need to do this for
  // the inspector (and only once per clone of the inspector)
  if (accessType == INSPECTOR_ACCESS && !gInspectorLoopProcessed[forallID]) {
    gDoOptimizationIE[forallID] = isIEOptimizationValid(call);
  }

  // If doOptimization is false, then wipe out the entire optimization.
  // But it is a bit complicated to try to do that during prefolding.
  // It is easier to do the removal after all resolution is done. So
  // We "flag" the optimization for removal here and do the removal
  // in executeAccessCallPostAnalysis.
  Expr *insertPoint = NULL;
  if (!gDoOptimizationIE[forallID]) {
    if (accessType == INSPECTOR_ACCESS && !gInspectorLoopProcessed[forallID]) {
      if (fReportIrregArrayAccesses) {
        printf("!!! Optimization INVALID; code will be removed after resolution\n");
      }
      // NEW: instead of trying to remove the code now, just flag the corresponding
      // CallExprs that relate to this optimization and do the removal during post
      // resolution. We'll replace the call with the original access
      forv_Vec(CallExpr, fCall, gCallExprs) {
        if (fCall->isNamed("staticCheckCallIE")) {
          int64_t argID;
          get_int(toSymExpr(fCall->get(1)), &argID);
          if (argID == (int64_t)forallID) {
            gDeadCodeToRemoveIE.insert(fCall);
          }
        }
      }
    }
  }

  // If doOptimization is true, we can continue with building up the
  // remaining portions of the inspector/executor loop.
  if (gDoOptimizationIE[forallID]) {
    if (accessType == INSPECTOR_ACCESS) {
      repl = processInspectorAccess(call);
    }
    else if (accessType == EXECUTOR_ACCESS) {
      repl = processExecutorAccess(call);
    }
    else {
      INT_FATAL("Unknown irregular access type");
    }
  }
  else {
    // If we're processing the inspector loop, reverting the access means
    // completely removing the loop, since it does nothing now. We'll
    // handle that in preFold.cpp upon return from this function
    if (accessType == INSPECTOR_ACCESS) {
      repl = NULL;
    }
    else {
      repl = revertPrimitiveIE(call);
    }
  }

  printIEPreFoldFooter(call);

  // Indicates that we have processed the inspector or executor loop.
  // Allows us to not repeat certain steps above when we encounter
  // a clone of the inspector/executor loop.
  if (accessType == INSPECTOR_ACCESS) {
    gInspectorLoopProcessed[forallID] = true;
  }
  else {
    gExecutorLoopProcessed[forallID] = true;
  }

  return repl;

} /* end of preFoldMaybeIrregAccess */


//##################################################################################
/*
    Simply prints out some info when we enter prefoldMaybeIrregAccess()
*/
static void printIEPreFoldHeader(CallExpr *call)
{
  if (fReportIrregArrayAccesses) {
    // Pull out the arguments to the primitive.
    int64_t accessType, forallID;
    get_int(toSymExpr(call->get(5)), &accessType);
    get_int(toSymExpr(call->get(6)), &forallID);
    Symbol *A = toSymExpr(call->get(11))->symbol();
    Symbol *B = toSymExpr(call->get(12))->symbol();

    if (!gInspectorLoopProcessed[forallID] && accessType == INSPECTOR_ACCESS) {
      printf("\n+ [INSPECTOR-EXECUTOR] Pre-Folding Analyzing candidate at %s: ", call->stringLoc());
      printf("parent -> %s, call -> %s, ", A->name, B->name);
      printf("access type -> INSPECTOR\n");
    }
    else if(!gExecutorLoopProcessed[forallID] && accessType == EXECUTOR_ACCESS) {
      printf("\n+ [INSPECTOR-EXECUTOR] Pre-Folding Analyzing candidate at %s: ", call->stringLoc());
      printf("parent -> %s, call -> %s ", A->name, B->name);
      printf("access type -> EXECUTOR\n");
    }
  }
} /* end of printIEPreFoldHeader */

//##################################################################################
/*
    Simply prints out some info when we exit prefoldMaybeIrregAccess()
*/
static void printIEPreFoldFooter(CallExpr *call)
{
  if (fReportIrregArrayAccesses) {
    // Pull out the arguments to the primitive.
    int64_t accessType, forallID;
    get_int(toSymExpr(call->get(5)), &accessType);
    get_int(toSymExpr(call->get(6)), &forallID);

    if (!gInspectorLoopProcessed[forallID] && accessType == INSPECTOR_ACCESS) {
      printf("### [INSPECTOR-EXECUTOR] Pre-Folding Analysis Complete ###\n");
    }
    else if (!gExecutorLoopProcessed[forallID] && accessType == EXECUTOR_ACCESS) {
      printf("### [INSPECTOR-EXECUTOR] Pre-Folding Analysis Complete ###\n");
    }
  }
} /* end of printIEPreFoldFooter */

//##################################################################################
/*
    This function performs a series of checks/validations to see whether we can
    (or should) perform the inspector-executor optimization. Below is the list of
    requirements as of now, assuming the access-of-interest is A[B[i]]:

    1.) Both A and B must be arrays

    2.) A supports the localSubdomain query

    3.) The forall must iterate over a distributed domain/array

    4.) The all loop iterator syms involved in the access must be arrays/domains

    5.) The element type of A must be a POD or record

    6.) If the element type of A is a record, the fields accessed must only
        be POD fields.

    7.) If the forall is not in a function, check for a valid outer loop.

    If any one of these checks if false, we stop and return false. There is no
    need to do all the checks in that case.

    We may add more do this list as we make the optimization more robust.

    Some checks we need cannot be performed until after resolution, such as
    detecting invalid modifications to A and B. We do these checks as part
    of our post-resolution analysis.

    Arguments:
    call -> The MAYBE_IRREG_ACCESS primitive

    Return:
    true if the optimization is valid, false otherwise

*/
static bool isIEOptimizationValid(CallExpr *call)
{
  bool retval;

  int64_t forallID;
  get_int(toSymExpr(call->get(6)), &forallID);
  VarSymbol *hasSingleLocalSubdomain = (VarSymbol *)(toSymExpr(call->get(7))->symbol());
  VarSymbol *isForallDistributed = (VarSymbol *)(toSymExpr(call->get(8))->symbol());
  Symbol *A = toSymExpr(call->get(11))->symbol();
  Symbol *B = toSymExpr(call->get(12))->symbol();
  int64_t numLoopIteratorSyms;
  get_int(toSymExpr(call->get(14)), &numLoopIteratorSyms);

  // 1.) Check whether both A and B are arrays.
  bool isArrayA = A->getValType()->symbol->hasFlag(FLAG_ARRAY);
  bool isArrayB = B->getValType()->symbol->hasFlag(FLAG_ARRAY);
  retval = (isArrayA && isArrayB);
  if (fReportIrregArrayAccesses) {
    if (retval) {
      printf("\t- %s and %s are arrays\n", A->name, B->name);
    }
    else {
      printf("\t- %s and/or %s are NOT arrays\n", A->name, B->name);
    }
  }
  if (!retval) {
    return false;
  }

  // 2.) if hasSingleLocalSubdomain is false, it means that A is an
  // array that will not support the .localSubdomain()
  // query that we need to do as part of the optimization.
  retval = (hasSingleLocalSubdomain == gTrue);
  if (fReportIrregArrayAccesses) {
    if (retval) {
      printf("\t- %s supports the localSubdomain() query\n", A->name);
    }
    else {
       printf("\t- %s DOES NOT support the localSubdomain() query\n", A->name);
    }
  }
  if (!retval) {
    return false;
  }

  // 3.) if isForallDistributed is false, it means that the forall
  // is not iterating over a distributed domain or array. Therefore,
  // we can't reason about its locality.
  retval = (isForallDistributed == gTrue);
  if (fReportIrregArrayAccesses) {
    if (retval) {
      printf("\t- forall is iterating over a distributed domain/array\n");
    }
    else {
       printf("\t- forall is NOT iterating over a distributed domain/array\n");
    }
  }
  if (!retval) {
    return false;
  }

  // 4.) indexIterator must be an array or domain, and all loop iterator syms
  //     must be arrays or domains
  Symbol *indexIterator = toSymExpr(call->get(10))->symbol();
  bool isArray = indexIterator->getValType()->symbol->hasFlag(FLAG_ARRAY);
  bool isDomain = indexIterator->getValType()->symbol->hasFlag(FLAG_DOMAIN);
  retval = (isArray || isDomain);
  if (fReportIrregArrayAccesses && retval) {
    printf("\t- index iterator %s is an array or domain\n", indexIterator->name);
  }
  else if (fReportIrregArrayAccesses && !retval) {
    printf("\t- index iterator %s is NOT an array nor domain\n", indexIterator->name);
  }
  if (!retval) {
    return false;
  }
  // loop iterator syms start at index 15 in the primitive
  for (int64_t i = 15; i < (15+numLoopIteratorSyms); i++) {
    Symbol *sym = toSymExpr(call->get(i))->symbol();
    isArray = sym->getValType()->symbol->hasFlag(FLAG_ARRAY);
    isDomain = sym->getValType()->symbol->hasFlag(FLAG_DOMAIN);
    retval = (isArray || isDomain);
    if (fReportIrregArrayAccesses && retval) {
      printf("\t- loop iterator %s is an array or domain\n", sym->name);
    }
    else if (fReportIrregArrayAccesses && !retval) {
      printf("\t- loop iterator %s is NOT an array nor domain\n", sym->name);
    }
    if (!retval) {
      return false;
    }
  }

  // 5.) Check that A's element type is a POD or a record
  // Note: we use propagateNotPOD() instead is isPOD, since
  // isPOD should only be called AFTER resolution. If we are here,
  // then we know A is an array.
  Type *AeltType = arrayElementType(A->getValType());
  bool isRecordA = isRecord(AeltType);
  bool isPODA = !(propagateNotPOD(AeltType));
  retval = (isRecordA || isPODA);
  if (fReportIrregArrayAccesses) {
    printf("\t- %s's element type is ", A->name);
    if (isRecordA) {
      printf("record\n");
    }
    else if (isPODA) {
      printf("POD\n");
    }
    else {
      printf("not supported\n");
    }
  }
  if (!retval) {
    return false;
  }

  // 6.) If A's elements are records, we need to ensure that any fields
  //     accessed through A[B[i]] are POD types. This is because we
  //     aggregation to update the replicated arrays, and we cannot
  //     aggregate non-POD types. Also, this allows us to do a performance
  //     optimization. While we check for non-POD field accesses, we can
  //     log which POD fields we do access. Then, we will only aggregate
  //     those fields. We add these valid field postions to the global
  //     gFieldPositionsIE map/vector.
  //
  // NEW: if we are using the optimized inspector, we are dealing with on-statements.
  // So our call is in a "fn on_fn", so we won't find the enclosing forall through
  // the "provided" enclosingForallStmt(). We'll use our own that goes across call sites.
  // Normally this would be problematic as resolution hasn't finished completely, but
  // since we are looking for a very specific call-path, it is OK.
  compute_call_sites();
  ForallStmt *forall = findEnclosingForallLoop(call);
  INT_ASSERT(forall != NULL);
  if (isRecordA) {
    // we are in this function if we are processing the inspector loop. But
    // we stripped it down so it doesn't have any statements besides the
    // primitive call. So to do the following analysis, we need to look at
    // the executor loop. We can find it by looking at all CallExprs and
    // find the matching executor primitive.
    CallExpr *executorCall = NULL;
    forv_Vec(CallExpr, c, gCallExprs) {
      if (c->isPrimitive(PRIM_MAYBE_IRREG_ACCESS)) {
        int64_t accessType, executorID;
        get_int(toSymExpr(c->get(5)), &accessType);
        get_int(toSymExpr(c->get(6)), &executorID);
        // without using our previous statiCheck symbol to look for the
        // matching executor loop, we may find a version of the executor
        // that hasn't been resolved. So to prevent this, not only does
        // the forall ID have to match, but the symbol A must have a valid
        // resolved type (that is what we need to get in fieldAccessesAreValidIE()
        // anyways) and it must match the same A from our inspector primitive
        if (accessType == EXECUTOR_ACCESS && executorID == forallID) {
          Symbol *Ac = toSymExpr(c->get(11))->symbol();
          Type *AeltType = arrayElementType(Ac->getValType());
          if (AeltType != NULL && Ac == A) {
            executorCall = c;
            break;
          }
        }
      }
    }
    INT_ASSERT(executorCall != NULL);
    retval = fieldAccessesAreValidIE(executorCall);
  }
  if (fReportIrregArrayAccesses && isRecordA) {
    if (retval) {
      printf("\t- Record elements from %s only access POD fields\n", A->name);
    }
    else {
      printf("\t- Record elements from %s access non-POD fields (not supported)\n", A->name);
    }
  }
  if (!retval) {
    return false;
  }

  // 7.) If the forall is not in a function (the module init doesn't count),
  //     ensure that we have an enclosing serial loop. We know whether we are not
  //     in a function if forall->optInfo.functionID is NOT_IN_FUNCTION. Since we don't have to
  //     go across function calls to look for the loop, we can do it here (before
  //     resolution has finished building up the proper call graph).
  if (forall->optInfo.functionID == NOT_IN_FUNCTION) {
    retval = false;
    for (Expr* curr = forall->parentExpr; curr; curr = curr->parentExpr) {
      if (toWhileStmt(curr) || toForLoop(curr)) {
        retval = true;
      }
    }
    if (fReportIrregArrayAccesses) {
      if (retval) {
        printf("\t- forall is nested in an outer serial loop\n");
      }
      else {
        printf("\t- forall is NOT nested in an outer serial loop\n");
      }
    }
  }
  return retval;

} /* end of isIEOptimizationValid */

//##################################################################################
/*
    Given a CallExpr call that is the PRIM_MAYBE_IRREG_ACCESS primitive, where we
    know that A's element type is a record, determine whether we have something
    like "ref t = A[B[i]]" or "var t = A[B[i]]". For t, ensure that the fields
    accessed are POD types. If we detect a non-POD field access, we return false.
    For POD field accesses, we log their field positions in gFieldPositionsIE for
    an optimization performed in the executorPreamble.

    Note that we track accessed to t across function calls if t is passed into
    a function.

    Arguments:
    call -> the MAYBE_IRREG_ACCESS primitive

    Return:
    true if the field accesses are all to POD types, false otherwise
*/
static bool fieldAccessesAreValidIE(CallExpr *call)
{
  int64_t forallID;
  get_int(toSymExpr(call->get(6)), &forallID);
  Symbol *A = toSymExpr(call->get(11))->symbol();
  Type *AeltType = arrayElementType(A->getValType());
  AggregateType *at = toAggregateType(AeltType);

  Symbol *LHS = NULL;
  // Look for move(LHS, call)
  if (CallExpr *parent = toCallExpr(call->parentExpr)) {
    if (parent->isPrimitive(PRIM_MOVE)) {
      LHS = (toSymExpr(parent->get(1)))->symbol();
    }
  }
  INT_ASSERT(LHS);

  // Look for a move into a ref or var "t" where LHS from above
  // is on the RHS.
  Symbol *t = NULL;
  for_SymbolSymExprs(symexpr, LHS) {
    if (CallExpr *symCall = toCallExpr(symexpr->parentExpr)) {
      // Case 1: ref t = A[B[i]]
      if (symCall->isPrimitive(PRIM_ADDR_OF)) {
        if (CallExpr *moveCall = toCallExpr(symCall->parentExpr)) {
          if (moveCall->isPrimitive(PRIM_MOVE)) {
            // LHS of move is t
            t = (toSymExpr(moveCall->get(1)))->symbol();
            break;
          }
        }
      }
      // Case 2: var t = A[B[i]]
      else if (symCall->isPrimitive(PRIM_INIT_VAR)) {
        // Ensure that 2nd arg is symexpr
        if (symexpr == toSymExpr(symCall->get(2))) {
          // first arg is t
          t = (toSymExpr(symCall->get(1)))->symbol();
        }
      }
    }
  }
  INT_ASSERT(t);

  return detectFieldAccesses(t, at, forallID);

} /* end of fieldAccessesAreValidIE */

//##################################################################################
/*
    Processes the access when it is part of the inspector loop. This is called
    from preFoldMaybeIrregAccess(). The first thing we do is find the enclosing
    forall for call (which is the PRIM_MAYBE_IRREG_ACCESS node).

    We add the call to inspectorPreamble() before the loop and sortReplIndices() after
    the loop.

    We then replace call with inspectAccess(A, B[i]) (though we actually pass in
    some shadow variables instead of A, which correspond to the replicated-array
    data).

    Arguments:
    call -> The MAYBE_IRREG_ACCESS primitive that is part of the inspector loop

    Return:
    CallExpr* -> new call to inspectAccess()
*/
static CallExpr *processInspectorAccess(CallExpr *call)
{
  // Pull out the args we'll need
  int64_t forallID;
  get_int(toSymExpr(call->get(6)), &forallID);
  // Simple base, BCall is just B[i] from A[B[i]]. But in general
  // it was a CallExpr that was the entire index expression into A.
  Expr *BCall = call->get(13)->remove();

  // Get the enclosing forall
  compute_call_sites();
  ForallStmt *forall = findEnclosingForallLoop(call);
  INT_ASSERT(forall != NULL);
  INT_ASSERT(forall->optInfo.cloneTypeIE == INSPECTOR);

  if (fReportIrregArrayAccesses && !gInspectorLoopProcessed[forallID]) {
    printf("\t- $$$ Optimization VALID at Pre-Folding; replacing primitive with inspectAccess()\n");
  }

  // Build up the call to inspectAccess
  Symbol *replD = toSymExpr(call->get(1))->symbol();
  Symbol *arrDom = toSymExpr(call->get(2))->symbol();
  INT_ASSERT(replD != NULL);
  INT_ASSERT(arrDom != NULL);
  return new CallExpr("inspectAccess",
                      replD,
                      arrDom,
                      BCall);

} /* end of processInspectorAccess */

//##################################################################################
/*
    Processes the access when it is part of the executor loop. This is called
    from preFoldMaybeIrregAccess(). The first thing we do is find the enclosing
    forall for call (which is the PRIM_MAYBE_IRREG_ACCESS node). From there,
    we add the call to executorPreamble() before the forall and then replace
    the primitive (call) with a call to executeAccess().

    We also copy over some Symbols that we'll need during post-resolution.
    They tend to not stick around after prefolding unless we save them off.

    Arguments:
    call -> The MAYBE_IRREG_ACCESS primitive that is part of the executor loop

    Return:
    CallExpr* -> new call to executeAccess()

*/
static CallExpr *processExecutorAccess(CallExpr *call)
{
  // Pull out the args we'll need
  VarSymbol *ieIDVar = (VarSymbol *)(toSymExpr(call->get(3))->symbol());
  VarSymbol *ieHash = (VarSymbol *)(toSymExpr(call->get(4))->symbol());
  int64_t forallID;
  get_int(toSymExpr(call->get(6)), &forallID);
  Symbol *forallIterSym = toSymExpr(call->get(9))->symbol();
  Symbol *indexIterator = toSymExpr(call->get(10))->symbol();
  Symbol *A = toSymExpr(call->get(11))->symbol();
  Symbol *B = toSymExpr(call->get(12))->symbol();
  // Simple base, BCall is just B[i] from A[B[i]]. But in general
  // it was a CallExpr that was the entire index expression into A. 
  Expr *BCall = call->get(13)->remove();


  // 2.) Next, we need to get a reference to the executor loop.
  ForallStmt *forall = enclosingForallStmt(call);
  INT_ASSERT(forall != NULL);
  INT_ASSERT(forall->optInfo.cloneTypeIE == EXECUTOR);

  // 3.) add call to executorPreamble before the forall
  // NOTE: because this is inserted before the forall, which is
  // being resolved now, we need to manually resolve the call.
  //
  // If A's element type is a record, then we'll want to call
  // a special version of the preamble. Otherwise, it is assumed
  // that A's element type is a POD type (we check for this before
  // we get here).
  CallExpr *executorPreamble = NULL;
  if (isRecord(arrayElementType(A->getValType()))) {
    executorPreamble = new CallExpr("executorPreambleRecords",
                                    A, ieIDVar, ieHash);
    for (auto& pos : gFieldPositionsIE[forallID]) {
      executorPreamble->insertAtTail(new_IntSymbol(pos));
    }
  }
  else {
    executorPreamble = new CallExpr("executorPreamble",
                                    A, ieIDVar, ieHash);
  }
  BlockStmt *dummyBlock = new BlockStmt();
  dummyBlock->insertAtTail(executorPreamble);
  forall->insertBefore(dummyBlock);
  normalize(dummyBlock);
  resolveBlockStmt(dummyBlock);
  dummyBlock->flattenAndRemove();

  // 4.) Ensure that things make it over to post resolution
  forall->optInfo.ieID = (int)forallID;
  forall->optInfo.ieForallIteratorSym = forallIterSym;
  forall->optInfo.ieIndexIterator = indexIterator;
  std::pair<Symbol *, Symbol *> candidate;
  candidate.first = A;
  candidate.second = B;
  // TODO: assuming 1 candidate for the forall
  forall->optInfo.ieCandidatesResolved.push_back(candidate);
  int64_t numLoopIteratorSyms, numLoopIndexSyms;
  forall->optInfo.ieLoopIteratorSyms.clear();
  // the number of loop iterators is at index 13 because we removed
  // BCall above (which was at 13). Given iterSym at index i, its type
  // is at (i+numLoopIteratorSyms);
  get_int(toSymExpr(call->get(13)), &numLoopIteratorSyms);
  for (int64_t i = 14; i < (14+numLoopIteratorSyms); i++) {
    Symbol *sym = toSymExpr(call->get(i))->symbol();
    int64_t iterType;
    get_int(toSymExpr(call->get(i+numLoopIteratorSyms)), &iterType);
    std::pair<Symbol *, ieIndexIteratorType> iterPair(sym, (ieIndexIteratorType)iterType);
    forall->optInfo.ieLoopIteratorSyms[iterPair] = true;
  }
  // (14+numLoopIteratorSyms) is the first loopIteratorType. There
  // are numLoopIteratorSyms of those and then we get to the number of
  // loop index symbols. So we want to start at (14 + 2*numLoopIteratorSyms)
  int idx = 14 + (2*numLoopIteratorSyms);
  // Similar to above but for the loop index symbols
  get_int(toSymExpr(call->get(idx)), &numLoopIndexSyms);
  forall->optInfo.ieIndexSymbols.clear();
  idx++;
  for (int64_t i = idx; i < idx+numLoopIndexSyms; i++) {
    Symbol *sym = toSymExpr(call->get(i))->symbol();
    forall->optInfo.ieIndexSymbols.insert(sym);
  }

  // 5.) Build up the call to executeAccess
  Symbol *replArr = toSymExpr(call->get(1))->symbol();
  Symbol *arrDom = toSymExpr(call->get(2))->symbol();
  INT_ASSERT(replArr != NULL);
  INT_ASSERT(arrDom != NULL);

  if (fReportIrregArrayAccesses && !gExecutorLoopProcessed[forallID]) {
    printf("\t- $$$ Optimization VALID at Pre-Folding; replacing primitive with executeAccess()\n");
  }

  return new CallExpr("executeAccess",
                      arrDom,
                      replArr,
                      A,
                      BCall);

} /* end of processExecutorAccess */

//##################################################################################
/*
    Change the MAYBE_IRREG_ACCESS primitive to A[B[i]]. 

    This is called when we determine that the primitive is not valid for the
    optimization.

    Arguments:
    call -> The MAYBE_IRREG_ACCESS primitive

    Return:
    CallExpr* -> call to A[B[i]]
*/
static CallExpr *revertPrimitiveIE(CallExpr *call)
{
  // Pull out the args we'll need
  int64_t accessType, forallID;
  get_int(toSymExpr(call->get(5)), &accessType);
  get_int(toSymExpr(call->get(6)), &forallID);
  Symbol *A = toSymExpr(call->get(11))->symbol();
  // Simple base, BCall is just B[i] from A[B[i]]. But in general
  // it was a CallExpr that was the entire index expression into A.
  Expr *BCall = call->get(13)->remove();

  if (fReportIrregArrayAccesses) {
    if (!gInspectorLoopProcessed[forallID] && accessType == INSPECTOR_ACCESS) {
      printf("!!! Optimization INVALID at Pre-Folding; changing primitive back to original access\n");
    }
    else if (!gExecutorLoopProcessed[forallID] && accessType == EXECUTOR_ACCESS) {
      printf("!!! Optimization INVALID at Pre-Folding; changing primitive back to original access\n");
    }
  }

  return new CallExpr(A, BCall);
} /* end of revertPrimitiveIE */


///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                      Post-resolution Related Functions                    //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
/*
    These functions perform some post resolution analysis and code transformation.
    A majority of the tasks involve detecting invalid modifications to the
    arrays A and B from A[B[i]], as well as the forall loop's domain. We also
    do call path analysis to ensure that each call path to the function that
    contains the forall loop has an outer serial loop and does not have
    any invalid enclosing structures. Note that if the forall is not in a function
    (i.e., not in a function that isn't the module init), we do not need to
    do call path analysis.

    We wait until after resolution to do these checks because argument/formal
    intents have been resolved. This makes it quite easy to detect whether we
    have a write (modification) to A or B, as such writes will be seen as
    CallExprs that take in A or B as arguments. Therefore, if those arguments
    have a certain intent, we know that they are modified/written to. Also, after
    resolution, function calls have been resolved. This is key for the call path
    analysis since we need to be able to tell the difference between foo(x:real)
    and foo(x:int).

    Another crucial task that we perform, assuming we detect no invalid writes,
    is adding calls to inspectorOn() after any writes to B and its domain,
    A's domain and the forall/loop domain(s). This ensures that the inspector is turned
    back on and ran if anything changes that could alter the locality and
    execution of the forall. This is a crucial correctness component of the
    optimization. We handle a few cases here, such as if B is a ref of another
    array or if B is a ref to a field in a record.

    For A, B and the other arrays/domains to be valid at this point, we have the following conditions:

    1.) All of them CANNOT be written to within the forall. This is crucial for B,
        but we could relax it for A with some extra care.

    2.) B and its domain, A's domain and the forall domain CANNOT be modified just outside
        of the forall. In other words, the forall must be able to run multiple times
        without these changing. This is a performance consideration, as we want to run the
        optimized loop more than once to offset the cost of the inspector.

    If we find invalid writes, then we change statiCheckCall to be false, which
    will effectively turn off the optimization (dead-code elimination will
    wipe out the entire "optimization" branch).
*/

//##################################################################################
/*
    Main function for performing the checks/analysis described above for A[B[i]].
    It is declared in forallOptimizations.h because it is called from
    cullOverReferences.cpp.

    Before we get to this call, prefolding has finished. If everything was valid,
    then A[B[i]] will have been replaced with inspectAccess() and executeAccess()
    within the inspector and executor foralls, respectively. If something was invalid
    during prefolding, then those function calls won't exist. In that case, there is
    nothing for us to do here, as further checks are not needed.

    The first task we do is to ensure that we don't have any cycles in the call
    graph related to the function that contains an optimized forall (this does not
    apply if a forall is not in a function). A cycle indicates a recursive call
    somewhere along the call path. That is bad for several reasons, most notably
    because it will cause the compiler to go into an infinite loop during some of
    the checks we do later. If we find a cycle w.r.t. a given forall in a function,
    we invalidate that forall and any other forall that was optimized in that
    function.

    To "find" the foralls we have optimized, we find all calls to executeAccess(). We only need to
    look at the executor loop, since the checks we plan to do are identical for both
    the inspector and executor loop. From a given executeAccess() call, we can get
    the enclosing forall loop, which leads us to all the info we need.

    If our analysis tells us that we have invalid modifications, then we set
    static-check to false. This check is a param that will essentially turn the
    optimization on/off (if static-check is false, dead-code elimination will wipe
    out the inspector/executor loops). At this point, it is set to true. So if we
    don't find any invalid modifications, we do not need to do anything.

    To detect modifications, we look at all SymExprs involving A, B, their domains
    and the forall loop domain. If the symbol is passed to a ref formal, then we conclude
    that the symbol is modified. The logic here is that all modifications (including assignment)
    will occur via function calls that accept symbol as arguments. At this point in post-resolution,
    arguments have their intents correctly set. For arrays and domains, which all we are
    considering, their intents will be set to ref if they are modified by the function.

    We specifically do these checks at this point in compilation because something
    like this(B,i), which is added for statements like B[i], will have a const-ref
    intent when B[i] is part of a read and a ref intent when B[i] is part of a write.

    After, if the checks pass, we will add the appropriate call(s) to turn on the
    inspector after valid writes. Note that if we find an invalid write in the above
    checks, we invalidate the entire optimization. There are cases when that is overly
    cautious, as the invalid write could be on just one call path to the function that
    contains the forall. But the solution to address that (dynamic call path analysis)
    cannot handle all such cases. Since it is not a correctness issue, I am opting to
    leave it alone for now.

    When we've processed all relevant forall loops for write/modifcation analyis, we
    can then perform call path analysis to ensure that each call to the function (if
    there is one) that contains the forall is valid. Rather than statically trying to
    undo the optimization if there is something invalid, we effectively do it at runtime
    by calling the set/unset methods for the call path flags.

    Arguments:
    None

    Return:
    None
*/
void inspectorExecutorPostAnalysis()
{
  // Keep track of the executor foralls we process; we only need to process
  // one of them (not all of their clones) for the write/mod analysis.
  std::map<int, bool> executorProcessed;

  // First, for anything we wanted to remove/invalidate during prefolding,
  // do that. We added relevant CallExprs to gDeadCodeToRemoveIE so we could
  // process them here
  for (auto &call : gDeadCodeToRemoveIE) {
    if (call->parentExpr == NULL) {
      // this code is no longer reachable, must have been removed by something else?
      continue;
    }
    // TODO: be more careful about getting the CondStmt
    if (CondStmt *cond = toCondStmt(call->parentExpr->next->next->next)) {
      BlockStmt *b = new BlockStmt();
      b->insertAtHead(cond->elseStmt->remove());
      cond->insertAfter(b);
      cond->thenStmt->remove();
      cond->remove();
    }
  }

  // Next, invalidate any forall that is in a function where there is a
  // recursive call along the call path.
  bool firstPrint = true;
  forv_Vec(CallExpr, call, gCallExprs) {
    if (call->parentExpr != NULL && call->theFnSymbol() && call->theFnSymbol()->hasFlag(FLAG_EXECUTE_ACCESS)) {
      if (firstPrint && fReportIrregArrayAccesses) {
        printf("\n+ [INSPECTOR-EXECUTOR] Looking for cycles in the function call graph\n");
        firstPrint = false;
      }
      detectCyclesInCallGraphIE(call, executorProcessed);
    } /* end of if call is executeAccess */
  } /* end of forv_Vec(CallExpr, call, gCallExps) */

  // Next, look for invalid modifications to the various arrays/symbols/domains
  executorProcessed.clear();
  firstPrint = true;
  forv_Vec(CallExpr, call, gCallExprs) {
    if (call->parentExpr != NULL && call->theFnSymbol() && call->theFnSymbol()->hasFlag(FLAG_EXECUTE_ACCESS)) {
      if (firstPrint && fReportIrregArrayAccesses) {
        printf("\n+ [INSPECTOR-EXECUTOR] Performing write/modification analysis for inspector-executor\n");
        firstPrint = false;
      }
      executeAccessCallPostAnalysis(call, executorProcessed);
    } /* end of if call is executeAccess */
  } /* end of forv_Vec(CallExpr, call, gCallExps) */

  // Next, we do call path analysis. The outcome here is that we
  // will insert calls to set/unset hasOuterLoop and hasInvalidEnclosingStructure
  // for a function of interest that contains a forall being processed. Note
  // that we only add the set/unset calls along valid paths. The default values
  // for the flags are false, so that if we didn't have a valid path, we don't
  // need to do anything. If we don't find any valid paths, we should print something
  // to let the user know.
  firstPrint = true;
  executorProcessed.clear();
  forv_Vec(CallExpr, call, gCallExprs) {
    if (call->parentExpr != NULL && call->theFnSymbol() && call->theFnSymbol()->hasFlag(FLAG_EXECUTE_ACCESS)) {
      if (firstPrint && fReportIrregArrayAccesses) {
        printf("\n+ [INSPECTOR-EXECUTOR] Performing call path analysis for inspector-executor\n");
        firstPrint = false;
      }
      dynamicCallPathAnalysisIE(call, executorProcessed);
    }
  }

  if (firstPrint == false && fReportIrregArrayAccesses) {
    printf("### [INSPECTOR-EXECUTOR] Post Analysis Complete ###\n");
  }
} /* end of inspectorExecutorPostAnalysis */

//##################################################################################
/*
    For a given CallExpr call that is a call to executeAccess() in an IE-optimized
    forall, determine whether the function that contains the forall is part of a
    recursive cycle in the function call graph. If it is, invalidate the optimized
    forall, and any other IE-optimized forall in the function.

    Arguments:
    call -> the CallExpr to executeAccess in a forall
    executorProcessed -> keeps track of the foralls we have processed

    Return:
    None
*/
static void detectCyclesInCallGraphIE(CallExpr *call,
                                      std::map<int, bool> &executorProcessed)
{
  ForallStmt *forall = enclosingForallStmt(call);
  INT_ASSERT(forall != NULL);
  int forallID = forall->optInfo.ieID;

  if (executorProcessed.count(forallID) > 0) {
    // already processed
    return;
  }
  // First time processing this forall
  executorProcessed[forallID] = true;

  // Don't bother if this forall is no longer valid or it is not
  // in a function
  if (forall->optInfo.cloneTypeIE == INVALID_OPT || forall->optInfo.functionID == NOT_IN_FUNCTION) {
    return;
  }

  if (fReportIrregArrayAccesses) {
    printf("\t- Processing forall at %s\n", forall->stringLoc());
  }

  // Perform a DFS of the call graph, starting from the function that contains the
  // forall. For each call site we process, we add the FnSymbol to a set. If we see that the
  // set already contains the FnSymbol, we have a cycle.
  FnSymbol *rootFn = getEnclosingFunction(call);
  std::set<FnSymbol *> visitedFunctions;
  visitedFunctions.insert(rootFn);
  compute_call_sites();
  bool hasCycle = depthFirstSearchIE(rootFn, visitedFunctions);
  if (!hasCycle) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t- No cycles found\n");
    }
  }
  else {
    if (fReportIrregArrayAccesses) {
      printf("\t\t- Recursive cycle detected on call path; invalidating ALL optimized foralls in %s\n", rootFn->name);
    }

    // Find all optimized forall's in this function and invalidate them
    std::vector<ForallStmt*> forallLoops;
    collectForallStmts(rootFn, forallLoops);
    std::set<int> forallInvalidated;
    for (auto &loop : forallLoops) {
      if (loop->optInfo.cloneTypeIE == EXECUTOR) {
        int ID = loop->optInfo.ieID;
        if (forallInvalidated.count(ID) == 0) {
          forallInvalidated.insert(ID);
          if (fReportIrregArrayAccesses) {
            printf("\t\t\t- invalidating forall at %s\n", loop->stringLoc());
          }
          loop->optInfo.cloneTypeIE = INVALID_OPT;
          removeOptimizationIE(forallID, rootFn);
        }
      }
    }
  }

} /* end of detectCyclesInCallGraphIE */

//##################################################################################
/*
    Performs a Depth First Search (DFS) of the call graph. For each FnSymbol we
    come across, we add it to a set. If we find that the FnSymnol is already in
    the set, then we have a cycle and we return true.

    Arguments:
    fn -> the current FnSymbol we are processing
    visitedFunctions -> set of FnSymbols we've seen on this path

    Return:
    true if we found a cycle, false otherwise.
*/
static bool depthFirstSearchIE(FnSymbol *fn,
                               std::set<FnSymbol *> &visitedFunctions)
{
  bool retval = false;
  forv_Vec(CallExpr, call, *fn->calledBy) {
    // is call in a function? If so, look at who calls that
    if (FnSymbol *parentFn = toFnSymbol(call->parentSymbol)) {
      if (visitedFunctions.count(parentFn) > 0) {
        // Cycle detected
        retval = true;
        break;
      }
      else {
        visitedFunctions.insert(parentFn);
        retval = depthFirstSearchIE(parentFn, visitedFunctions);
        // If we found a cycle, break out
        if (retval) {
          break;
        }
        // Pop off parentFn from the path
        visitedFunctions.erase(parentFn);
      }
    }
  }
  return retval;
} /* end of depthFirstSearchIE */

//##################################################################################
/*
    For a given CallExpr call that has been determined to be a call to the
    executeAccess() function, we will look at the modifications to arrays A
    and B as part of the A[B[i]] construct that we are optimizing, as well as
    their domains and the forall loop's domain. If any of those modifications
    are invalid, then we "undo" the optimization as it has been applied thus far.

    If the modifications are valid, we then insert calls to inspectorOn()
    after the valid writes to B, its domain, A's domain and the forall loop's
    domain.

    We also apply the above checks/steps to any symbol that the forall or
    any inner loop iterates over.

    NOTE: We do perform inter-procedural analysis to detect writes to the
    arrays when those arrays were passed into a function that contains
    the forall of interest. We also handle when the symbols are refs (aliases)
    to other symbols.

    Arguments:
    call -> CallExpr corresponding to a call to inspectAccess()
    executorProcessed -> map that says whether the executor forall corresponding
                         to this call has been processed already

    Return:
    None
*/
static void executeAccessCallPostAnalysis(CallExpr *call,
                                          std::map<int, bool> &executorProcessed)
{
  ForallStmt *forall = enclosingForallStmt(call);
  INT_ASSERT(forall != NULL);
  int forallID = forall->optInfo.ieID;

  if (executorProcessed.count(forallID) > 0) {
    // already processed
    return;
  }
  // First time processing this forall
  executorProcessed[forallID] = true;

  // Skip if the forall was marked as invalid by an earlier analysis
  if (forall->optInfo.cloneTypeIE == INVALID_OPT) {
    return;
  }

  if (fReportIrregArrayAccesses) {
    printf("\t- Processing forall at %s\n", forall->stringLoc());
  }

  // We need to be able to find at least 1 outer serial loop that encloses the forall.
  // If we can't find one, then this forall is invalid. We do a separate pass for
  // call-path analysis afterwards to deal with multiple call sites, etc. But if
  // we don't have a single path with an outer loop, we're done
  compute_call_sites();
  Expr *loop = findEnclosingSerialLoop(forall);
  if (loop == NULL) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t- !!! no outer loops detected for forall; optimization is invalid\n");
    }
    forall->optInfo.cloneTypeIE = INVALID_OPT;
    removeOptimizationIE(forallID, NULL);
    return;
  }

  // Before we do all the complicated checks, there is a more straightforward check to
  // do: for each index variable that was used in the candidate access, ensure it is
  // read-only within the forall.
  std::map<Symbol *, std::map<CallExpr *, bool>> indexSymsModifications;
  std::map<Symbol *, bool> aliasesAnalyzed;
  std::map<Symbol *, std::set<Symbol *>> aliasIndexSymbols;
  std::set<Symbol *> indexSyms = forall->optInfo.ieIndexSymbols;
  compute_call_sites();
  for (auto &sym : indexSyms) {
    aliasesAnalyzed[sym] = true;
    findAllModificationsToSymbol(sym,
                                 (Expr*)call->parentExpr,
                                 indexSymsModifications,
                                 aliasesAnalyzed,
                                 aliasIndexSymbols,
                                 false,
                                 NULL);
    aliasesAnalyzed.clear();
  }
  // For each modification, see if it's in the scope of the forall loop
  for (auto &elem : indexSymsModifications) {
    Symbol *sym = elem.first;
    // For every modification involing sym...
    for (auto &mods : elem.second) {
      CallExpr *mod = mods.first;
      // does forall contain the modification?
      if (doesExprContainExpr(mod, forall)) {
        if (fReportIrregArrayAccesses) {
          // TODO: this will print call_tmp in the case of some alias
          printf("\t\t- !!! %s cannot be modified in forall loop\n", sym->name);
        }
        forall->optInfo.cloneTypeIE = INVALID_OPT;
        removeOptimizationIE(forallID, NULL);
        return;
      }
    }
  }
  

  std::pair<Symbol *, Symbol *> candidate = forall->optInfo.ieCandidatesResolved[0];
  Symbol *A = candidate.first;
  Symbol *B = candidate.second;
  Symbol *forallIteratorSym = forall->optInfo.ieForallIteratorSym;
  Symbol *indexIteratorSym = forall->optInfo.ieIndexIterator;
  ieIndexIteratorType indexIteratorType = forall->optInfo.indexIteratorType;

  // Get the loop iterator syms; these are the symbols for any loop iterators that yield
  // symbols used within the A[B[i]] access. We want to track changes to them, as they can
  // influence the A[B[i]] access pattern. Each sym has its ieIndexIteratorType type noted as
  // well.
  std::map<std::pair<Symbol *, ieIndexIteratorType>, bool>loopIteratorSyms = forall->optInfo.ieLoopIteratorSyms;

  if (fReportIrregArrayAccesses) {
    printf("\t\t- checking for invalid modifications to %s, %s, their domains, the forall domain and index iterators\n", A->name, B->name);
  }

  // 1.) We need to get the domains for A and B. Changes to either would
  //     require the inspector to be re-ran.
  bool isRecFieldAdom = false, isRecFieldBdom = false;
  AggregateType *atA;
  AggregateType *atB;
  Symbol *Adom = domainSymbolForArray(A, call, isRecFieldAdom, aliasesAnalyzed, atA);
  aliasesAnalyzed.clear();
  Symbol *Bdom = domainSymbolForArray(B, call, isRecFieldBdom, aliasesAnalyzed, atB);
  aliasesAnalyzed.clear();
  if (Adom == NULL || Bdom == NULL) {
    if (fReportIrregArrayAccesses) {
      if (Adom == NULL) {
        printf("\t\t- !!! could not find %s's domain symbol; cannot apply optimization\n", A->name);
      }
      if (Bdom == NULL) {
        printf("\t\t- !!! could not find %s's domain symbol; cannot apply optimization\n", B->name);
      }
    }
    forall->optInfo.cloneTypeIE = INVALID_OPT;
    removeOptimizationIE(forallID, NULL);
    return;
  }

  // 2.) If the forallIteratorSym is an array, we need to get its domain. If
  //     the domain changes, it could change where tasks execute, and thus the
  //     remote access pattern of A[B[i]]. But forallIteratorSym could be a
  //     domain already; if so, we don't need to do anything.
  //
  // NEW: before, we would attempt to only look at things that we had not seen
  //      already (i.e., forallIteratorDom != Adom or Bdom). That just makes the code
  //      pretty messy and hard to follow. Since all of our modifications will be stored
  //      in a std::map, it doesn't matter if we process the same symbol twice.
  Symbol *forallIteratorDom = NULL;
  bool isRecFieldForallIterSym = false;
  AggregateType *atForallIterSym = NULL;
  if (forallIteratorSym->getValType()->symbol->hasFlag(FLAG_DOMAIN)) {
    forallIteratorDom = forallIteratorSym;
  }
  else {
    forallIteratorDom = domainSymbolForArray(forallIteratorSym, call, isRecFieldForallIterSym, aliasesAnalyzed, atForallIterSym);
  }
  if (forallIteratorDom == NULL) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t- !!! could not find forall iterator %s's domain symbol; cannot apply optimization\n", forallIteratorSym->name);
    }
    forall->optInfo.cloneTypeIE = INVALID_OPT;
    removeOptimizationIE(forallID, NULL);
    return;
  }

  // 3.) The indexIteratorSym is "foo" from either "for i in foo" or
  //     "for i in foo.domain". We do not need to do anything in the case
  //     of the former, as we simply track changes to foo; we don't care about
  //     its domain. If it is the latter, we need to find the "real" symbol for
  //     foo's domain.
  //
  //     To summarize: foo's domain is only relevant if indexIteratorType is
  //     equal to DOT_DOMAIN or DOT_DOMAIN_REC_FIELD.
  Symbol *indexIteratorDom = NULL;
  bool isRecFieldIndexIterSym = false;
  AggregateType *atIndexIterSym = NULL;
  if (indexIteratorType == DOT_DOMAIN || indexIteratorType == DOT_DOMAIN_REC_FIELD) {
    indexIteratorDom = domainSymbolForArray(indexIteratorSym, call, isRecFieldIndexIterSym, aliasesAnalyzed, atIndexIterSym);
    if (indexIteratorDom == NULL) {
      if (fReportIrregArrayAccesses) {
        printf("\t\t- !!! could not find index iterator %s's domain symbol; cannot apply optimization\n", indexIteratorSym->name);
      }
      forall->optInfo.cloneTypeIE = INVALID_OPT;
      removeOptimizationIE(forallID, NULL);
      return;
    }
  }

  // 4.) We now have all the symbols and their domains that we need.
  //     The next step is to find all modifications to these symbols.
  //     This does the heavy lifting of looking for aliases to these
  //     symbols and finding modifications to those aliases. It'll
  //     also correctly handle cases where we are referencing fields
  //     of records.
  //
  //     The array/symbol A is the only case that will allow for
  //     modifications directly outside of the forall, and where
  //     modifications do not require a call to inspectorOn(). For
  //     that reason, we store its modifications in a separate map.
  //     All other symbols have the same requirements in terms of
  //     where their modifications are allowed to be and when they
  //     need calls to inspectorOn(). So we store all of those in
  //     one map.
  //
  //     So we can do our call-path analysis later, the modifications
  //     map stores Symbol* as the keys. These Symbols are the "target"
  //     of the write/modification. The keys are mapped to vectors of
  //     CallExprs, where the CallExpr is the actual write. He also associate
  //     a bool with each CallExpr so we can make it as a valid or invalid
  //     write.
  //
  //     We also keep track of the aliases we found. Given something like
  //     "ref x = y", the map will add an entry for "y" that is associated
  //     with a set containing "x". If we find another alias to y, we add
  //     it to the set. This map is different from the aliasesAnalyzed map,
  //     which is reset for each call to findAllModificationsToSymbol(). That
  //     map keeps track of which aliases we've processed for a given call, so
  //     we don't get stuck in an infinite loop.
  std::map<Symbol *, std::map<CallExpr *, bool>> modificationsAOnly;
  std::map<Symbol *, std::map<CallExpr *, bool>> modifications;
  std::map<Symbol *, std::set<Symbol *>> aliasSymbols;
  compute_call_sites();
  aliasesAnalyzed.clear();
  aliasesAnalyzed[A] = true;
  findAllModificationsToSymbol(A,
                               forall->parentExpr,
                               modificationsAOnly,
                               aliasesAnalyzed,
                               aliasSymbols,
                               false,
                               NULL);
  aliasesAnalyzed.clear();
  aliasesAnalyzed[B] = true;
  findAllModificationsToSymbol(B,
                               forall->parentExpr,
                               modifications,
                               aliasesAnalyzed,
                               aliasSymbols,
                               false,
                               NULL);
  aliasesAnalyzed.clear();
  aliasesAnalyzed[Adom] = true;
  findAllModificationsToSymbol(Adom,
                               forall->parentExpr,
                               modifications,
                               aliasesAnalyzed,
                               aliasSymbols,
                               isRecFieldAdom,
                               atA);
  aliasesAnalyzed.clear();
  aliasesAnalyzed[Bdom] = true;
  findAllModificationsToSymbol(Bdom,
                               forall->parentExpr,
                               modifications,
                               aliasesAnalyzed,
                               aliasSymbols,
                               isRecFieldBdom,
                               atB);
  aliasesAnalyzed.clear();
  aliasesAnalyzed[forallIteratorDom] = true;
  findAllModificationsToSymbol(forallIteratorDom,
                               forall->parentExpr,
                               modifications,
                               aliasesAnalyzed,
                               aliasSymbols,
                               isRecFieldForallIterSym,
                               atForallIterSym);
  aliasesAnalyzed.clear();
  if (indexIteratorDom == NULL) {
    aliasesAnalyzed[indexIteratorSym] = true;
    findAllModificationsToSymbol(indexIteratorSym,
                                 forall->parentExpr,
                                 modifications,
                                 aliasesAnalyzed,
                                 aliasSymbols,
                                 false,
                                 NULL);
  }
  else {
    aliasesAnalyzed[indexIteratorDom] = true;
    findAllModificationsToSymbol(indexIteratorDom,
                                 forall->parentExpr,
                                 modifications,
                                 aliasesAnalyzed,
                                 aliasSymbols,
                                 isRecFieldIndexIterSym,
                                 atIndexIterSym);
  }
  aliasesAnalyzed.clear();

  // 5.) We need to do the same types of checks as (3) but for each index iterator.
  //     These are the iterators that yield symbols used in the A[B[i]] access.
  //     We want to track changes to them since they could change the access pattern.
  //
  //     We have postponed this step until now because we can more easily keep track
  //     of the various things we need for each index iterator. In this way, we can
  //     process an iterator symbol and find its modifications right after.
  for (auto &elem : loopIteratorSyms) {
    Symbol *sym = elem.first.first;
    ieIndexIteratorType iterType = elem.first.second;
    Symbol *iterDom = NULL;
    bool isRecFieldIterSym = false;
    AggregateType *atIterSym = NULL;
    // 5.1.) If sym is from a .domain, get the domain
    if (iterType == DOT_DOMAIN || iterType == DOT_DOMAIN_REC_FIELD) {
      iterDom = domainSymbolForArray(sym, call, isRecFieldIterSym, aliasesAnalyzed, atIterSym);
      if (iterDom == NULL) {
        if (fReportIrregArrayAccesses) {
          printf("\t\t- !!! could not find index iterator %s's domain symbol; cannot apply optimization\n", sym->name);
        }
        forall->optInfo.cloneTypeIE = INVALID_OPT;
        removeOptimizationIE(forallID, NULL);
        return;
      }
    } /* end of if iterType */

    // 5.2) Now we can track modifications to the iterator.
    if (iterDom == NULL) {
      aliasesAnalyzed.clear();
      aliasesAnalyzed[sym] = true;
      findAllModificationsToSymbol(sym,
                                   forall->parentExpr,
                                   modifications,
                                   aliasesAnalyzed,
                                   aliasSymbols,
                                   false,
                                   NULL);
    }
    else {
      aliasesAnalyzed.clear();
      aliasesAnalyzed[iterDom] = true;
      findAllModificationsToSymbol(iterDom,
                                   forall->parentExpr,
                                   modifications,
                                   aliasesAnalyzed,
                                   aliasSymbols,
                                   isRecFieldIterSym,
                                   atIterSym);
    }

  } /* end of for (auto &elem) */

  // Now we can clean up the aliasSymbols map. We may have
  // something like call_tmp is an alias to A, and FOO is an alias
  // to call_tmp. This should just be represented as FOO and call_tmp
  // are aliases to A.
  // TODO: we currently do not use aliasSymbolsCleaned for any analysis.
  // We created it in preparation of more call path analysis but opted not
  // to do that for now.
  //
  //std::map<Symbol *, std::set<Symbol *>> aliasSymbolsCleaned;
  //cleanUpAliasSymbols(aliasSymbols, aliasSymbolsCleaned);

  // 6.) Now we look at our modifications and detect invalid ones. No modifications
  //     to any of the symbols can be within the forall loop. No modifications to
  //     the symbols can be directly before ("outside") of the forall loop, with
  //     the exception of A.
  bool allowWrites = gFieldPositionsIE.count(forallID) > 0;
  if (isSymbolModifiedInForall(forall, modificationsAOnly, allowWrites) ||
      isSymbolModifiedInForall(forall, modifications, false)) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t- !!! Invalid modification to an array/domain detected in forall; optimization is INVALID\n");
      forall->optInfo.cloneTypeIE = INVALID_OPT;
      removeOptimizationIE(forallID, NULL);
      return;
    }
  }
  if (isSymbolModifiedBeforeForall(forall, modifications)) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t- !!! Invalid modification to an array/domain detected outside of forall; optimization is INVALID\n");
      forall->optInfo.cloneTypeIE = INVALID_OPT;
      removeOptimizationIE(forallID, NULL);
      return;
    }
  }

  if (fReportIrregArrayAccesses) {
    printf("\t\t- $$$ Optimization is VALID\n");
    printf("\t\t- Adding calls to inspectorOn() after modifications to arrays/domains of interest\n");
    // Only thing we don't add a call to inspectorOn is A.
  }
  turnInspectorOnAfterModifcations(forall, modifications);

} /* end of executeAccessCallPostAnalysis */

//##################################################################################
/*
    Given the Symbol for an array, attempt to find the Symbol for its domain.
    We need the array's domain symbol so we can track modifications to it. If the
    array's domain changes, we need to make sure it isn't within the forall loop
    (for A and B) or just outside the forall (for B). For any valid changes to
    the domain, we'll insert calls to inspectorOn() after it in a later step.

    Our approach here is to work back from the array and recognize the AST
    that is produced for var arr : [DD] type. This can start off differently
    if the array is split-initialized (i.e., var arr : [DD]; arr = 1). The
    details below will explain

    If the array is not split-initialized, we'll see a PRIM_MOVE into
    "arr" where the RHS is a call to chpl__convertRuntimeTypeToValue.
    What we want to extract is the first argument to this call.

    If the array is split-initialized, we'll see a PRIM_MOVE into
    "arr" where the RHS is a init_coerce_tmp SymExpr. If we have
    this case, we need to look at all SymExprs related to the
    init_coerce_tmp symbol. What we will look for is a PRIM_MOVE
    into init_coerce_tmp where the RHS is a call to chpl__coerceCopy.
    What we want to get is the first argument to this call.

    At this point, whether we have split-initialization or not, we have
    a Symbol to move onto the next step. Call this firstSym.

    If we had split initialization, we skip this step. Otherwise, we
    are looking for a PRIM_MOVE into firstSym where the RHS is a call
    to .v, which is PRIM_GET_MEMBER_VALUE. What we want to get is the
    first argument to this call.

    Consider the symbol we have now as secondSym. If we had split
    initialization, secondSym is the same as firstSym. From here on
    out, the steps are the same for both cases.

    The next step is to look for a PRIM_MOVE into secondSym where
    the RHS is a call to chpl__buildArrayRuntimeType. We extract
    the 1st argument to this call and refer to it as thirdSym.

    Lastly, we look for a PRIM_MOVE into thirdSym where the RHS is
    a call to chpl__ensureDomainExpr. The 1st argument to this call
    is our domain symbol.

    Before we start all of the above steps, we check whether the
    Symbol arr is a formal to a function. If that is the case, we
    call this function recursively for the actual at each call
    site.

    We also check whether the Symbol is a reference to something
    like rec.field. In that case, we'll call this function recursively
    on the field Symbol.

    Arguments:
    arr -> the array to find the domain for
    expr -> starting Expr for when we look to see if we are in a function
    isRecordField -> set to true if we determine that arr is a ref to a record field
    aliasesAnalyzed -> keeps track of the aliases we've analyzed
    at -> stores the record type if array is a ref to a record field.

    Return:
    the Symbol of the domain, or NULL if we can't find it
*/
static Symbol *domainSymbolForArray(Symbol *arr,
                                    Expr *expr,
                                    bool &isRecordField,
                                    std::map<Symbol *, bool> &aliasesAnalyzed,
                                    AggregateType *&at)
{
  // Added arr to the aliasesAnalyzed map so we don't infinitely recurse
  aliasesAnalyzed[arr] = true;

  Symbol *retval = NULL;
  bool isSplitInit = false;
  isRecordField = false;

  // If arr is something like "ref arr = r.field", then we
  // want to get the domain symbol corresponding to field.
  // During normalization, we computed a map of AggregateTypes
  // to another map of array-field-positions to the corresponding
  // domain-field-position. So use the AggregateType that
  // isSymbolRecordField populates as a look-up into the map
  // and then find the array field that corresponds to fieldSym
  // (also populated by isSymbolRecordField).
  Symbol *fieldSym = NULL;
  at = NULL;
  if (isSymbolRecordField(arr, fieldSym, at)) {
    if (gArrFieldsToDomFields.count(at)) {
      isRecordField = true;
      // If we started with an array, get its domain symbol via
      // the gArrFieldsToDomFields map
      if (arr->getValType()->symbol->hasFlag(FLAG_ARRAY)) {
        std::map<int,int> fieldLocs = gArrFieldsToDomFields[at];
        for(auto& elem : fieldLocs) {
          Symbol *tmp1 = at->getField(elem.first);
          if (tmp1 == fieldSym) {
            Symbol *sym = at->getField(elem.second);
            return sym;
          }
        }
      }
      else {
        // Else, arr is a domain, so we just use fieldSym
        return fieldSym;
      }
    }
    else {
      return NULL;
    }
  }

  compute_call_sites();

  // If arr is a formal, call this function on the
  // actual at each call site
  if (ArgSymbol* arg = toArgSymbol(arr->defPoint->sym)) {
    for (Expr* curr = expr->parentExpr; curr; curr = curr->parentExpr) {
      if (FnSymbol *fn = toFnSymbol(curr->parentSymbol)) {
        int argPos = -1, currPos = 0;
        for_alist(formal, fn->formals) {
          if(ArgSymbol* arg1 = toArgSymbol(toDefExpr(formal)->sym)) {
            if (arg1 == arg) {
              argPos = currPos;
              break;
            }
          }
          currPos++;
        }
        INT_ASSERT(argPos != -1);
        forv_Vec(CallExpr, fnCall, *fn->calledBy) {
          Symbol *callSiteArr = toSymExpr(fnCall->get(argPos+1))->symbol();
          return domainSymbolForArray(callSiteArr, (Expr *)fnCall, isRecordField, aliasesAnalyzed, at);
        }
      }
      break;
    }
  }

  // Before we start looking for the specific pattern, let's see if we
  // have an alias situation, like ref arr = FOO. If so, we'll want to
  // look for FOO's domain.
  // Problem is that the call to detectAliasesInCall will trigger on case
  // 4 but we don't want that to happen. Quick work-around is to pass in a flag
  // that does not do that check.
  for_SymbolSymExprs(symexpr, arr) {
    if (isCallExpr(symexpr->parentExpr)) {
      CallExpr *symCall = toCallExpr(symexpr->parentExpr);
      if (symCall->isPrimitive(PRIM_MOVE) || symCall->isPrimitive(PRIM_ADDR_OF)) {
        Symbol *alias = detectAliasesInCall(symCall, symexpr, false);
        if (alias != NULL && !aliasesAnalyzed.count(alias)) {
          aliasesAnalyzed[alias] = true;
          return domainSymbolForArray(alias, expr, isRecordField, aliasesAnalyzed, at);
        }
      }
    }
  }

  // 1.) Look for the PRIM_MOVE into arr
  // where the RHS is a call to chpl__convertRuntimeTypeToValue.
  // But we may have split initialization, which looks different.
  // If that is the case, isSplitInit will be set to true. But we also
  // need to consider that we have an alias, like ref arr = foo. In that
  // case, we need to call this function recursively on foo.
  Symbol *firstSym = NULL;
  for_SymbolSymExprs(symexpr, arr) {
    firstSym = getFuncFirstArg(symexpr, "chpl__convertRuntimeTypeToValue", &isSplitInit);
    if (firstSym) {
      break;
    }
  } /* end of for_SymbolSymExprs(symexpr, arr) */

  if (firstSym == NULL) {
    return NULL;
  }

  // 2.) If we had split-initialization, we skip this step. Otherwise,
  // we look for the call to PRIM_GET_MEMBER_VALUE
  Symbol *secondSym = NULL;
  if (isSplitInit == false) {
    for_SymbolSymExprs(symexpr, firstSym) {
      secondSym = getFuncFirstArg(symexpr, PRIM_GET_MEMBER_VALUE);
      if (secondSym) {
        break;
      }
    }
  }
  else {
    secondSym = firstSym;
  }

  if (secondSym == NULL) {
    return NULL;
  }

  // 3.) Now we do the same pattern as we have been doing thus far but
  // to look for a call to chpl__buildArrayRuntimeType
  Symbol *thirdSym = NULL;
  for_SymbolSymExprs(symexpr, secondSym) {
    thirdSym = getFuncFirstArg(symexpr, "chpl__buildArrayRuntimeType", NULL);
    if (thirdSym) {
      break;
    }
  }

  if (thirdSym == NULL) {
    return NULL;
  }

  // 4.) Finally, our domain symbol will be the first argument to
  // chpl__ensureDomainExpr
  for_SymbolSymExprs(symexpr, thirdSym) {
    retval = getFuncFirstArg(symexpr, "chpl__ensureDomainExpr", NULL);
    if (retval) {
      break;
    }
  }

  return retval;
} /* end of domainSymbolForArray */

//##################################################################################
/*
    Given a Symbol sym, find all modifications (i.e., writes) to sym.

    There are a few tricks that we do here that are pretty important. We will find
    all modifications to sym in its scope, but also detect if sym is a formal to
    function. In that case, we'll look at all call sites of the function and look
    for modifications to the actual/argument to the call. This is recursive.
    Our starting point is the forall loop that is assumed to be the inspector loop.
    We have the Symbol that corresponds to either A or B in A[B[i]]. For each
    recursive call we make, expr will refer to the CallExpr (call site) of the
    function.

    We also detect alias chaining. If sym is a reference to something, we'll track
    modifications to whatever it is referencing. We can do this for however many
    chains/nests we have.

    Finally, we can detect the case of sym = rec.foo. In that case, what we
    want to track are modifications to the field "foo" within the record.

    The alias detection is done in detectAliasesInCall(). To avoid infinite recursion,
    the aliasesAnalzyed map keeps track of which aliases (Symbols) we've processed.

    Arguments:
    sym ->  the Symbol to analyze
    expr -> the Expr that we work backwards from
    modifications -> map that stores the writes we find
    aliasesAnalyzed -> map used to track which aliases we have analyzed
    aliasSymbols -> map to store the aliases and where they "came" from
    isRecordField -> true if sym is the field of a record, false otherwise.
                     This only applies when we call this on the array's domain symbols
    at -> the record type if isRecordField is true.

    Return:
    None; modifications map is updated.
*/
static void findAllModificationsToSymbol(Symbol *sym,
                                         Expr *expr,
                                         std::map<Symbol *, std::map<CallExpr *, bool>> &modifications,
                                         std::map<Symbol *, bool> &aliasesAnalyzed,
                                         std::map<Symbol *, std::set<Symbol *>> &aliasSymbols,
                                         bool isRecordField,
                                         AggregateType *at)
{
  // If isRecordField is true, then sym is the Symbol for a record field. This
  // would only be true for the cases when we call this with one of the array's
  // domain symbols. What we do is find the field accessor function for the
  // symbol and track modifications to the LHS of the calls to that function.
  // If isRecordField is not true, then we may still have something like
  // "ref sym = r.arr". The call to isSymbolRecord will determine this and
  // return arr's field accessor. If either of these cases happen, then
  // fieldFn is non-NULL and we can proceed in the same way.
  FnSymbol *fieldFn = NULL;
  if (isRecordField && at != NULL) {
    forv_Vec(FnSymbol, method, at->methods) {
      if (method != NULL) {
        if (method->hasFlag(FLAG_FIELD_ACCESSOR)) {
          if (method->name == sym->name) {
            fieldFn = method;
            break;
          }
        }
      }
    }
  }
  else {
    Symbol *dummy;
    AggregateType *dummyAT;
    fieldFn = isSymbolRecordField(sym, dummy, dummyAT);
  }
  if (fieldFn) {
    forv_Vec(CallExpr, fnCall, *fieldFn->calledBy) {
      if (CallExpr *parentCall = toCallExpr(fnCall->parentExpr)) {
        // Make sure it's a move
        if (parentCall->isPrimitive(PRIM_MOVE)) {
          // 1st arg is the LHS
          Symbol *lhs = (toSymExpr(parentCall->get(1)))->symbol();
          // Look for modifications to lhs
          findAllModificationsToSymbol(lhs, parentCall, modifications, aliasesAnalyzed, aliasSymbols, false, at);
        }
      }
    }
  }

  // If we aren't dealing with fields of records, look at all SymExprs for
  // sym in the current scope. We can see as far back until we hit a function
  // definition. So after this loop, we'll see whether we are in a function body
  // and if sym is a formal.
  for_SymbolSymExprs(symexpr, sym) {
    // All writes will be CallExprs that take in arr as an argument
    if (isCallExpr(symexpr->parentExpr)) {
      CallExpr *symCall = toCallExpr(symexpr->parentExpr);
      if (isCallExprValid(symCall)) {
        ArgSymbol *formal = actual_to_formal(symexpr);
        // the intent will tell us whether we are looking at a write
        if (formal->intent == INTENT_REF || formal->intent == INTENT_REF_MAYBE_CONST) {
          modifications[sym][symCall] = true;
        }
      }
      // See whether we have an alias in this symCall. If so, and we haven't processed
      // that alias, find all modifications to the alias.
      Symbol *alias = detectAliasesInCall(symCall, symexpr, true);
      if (alias != NULL && !aliasesAnalyzed.count(alias)) {
        aliasSymbols[sym].insert(alias);
        aliasesAnalyzed[alias] = true;
        findAllModificationsToSymbol(alias, expr, modifications, aliasesAnalyzed, aliasSymbols, false, at);
      }
    }
    else {
      // some cases have NULL parentExprs, like shadow variables.
      if (symexpr->parentExpr != NULL) {
        INT_FATAL(symexpr, "unknown case");
      }
    }
  }

  // Is sym an argument to a function (i.e., a formal)?
  if (ArgSymbol* arg = toArgSymbol(sym->defPoint->sym)) {
    // Walk backwards to get the FnSymbol
    for (Expr* curr = expr->parentExpr; curr; curr = curr->parentExpr) {
      if (FnSymbol *fn = toFnSymbol(curr->parentSymbol)) {
        // fn is the FnSymbol where arg is the formal.
        // Determine the argument position of arg
        int argPos = -1, currPos = 0;
        for_alist(formal, fn->formals) {
          if(ArgSymbol* arg1 = toArgSymbol(toDefExpr(formal)->sym)) {
            if (arg1 == arg) {
              argPos = currPos;
              break;
            }
          }
          currPos++;
        }
        INT_ASSERT(argPos != -1);
        // Call this function recursively for each call site.
        // We pass in the Symbol for the argument arr to each
        // call site.
        forv_Vec(CallExpr, fnCall, *fn->calledBy) {
          Symbol *callSiteArr = toSymExpr(fnCall->get(argPos+1))->symbol();
          findAllModificationsToSymbol(callSiteArr, (Expr *)fnCall, modifications, aliasesAnalyzed, aliasSymbols, false, at);
        }
        break;
      }
    }
  }

} /* end of findAllModificationsToSymbol */


//##################################################################################
/*
    Given a CallExpr call and a SymExpr symexpr that is an argument to call, check
    for specific cases of aliasing.

    We call this from findAllModificationsToSymbol() and we want to check for the
    following cases, assuming we are looking at A[B[i]] and B is the symbol we
    want to track modifications to:

    1.) ref B = rec.arr
        ... A[B[i]] ...

    In this case, we want to see that B is a reference to a record field and
    find modifications to the field arr within the record rec.

    2.) ref B = foo;
        ... A[B[i]] ...

    In this case, we want to see that B is a reference to another array and
    find the modifications to that array (foo).

    3.) ref foo = bar;
        ref B = foo;
        ... A[B[i]] ...

    In this case, B is a reference to another reference. So we follow the chain
    up, analyzing each alias we find.

    4.) ref foo = B;
        foo = ...

    In this case, foo gets a reference to B and foo is modified. So we want to
    track changes to foo.

    5.) ref b = B[0..2]
        b = ...

    In this case, we need to detect getting a ref to a slice of B and writing
    to that ref. We first need to recognize the pattern that is used to "use"
    the slice to access B. From there, we look up to ensure we find the
    call to chpl_build_bounded_range.

    Some of these cases are subsets of each other. But depending on which "part"
    we are analyzing, they'll look different. So we need to handle them differently.

    Arguments:
    call -> the CallExpr to analyze
    symexpr -> the SymExpr that is an argument to call
    checkBase4 -> set to false if we should ignore the 4th case. This is the case
                  when this is called from domainSymbolForArray().

    Return:
    the Symbol of the alias if we found one, NULL otherwise.
*/
static Symbol *detectAliasesInCall(CallExpr *call,
                                   SymExpr *symexpr,
                                   bool checkCase4)
{
  Symbol *retval = NULL;
  // case 1:
  // This looks like "move B, rec.arr"
  // symCall is the PRIM_MOVE and symexpr is referring to rec.arr,
  // which is a call_tmp that was created to refer to rec.arr.
  if (call->isPrimitive(PRIM_MOVE)) {
    // is symexpr 2nd arg
    if (symexpr == toSymExpr(call->get(2))) {
      // first arg is an alias (B) so we should analyze it
      // iff it is a ref
      Symbol *sym = (toSymExpr(call->get(1)))->symbol();
      if (sym->hasFlag(FLAG_REF_VAR)) {
        retval = (toSymExpr(call->get(1)))->symbol();
      }
    }
    // case 2:
    // This looks like "move B, (addr of foo)"
    // symCall is the PRIM_MOVE and symexpr is referring to B
    if(symexpr == toSymExpr(call->get(1))) {
      // Check for the PRIM_ADDR_OF call as the 2nd arg to PRIM_MOVE
      CallExpr *addrOfCall = toCallExpr(call->get(2));
      if (addrOfCall != NULL && addrOfCall->isPrimitive(PRIM_ADDR_OF)) {
        // look for modifications to the first arg of PRIM_ADDR_OF (B)
        retval = (toSymExpr(addrOfCall->get(1)))->symbol();
      }
      // case 3:
      // This looks like "move B, foo" where B and foo are refs
      else if (call->numActuals() == 2) {
        SymExpr *argSymExpr1 = toSymExpr(call->get(1));
        SymExpr *argSymExpr2 = toSymExpr(call->get(2));
        if (argSymExpr1 != NULL && argSymExpr2 != NULL && !isCallExpr(argSymExpr1) && !isCallExpr(argSymExpr2)) {
          VarSymbol *arg1 = toVarSymbol(argSymExpr1->symbol());
          VarSymbol *arg2 = toVarSymbol(argSymExpr2->symbol());
          if (arg1->hasFlag(FLAG_REF_VAR) && arg2->hasFlag(FLAG_REF_VAR)) {
            retval = (toSymExpr(call->get(2)))->symbol();
          }
        }
      }
    } /* end of if symexpr == toSymExpr(symCall->get(1)) */
  } /* end of if (symCall->isPrimitive(PRIM_MOVE)) */

  // case 4:
  // This looks like "move foo, (addr of B)"
  else if (call->isPrimitive(PRIM_ADDR_OF) && checkCase4 == true) {
    // is parentExpr a PRIM_MOVE?
    CallExpr *parentCall = toCallExpr(call->parentExpr);
    if (parentCall != NULL && parentCall->isPrimitive(PRIM_MOVE)) {
      // 1st arg is the alias
      retval = (toSymExpr(parentCall->get(1)))->symbol();
    }
  }

  // case 5:
  // This has a few steps involve, starting with call being a call to
  // this() and the parent of call is a move. The last argument to this()
  // will be a call_tmp; this is the index/expression used to access the
  // array. We look at SymExprs for the call_tmp and look for the case
  // where we have a move into the call_tmp and the RHS is a call to
  // chpl_build_bounded_range.
  else if (call->isNamed("this")) {
    if (CallExpr *parentCall = toCallExpr(call->parentExpr)) {
      if (parentCall->isPrimitive(PRIM_MOVE)) {
        // Get the last arg to this()
        Symbol *indexArg = (toSymExpr(call->get(call->argList.length)))->symbol();
        INT_ASSERT(indexArg != NULL);
        // Look for SymExprs involving indexArg. Specifically check for
        // moves into indexArg that call chpl_build_bounded_range
        for_SymbolSymExprs(symexpr, indexArg) {
          if (CallExpr *symCall = toCallExpr(symexpr->parentExpr)) {
            if (symCall->isPrimitive(PRIM_MOVE)) {
              CallExpr *rhs = toCallExpr(symCall->get(2));
              if (rhs != NULL) {
                if (rhs->isNamed("chpl_build_bounded_range")) {
                  retval = (toSymExpr(parentCall->get(1)))->symbol();
                  break;
                }
              }
            }
          }
        }
      }
    }
  }

  return retval;

} /* detectAliasesInCall */

//##################################################################################
/*
    Given a Symbol sym, determine whether it is "derived" from the field of a
    record. In other words, detect the following:

        ref sym = someRecord.field;

    If we find this, we return the FnSymbol for the field accessor function.
    We also populate the fielSym and at pointers, which correspond to the
    field's Symbol and the enclosing AggregateType.

    Arguments:
    sym -> the Symbol to analyze
    fieldSym -> pointer to the field's Symbol if we find it
    at -> pointer to the AggregateType that contains the field

    Return:
    The FnSymbol of the field accessor if we find one, NULL otherwise
*/
static FnSymbol *isSymbolRecordField(Symbol *sym,
                                     Symbol *&fieldSym,
                                     AggregateType *&at)
{
  Symbol *callTmpSym = NULL;
  for_SymbolSymExprs(symexpr, sym) {
    if (isCallExpr(symexpr->parentExpr)) {
      CallExpr *symCall = toCallExpr(symexpr->parentExpr);
      // ref sym = someRecord.field will be a PRIM_MOVE
      if (symCall->isPrimitive(PRIM_MOVE)) {
        // Ensure symexpr is the first arg
        if (symexpr == toSymExpr(symCall->get(1))) {
          // If the 2nd argument to the move is not a CallExpr,
          // then it is likely a call_tmp that we can do further
          // analysis on.
          if (!toCallExpr(symCall->get(2))) {
            Symbol *tmp = (toSymExpr(symCall->get(2)))->symbol();
            // TODO: crashes if the 2nd arg is not the call_tmp we
            // expect, but a ref var. But seems to work without it for now.
            //callTmpSym = (tmp->getSingleDef())->symbol();
            callTmpSym = tmp;
            break;
          }
        }
      }
    }
  }
  if (callTmpSym == NULL) {
    return NULL;
  }

  // Given the Symbol for call_tmp, look at its SymExprs and look
  // for those where the parent is a PRIM_MOVE call, call_tmp is the
  // first argument and the 2nd argument is a call to a field accessor.
  FnSymbol *fieldFn = NULL;
  for_SymbolSymExprs(symexpr, callTmpSym) {
    if (isCallExpr(symexpr->parentExpr)) {
      CallExpr *symCall = toCallExpr(symexpr->parentExpr);
      if (symCall->isPrimitive(PRIM_MOVE)) {
        // Ensure symexpr is first arg
        if(symexpr == toSymExpr(symCall->get(1))) {
          // Ensure 2nd arg is a call; this is the potential call to the field accessor
          if (CallExpr *fieldCall = toCallExpr(symCall->get(2))) {
            if (FnSymbol* targetFn = fieldCall->resolvedFunction()) {
              if (targetFn->hasFlag(FLAG_FIELD_ACCESSOR)) {
                at = toAggregateType(targetFn->getFormal(1)->getValType());
                fieldSym = at->getField(targetFn->name);
                INT_ASSERT(fieldSym->type == targetFn->retType->getValType());
                fieldFn = targetFn;
                break;
              }
            }
          }
        }
      }
    }
  }
  return fieldFn;

} /* end of isSymbolRecordField */

//##################################################################################
/*
    Once we have created the alias symbol map, which maps a Symbol to a set of
    symbols that are aliases, we can clean it up by "resolving" the alias chains.
    For example, the origAliases map may tell us that call_tmp is an alias to FOO,
    and FOO is an alias to A. For our purposes later, it will be easier if we just
    store the info that call_tmp is an alias to A.

    So this function processes the entries in origAliases and creates a new map
    with "cleaned up" aliases, newAliases.

    Arguments:
    origAliases -> original map of aliases
    newAliases -> new map of aliases that are "cleaned up"

    Return:
    None
*/
/*static void cleanUpAliasSymbols(std::map<Symbol *, std::set<Symbol *>> &origAliases,
                                std::map<Symbol *, std::set<Symbol *>> &newAliases)
{
  // 1.) Find the Symbols that are the "original" Symbols (i.e., they are not
  // aliases to other Symbols). To determine this, we look at each key K in origAliases and
  // see whether K appears in any of the sets within origAliases. If it does,
  // it means that K is an alias to something.
  for (auto &elem : origAliases) {
    Symbol *sym = elem.first;
    bool isAlias = false;
    for (auto &elem2 : origAliases) {
      if (elem2.second.count(sym) > 0) {
        isAlias = true;
        break;
      }
    }
    if (!isAlias) {
      // sym is an "original" symbol. Create an entry in
      // newAliases and add origAliases[sym]'s set of aliases to it.
      for (auto &alias : elem.second) {
        newAliases[sym].insert(alias);
      }
    }
  }
  // For every entry/key we added to newAliases, remove it from origAliases
  // so we don't attempt to process it in the steps below.
  for (auto &elem : newAliases) {
    origAliases.erase(elem.first);
  }

  // 2.) Now we know which Symbols are not derived from others (i.e., the
  // Symbols that are NOT aliases). Each of these original Symbols has their
  // "closest" aliases set in the newAliases map. So, for each of these closest
  // aliases, see whether they are entries in origAliases; this means that there
  // are Symbols derived from them. But we know that those aliases are actually
  // aliases to the original symbol. So add them to newAliases. If we added new
  // aliases, we want to repeat this process, in case those new aliases have aliases.
  // We repeat this for a given original symbol until there are no new aliases to
  // process.
  //
  // We do a first pass separately to "prime up" the newAliasesToProcess set and then
  // do a while-loop that runs until we are no more new aliases.
  for (auto &elem : newAliases) {
    std::set<Symbol *> newAliasesToProcess;
    Symbol *origSym = elem.first;
    // prime up newAliasesToProcess
    for (auto &alias : elem.second) {
      if (origAliases.count(alias) > 0) {
        // alias has aliases; but those alases are just aliases
        // to origSym. So add them to newAliases[origSym]. Since
        // we are iterating over that set here, add them to a temporary
        // set first.
        for (auto &otherAlias : origAliases[alias]) {
          newAliasesToProcess.insert(otherAlias);
        }
      }
    }
    // If we found other aliases, add them.
    for (auto &alias : newAliasesToProcess) {
      newAliases[origSym].insert(alias);
    }

    // Now, process each alias in newAliasesToProcess. Repeat
    // until that set is empty
    while (newAliasesToProcess.size() > 0) {
      std::set<Symbol *> tempset;
      for (auto &alias : newAliasesToProcess) {
        if (origAliases.count(alias) > 0) {
          for (auto &otherAlias : origAliases[alias]) {
            tempset.insert(otherAlias);
          }
        }
      }
      for (auto &alias : tempset) {
        newAliases[origSym].insert(alias);
      }
      newAliasesToProcess.swap(tempset);
    }
  }

}*/ /* end of cleanUpAliasSymbols */

//##################################################################################
/*
    Given a map of writes to a symbol and a forall loop (assumed to be the
    inspector loop), determine whether any writes made to the symbol are invalid
    In this function, this means that the symbol is modified in a statement
    that is within the forall. If we find such a case, we return false.

    The map of writes was computed via findAllModificationsToSymbol(). For
    any invalid writes we come across, we set their value to false in the map.

    There is a special case to consider, which is when the symbol we are analyzing
    is an array of records. In that case, we can write to the array as long as
    we are not writing to a field that is being replicated. We know the such
    fields via the gFieldPositionsIE map we built during pre-folding.
    TODO: Do not have this implemented yet, as it is sort of a nasty situation.
    For now, if A stores records, we allow for writes to A.

    Arguments:
    forall -> inspector forall loop
    modifications -> map that stores the writes to process
    allowWrites -> hack for now to allow writes to A when it stores records.

    Return:
    true if symbol is modified in the forall, false otherwise. We also
    modify modifications for each invalid write we find.
*/
static bool isSymbolModifiedInForall(ForallStmt *forall,
                                     std::map<Symbol *, std::map<CallExpr *, bool>> &modifications,
                                     bool allowWrites)
{
  bool retval = false;
  for (auto &elem : modifications) {
    // For every modification involing sym...
    for (auto &mods : elem.second) {
      CallExpr *mod = mods.first;
      // does forall contain the modification?
      if (doesExprContainExpr(mod, forall) && !allowWrites) {
        retval = true;
        mods.second = false; // invalid write
      }
    }
  }
  return retval;
} /* end of isSymbolModifiedInForall */

//##################################################################################
/*
    For a Symbol sym (let's call it B), check whether it is modified "before" the
    forall. At this point in the analysis, we know we have the following structure
    (more or less):

        ....
        for it in NUM_ITERS {
            ....
            forall i in 0..#N {
                ...A[B[i]]...
            }
            ....
        }
        ....

    We do this for each Symbol in modifications, which is a map of Symbols to
    CallExprs (the modification).

    To put it into words, we know that the forall is enclosed in at least one outer
    for-loop. That is key, since it means the forall is executed more than once, which
    allows for the inspector loop to be amortized over multiple executions of the
    optimized executor loop.

    However, the optimization will be invalid if B is written to within the for-loop
    above. Specifically, if B is written to in such a way that the write happens before/after
    each execution of the forall, then the inspector loop would need to be ran everytime.
    That is a non-starter for the optimization.

    What we do is find the enclosing for-loop for the forall and then look at all modifications
    to B. For each modification, we check whether it is within the for-loop. If a write
    is contained in the for-loop, then the optimization is not valid.

    The map modifications contains all modifications to B, across all call sites if B
    was a formal to a function (i.e., if the inspector loop was inside of a function).
    The map holds a value of true if the write is valid thus far, and false otherwise.

    In our case, sym (B) is an array. If we had something like ref B = someRec.arr, then
    we also found all modifications to the field arr. We also find modifications to any
    aliases that B was derived from (i.e., ref B = foo).

    Arguments:
    forall -> the forall that is assumed to be the inspector loop
    modifications -> map of writes/modifications to the array

    Return:
    true if the array is modified before the forall, false otherwise.
    The modifications map is also updated for each invalid write we find.
*/
static bool isSymbolModifiedBeforeForall(ForallStmt *forall,
                                         std::map<Symbol *, std::map<CallExpr *, bool>> &modifications)
{
  // Get the enclosing (closest) serial loop that contains the forall
  compute_call_sites();
  Expr *loop = findEnclosingSerialLoop(forall->parentExpr);
  INT_ASSERT(loop != NULL);

  // Look at each modifications. If the modification is within the
  // loop, then it is invalid. We ignore modifications to A,
  // since those are OK.
  bool retval = false;
  for (auto &elem : modifications) {
    for (auto &mods : elem.second) {
      CallExpr *mod = mods.first;
      // ignore/skip if this is a call to prefetch or prefetchIter
      if (mod->isNamed("prefetch") || mod->isNamed("prefetchIter")) {
        continue;
      }
      bool isValidMod = mods.second;
      if (isValidMod) { // modification is valid thus far
        if (doesExprContainExpr(mod, loop)) {
          retval = true;
          mods.second = false; // invalid write.
        }
      }
    }
  }
  return retval;
} /* end of isSymbolModifiedBeforeForall */

//##################################################################################
/*
    Add calls to ieObj.inspectorOn() after each modification (CallExpr) in the
    modifications map if it has been marked as a valid modification. These
    specifically correspond to writes to B from A[B[i]] that we optimized,
    which are also gathered from across call sites if forall is part of
    a function where B was an argument.

    This is a somewhat naive approach, as we only need to insert the call after
    the write to B that is "closest" to the forall loop of interest. I am not
    sure how to do that just yet, so we will just add the calls after all the
    valid writes.

    There is a special case we want to handle, which is when the write to B
    is performed inside of a loop that is NOT the loop which contains the
    forall. So something like:

        forall i in B.domain {
            B[i] = ...
        }

    In this case, we do not want to insert the call to inspectorOn() in
    the loop. Rather, we want it to be inserted after the loop. This
    applies to for loops, forall loops, etc.

    Arguments:
    forall -> the forall loop of interest (assumed to be the inspector loop)
    modifications -> map of modifications/writes to the array

    Return:
    None
*/
static void turnInspectorOnAfterModifcations(ForallStmt *forall,
                                             std::map<Symbol *, std::map<CallExpr *, bool>> &modifications)
{
  VarSymbol *ieFlag = forall->optInfo.inspectorFlag;
  INT_ASSERT(ieFlag != NULL);
  // Process each valid write
  for (auto &elem : modifications) {
    for (auto &mods : elem.second) {
      CallExpr *mod = mods.first;
      bool isValidMod = mods.second;
      if (isValidMod == false) {
        continue; // skip invalid writes; shouldn't be any though
      }
      insertCallToInspectorOn(ieFlag, mod, forall);
    }
  }
} /* end of turnInspectorOnAfterModifcations */


//##################################################################################
/*
    Attempts to insert a call to inspectorOn(ieFlag) after the specified CallExpr.
    It is assumed that the CallExpr is a valid write/modification to the sym.

    We do some checks here to see if the CallExpr is within a loop, as we do
    something different in that case (see insertInspectorOnAfterLoop()).

    Arguments:
    ieFlag -> VarSymbol for the InspectorFlag object
    mod -> the modification (CallExpr) to process
    forall -> the forall loop of interest

    Return:
    None
*/
static void insertCallToInspectorOn(VarSymbol *ieFlag,
                                    CallExpr *mod,
                                    ForallStmt *forall)
{
  // Create the call to inspectorOn(). This is a procedure we
  // added to the "well known" functions and have done a couple
  // tricks so we can call it post-resolution without issues.
  CallExpr *ieOn = new CallExpr(gInspectorOn, ieFlag);
  BlockStmt *dummyBlock = new BlockStmt();
  dummyBlock->insertAtTail(ieOn);

  int retval = false;

  // Is the write inside of a loop of any kind?
  if (Expr *loop = findEnclosingLoop(mod)) {
    retval = insertInspectorOnAfterLoop(loop, forall, dummyBlock, ieFlag);
  }

  // If mod is not in a loop, or we did not insert after the loop,
  // then we want to add the call after the mod. But there is a case
  // we need to handle differently, which is when we are dealing with a mod
  // that is a field-of-record access. In that case, we insert
  // after mod's parentExpr.
  if (retval == NOT_INSERTED) {
    CallExpr *insertPoint = NULL;
    // Handle field-of-record access
    if (CallExpr *modParentCall = toCallExpr(mod->parentExpr)) {
      if (modParentCall->isPrimitive(PRIM_MOVE)) {
        insertPoint = modParentCall;
      }
    }
    if (insertPoint != NULL) {
      insertPoint->insertAfter(dummyBlock);
    }
    else {
      mod->insertAfter(dummyBlock);
    }
  }

  // Finally, normalize, resolve and flatten, only if
  // we didn't already insert
  if (retval != ALREADY_INSERTED) {
    normalize(dummyBlock);
    resolveBlockStmt(dummyBlock);
    dummyBlock->flattenAndRemove();
  }

} /* end of insertCallToInspectorOn */

//##################################################################################
/*
    Insert a call to inspectorOn(ym after a loop. This is just a bit of
    refactoring/clean-up for insertCallToInspectorOn().

    We do not always do the insert. If the loop contains the forall, then we do
    not want to insert after the loop. To see why, consider the following:

        for it in 0..#NUM_ITERS {
            for n in 0..#N {
                forall i in B.domain {
                    ... A[B[i]] ...
                }
            }
            B = ...
        }

    In this case, we'd see that B is written to within a for-loop (the outermost one).
    If we were to insert the call to inspectorOn() outside of that for-loop, then
    the call would only trigger after the outer-loop has ran all of its iterations.
    That is incorrect, as what we want is to turn the inspector on after each iteration
    of the outer-loop. That way, we re-run the inspector appropriately.

    We also check whether inspectorOn(ieFlag) has been already inserted after the loop.
    That can happen when multiple modifications to B are made in the same loop. There's
    no need to add multiple calls. In that case, we return ALREADY_INSERTED

    Arguments:
    loop -> loop to insert after
    forall -> forall of interest
    dummyBlock -> BlockStmt that contains the call to inspectorOn
    ieFlag -> InspectorFlag object tied to this optimization

    Return:
    NOT_INSERTED, INSERTED or ALREADY_INSERTED
*/
static int insertInspectorOnAfterLoop(Expr *loop,
                                      ForallStmt *forall,
                                      BlockStmt *dummyBlock,
                                      VarSymbol *ieFlag)
{
  // Does loop contain forall? If so, we DO NOT want to
  // insert the call after loop.
  if (doesExprContainExpr(forall, loop)) {
    return NOT_INSERTED;
  }

  // ####### Forall Loops #######
  if (ForallStmt *fs = toForallStmt(loop)) {
    if (!isInspectorOnCall(fs->next, ieFlag)) {
      fs->insertAfter(dummyBlock);
      return INSERTED;
    }
    else {
      return ALREADY_INSERTED;
    }
  }

  // ####### For Loops #######
  if (ForLoop *f = toForLoop(loop)) {
    // this for-loop may be part of a forall loop's
    // follower. If that is the case, we want to insert after
    // the forall, not the for
    Symbol *loopIter = f->iteratorGet()->symbol();
    if (strcmp(loopIter->name, "chpl__followIter") == 0) {
      if (ForallStmt *fs = enclosingForallStmt(f)) {
        if (!isInspectorOnCall(fs->next, ieFlag)) {
          fs->insertAfter(dummyBlock);
          return INSERTED;
        }
        else {
          return ALREADY_INSERTED;
        }
      }
    }
    else {
      if (!isInspectorOnCall(f->next, ieFlag)) {
        f->insertAfter(dummyBlock);
        return INSERTED;
      }
      else {
        return ALREADY_INSERTED;
      }
    }
  } /* end of if ForLoop */

  // ####### While Loops #######
  if (WhileStmt *ws = toWhileStmt(loop)) {
    if (!isInspectorOnCall(ws->next, ieFlag)) {
      ws->insertAfter(dummyBlock);
      return INSERTED;
    }
    else {
      return ALREADY_INSERTED;
    }
  }

  // Should never get to this point
  INT_FATAL(loop, "unsupported loop type");

  return NOT_INSERTED;

} /* end of insertInspectorOnAfterLoop */

//##################################################################################
/*
    Given an Expr, see whether it is a call to inspectorOn() that uses the same
    ieObj Symbol provided to this function. We call this function before
    inserting a call to inspectorOn() in turnInspectorOnAfterModifcations().
    If a loop has multiple writes to a given array B, we do not need to
    insert multiple calls to inspectorOn(). In that case. expr is
    loop->next.

    Arguments:
    expr -> the Expr to analyze
    ieFlag -> the InspectorFlag object to match on

    Return:
    true if expr is the call, false otherwise
*/
static bool isInspectorOnCall(Expr *expr,
                              VarSymbol *ieFlag)
{
  if (CallExpr *ieOnCall = toCallExpr(expr)) {
    if (FnSymbol *ieOnFn = ieOnCall->theFnSymbol()) {
      if (ieOnFn->hasFlag(FLAG_INSPECTOR_ON)) {
        if (Symbol *symTmp = (toSymExpr(ieOnCall->get(1)))->symbol()) {
          if (symTmp == ieFlag) {
            return true;
          }
        }
      }
    }
  }
  return false;
} /* end of isInspectorOnCall */

//##################################################################################
/*
    Given a CallExpr call that is the call to executeAccess() in some executor
    forall loop, perform call-path analysis to properly set the "hasOuterLoop"
    and "hasInvalidEnclosingStructure" flags. These will are checked on a per-function
    basis, where if they control whether the optimized forall is executed. As such,
    this only applies when the forall is inside of a function (that isn't the module
    init).

    Arguments:
    call -> the CallExpr within the forall of interest
    forallProcessed -> tells us whether a given forall has been processed already

    Return:
    None
*/
static void dynamicCallPathAnalysisIE(CallExpr *call,
                                      std::map<int, bool> &forallProcessed)
{
  // 1.) Get a handle to the enclosing forall. We use that to tell us
  //     things about the enclosing function.
  ForallStmt *forall = enclosingForallStmt(call);
  INT_ASSERT(forall != NULL);
  int forallID = forall->optInfo.ieID;
  if (forallProcessed.count(forallID) > 0) {
    // already processed
    return;
  }
  // First time processing this forall
  forallProcessed[forallID] = true;
  // Don't bother if this forall is not longer valid or it is not
  // in a function
  if (forall->optInfo.cloneTypeIE == INVALID_OPT || forall->optInfo.functionID == NOT_IN_FUNCTION) {
    return;
  }

  if (fReportIrregArrayAccesses) {
    printf("\t- Processing forall at %s\n", forall->stringLoc());
  }

  // 2.) Get the FnSymbol for the enclosing function
  FnSymbol *fn = getEnclosingFunction(forall);
  INT_ASSERT(fn != NULL);

  // 3.) Now that we have the function and we know the forall inside is valid, do the
  //     call path analysis. Essentially, look at the call sites of the function. Check
  //     for outer loops around the call sites or invalid enclosing structures (forall, coforall, etc.).
  //     Once we identify the proper places, add calls to set/unset the call path flags.
  //     We keep track of two things: the AST nodes to add calls around to set/unset the hasOuterLoop flag
  //     and the AST nodes to add calls around to set/unset the hasInvalidEnclosingStructure flag.
  //     These two sets will be populated by findLocationsForCallPathFlags(). We use sets so we can
  //     automatically ignore duplicates.
  std::set<Expr *>hasOuterLoopLocs;
  std::set<Expr *>hasInvalidEnclosingStructureLocs;
  compute_call_sites();
  findLocationsForCallPathFlagsIE(fn,
                                  forall->getModule()->initFn,
                                  hasOuterLoopLocs,
                                  hasInvalidEnclosingStructureLocs,
                                  NULL,
                                  NULL);

  // How to know that we don't have any valid paths? Clearly if
  // we didn't find any outer loops, that is invalid. But for every
  // outer loop we found, we could have also found an invalid structure
  // on that path. For now, only handle the case mentioned. This isn't a
  // huge deal, as for an invalid path we will not do the optimization due
  // to the isCallPathValid() check. It just would be nice to statically
  // clean up the optimization when we know it'll never happen.
  if (hasOuterLoopLocs.size() == 0) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t- !!! all call paths to forall at %s are invalid\n", forall->stringLoc());
    }
    forall->optInfo.cloneTypeIE = INVALID_OPT;
    removeOptimizationIE(forallID, fn);
    return;
  }

  if (fReportIrregArrayAccesses) {
    printf("\t\t- Inserting calls to set/unset call-path flags at runtime for forall at %s\n", forall->stringLoc());
  }
  // Now we have locations of where to insert the set/unset calls for this function.
  //
  // Add calls for the hasOuterLoop flag. We inser the set call before each expression
  // and the unset call after each expression. In this case, each expression is a loop.
  for (auto &expr : hasOuterLoopLocs) {
    CallExpr *setHasOuterLoopCall = new CallExpr(gSetHasOuterLoop, new_IntSymbol(forall->optInfo.functionID));
    CallExpr *unsetHasOuterLoopCall = new CallExpr(gUnsetHasOuterLoop, new_IntSymbol(forall->optInfo.functionID));
    BlockStmt *dummySet = new BlockStmt();
    dummySet->insertAtTail(setHasOuterLoopCall);
    BlockStmt *dummyUnset = new BlockStmt();
    dummyUnset->insertAtTail(unsetHasOuterLoopCall);
    expr->insertBefore(dummySet);
    expr->insertAfter(dummyUnset);
    normalize(dummySet);
    resolveBlockStmt(dummySet);
    dummySet->flattenAndRemove();
    normalize(dummyUnset);
    resolveBlockStmt(dummyUnset);
    dummyUnset->flattenAndRemove();
  }
  // Do the same but for the invalid enclosing structures
  for (auto &expr : hasInvalidEnclosingStructureLocs) {
    CallExpr *setHasInvalidStructureCall = new CallExpr(gSetHasInvalidEnclosingStructure, new_IntSymbol(forall->optInfo.functionID));
    CallExpr *unsetHasInvalidStructureCall = new CallExpr(gUnsetHasInvalidEnclosingStructure, new_IntSymbol(forall->optInfo.functionID));
    BlockStmt *dummySet = new BlockStmt();
    dummySet->insertAtTail(setHasInvalidStructureCall);
    BlockStmt *dummyUnset = new BlockStmt();
    dummyUnset->insertAtTail(unsetHasInvalidStructureCall);
    expr->insertBefore(dummySet);
    expr->insertAfter(dummyUnset);
    normalize(dummySet);
    resolveBlockStmt(dummySet);
    dummySet->flattenAndRemove();
    normalize(dummyUnset);
    resolveBlockStmt(dummyUnset);
    dummyUnset->flattenAndRemove();
  }

} /* end of dynamicCallPathAnalysisIE */

//##################################################################################
/*
    This function finds the locations that we want to insert call to set/unset the
    call path flags, hasOuterLoop and hasInvalidEnclosingStructure. It traverses
    the call graph starting from the initial value of the FnSymbol fn, which is
    the function that contains the forall of interest. For a given path, it
    looks for enclosing outer serial loops or invalid structures (forall, coforall, etc.).
    It notes that locations that are furthest from the function and will record those
    into the appropriate std::set. The reason for looking back as far as possible is
    to eliminate redudant calls to the set/unset methods. For example, if the function
    is nested in three outer loops, we only need to set the hasOuterLoop flag right
    before the outermost loop. Same goes for nested invalid structures.

    The actual setting/unsetting of the flags is performed in dynamicCallPathAnalysisIE();
    this function just does the call path analysis to find where they need to
    be inserted.

    This function is naturally recurisve. We do a Depth First Search (DFS)
    traversal of the call graph by looking at looking at a given FnSymbol's
    calledBy vector. We explore a call path until the only thing that calls
    the FnSymbol is either the module init function (modInitFn) or "chpl_gen_main"
    Once we hit that, we're at the end of the call path. It is at that point
    that we look at where (if there are any) our furthest outer loop and invalid
    structure was. Those get added to the appropriate sets.

    Arguments:
    fn -> The current function to analyze
    modInitFn -> The module init function to stop at
    hasOuterLoopLocs -> the Exprs where we want to add calls to set/unset the
                        hasOuterLoop flag (done later)
    hasInvalidEnclosingStructureLocs -> the Exprs where we want to add calls to
                                        set/unset the hasInvalidEnclosingStructure flag (done later)
    lastOuterLoop -> the last outer loop we found on the current call path
    lastInvalidStructure -> the last invalid structure we found on the current call path
*/
static void findLocationsForCallPathFlagsIE(FnSymbol *fn,
                                            FnSymbol *modInitFn,
                                            std::set<Expr *> &hasOuterLoopLocs,
                                            std::set<Expr *> &hasInvalidEnclosingStructureLocs,
                                            Expr *lastOuterLoop,
                                            Expr *lastInvalidStructure)
{
  // If fn is the modInitFn or chpl_gen_main, then we're done with
  // this particular call path. If lastOuterLoop is not NULL, add it
  // to the set. Same for lastInvalidStructure. In either case,
  // "reset" these last-pointers to NULL for the next call path.
  if (fn == modInitFn || fn == chpl_gen_main) {
    if (lastOuterLoop != NULL) {
      hasOuterLoopLocs.insert(lastOuterLoop);
    }
    if (lastInvalidStructure != NULL) {
      hasInvalidEnclosingStructureLocs.insert(lastInvalidStructure);
    }
    lastOuterLoop = NULL;
    lastInvalidStructure = NULL;
    return;
  }

  // Otherwise, look at each call site of fn. For each call site, look
  // for an enclosing serial loop, or an enclosing invalid structure.
  // If we find these, set the last-pointers appropriately
  forv_Vec(CallExpr, call, *fn->calledBy) {
    for (Expr* curr = call->parentExpr; curr; curr = curr->parentExpr) {
      // Check for enclosing loops
      if (toWhileStmt(curr) || toForLoop(curr)) {
        lastOuterLoop = curr;
      }
      // Check for invalid structures
      else if (toForallStmt(curr)) {
        lastInvalidStructure = curr;
      }
    } /* end of for Expr curr */
    if (FnSymbol *parentFn = toFnSymbol(call->parentSymbol)) {
      if (parentFn->hasFlag(FLAG_BEGIN) || parentFn->hasFlag(FLAG_COBEGIN_OR_COFORALL)) {
        // What we really need a hook to the coforall/begin/cobegin itself. We need to look-up
        // from the on_fn/begin_fn until we hit a BlockStmt
        forv_Vec(CallExpr, fnCall, *parentFn->calledBy) {
          for (Expr* curr = fnCall->parentExpr; curr; curr = curr->parentExpr) {
            if (isBlockStmt(curr)) {
              lastInvalidStructure = curr;
              break;
            }
          }
        }
      }
    }

    // Now look at the FnSymbol that call is in and call this function
    // recursively on that
    if (FnSymbol *nextFn = getEnclosingFunction(call)) {
      findLocationsForCallPathFlagsIE(nextFn, modInitFn, hasOuterLoopLocs,
                                      hasInvalidEnclosingStructureLocs,
                                      lastOuterLoop, lastInvalidStructure);
    }
  } /* end of forv_Vec */

} /* end of findLocationsForCallPathFlagsIE */

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                      Utility Related Functions                            //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
/*
    Below are various functions used in different stages of the inspector-executor
    optimization. Most of them relate to walking back through the AST to find
    enclosing loops.
*/

//##################################################################################
/*
    When a forall is deemed invalid for the IE optimization, this function wipes
    it out. It finds the call to staticCheckCallIE, which is used in the
    "if do optimization" check. So we move the else-statement of that if to
    go before the if and then remove the if all together.

    *** CALLED DURING POST-RESOLUTION ***
   
    Arguments:
    ID -> the ID of the forall to match on
    fn -> the FnSymbol whose body contains the forall to invalidate

    Return:
    The BlockStmt that now contains the original forall
*/
static void removeOptimizationIE(int ID,
                                 FnSymbol *fn)
{
  std::vector<CallExpr *> calls;
  if (fn != NULL) {
    collectCallExprs(fn->body, calls);
  }
  else {
    // hacky but puts relevant gCallExprs into a std::vector
    // so we can use the same loop for the case when we have
    // a function (see above)
    forv_Vec(CallExpr, fCall, gCallExprs) {
      if (fCall->isNamed("staticCheckCallIE")) {
        calls.push_back(fCall);
      }
    }
  }

  Expr *retval = NULL;
  for (auto &fCall : calls) {
    if (fCall->isNamed("staticCheckCallIE")) {
      int64_t argID;
      get_int(toSymExpr(fCall->get(1)), &argID);
      if (argID == (int64_t)ID) {
        // fCall is the staticCheckCallIE call. It's parentExpr should
        // be a PRIM_MOVE. After that move will be DefExpr and then another
        // PRIM_MOVE and finally the CondStmt. We should probably do
        // checks for all that, but for now just assume its true.
        if (CondStmt *cond = toCondStmt(fCall->parentExpr->next->next->next)) {
          retval = (Expr*)(cond->prev);
          // Make an empty BlockStmt and copy the else-stmt into it
          BlockStmt *b = new BlockStmt();
          b->insertAtHead(cond->elseStmt->remove());
          // Put the block before the CondStmt
          cond->insertAfter(b);
          // Remove the CondStmt
          cond->thenStmt->remove();
          cond->remove();
        }
      }
    }
  }
} /* end of removeOptimizationIE */

//##################################################################################
/*
    Look at all of the AggregateTypes and build up a mapping of their fields which
    are arrays to the corresponding domain field. The map we use is the global
    gArrFieldsToDomFields map, where the keys are the AggregateTypes and the values
    are maps of array-to-domain field locations.

    The purpose of doing this is so we can look up a field symbol of an AggregateType
    during post-resolution and get the corresponding domain for further checks.

    This is called only once, not per forall.

    *** CALLED DURING NORMALIZATION ***

    Arguments:
    None

    Return:
    None
*/
static void mapArrayFieldsToDomainFields()
{
  forv_Vec(AggregateType, at, gAggregateTypes) {
    if (gArrFieldsToDomFields.count(at)) {
      continue;
    }
    std::map<int, int> fieldLocs;
    for(int i = 1; i <= at->numFields(); i++) {
      Symbol *field = at->getField(i);
      // Is the field an array? We know this by looking at
      // field->defPoint->init and seeing if it is a CallExpr to
      // UnresolvedSymExpr chpl__buildArrayRuntimeType.
      Expr *tmp = NULL;
      if (field->defPoint->init != NULL) {
        tmp = field->defPoint->init;
      }
      else if (field->defPoint->exprType != NULL) {
        tmp = field->defPoint->exprType;
      }
      if (tmp == NULL) { continue; }
      if(CallExpr *call = toCallExpr(tmp)) {
        if (UnresolvedSymExpr *uSE = toUnresolvedSymExpr(call->baseExpr)) {
          if (strcmp(uSE->unresolved, "chpl__buildArrayRuntimeType") == 0) {
            // The domain should be an argument to chpl__ensureDomainExpr
            // which is on the RHS of call
            if (CallExpr *call2 = toCallExpr(call->get(1))) {
              if (UnresolvedSymExpr *uSE2 = toUnresolvedSymExpr(call2->baseExpr)) {
                if (strcmp(uSE2->unresolved, "chpl__ensureDomainExpr") == 0) {
                  if (SymExpr *domSE = toSymExpr(call2->get(1))) {
                    Symbol *dom = domSE->symbol();
                    fieldLocs[i] = at->getFieldPosition(dom->name);
                  }
                }
              }
            }
          }
        }
      }
    }
    gArrFieldsToDomFields[at] = fieldLocs;
  }
} /* end of mapArrayFieldsToDomainFields*/

//##################################################################################
/*
    This is called from pruneResolvedTree(), so we put its declaration in
    ForallStmt.h

    The purpose of this call is to remove any entries in the global
    gArrFieldsToDomFields map that correspond to AggregateTypes that will be
    removed from the AST (because they were generic). We need to do this because
    if we don't, the map seems to get corrupted/messed up from the keys pointing
    to NULL/garbage values.
*/
void pruneArrayFieldsToDomainFieldsMap()
{
  std::vector<AggregateType *> deleteAT;
  for (auto& elem : gArrFieldsToDomFields) {
    AggregateType *at = elem.first;
    INT_ASSERT(at != NULL);
    if (!at->inTree()) {
      // the at will be deleted, so remove it from the map.
      // We don't want to remove while we are iterating, so add
      // it to a vector to delete later
      deleteAT.push_back(at);
    }
  }
  for (auto& at : deleteAT) {
    gArrFieldsToDomFields.erase(at);
  }
} /* end of pruneArrayFieldsToDomainFieldsMap */

//##################################################################################
/*
    Given an Expr expr, find the function it is enclosed in.

    This is called from cloneFunctionsWithInvalidCallSites

    *** CALLED DURING NORMALIZATION ***

    Arguments:
    expr -> the Expr to analyze

    Return:
    The FnSymbol if we found it, NULL otherwise
*/
static FnSymbol *getEnclosingFunction(Expr *expr)
{
  for (Expr* curr = expr->parentExpr; curr; curr = curr->parentExpr) {
    if (FnSymbol *fn = toFnSymbol(curr->parentSymbol)) {
      return fn;
    }
  }
  return NULL;
} /* end of getEnclosingFunction */

//##################################################################################
/*
    Given an Expr expr, find the enclosing for loop (if there is one).

    This is called from analyzeCandidateIE and analyzeCandidateIWA, which are
    called during normalization

    *** CALLED DURING NORMALIZATION ***

    Arguments:
    expr -> the Expr to analyze

    Return:
    The for loop if we found it, NULL otherwise
*/
static ForLoop *findEnclosingForLoop(Expr *expr)
{
  for (Expr* curr = expr->parentExpr; curr; curr = curr->parentExpr) {
    // Check for enclosing for-loop
    if (ForLoop* forloop = toForLoop(curr)) {
      return forloop;
    }
  }
  return NULL;
} /* end of findEnclosingForLoop */

//##################################################################################
/*
    Loops for the closest enclosing forall loop. We need this to work across
    function call sites because in pre-folding, we need to get the inspector
    primitive's enclosing forall. But with the new optimization we do for the
    inspector, the primitive is within an on-statement, which is a function.

    *** PRE-FOLDING ***

    Arguments:
    expr -> The expression to look at/test

    Return:
    ForallStmt * -> the forall loop we found or NULL if we did not find one
*/
static ForallStmt *findEnclosingForallLoop(Expr *expr)
{
  ForallStmt *retval = NULL;
  for (Expr* curr = expr->parentExpr; curr; curr = curr->parentExpr) {
    // Check for enclosing for-loop
    if (ForallStmt* forallLoop = toForallStmt(curr)) {
      return forallLoop;
    }
  }
  // Check for enclosing function. If we find one, recursively call
  // this.
  if (FnSymbol *fn = toFnSymbol(expr->parentSymbol)) {
    forv_Vec(CallExpr, fnCall, *fn->calledBy) {
      retval = findEnclosingForallLoop(fnCall->parentExpr);
      if (retval) {
        return retval;
      }
    }
  }
  return retval;
} /* end of findEnclosingForallLoop */

//##################################################################################
/*
    Given an expression, attempt to find an enclosing loop. This may be a forall,
    for, do-while, while-do, etc. We return the expression as a Expr * and then
    we can cast it to whatever we need to at the call site.

    Note: not explicitly checking for coforalls.

    *** CALLED PRE-FOLDING and POST-RESOLUTION ***

    Arguments:
    expr -> The expression to look at/test

    Return:
    Expr * -> the loop we found or NULL if we did not find one
*/

static Expr *findEnclosingLoop(Expr *expr)
{
  Expr *retval = NULL;
  for (Expr* curr = expr->parentExpr; curr; curr = curr->parentExpr) {
    // Check for enclosing loops
    if (toForallStmt(curr)  ||
        toWhileStmt(curr)   || // handles while and do-whiles
        toForLoop(curr)) {
      return curr;
    }
  }
  // Check for enclosing function. If we find one, recursively call
  // this.
  if (FnSymbol *fn = toFnSymbol(expr->parentSymbol)) {
    forv_Vec(CallExpr, fnCall, *fn->calledBy) {
      retval = findEnclosingLoop(fnCall->parentExpr);
      if (retval) {
        return retval;
      }
    }
  }
  return retval;
} /* end of findEnclosingLoop */

//##################################################################################
/*
    Same as above but only looks for serial loops: for, while, do-while.

    *** CALLED PREFOLDING ***

    Arguments:
    expr -> The expression to look at/test

    Return:
    Expr * -> the loop we found or NULL if we did not find one
*/

static Expr *findEnclosingSerialLoop(Expr *expr)
{
  Expr *retval = NULL;
  for (Expr* curr = expr->parentExpr; curr; curr = curr->parentExpr) {
    // Check for enclosing loops
    if (toWhileStmt(curr)   || // handles while and do-whiles
        toForLoop(curr)) {
      return curr;
    }
  }
  // Check for enclosing function. If we find one, recursively call
  // this.
  if (FnSymbol *fn = toFnSymbol(expr->parentSymbol)) {
    forv_Vec(CallExpr, fnCall, *fn->calledBy) {
      retval = findEnclosingSerialLoop(fnCall->parentExpr);
      if (retval) {
        return retval;
      }
    }
  }
  return retval;

} /* end of findEnclosingSerialLoop */

//##################################################################################
/*
    This is somewhat equivalent to gatherForallInfo() but for for-loops. What we
    are doing is gathering info regarding the loop's domain/iterator. We need
    this info to do some checks for the loop's domain relative to A[B[i]],
    specifically ensuring that the loop is iterating over a domain that is equal
    to B's domain and that i is something yielded by the loop's iterator.

    *** CALLED DURING NORMALIZATION ***

    Arguments:
    f -> the for loop

    Return:
    None; we update the ForLoop's internal vectors
*/
static void gatherForLoopInfo(ForLoop *f)
{
  getForLoopIndexVars(f);

  // Not 100% sure how accurate this is, but a for-loop is enclosed in a BlockStmt
  // that contains the info about its domain/iterator. We can get the loop's
  // iterator Symbol via iteratorGet(). From there, we look at all its SymExprs
  // and look specifically for the _getIterator call. From there, we can pass
  // the CallExpr into various checks to get the domain and array symbol
  Symbol *itSymbol = f->iteratorGet()->symbol();
  for_SymbolSymExprs(symexpr, itSymbol) {
    if (CallExpr *symCall = toCallExpr(symexpr->parentExpr)) {
      // symCall should be a move, where the first argument is symexpr
      if (symCall->isPrimitive(PRIM_MOVE) && symCall->get(1) == symexpr) {
        // Looking for when the 2nd arg to symCall is a call to _getIterator
        CallExpr *getIteratorCall = toCallExpr(symCall->get(2));
        if (getIteratorCall != NULL && getIteratorCall->isNamed("_getIterator")) {
          Expr *expr = getIteratorCall->get(1);
          getForLoopDomainInfo(f, expr);
        } /* end if getIteratorCall != NULL */
      } /* end if symCall->get(1) == symexpr */
    } /* end if CallExpr *symCall */
  } /* end for_SymbolSymExprs */

  f->forLoopInfoGathered = true;
} /* end of gatherForLoopInfo */

//##################################################################################
/*
    Extracts loop index variables from a for-loop.

    *** CALLED DURING NORMALIZATION ***

    Arguments:
    f -> the for loop

    Return:
    None; we update the ForLoop's internal vectors
*/
static void getForLoopIndexVars(ForLoop *f)
{
  // Get index vars. Not sure how robust this is. We get the indexOfInterest
  // Symbol from the loop. We look at its associated SymExprs and check for
  // the case when its parentExpr is a move. The 1st argument to that move
  // is the loop index (the 2nd arg is the SymExpr).
  Symbol *indexOfInterestSymbol = f->indexGet()->symbol();
  std::vector<SymExpr*> symExprs;
  collectSymExprsFor(f, indexOfInterestSymbol, symExprs);
  for_vector(SymExpr, symexpr, symExprs) {
    CallExpr *moveCall = toCallExpr(symexpr->parentExpr);
    if (moveCall != NULL && moveCall->isPrimitive(PRIM_MOVE)) {
      if (SymExpr *idxSymExpr = toSymExpr(moveCall->get(1))) {
        f->indexVars.push_back(idxSymExpr);
      }
    }
  }
  for (auto& curIndexVar : f->indexVars) {
    Symbol *loopIdxSym = NULL;
    std::vector<Symbol *> multiDIndices;
    if (SymExpr* se = toSymExpr(curIndexVar)) {
        loopIdxSym = se->symbol();
    }
    else if (DefExpr* de = toDefExpr(curIndexVar)) {
      loopIdxSym = de->sym;
    }
    else {
      INT_FATAL("Loop index cannot be extracted");
    }
    if (loopIdxSym->hasFlag(FLAG_INDEX_OF_INTEREST)) {
      multiDIndices = getForLoopIndexSymbols(f, loopIdxSym);
    }
    else {
      multiDIndices.push_back(loopIdxSym);
    }
    f->multiDIndices.push_back(multiDIndices);
  }
} /* end of getForLoopIndexVars */

//##################################################################################
/*
    Copy of getLoopIndexSymbols() but for for-loops.

    *** CALLED DURING NORMALIZATION ***

    Arguments:
    f -> for loop of interest
    baseSym -> symbol for array of interest

    Return:
    vector of Symbol *'s that are the loop index symbols
*/
static std::vector<Symbol *> getForLoopIndexSymbols(ForLoop *f,
                                                    Symbol *baseSym) {
  std::vector<Symbol *> indexSymbols;
  int indexVarCount = -1;
  int bodyExprCount = 1;

  AList &bodyExprs = f->body;

  // find the check_tuple_var_decl and get the size of the tuple
  if (CallExpr *firstCall = toCallExpr(bodyExprs.get(bodyExprCount++))) {
    if (firstCall->isNamed("_check_tuple_var_decl")) {
      if (SymExpr *firstArgSE = toSymExpr(firstCall->get(1))) {
        if (firstArgSE->symbol() == baseSym) {
          if (SymExpr *secondArgSE = toSymExpr(firstCall->get(2))) {
            if (VarSymbol *vs = toVarSymbol(secondArgSE->symbol())) {
              indexVarCount = vs->immediate->int_value();
            }
          }
        }
      }
    }
  }

  if (indexVarCount != -1) {
    INT_ASSERT(indexVarCount > 0);

    // push every element (subindex) of the index tuple to the vector
    for (int i = 0 ; i < indexVarCount ; i++) {
      if (DefExpr *indexDE = toDefExpr(bodyExprs.get(bodyExprCount++))) {
        Symbol *indexSym = indexDE->sym;
        if(isSubIndexAssignment(bodyExprs.get(bodyExprCount++),
                                indexSym, i, baseSym)) {
          indexSymbols.push_back(indexSym);
        }
      }
    }
  }

  // we must have pushed the same number of indexes to the vector as we
  // initially found. Otherwise, clear the vector, which denotes an unknown
  // pattern.
  if (indexVarCount == -1 ||
      ((std::size_t)indexVarCount) != indexSymbols.size()) {
    INT_FATAL("Can't recognize loop's index symbols");
  }

  return indexSymbols;

} /* end of getForLoopIndexSymbols */


//##################################################################################
/*
    Given a ForLoop and an expression that represents the domain iterated over,
    extract out some info such as the Symbol of the domain and the Symbol of the
    base of the domain.

    *** CALLED DURING NORMALIZATION ***

    Arguments:
    f -> the for loop
    expr -> domain expression

    Return:
    None; we update the ForLoop's internal vectors
*/
static void getForLoopDomainInfo(ForLoop *f,
                                 Expr *expr)
{
  Symbol *iterSym = NULL;
  Expr *dotDomIterExpr = NULL;
  Symbol *dotDomIterSym = NULL;
  Symbol *dotDomIterSymDom = NULL;

  if (isUnresolvedSymExpr(expr) || isSymExpr(expr)) {
    if (SymExpr *iterSE = toSymExpr(expr)) {
      iterSym = iterSE->symbol();
    }
  }
  else if (Symbol *dotDomBaseSym = getDotDomBaseSym(expr)) {
    // dotDomBaseSym is B
    // dotDomIterSymDom is B's domain from B.domain
    dotDomIterExpr = expr;
    dotDomIterSym = dotDomBaseSym;
    dotDomIterSymDom = getDomSym(dotDomIterSym);
  }

  // Add things to the vectors
  f->iterSym.push_back(iterSym);
  f->dotDomIterExpr.push_back(dotDomIterExpr);
  f->dotDomIterSym.push_back(dotDomIterSym);
  f->dotDomIterSymDom.push_back(dotDomIterSymDom);

} /* end of getForLoopDomainInfo */

//##################################################################################
/*
    Starting from the CallExpr call, find all enclosing for and forall loops. For
    each loop found, extract out its loop index symbols and loop iterator symbols.
    These symbols are added to their respective vectors.

    The point in doing this is to build up the potentially valid loop index symbols
    that can be used in the irregular memory access expression. We only only symbols
    that are yielded from an enclosing loop, and only those that are yielded from an
    array or domain. Since we can't determine whether we have an array or domain during
    normalization, we save them off and do it during prefolding.

    For each iterator symbol we extract, we also note whether it is from a "normal"
    iterator like "for i in A" or a dot-domain iterator like "for i in A.domain".
    That is useful info for post-resolution. However, we need to refine these a bit,
    as we could have something like "for i in A" but A is "ref A = foo.field". We
    categorize this as NORMAL_REC_FIELD. We also have something like "for i in A.domain"
    and A is "ref A = foo.field" (called DOT_DOMAIN_REC_FIELD). We need to check for
    this as it tells us the actual Symbol we want to track. We have a function called
    isSymbolDefinedInBlock() that will determine such things, as well as give us the
    actual symbol we want. But, as the name suggest, its main purpose is to determine
    whether a given symbol is defined in a block. We normally use it to see whether
    something is defined in the forall of interest. But for our purposes here, the
    block we analyze is the block of the outer-most loop we find here.

    NOTE: we do not do these checks/extractions across function calls.

    *** CALLED DURING NORMALIZATION ***

    Arguments:
    call -> the CalLExpr to start from (assumed to be B[expr] from A[expr(B[expr])]
    loopIndexSyms -> vector to hold loop index symbols
    loopIteratorSyms -> vector to hold loop iterator symbols

    Return:
    true if things are valid, false otherwise
    vectors are updated
*/
static bool extractAllLoopSyms(CallExpr *call,
                               std::vector<Symbol *> &loopIndexSyms,
                               std::vector<std::pair<Symbol *, ieIndexIteratorType>> &loopIteratorSyms)
{
  // Starting from call->parentExpr, look "up" and check for enclosing
  // for or forall loops. Keep track of the last loop we found
  Stmt *lastLoop = NULL;
  for (Expr* curr = call->parentExpr; curr; curr = curr->parentExpr) {
    //
    // HANDLE FOR-LOOPS
    //
    if (ForLoop* forLoop = toForLoop(curr)) {
      lastLoop = forLoop;
      gatherForLoopInfo(forLoop);
      // Save off the Symbols found. forLoop->multiDIndices is a vector of
      // vectors of Symbol *. Only do this if a given Symbol was yielded by
      // something that is potentially an array/domain.
      int currIdx = 0;
      for (auto &symVec : forLoop->multiDIndices) {
        Symbol *loopIteratorSym = NULL;
        ieIndexIteratorType iterType;
        if (forLoop->iterSym.size() > 0) {
          if (forLoop->iterSym[currIdx] != NULL) {
            loopIteratorSym = forLoop->iterSym[currIdx];
            iterType = NORMAL;
          }
        }
        if (loopIteratorSym == NULL && forLoop->dotDomIterSym.size() > 0) {
          if (forLoop->dotDomIterSym[currIdx] != NULL) {
            loopIteratorSym = forLoop->dotDomIterSym[currIdx];
            iterType = DOT_DOMAIN;
          }
        }
        if (loopIteratorSym != NULL) {
          std::pair<Symbol *, ieIndexIteratorType> iterPair(loopIteratorSym, iterType);
          // For each sym involved with this iterator, push it onto the vector.
          // We also do a corresponding push of the iterator sym to its vector, so
          // both vectors match-up
          for (auto &sym : symVec) {
            loopIteratorSyms.push_back(iterPair);
            loopIndexSyms.push_back(sym);
          }
        }
        currIdx++;
      }
    } /* end of if for-loop */

    //
    // HANDLE FORALL-LOOPS
    //
    else if (ForallStmt *forallLoop = toForallStmt(curr)) {
      lastLoop = forallLoop;
      int currIdx = 0;
      for (auto &symVec : forallLoop->optInfo.multiDIndices) {
        Symbol *loopIteratorSym = NULL;
        ieIndexIteratorType iterType;
        if (forallLoop->optInfo.iterSym.size() > 0) {
          if (forallLoop->optInfo.iterSym[currIdx] != NULL) {
            loopIteratorSym = forallLoop->optInfo.iterSym[currIdx];
            iterType = NORMAL;
          }
        }
        if (loopIteratorSym == NULL && forallLoop->optInfo.dotDomIterSym.size() > 0) {
          if (forallLoop->optInfo.dotDomIterSym[currIdx] != NULL) {
            loopIteratorSym = forallLoop->optInfo.dotDomIterSym[currIdx];
            iterType = DOT_DOMAIN;
          }
        }
        if (loopIteratorSym != NULL) {
          std::pair<Symbol *, ieIndexIteratorType> iterPair(loopIteratorSym, iterType);
          for (auto &sym : symVec) {
            loopIteratorSyms.push_back(iterPair);
            loopIndexSyms.push_back(sym);
          }
        }
      }
    } /* end of if forall loop */
  } /* end of for expr */

  // Now we want to refine our iterator syms/types by determining whether we have aliases
  // to record fields, etc. We do this by calling isSymbolDefinedInBlock, using the body
  // of the last loop we found above.
  BlockStmt *body = NULL;
  if (ForLoop *f = toForLoop(lastLoop)) {
    for_alist(fnode, f->body) {
      if (isBlockStmt(fnode)) {
        body = toBlockStmt(fnode);
        break;
      }
    }
  }
  else if (ForallStmt *f = toForallStmt(lastLoop)) {
    body = f->loopBody();
  }
  INT_ASSERT(body != NULL);
  for (auto &elem : loopIteratorSyms) {
    Symbol *sym = elem.first;
    ieIndexIteratorType iterType = elem.second;
    bool isRecField = false;
    Symbol *alias = isSymbolDefinedInBlock(sym,
                                           body,
                                           isRecField);
    if (alias == NULL) {
      if (fReportIrregArrayAccesses) {
        printf("\t\t !!! index iterator %s is defined as a var inside of the loop\n", sym->name);
      }
      return false;
    }
    elem.first = alias;
    if (iterType == NORMAL && isRecField == true) {
      elem.second = NORMAL_REC_FIELD;
    }
    else if (iterType == DOT_DOMAIN && isRecField == true) {
      elem.second = DOT_DOMAIN_REC_FIELD;
    }
  }

  return true;
} /* end of extractAllLoopSyms */

//##################################################################################
/*
    Given a candidate CallExpr that represents B[i] in A[B[i]] and info about its
    enclosing loop (for or forall), determine whether the loop domain is valid.
    Right now, this simply means that "i" is yielded by the loop. In prefolding, we
    check whether the index iterator that yields "i" is an array or domain.

    *** CALLED DURING NORMALIZATION ***

    Arguments:
    call -> the B[i] CallExpr
    parentCall -> the A[B[i]] CallExpr
    loopIndexSyms -> vector of all enclosing loops' index symbols
    loopIteratorSyms -> same as above but for loop iterator symbols
    loopBody -> the body of the for/forall loop
    multiDIndices -> holds Symbols of the loop indices
    iterSym -> holds the Symbol for B in "forall i in B"
    dotDomIterSym -> holds the Symbol for B in "forall i in B.domain"
    optInfo -> instance of the forall's optInfo
    loopIterSymsUsed -> stores the loop iterator syms from loopIteratorSyms
                        that were determined to actually be used in call and parentCall.

    Return:
    true if the loop domain is valid, false otherwise
*/
static bool isLoopDomainValidIE(CallExpr *call,
                                CallExpr *parentCall,
                                std::vector<Symbol *> loopIndexSyms,
                                std::vector<std::pair<Symbol *, ieIndexIteratorType>> loopIteratorSyms,
                                BlockStmt *loopBody,
                                std::vector< std::vector<Symbol *> > multiDIndices,
                                std::vector<Symbol *> iterSym,
                                std::vector<Symbol *> dotDomIterSym,
                                ForallOptimizationInfo &optInfo,
                                std::map<std::pair<Symbol *, ieIndexIteratorType>, bool> &loopIterSymsUsed)
{
  SymExpr *baseSE = toSymExpr(call->baseExpr);
  if (baseSE != NULL) {
    Symbol *accBaseSym = baseSE->symbol();

    // Prevent making changes to `new C[i]`
    if (CallExpr *temp = toCallExpr(call->parentExpr)) {
      if (temp->isPrimitive(PRIM_NEW)) { return false; }
    }

    // don't analyze further if the call base is a yielded symbol
    if (accBaseSym->hasFlag(FLAG_INDEX_VAR)) { return false; }

    // Ensure that the loop is iterating over a domain or array.
    // We know this by checking the sizes of iterSym and dotDomIterSym.
    // iterSym will hold "foo" in "forall i in foo" and dotDomIterSym
    // will hold "bar" in "forall i in bar.domain". We'll do checks later
    // to ensure "foo" or "bar" is an array/domain.
    if (iterSym.size() == 0 && dotDomIterSym.size() == 0) {
      return false;
    }

    // give up if the B[i] uses a different symbol than the symbols yielded by
    // one of the iterators. We do the same check for parentCall, since it
    // could be something like A[B[i]+i]. These checks are all done w.r.t. any
    // of the enclosing loops we found earlier. We stored all such loop index
    // symbols in loopIndexSyms.
    bool callIsValid = false;
    bool parentCallIsValid = false;
    std::vector<int> loopIndexSymsUsed;
    if (callHasValidExpression(call, call, loopIndexSyms, loopIndexSymsUsed)) {
      callIsValid = true;
    }
    if (callHasValidExpression(parentCall, call, loopIndexSyms, loopIndexSymsUsed)) {
      parentCallIsValid = true;
    }
    if (!callIsValid || !parentCallIsValid) {
      return false;
    }
    // For any loop index symbols determined to be used in call/parent call, add their
    // corresponding loop iterator symbol to the map
    for (auto idx: loopIndexSymsUsed) {
      Symbol *loopIterSym = loopIteratorSyms[idx].first;
      ieIndexIteratorType iterType = loopIteratorSyms[idx].second;
      std::pair<Symbol *, ieIndexIteratorType> iterPair(loopIterSym, iterType);
      loopIterSymsUsed[iterPair] = true;
    }

    // (i,j) in for (i,j) in bla is a tuple that is index-by-index accessed
    // in loop body that throw off this analysis
    if (accBaseSym->hasFlag(FLAG_INDEX_OF_INTEREST)) { return false; }

    // give up if the base symbol is a shadow variable
    if (isShadowVarSymbol(accBaseSym)) {
      return false;
    }

    // The loop info we have is for the loop that contains A[B[i]].
    // We just ensured above that this loop yields "i". So we need
    // to extract the index iterator symbol and ensure it is not
    // defined inside the loop in an invalid way. We allow it if
    // it is a ref to something outside of the loop. If it is a ref
    // to something outside of the loop, we get that outside alias
    // and use that as our ieIndexIterator. The special case is when
    // the iterator is defined as the field of a record, like
    // "ref foo = rec.field". In that case, we still use foo but mark
    // it as "special" for later uses.
    //
    // If iterSym[idx] is not NULL, then we have a case of
    // "for i in foo". Else, we look at dotDomIterSym[idx], which
    // gives us foo from "for i in foo.domain". Once we have foo,
    // then we check to see if it is defined inside or outside the
    // loop.
    //
    // TODO: assume we only have 1 iterator for the loop, so idx=0
    int idx = 0;
    if (iterSym[idx] != NULL) {
      optInfo.ieIndexIterator = iterSym[idx];
    }
    else if (dotDomIterSym[idx] != NULL) {
      optInfo.ieIndexIterator = dotDomIterSym[idx];
    }
    INT_ASSERT(optInfo.ieIndexIterator != NULL);

    // Now see if ieIndexIterator is defined in the loop or not.
    // If this returns NULL, then we have an invalid symbol (it's
    // defined in the loop as a var and not a ref).
    bool isRecField = false;
    Symbol *alias = isSymbolDefinedInBlock(optInfo.ieIndexIterator,
                                           loopBody,
                                           isRecField);

    if (alias == NULL) {
      if (fReportIrregArrayAccesses) {
        printf("\t\t !!! index iterator %s is defined as a var inside of the loop\n", optInfo.ieIndexIterator->name);
      }
      return false;
    }
    if (fReportIrregArrayAccesses) {
      if (alias == optInfo.ieIndexIterator && isRecField == false) {
        printf("\t\t- index iterator %s is defined outside of the loop\n", alias->name);
      }
      else if (alias != optInfo.ieIndexIterator && isRecField == false) {
        printf("\t\t- index iterator %s is defined as a ref to %s outside of the loop\n", optInfo.ieIndexIterator->name,
                                                                                        alias->name);
      }
      else if (alias == optInfo.ieIndexIterator && isRecField == true) {
        printf("\t\t- index iterator %s is defined in the loop as a ref to a record field\n", alias->name);
      }
      else if (alias != optInfo.ieIndexIterator && isRecField == true) {
        printf("\t\t- index iterator %s is defined as a ref to %s that is a record field\n", optInfo.ieIndexIterator->name,
                                                                                           alias->name);
      }
    }

    optInfo.ieIndexIterator = alias;

    // Set up the index iterator types
    if (iterSym[idx] != NULL && isRecField == false) {
      optInfo.indexIteratorType = NORMAL;
    }
    else if (iterSym[idx] != NULL && isRecField == true) {
      optInfo.indexIteratorType = NORMAL_REC_FIELD;
    }
    else if (dotDomIterSym[idx] != NULL && isRecField == false) {
      optInfo.indexIteratorType = DOT_DOMAIN;
    }
    else if (dotDomIterSym[idx] != NULL && isRecField == true) {
      optInfo.indexIteratorType = DOT_DOMAIN_REC_FIELD;
    }

    return true;
  }

  return false;

} /* end of isLoopDomainValidIE */

//##################################################################################
/*
    This is a copy of callHasSymArguments but modified for the inspector-executor
    optimization.

    *** CALLED NORMALIZATION ***

    At a high level, this function checks whether the CallExpr ce, which is assumed
    to be B[expr] or A[B[expr] op expr] from A[B[expr] op expr], uses the same Symbol
    as yielded by the loop iterator. These Symbols are in the vector syms.

    The original version of this function looks specifically for B[i], but we want
    to support more complex expressions, such as B[i*1]. To be exact, we support
    any binary operator involving a symbol yielded by the loop iterator and
    constants. We also call this with the "top level" A[B[i]] CallExpr to support
    things like A[B[i]+1].

    We have a 2nd CallExpr we pass in that is always the B[expr] call. This is
    only relevant for the case when we pass in A[B[expr] op expr] as the first argument.
    When processing the CallExpr A[B[expr] op expr], we will eventually hit B[expr]. It does
    not match any of our valid cases, but we want to ignore it since we will analyze it
    on its own in a separate call to this function.

    Arguments:
    ce -> CallExpr representing B[expr] or A[expr] from something like A[B[i]]
    ignore -> CallExpr always representing B[expr]
    syms -> vector of Symbols we are trying to match on. These are represent
            Symbols from any of the loops "above" ce. These are the only Symbols
            that can be used in "expr".

    Return:
    true if ce has "valid" arguments, false otherwise
*/
static bool callHasValidExpression(CallExpr *ce,
                                   CallExpr *ignore,
                                   const std::vector<Symbol *> &syms,
                                   std::vector<int> &loopIndexSymsUsed)
{
  bool retval = true;
  for (int i = 0 ; i < ce->argList.length ; i++) {
    // If we have a SymExpr, it must be one of the Symbols in syms, or
    // a constant/immediate.
    if (SymExpr *arg = toSymExpr(ce->get(i+1))) {
      if (arg->symbol()->isImmediate()) {
        continue;
      }
      bool temp = false;
      int idx = 0;
      for (auto &sym : syms) {
        if (arg->symbol() == sym) {
          temp = true;
          loopIndexSymsUsed.push_back(idx);
          break;
        }
        idx++;
      }
      if (temp == false) {
        retval = false;
      }
    }

    // If ce's argument is a CallExpr, ensure it is a binary operator:
    //
    //  + - * / % ** & | ^ << >> && || == != <= >= < >
    //
    // From a general point of view, any CallExpr with two arguments
    // can be considered a binary operator. But we do not want to count
    // things like func(a,b) which would match on that criterion. So we
    // will be a bit verbose and look for the specific operator itself.
    //
    // If ce's argument is a CallExpr and is the same as "ignore", then
    // we ignore it and continue.
    else if (CallExpr *callArg = toCallExpr(ce->get(i+1))) {
      if (isCallExprBinaryOperator(callArg)) {
        retval = callHasValidExpression(callArg, ignore, syms, loopIndexSymsUsed);
      }
      else if (callArg == ignore) {
        continue;
      }
      else {
        retval = false;
      }
    }

    // Otherwise, something unexpected/unknown
    else {
      retval = false;
    }

    if (retval == false) {
      break;
    }
  } /* end of for-loop over ce's args */

  return retval;
}

//##################################################################################
/*
    Given a a CallExpr, return true if it represents a known binary operator.
    Otherwise, return false.

    We specifically look for the following operators:

        + - * / % ** & | ^ << >> && || == != <= >= < >

    *** CALLED NORMALIZATION ***

    Arguments:
    call -> the CallExpr to analyze

    Return:
    true is call is a known binary operator, false otherwise
*/
static bool isCallExprBinaryOperator(CallExpr *call)
{
  if (call->isNamed("+")  || call->isNamed("-")  || call->isNamed("*")  ||
      call->isNamed("/")  || call->isNamed("%")  || call->isNamed("**") ||
      call->isNamed("&")  || call->isNamed("|")  || call->isNamed("^")  ||
      call->isNamed("<<") || call->isNamed(">>") || call->isNamed("&&") ||
      call->isNamed("||") || call->isNamed("==") || call->isNamed("!=") ||
      call->isNamed("<=") || call->isNamed(">=") || call->isNamed("<")  ||
      call->isNamed(">")) {
    return true;
  }
  return false;
} /* end of isCallExprBinaryOperator */

//##################################################################################
/*
    Given a Symbol sym and a BlockStmt blckStmt, determine whether sym is a ref/alias
    and if so, whether what it is referring to is defined in blckStmt. The goal is to
    return the "end" of the alias chain, so we have a Symbol for something that is
    outside of blckStmt. We plan to use this Symbol for tracking purposes later.

    This is called recursively to handle multiple "layers" of aliasing. In our use case,
    blckStmt is the body of the forall of interest and sym is the symbol that yields "i".
    For each recursive call, blckStmt stays the same but sym will be the current point in
    the alias chain to evaluate.

    Things can get a bit tricky with various refs to other things. If we have
    something like ref B = r.arr, then we need to ensure that "r" is not defined in
    the body. But we don't want to use "r" as the final return from this function,
    as it isn't an array and we can't get its domain symbol. We can handle that by
    returning the "last valid" symbol instead. But we also could have something
    like ref B = arrays[0]. In that case, we wouldn't trigger any of our checks
    and we would just return B. For now, that is just something we'll have to
    deal with. It is a production concern, not a research concern.

    *** CALLED NORMALIZATION ***

    Arguments:
    sym -> the Symbol to analyze
    blckStmt -> the BlockStmt to check for Symbol's defPoint
    isRecField -> set to true if sym refers to a record field.

    Return:
    Symbol * -> the Symbol at the "end" of the aliases if it is not defined
    in blckStmt, NULL otherwise
*/
static Symbol *isSymbolDefinedInBlock(Symbol *sym,
                                      BlockStmt *blckStmt,
                                      bool &isRecField)
{
  Symbol *retval = sym;
  // Is sym defined in the block?
  if (blckStmt->contains(sym->defPoint)) {
    VarSymbol* var = toVarSymbol(sym->defPoint->sym);
    // Is sym a ref variable?
    if (var->hasFlag(FLAG_REF_VAR)) {
      Symbol *aliasSym = NULL;
      Expr *expr = sym->defPoint->init;
      // Handle case when we have ref B = rec.foo. We want to see whether
      // rec is defined inside the block.
      // NOTE: if we have something like ref B = R[i].foo, we will not find R.
      // We will just abort in this case.
      if (CallExpr *call = toCallExpr(expr)) {
        if (call->isNamedAstr(astrSdot)) {
          // aliasSym would be the class/object (LHS of the ".")
          if (SymExpr *symexpr = toSymExpr(call->get(1))) {
            isRecField = true;
            aliasSym = (toSymExpr(call->get(1)))->symbol();
            Symbol *tmp = isSymbolDefinedInBlock(aliasSym, blckStmt, isRecField);
            // If tmp == aliasSym, then it means we found the end of the alias
            // chain, where aliasSym is defined outside of the body. Normally we'd
            // return the Symbol at the end of the chain, but in the case here, that
            // would be the class/object (rec). We can't get a domain symbol from that,
            // so instead return the last "valid" Symbol. In the case of ref B = rec.foo,
            // that would be B.
            if (tmp != aliasSym) {
              retval = tmp;
            }
          }
          else {
            // we have some form of "." that we cannot handle
            return NULL;
          }
        }
      }
      else {
        // Simple case of ref B = foo, where we want to analyze foo.
        aliasSym = (toSymExpr(sym->defPoint->init))->symbol();
        retval = isSymbolDefinedInBlock(aliasSym, blckStmt, isRecField);
      }
    }
    else {
      // sym is defined in the loop body and is not a ref; we do not allow this
      return NULL;
    }
  } /* end of if loopBody->contains() */

  return retval;

} /* end of isSymbolDefinedInBlock */


//##################################################################################
/*
    Given a Symbol that is assumed to have the type at, look for accesses to the
    symbol's fields. If any of these accesses are to non-POD types, return false.
    If we don't find any such accesses, then return true. If we find that sym is
    passed into a function call, we'll find that function and analyze its body
    for accesses. We do this recursively.

    We also build up the field positions for the POD fields accessed and store them
    in gFieldPositionsIE.

   *** CALLED PRE-FOLDING ***

    Arguments:
    sym -> the Symbol to analyze
    at -> the type of sym
    ID -> used to index into gFieldPositionsIE

    Return:
    true if only POD fields are accessed, false otherwise
*/
static bool detectFieldAccesses(Symbol *sym,
                                AggregateType *at,
                                int64_t ID)
{
  for_SymbolSymExprs(symexpr, sym) {
    if (CallExpr *symCall = toCallExpr(symexpr->parentExpr)) {
      if(Symbol *fieldSym = isFieldAccess(symCall, at)) {
        if (propagateNotPOD(fieldSym->getValType())) {
          // access to non-POD field
          return false;
        }
        else {
          // fieldSym is a POD field. Get its index/position and add it to the vector.
          // NOTE: within the compiler, field positions are 1-based but within
          // Chapel via the Reflection module, they are 0-based.
          int pos = at->getFieldPosition(fieldSym->name);
          INT_ASSERT(pos >= 0);
          gFieldPositionsIE[ID].push_back(pos-1);
        }
      }
      else {
        // is symCall a call to a function where t is an argument?
        if (toUnresolvedSymExpr(symCall->baseExpr)) {
          // TODO: not sure how best to detect whether we have a function call?
          // Are all UnresolvedSymExpr's function calls? For now, we'll be stupid
          // and assume it is. So find the arg pos of sym in the call so we can use
          // that when analyzing the function itself
          int argPos = -1;
          for (int i = 1 ; i <= symCall->argList.length ; i++) {
            if (symexpr == toSymExpr(symCall->get(i))) {
              argPos = i;
              break;
            }
          }
          INT_ASSERT(argPos > 0);
          forv_Vec(FnSymbol, fn, gFnSymbols) {
            if (symCall->isNamed(fn->name)) {
              // fn is the function that symCall calls
              // invoke this function on the formal
              Symbol *symFormal = NULL;
              int pos = 1;
              for_alist(formal, fn->formals) {
                if (pos == argPos) {
                  symFormal = toArgSymbol(toDefExpr(formal)->sym);
                  break;
                }
                pos++;
              }
              INT_ASSERT(symFormal != NULL);
              return detectFieldAccesses(symFormal, at, ID);
            }
          }
        }
      }
    }
  } /* end of for_SymbolSymExprs(symexpr, t) */
  return true;
} /* detectFieldAccesses */

//##################################################################################
/*
    Given a CallExpr call, determine whether it is an access to a record's field,
    where the record type is specified by at.

    If it is, return the Symbol of the field being accessed. Else, return NULL.

    We call this during pre-folding, so we look specifically for the _mt methodtoken.

     *** CALLED PRE-FOLDING ***

    Arguments:
    call -> the CallExpr to analyze
    at -> the AggregateType we are looking for a field access to

    Return:
    Symbol * of the field, NULL if call is not a field access
*/
static Symbol *isFieldAccess(CallExpr *call,
                             AggregateType *at)
{
  if (call->numActuals() == 2) {
    // First arg _mt?
    if (call->get(1)->getValType() == dtMethodToken) {
      // baseExpr is the field accessor
      if (UnresolvedSymExpr* base = toUnresolvedSymExpr(call->baseExpr)) {
        if (Symbol* fieldSym = at->getField(base->unresolved, false)) {
          if (!fieldSym->hasFlag(FLAG_PARAM) && !fieldSym->hasFlag(FLAG_TYPE_VARIABLE)) {
            return fieldSym;
          }
        }
      }
    }
  }
  return NULL;
} /* end of isFieldAccess */

//##################################################################################
/*
    Given a CallExpr, return true if it is valid for us to look at it
    during findAllModificationsToSymbol(). We put these checks here because it
    cleans up the if-structure a bit. We return false if the call is a primitive
    or if the call is to inspectAccess() or executeAccess().

    *** CALLED POST-RESOLUTION ***

    Arguments:
    call -> CallExpr to check

    Return:
    true if call is valid for checking, false otherwise
*/
static bool isCallExprValid(CallExpr *call)
{
  if (call->isPrimitive()) {
    return false;
  }
  if (call->theFnSymbol()) {
    if (call->theFnSymbol()->hasFlag(FLAG_INSPECT_ACCESS)) {
      return false;
    }
    if (call->theFnSymbol()->hasFlag(FLAG_EXECUTE_ACCESS)) {
      return false;
    }
    if (call->theFnSymbol()->hasFlag(FLAG_INSPECTOR_PREAMBLE)) {
      return false;
    }
    if (call->theFnSymbol()->hasFlag(FLAG_EXECUTOR_PREAMBLE)) {
      return false;
    }
  }
  return true;
} /* end of isCallExprValid */


//##################################################################################
/*
    Given an expression expr, start looking backwards until you find an expression that
    matches matchExpr. If we find a match, return true. Otherwise, if we never find
    a match, return false.

    We recursively call this function to handle cases when the expression is inside
    of a function. We'll look at all call sites of the function and go backward from
    there.

    We are specifically look for expressions that are nested/enclosed by other expressions.
    Given a forall loop that is nested within a for-loop, we say that the forall loop is
    contained within the for-loop.

    We are usually calling this where matchExpr is some loop and we want to see whether
    expr is contained in that loop. Since we sometimes do this for forall loops and for-loops,
    we can just generalize it to expressions.

    *** CALLED DURING NORMALIZATION and POST-RESOLUTION ***

    Arguments:
    expr -> current expression to test/look at
    matchExpr -> the expression we want to match on

    Return:
    true if expr is contained within matcExpr, false otherwise
*/

static bool doesExprContainExpr(Expr *expr,
                                Expr *matchExpr)
{
  bool retval = false;
  for (Expr* curr = expr->parentExpr; curr; curr = curr->parentExpr) {
    if (curr == matchExpr) {
      return true;
    }
  }
  // Check for enclosing function. If we find one, recursively call
  // this.
  if (FnSymbol *fn = toFnSymbol(expr->parentSymbol)) {
    forv_Vec(CallExpr, fnCall, *fn->calledBy) {
      retval = doesExprContainExpr(fnCall->parentExpr, matchExpr);
      if (retval) {
        return retval;
      }
    }
  }
  return retval;
} /* end of doesExprContainExpr */

//##################################################################################
/*
    Given an SymExpr, check that it is of the form

        Call move
          symexpr
          Call
            Symexpr fn funcName
            Symexpr arg1
            ...

    This is a utility function used in domainSymbolForArray() during post-resolution.
    We need to repeat this detection a few times and it gets messy.

    So we see whether symexpr's parent is a PRIM_MOVE and whether the RHS of the move
    is a call to the specified function. If it is, we'll return the Symbol for the
    first argument to the function call.

    However, we also need to detect the case where we have split initialization. In
    that case, we have something like:

        Call move
            symexpr
            Symexpr val init_coerce_tmp


    If we have that, we look at all SymExprs related to init_coerce_tmp and call this
    function (getFuncFirstArg) to look for the call to "chpl__coerceCopy". We also set
    isSplitInit to true.

    **** CALLED DURING POST-RESOLUTION ****

    Arguments:
    symexpr -> the symexpr to analyze
    funcName -> string of the function name to check for
    isSplitInit -> true if we detected split initialization, false otherwise

    Return:
    Symbol of the 1st argument to the function, NULL otherwise
*/
static Symbol *getFuncFirstArg(SymExpr *symexpr,
                               const char *funcName,
                               bool *isSplitInit)
{
  Symbol *retval = NULL;
  if (isCallExpr(symexpr->parentExpr)) {
    CallExpr *call = toCallExpr(symexpr->parentExpr);
    if (call->isPrimitive(PRIM_MOVE)) {
      if (isCallExpr(call->get(2))) {
        CallExpr *fnCall = toCallExpr(call->get(2));
        if (fnCall->resolvedFunction()) {
          if (fnCall->isNamed(funcName)) {
            retval = (toSymExpr(fnCall->get(1)))->symbol();
            return retval;
          }
        }
      }
      else {
        // May be split-init
        SymExpr *tmp = toSymExpr(call->get(2));
        if (Symbol *initCoerceTmp = tmp->symbol()) {
          if (initCoerceTmp->name == astr_init_coerce_tmp) {
            for_SymbolSymExprs(symexpr2, initCoerceTmp) {
              // avoid infinite recursion
              if (symexpr != symexpr2) {
                retval = getFuncFirstArg(symexpr2, "chpl__coerceCopy", isSplitInit);
                if (retval != NULL) {
                  *isSplitInit = true;
                  return retval;
                }
              }
            }
          }
        }
      }
    }
  }
  return retval;
} /* end of getFuncFirstArg */

//##################################################################################
/*
    Same as the above function but matches the function based on a primitive tag.

    Note: we do not need to look for split initialization, as this version of the
    function is only called when we already determined that we didn't have it.

    **** CALLED DURING POST-RESOLUTION ****

    Arguments:
    symexpr -> the symexpr to analyze
    prim -> primitive to match on

    Return:
    Symbol of the 1st argument to the function, NULL otherwise
*/
static Symbol *getFuncFirstArg(SymExpr *symexpr,
                               PrimitiveTag prim)
{
  Symbol *retval = NULL;
  if (isCallExpr(symexpr->parentExpr)) {
    CallExpr *call = toCallExpr(symexpr->parentExpr);
    if (call->isPrimitive(PRIM_MOVE)) {
      if (isCallExpr(call->get(2))) {
        CallExpr *fnCall = toCallExpr(call->get(2));
        if (fnCall->isPrimitive(prim)) {
          retval = (toSymExpr(fnCall->get(1)))->symbol();
        }
      }
    }
  }
  return retval;
} /* end of getFuncFirstArg */


//##################################################################################
/*
    Given an expression expr that is known to be within the ForallStmt forall,
    check to see if it is enclosed in any invalid constructs.

    We are specifically looking for the following cases:

    1.) expr cannot be in a forall that is enclosed in another forall
    2.) expr cannot be in an on statement
    3.) forall cannot be enclosed in a coforall, cobegin or begin

    Note, we do not go across call-sites here. That check was done
    in our pre-pass stage within cloneFunctionsWithInvalidCallSites().

    If we detect any invalid constructs, we return true.

    **** CALLED DURING NORMALIZATION ****

    Arguments:
    expr -> the expression to start from (A[B[i]])
    forall -> the loop that expr is known to be in

    Return:
    true if an invalid construct is found, false otherwise
*/
static bool checkForInvalidEnclosingConstructs(Expr *expr,
                                               ForallStmt *forall)
{
  // First, find the closest enclosing forall for expr, without going across
  // call-sites.
  ForallStmt *f = NULL;
  for (Expr *curr = expr->parentExpr; curr; curr = curr->parentExpr) {
    f = toForallStmt(curr);
    if (f != NULL) {
      break;
    }
  }
  // Simple check: if f is NOT the forall we passed in, it means that forall
  // is an "outer" forall that contains f, which in turn contains expr. This
  // is invalid, as we do not allow for A[B[i]] to be in a forall that is
  // nested in another forall
  if (f != forall) {
    return true;
  }

  // expr cannot be in an on-statement. This would allow for the remote
  // accesses A[B[i]] to be changed based on where the on statement is
  // executing the task. We would have to track changes to whatever the
  // on statement is "operating" on. That really isn't worth it, so just
  // invalidate the optimization instead. We stop this check once we
  // hit forall. To be complete, let's just ensure that A[B[i]] cannot be
  // in a coforall, cobegin, or begin as well.
  for (Expr *curr = expr; curr; curr = curr->parentExpr) {
    if (toForallStmt(curr) == forall) {
      break;
    }
    // sometimes get a "Migration: ** Unexpected call to blockInfoGet()"
    // when we see for and while loops. So just flat out skip over those
    if (toForLoop(curr) || toWhileStmt(curr)) {
      continue;
    }
    if (BlockStmt *block = toBlockStmt(curr)) {
      if (CallExpr *const info = block->blockInfoGet()) {
        bool retval = info->isPrimitive(PRIM_BLOCK_ON);
        retval = retval || info->isPrimitive(PRIM_BLOCK_BEGIN_ON);
        retval = retval || info->isPrimitive(PRIM_BLOCK_COBEGIN_ON);
        retval = retval || info->isPrimitive(PRIM_BLOCK_COFORALL_ON);
        retval = info->isPrimitive(PRIM_BLOCK_BEGIN);
        retval = retval || info->isPrimitive(PRIM_BLOCK_COBEGIN);
        retval = retval || info->isPrimitive(PRIM_BLOCK_COFORALL);
        if (retval) {
          return true;
        }
      }
    }
  }

  // Next, without going across call sites, check for the forall being inside
  // of a coforall, on, cobegin and begin. We also look for foralls. If we're here,
  // then the forall we found in the first step IS equal to the forall we passed
  // in. But that could still be enclosed in a forall.
  for (Expr *curr = forall->parentExpr; curr; curr = curr->parentExpr) {
    if (toForallStmt(curr)) {
      return true;
    }
    // sometimes get a "Migration: ** Unexpected call to blockInfoGet()"
    // for loops, so just flat out skip over them.
    if (toForLoop(curr) || toWhileStmt(curr)) {
      continue;
    }
    if (BlockStmt *block = toBlockStmt(curr)) {
      if (CallExpr *const info = block->blockInfoGet()) {
        bool retval = info->isPrimitive(PRIM_BLOCK_BEGIN);
        retval = retval || info->isPrimitive(PRIM_BLOCK_COBEGIN);
        retval = retval || info->isPrimitive(PRIM_BLOCK_COFORALL);
        retval = retval || info->isPrimitive(PRIM_BLOCK_BEGIN_ON);
        retval = retval || info->isPrimitive(PRIM_BLOCK_COBEGIN_ON);
        retval = retval || info->isPrimitive(PRIM_BLOCK_COFORALL_ON);
        if (retval) {
          return true;
        }
      }
    }
  }

  // If here, we didn't find any invalid constructs
  return false;

} /* end of checkForInvalidEnclosingConstructs */


//##################################################################################
/*
    Given a call site, determine whether it is enclosed in a forall, coforall,
    cobegin or begin statement. If we detect such a case, we return true.

    This works across function calls.

    We call this from cloneFunctionsWithInvalidCallSites() to determine whether
    a given call site for a function that contains a potential forall of interest
    is invalid.

    Note that this is slightly different from checkForInvalidEnclosingConstructs(),
    which is called from analyzeCandidateIE() during our "normal" pass. In that case,
    we do not go across function calls, as we already did that here.

    **** CALLED DURING NORMALIZATION ****

    Arguments:
    callSite -> the Expr to start from

    Return:
    true if an invalid construct is found, false otherwise
*/
static bool isCallSiteInvalid(Expr *callSite)
{
  for (Expr *curr = callSite->parentExpr; curr; curr = curr->parentExpr) {
    if (toForallStmt(curr)) {
      // call site is within a forall --> invalid
      return true;
    }
    // sometimes get a "Migration: ForLoop Unexpected call to blockInfoGet()"
    // message so just flat out skip over for-loops; same for while-loops
    if (toForLoop(curr)) {
      continue;
    }
    if (toWhileStmt(curr)) {
      continue;
    }
    if (BlockStmt *block = toBlockStmt(curr)) {
      if (CallExpr *const info = block->blockInfoGet()) {
        bool retval = info->isPrimitive(PRIM_BLOCK_BEGIN);
        retval = retval || info->isPrimitive(PRIM_BLOCK_COBEGIN);
        retval = retval || info->isPrimitive(PRIM_BLOCK_COFORALL);
        retval = retval || info->isPrimitive(PRIM_BLOCK_BEGIN_ON);
        retval = retval || info->isPrimitive(PRIM_BLOCK_COBEGIN_ON);
        retval = retval || info->isPrimitive(PRIM_BLOCK_COFORALL_ON);
        if (retval) {
          // callSite is within a coforall/cobegin/begin --> invalid
          return true;
        }
      }
    }
  }

  // If we're here, then we didn't find a nested forall or other construct
  // within the current function. So check to see if callSite is within
  // a function itself. If so, find all call-sites and check for enclosing constructs
  // at each call site.
  if (FnSymbol *fn = toFnSymbol(callSite->parentSymbol)) {
    forv_Vec(CallExpr, fnCall, gCallExprs) {
      if (fnCall->isNamed(fn->name)) {
        bool retval = isCallSiteInvalid((Expr *)fnCall);
        if (retval) {
          return true;
        }
      }
    }
  }

  // If here, we didn't find any invalid constructs (within the function that
  // contains expr).
  return false;

} /* end of isCallSiteInvalid */

//##################################################################################
/*
    Given a CallExpr call, return true if it is an assignment operator. This
    includes =, +=, -=, etc.

    **** CALLED DURING NORMALIZATION ****

    Arguments:
    call -> the CallExpr to check

    Return:
    true if a call is an assignment, false otherwise
*/
static bool isAssignment(CallExpr *call)
{
  if (call->isNamedAstr(astrSassign) == true) {
    return true;
  }
  if (call->isNamed("+=")  == true ||
      call->isNamed("-=")  == true ||
      call->isNamed("*=")  == true ||
      call->isNamed("/=")  == true ||
      call->isNamed("**=") == true ||
      call->isNamed("%=")  == true ||
      call->isNamed("&=")  == true ||
      call->isNamed("|=")  == true ||
      call->isNamed("^=")  == true ||
      call->isNamed("&&=") == true ||
      call->isNamed("||=") == true ||
      call->isNamed("<<=") == true ||
      call->isNamed(">>=") == true) {
    return true;
  }

  return false;

} /* end of isAssignment */


// Added by tbrolin 9/13/2022 - present
//
// Support for the adaptive remote prefetching (ARP) optimization.

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                      Normalization Related Functions                      //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
/*
    Entry function for the adaptive remote prefetching (ARP) optimization. The
    basic idea behind ARP is to insert calls to prefetch data into the remote
    cache. Each core (i.e., task) has its own remote cache that is managed by
    Chapel's runtime. When a remote get is issued by some task on locale,
    the data is brought over and stored in that task's remote cache. If the data
    is accessed again, the cache is searched first. Chapel allows for users to
    insert manual prefetches for remote data (well, it is not necessarily a
    user facing feature right now). Much like a CPU cache, the idea is to issue
    a non-blocking get for the data we will need in the future, so when we do
    need to access the data, it will be there already.

    When dealing with irregular reads like A[B[i]], the remote cache's automatic
    readahead is not going to work since it looks specifically for sequential accesses.
    However, a user could insert their own prefetch call, like prefetch(A[B[i+dist]]),
    where "dist" is some integer that represents how far ahead to prefetch for (assuming
    A[B[i]] is in a loop that is incrementing i).
    
    So the goal of ARP is to recognize situations where we can prefetch and automatically
    insert the prefetch calls. The "adpative" part comes in because we need a way to dial
    in the prefetch distance. Because each task performing a forall has its own remote cache,
    it needs to have its own distance. It is infeasible to suggest that the user would
    manage all of these individual distances. To this end, as the forall loop runs, each
    task will tune its own prefetch distance to optimize the prefetches. We have added
    lightweight counters to the remote cache that tell us whether the prefetches were
    unused (kicked out of the cache before being accessed) or waited on (did not arrive
    into the cache by the time we needed it). By running for "a bit" and then looking at
    these counters, a task should be able to make some decision about whether to increase
    or decrease the distance.

    The adaptive part is not going to be implemented within the compiler code below.
    It is purely on the Chapel end. The purpose of the compiler code is to do the code
    transformations and static analysis. The functions we insert calls to here will do
    the "real" optimization.

    With all that said, the end result of this optimization will be something like:

        reset_prefetch_counters();
        const lastValidIndex = getLastLoopIndex(..);
        const loopStride = getLoopStride(..);
        const numSampleIterations = getPrefetchSampleSize(..);
        forall i in ... with (var prefetchDistance, var count, var window) {
            param staticPrefetchCheck = chpl__isPrefetchSupported(..);
            if staticPrefetchCheck == true {
                if count < numSampleIterations {
                    count += 1
                }
                else {
                    adjustPrefetchDistance(prefetchDistance, window);
                    count = 0;
                }
                if (i+(prefetchDistance * loopStride)) <= lastValidIndex {
                    if isArray(loopIteratorSym) {
                        prefetch for array
                    }
                    else {
                        prefetch for domains and ranges
                    }
                }
            }
            original access replaced with primitive
        }

    As can be seen, there are a few code transformations to perform. But there are several different
    scenarios we need to handle, which may result in slightly different transformations than what we see
    above.

    Arguments:
    forall -> the forall loop to optimize

    Return:
    None
*/
void adaptiveRemotePrefetching(ForallStmt *forall)
{
  // If this loop has already been checked for this optimization,
  // return. This happens when we make a clone of the forall via
  // other optimizations.
  if (forall->optInfo.adaptiveRemotePrefetchingChecked) {
    return;
  }
  forall->optInfo.adaptiveRemotePrefetchingChecked = true;

  // Exit if this loop is the inspector loop from the IE optimization.
  // Regardless of what kind of accesses are still left in the inspector
  // loop, we don't want to do anything to them.
  if (forall->optInfo.cloneTypeIE == INSPECTOR) {
    return;
  }

  // Gather forall info. This gets us some information regarding the
  // loop's domain.
  if (!forall->optInfo.infoGathered) {
    gatherForallInfo(forall);
  }

  // Look for candidates in the loop. A candidate is A[B[i]] that
  // is on the RHS of an operation (i.e., a read). We do additional checks
  // regarding the loop domain. Note that this A[B[i]] may have been a
  // candidate for the IE optimization as well. Since we do the IE first,
  // we would have cloned the forall and replaced A[B[i]] with the IE primitive.
  // So the forall/A[B[i]] we see here now is the original (or some other unmodified
  // clone).
  findCandidatesARP(forall);

  // Only continue if we found candidates
  if (forall->optInfo.adaptiveRemotePrefetchingCandidates.size() == 0) {
    return;
  }

  forall->optInfo.arpID = gARPForallID++;

  // If we're here, then we have candidates. So generate the optimized
  // version of the forall loop. Note that we do not do any loop cloning
  // for this optimization, rather than "generate" we are modifying.
  
  optimizeLoopARP(forall);

} /* end of adaptivePrefetching */

//##################################################################################
/*
    Given a ForallStmt, look for candidates for the adaptive remote prefetching (ARP)
    optimization. We look for A[B[i]] accesses on the RHS of an operation (i.e.,
    reads). However, in this function we just look for A[B[i]], and then do the
    in-depth analysis in analyzeCandidateARP() to ensure it is a valid candidate.

    When we say "A[B[i]]", it can be much more complex/general than that. The
    "i" could be any expression as long as it uses the loop index variable that is
    yielded by the closest enclosing loop for the candidate access. Furthermore, B[i] could
    be used in an expression that ultimately indexes into A. So in general, we're
    looking at something like A[expr(B[expr])]. Determining that we have valid
    expressions is done in analyzeCandidateARP().

    Candidates that we find are added to the forall's optInfo vector of adaptive
    remote prefetching candidates.

    Arguments:
    forall -> the forall loop to analyze

    Return:
    None
*/
static void findCandidatesARP(ForallStmt* forall)
{
  std::vector<CallExpr *> callExprs;
  collectCallExprs(forall->loopBody(), callExprs);

  for_vector(CallExpr, call, callExprs) {
    // 1.) Ensure that call has a call-base, which means we
    //     have something like B[expr].
    if (getCallBase(call)) {
      // Correctly handles triple nested things like A[B[C[i]]].
      // We will apply the optimization to C[i]/B[C[i]], but not
      // to B[C[i]]/A[B[C[i]].
      if (doesCallHaveNestedCallBaseIE(call)) {
        continue;
      }

      // 2.) From call, look "up" until we find a CallExpr that
      //     we can get the call-base for. That would be "A" from
      //     something like A[B[expr]]. We are more flexible here when
      //     compared to the IE optimization, as we are not limited to
      //     just binary operations. We only consider the candidate invalid
      //     if we hit something that isn't a CallExpr. However, if we find
      //     one of the primitives, we cannot proceed with this candidate.
      CallExpr *parentCall = NULL;
      CallExpr *curr = call;
      bool isValid = true;
      while (isValid) {
        if ((curr = toCallExpr(curr->parentExpr))) {
          if (curr->isPrimitive(PRIM_MAYBE_IRREG_ACCESS) || 
              curr->isPrimitive(PRIM_MAYBE_IRREG_AGGREGATE_WRITE) ||
              curr->isPrimitive(PRIM_MAYBE_PREFETCH_CANDIDATE)) {
            isValid = false;
          }
          else if (getCallBase(curr)) {
            parentCall = curr;
            break;
          }
        }
        else {
          isValid = false;
        }
      } /* end of while isValid */
      if (isValid == false) { continue; }
      INT_ASSERT(parentCall != NULL);

      // Before we do the analysis, a quick check is to ensure
      // that parentCall is not in one of our other optimization primitives.
      // Likewise, parentCall cannot be part of an existing prefetch call.
      CallExpr *tmp = parentCall;
      while (tmp != NULL && tmp->parentExpr != NULL) {
        if (tmp->isPrimitive(PRIM_MAYBE_IRREG_ACCESS) || 
            tmp->isPrimitive(PRIM_MAYBE_IRREG_AGGREGATE_WRITE) ||
            tmp->isPrimitive(PRIM_MAYBE_PREFETCH_CANDIDATE)) {

          isValid = false;
          break;
        }
        else if (tmp->isNamed("prefetch")) {
          isValid = false;
          break;
        }
        tmp = toCallExpr(tmp->parentExpr);
      }
      if (isValid == false) { continue; }

      // Now we have call and parentCall, so do further
      // analysis
      analyzeCandidateARP(call, parentCall, forall);
    } /* end of if getCallBase */
  } /* end of for_vector */
} /* end of findCandidatesARP */

//##################################################################################
/*
    Given an irregular access of form A[expr(B[expr])], perform analysis to see 
    if it is a valid candidate for the adpative remote prefetching (ARP) optimization.

    First, A and B must be arrays but we cannot determine that until prefolding. So
    that is left until then.

    Next, we need to ensure that A[B[i]] is on the RHS of an operation (i.e., it is
    a read).

    Beyond that, most of the checks we do are to ensure that the loop that contains
    the candidate has the right structure. Specifically, it is this loop's index
    variable that must be used somewhere in the candidate access. This allows us to
    ensure/reason about how the loop "walks" through accesss pattern. This is crucial 
    because part of prefetching is to look ahead some number of iterations. This basically 
    means adding the prefetch distance to the loop index variable.
    
    If all checks pass, we create the candidate and add it to the vector. The
    candidate info will contain all of the info we need to move forward with
    the optimization.

    Arguments:
    call -> the B[expr] CallExpr
    parentCall -> the A[expr(B[expr])] CallExpr
    forall -> the forall loop to analyze

    Return:
    None
*/
static void analyzeCandidateARP(CallExpr *call,
                                CallExpr *parentCall,
                                ForallStmt *forall)
{
  Symbol *callBase = getCallBase(call);
  Symbol *parentCallBase = getCallBase(parentCall);

  // Only print info about this candidate if we haven't processed it before.
  bool oldFReport = fReportIrregArrayAccesses;
  if (gCandidatesAnalyzedARP.count(parentCall->stringLoc()) != 0) {
    fReportIrregArrayAccesses = false;
  }
  else {
    gCandidatesAnalyzedARP.insert(parentCall->stringLoc());
  }

  if (fReportIrregArrayAccesses) {
    printf("+ [ADAPTIVE REMOTE PREFETCH] Considering candidate irregular access at %s (forall at %s)\n", parentCall->stringLoc(),
                                                                                                         forall->stringLoc());
    printf("\t- Parent: %s, Call: %s\n", parentCallBase->name, callBase->name);
  }

  // A[B[i]] cannot be on the LHS of an operation. We can check for this
  // be seeing if parentCall's parent is an assignment, and if parentCall is
  // the first argument to the assignment.
  if (CallExpr *opCall = toCallExpr(parentCall->parentExpr)) {
    if (isAssignment(opCall)) {
      if (parentCall == toCallExpr(opCall->get(1))) {
        if (fReportIrregArrayAccesses) {
          printf("\t\t !!! irregular access cannot be on LHS on assignment\n");
        }
        fReportIrregArrayAccesses = oldFReport;
        return;
      }
    }
    else if (opCall->isNamed(".")  == true) {
      // If here, then we have something like A[B[i]].foo or
      // A[B[i]].func(). If func() takes in an argument, we could tell that
      // and abort. But if it does not take in an argument, it looks the same
      // as A[B[i]].foo, where foo would be a field. That would be allowed but
      // since we can't really tell the difference at this point, we don't allow
      // any "." expressions here.
      if (fReportIrregArrayAccesses) {
        printf("\t\t !!! irregular access cannot be on LHS on assignment\n");
      }
      fReportIrregArrayAccesses = oldFReport;
      return;
    }
  }

  // Now we can analyze the loop(s). We could have the A[B[i]] access directly inside
  // of the forall, or it could be in a for-loop that is itself nested in the forall.
  // Regardless, we want to look at the loop structure for whatever loop directly
  // contains the A[B[i]] access.
  int currSize = forall->optInfo.adaptiveRemotePrefetchingCandidates.size();
  ForLoop *f = findEnclosingForLoop(call);
  compute_call_sites(); // needed by doesExprContainExpr
  if (f != NULL && doesExprContainExpr(f, forall)) {
    // f is a for-loop that contains A[B[i]], and f is nested within
    // the forall. So f is the loop we want to analyze further.
    if (fReportIrregArrayAccesses) {
      printf("\t\t- Candidate access is in a for-loop (%s) that is nested in the forall\n", f->stringLoc());
    }
    if (!f->forLoopInfoGathered) {
      gatherForLoopInfo(f);
    }
    analyzeLoopStructureARP(parentCall,
                            call,
                            f->multiDIndices,
                            f->iterSym,
                            f->dotDomIterSym,
                            NULL,
                            f,
                            forall->optInfo.adaptiveRemotePrefetchingCandidates);
  }
  else {
    // the A[B[i]] access is directly contained within the forall, so
    // the forall is what we want to analyze further.
    analyzeLoopStructureARP(parentCall,
                            call,
                            forall->optInfo.multiDIndices,
                            forall->optInfo.iterSym,
                            forall->optInfo.dotDomIterSym,
                            forall,
                            NULL,
                            forall->optInfo.adaptiveRemotePrefetchingCandidates);
  }
  
  if (currSize < forall->optInfo.adaptiveRemotePrefetchingCandidates.size()) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t- enclosing loop(s) have valid structure\n");
    }
  }
  fReportIrregArrayAccesses = oldFReport;
} /* end of analyzeCandidateARP */

//##################################################################################
/*
    Determines whether the specified loop has a valid structure for the adaptive
    remote prefetching (ARP) optimization. If it does, it extracts various details
    that we'll need later and wraps them into a AdaptiveRemotePrefetchingCandidate
    struct and adds it to the vector of candidates.

    First, we need to ensure that the loop index variable is used in the index-expression
    to A[B[..]]. We pass in "parentCall", which is the A[expr(B[expr])]CallExpr. 

    Also note that we do not support loops that have zippered iterators or otherwise
    yield multiple loop index variables. This mostly has to do with how we transform
    the loop for the optimization, which requires a single loop iterator.

    Next, we need to ensure the loop itself has a supported form/structure.
    For a loop to be valid, it must have one of three forms:

        (1) for/forall loops that iterate over non-associative arrays/domains
                e.g., "for/forall elem in A where A" is an array or domain
        (2) for/forall loops that iterate over non-associative domains
                e.g., "for/forall i in A.domain"
        (3) for/forall loops that iterate over an explicit range
                e.g., "for/forall i in 0..#N"

    We also allow for the "by" clause to be used; when used on a loop that
    looks like (1) and (2), it actually will move our analysis to the same
    checks we do for (3). Case (3) is fairly complicated, so it will be performed
    in its own function.

    The array/domain in (1) and (2) must be non-associative because we need to be
    able to reason about the stride of the loop. In a language like C, this is the
    "i++" part of the loop. In Chapel, the for-each style of loops in (1) and (2)
    have an implicit stride, namely the stride of the underlying domain/array.
    An associative domain/array DOES NOT have a stride, as it is basically a hash
    table. Knowing the stride is key to effectively looking ahead at the loop
    iterations. For case (3), a range like "0..#N" has an implicit stride of 1,
    but we could also have "0..#N by 3", where the stride is explicitly 3. This
    is easy enough to detect at compile time.

    We cannot determine that the "B" in "for i in B" is an array or domain, let
    alone a non-associative array/domain. So that check is left for prefolding.
    But we can ensure that we do have the general form for one of the 3 cases
    above.
    
    To summarize, the following conditions will result a candidate NOT being created:

        A.) loop has zippered iterators/yields more than 1 loop index variable
        B.) loop index variable is NOT used in parentCall
        C.) loop is not one of the three forms described above

    Assuming that everything does pass, we create a candidate and add it to the vector,
    We want to extract a few details, like the stride of the loop, if possible.

    Arguments:
    parentCall -> the A[expr(B[expr])] CallExpr
    call -> the B[expr] CallExpr
    multiDIndices -> vector of loop index symbols
    iterSym -> vector of loop iterator symbols
    dotDomIterSym -> vector of loop iterator symbols when we had "B.domain"
    forall -> the forall loop, if parentCall is directly nested in it; NULL otherwise
    forloop -> the for loop that parentCall is directly nested in, or NULL
    candidates -> vector that we add a new candidate to
    
    Return:
    None; if the loop structure is valid we create a candidate and add it to
    the candidates vector.
*/
static void analyzeLoopStructureARP(CallExpr *parentCall,
                                    CallExpr *call,
                                    std::vector< std::vector<Symbol *> > multiDIndices,
                                    std::vector<Symbol *> iterSym,
                                    std::vector<Symbol *> dotDomIterSym,
                                    ForallStmt *forall,
                                    ForLoop *forloop,
                                    std::vector<AdaptiveRemotePrefetchingCandidate> &candidates)
{
  // 1.) Does the loop yield multiple index variables? This is the case if
  //     multiDIndices has more than 1 element. It seems that something
  //     like for (i,j) in A will have a single vector in multiDIndices but
  //     that vector has multiple elements. So we quit in that case.
  if (multiDIndices.size() != 1) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t!!! loop cannot yield more than one index\n");
    }
    return;
  }
  if (multiDIndices[0].size() != 1) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t!!! loop cannot yield more than one index\n");
    }
    return;
  }

  // 2.) We know we have a single loop index variable. So extract that and
  //     ensure that it is used somewhere in parentCall. We may have nested CallExprs
  //     so we'll use the utility collectSymExprsFor() to find uses of the symbol.
  //     NOTE: I am still not sure why multiDIndices is a vector of vectors.
  //     The gatherForallInfo function seems to only be capable of adding a
  //     single Symbol* to the "inner" vector anyways, so we just have a vector
  //     of single-element vectors.
  Symbol *loopIndexSym = multiDIndices[0][0];
  INT_ASSERT(loopIndexSym != NULL);
  std::vector<SymExpr *> symexprs;
  collectSymExprsFor(parentCall, loopIndexSym, symexprs);
  if (symexprs.size() == 0) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t!!! loop index %s must be used in %s[expr] access\n", loopIndexSym->name, getCallBase(call)->name);
    }
    return;
  }
  // Need to make sure that loopIndexSym itself is not a baseExpr or something.
  // We would see that in the NAS-CG utils where we have "forall coord in coords { ...row_nnz[coord(0)] }.
  // Here, coord(0) is call and loopIndexSym is corod, but call's baseExpr is coord.
  for (auto &symexpr : symexprs) {
    if (CallExpr *symCall = toCallExpr(symexpr->parentExpr)) {
      if (Symbol *callBase = getCallBase(symCall)) {
        if (callBase == loopIndexSym) {
          if (fReportIrregArrayAccesses) {
            printf("\t\t!!! loop index %s cannot be used as a call-base\n", loopIndexSym->name);
          }
          return;
        }
      }
    }
  }

  // 3.) We know we have a single loop index variable and it is used at least once
  //     within the A[expr(B[expr])] access. Now we want to ensure the loop itself has the
  //     proper structure. It must be one of the 3 cases outlined in the comment
  //     above. Recall that we do not allow for zippered iterators, so there should
  //     just be a single iterator to look at.
  //
  // Do we have case (1): for/forall i in A? If these vectors have non-NULL
  // values as checked below, then we DO NOT have an explicit "by" clause.
  // Therefore, the stride of the loop will be implicitly defined by the
  // stride of A (i.e., A.domain.stride if A is an array, or just A.stride
  // if A is a domain itself).
  if (iterSym[0] != NULL && dotDomIterSym[0] == NULL) {
    AdaptiveRemotePrefetchingCandidate candidate;
    candidate.forloop = forloop;
    candidate.byClauseStride = NULL;
    candidate.loopIteratorType = ARRAY_OR_DOMAIN;
    candidate.loopIteratorSym = iterSym[0];
    candidate.parentCall = parentCall;
    candidate.call = call;
    candidate.loopRangeOperator = NOT_A_RANGE;
    candidate.rangeStart = NULL;
    candidate.rangeEnd = NULL;
    candidate.prefetchIter_idx = NULL;
    candidate.originalIter_idx = loopIndexSym;
    candidate.prefetchDistance = NULL;
    candidates.push_back(candidate);
  } 
  // Do we have case (2): for/forall in A.domain? If so, pretty much the same
  // setup as case (1), in that we don't have a by clause
  else if (dotDomIterSym[0] != NULL) {
    AdaptiveRemotePrefetchingCandidate candidate;
    candidate.forloop = forloop;
    candidate.byClauseStride = NULL;
    candidate.loopIteratorType = EXPLICIT_DOMAIN;
    candidate.loopIteratorSym = dotDomIterSym[0];
    candidate.parentCall = parentCall;
    candidate.call = call;
    candidate.loopRangeOperator = NOT_A_RANGE;
    candidate.rangeStart = NULL;
    candidate.rangeEnd = NULL;
    candidate.prefetchIter_idx = NULL;
    candidate.originalIter_idx = loopIndexSym;
    candidate.prefetchDistance = NULL;
    candidates.push_back(candidate);
  }
  // Do we have case (3)? Case (3) handles explicit ranges, as well as any use
  // of "by". If we had something like "forall i in A.domain by 2", we would not
  // have triggered case (2). That is because of how "by" changes the way the AST
  // looks for the loop (i.e., gatherForallInfo and gatherForLoopInfo will not find
  // the loop iterator symbols)
  else {
    loopIteratesOverRangeOrUsesByClause(parentCall,
                                        call,
                                        forall,
                                        forloop,
                                        loopIndexSym,
                                        candidates);
  }

} /* end of analyzeLoopStructureARP */

//##################################################################################
/*
    This function is called from analyzeLoopStructureARP() when we have a loop that
    fits case (3). This is when the loop iterates over a range, or it iterates over
    an array/domain that uses a "by" clause.

    What we do here is basic pattern matching on the AST to detect whether we have
    a range or an array/domain with a by clause. For ranges, we need to look for the
    use of "#" and "<", which look different in the AST.

    The end result of this, if we find what we are looking for, is creating a candidate
    and adding it to the candidates vector.

    Arguments:
    parentCall -> the A[expr(B[expr])] CallExpr
    call -> the B[expr] CallExpr
    forall -> the forall loop, if parentCall is directly nested in it; NULL otherwise
    forloop -> the for loop that parentCall is directly nested in, or NULL
    loopIndexSym -> the loop index variable (we add it to a candidate if we make one).
    candidates -> vector that we add a new candidate to
    
    Return:
    None; if the loop structure is valid we create a candidate and add it to
    the candidates vector.
*/
static void loopIteratesOverRangeOrUsesByClause(CallExpr *parentCall,
                                                CallExpr *call,
                                                ForallStmt *forall,
                                                ForLoop *forloop,
                                                Symbol *loopIndexSym,
                                                std::vector<AdaptiveRemotePrefetchingCandidate> &candidates)
{
  // These are all the "things" we hope to fill in below. If we have a valid loop,
  // we'll create the candidate based on these. We know we don't have a candidate if
  // loopIteratorType is still set to INVALID_LOOP_TYPE by the end of our checks.
  Expr *byClauseStride = NULL;
  PrefetchLoopIteratorType loopIteratorType = INVALID_LOOP_TYPE;
  Symbol *loopIteratorSym = NULL;
  LoopRangeOperatorType loopRangeOperator = NOT_A_RANGE;
  Expr *rangeStart = NULL;
  Expr *rangeEnd = NULL;
  
  // There are various cases for us to consider for a forall/for loop:
  // Does it iterate over a range? Does it use a by clause? We can do
  // pattern matching for this. But first we need to get the call that
  // "creates" the loop iterator. From that, we can do the matching.
  // Many of the checks are the same for a forall and a for loop.
  CallExpr *iterCall = NULL;
  if (forall != NULL) {
    Expr *firstExpr = forall->getFirstExpr();
    Expr *nextExpr = forall->getNextExpr(firstExpr);
    // if nextExpr is a CallExpr, then we have what we want. Else, we 
    // may have a case like forall i in A.domain by 2. In this case, 
    // nextExpr is a SymExpr call_tmp. If so, look for a PRIM_MOVE
    // that where the RHS is a CallExpr
    if (isCallExpr(nextExpr)) {
      iterCall = toCallExpr(nextExpr);
    }
    else  {
      Symbol *iterSym = (toSymExpr(nextExpr))->symbol();
      if (iterSym == NULL) { return ;}
      for_SymbolSymExprs(symexpr, iterSym) {
        if (CallExpr *symCall = toCallExpr(symexpr->parentExpr)) {
          if (symCall->isPrimitive(PRIM_MOVE) && symCall->get(1) == symexpr) {
            iterCall = toCallExpr(symCall->get(2));
            if (iterCall != NULL) { break; }
          }
        }
      }
    }
  } /* end forall != NULL */
  else if (forloop != NULL) {
    Symbol *forloopIter = forloop->iteratorGet()->symbol();
    if (forloopIter == NULL) { return; }
    // Look at the SymExprs involving forloopIter. We're looking for
    // a PRIM_MOVE that calls _getIterator. When we find that, break out.
    for_SymbolSymExprs(symexpr, forloopIter) {
      if (CallExpr *symCall = toCallExpr(symexpr->parentExpr)) {
        if (symCall->isPrimitive(PRIM_MOVE) && symCall->get(1) == symexpr) {
          if (CallExpr *getIterCall = toCallExpr(symCall->get(2))) {
            if (getIterCall->isNamed("_getIterator")) {
              iterCall = toCallExpr(getIterCall->get(1));
              break;
            }
          }
        }
      }
    } /* end of for_SymbolSymExprs */
  } /* end of forloop != NULL */

  // If iterCall is NULL, we failed to get the loop iterator
  if (iterCall == NULL) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t!!! cannot statically determine loop iterator\n");
    }
    return;
  }

  // Now we can do pattern matching to determine what kind of loop we have
    
  //##############################################################
  //
  //  We have a "by" clause in the iterator. Possible cases are
  //
  //      forall/for i in A.domain by X
  //      forall/for i in 0..10 by X (for-loop calls chpl_direct_strided_range_iter)
  //      forall/for i in 0..<10 by X (for-loop calls chpl_direct_strided_range_iter)
  //      forall/for i in 0..#10 by X
  //      forall/for i in A by X 
  //
  //##############################################################
  if (iterCall->isNamed("chpl_by") || iterCall->isNamed("chpl_direct_strided_range_iter")) {
    // Extract the Expr that is used by the "by" clause; if we failed to do that,
    // then return
    byClauseStride = toExpr(iterCall->get(iterCall->argList.length));
    if (byClauseStride == NULL) { return; }

    // ### Handles the A.domain or (some) range cases ###
    // Is the first argument to iterCall a CallExpr? If so, see if it is ".domain", or
    // one of the range operators
    if (CallExpr *firstArgCall = toCallExpr(iterCall->get(1))) {
      // ### Handles the A.domain by X case ###
      if (Symbol *dotDomSym = getDotDomBaseSym((Expr*)firstArgCall)) {
        // We have something like forall i in A.domain; dotDomSym will be A
        loopIteratorType = EXPLICIT_DOMAIN;
        loopIteratorSym = dotDomSym;
      } /* dotDomSym = getDotDomBaseSym */

      // ### Handles the 0..10 by X and 0..<10 by X cases for forall loops ###
      else if (firstArgCall->isNamed("chpl_build_bounded_range")) {
        // First argument to firstArgCall is the range start,
        // second arugment is the range end
        rangeStart = toExpr(firstArgCall->get(1));
        rangeEnd = toExpr(firstArgCall->get(2));
        // What kind of range operator do we have, "<" or nothing?
        // We look at rangeEnd and see if it is a call to chpl__nudgeHighBound
        // for "<". If it is not a call, then it is "nothing". If it is a call
        // but not the one for "<", then I am not sure what it is, so exit.
        if (CallExpr *rangeOp = toCallExpr(rangeEnd)) {
          if (rangeOp->isNamed("chpl__nudgeHighBound")) {
            loopRangeOperator = NUDGE_HIGH_BOUND;
            loopIteratorType = RANGE;
          }
          else { return; }
        }
        else {
          loopRangeOperator = NO_OPERATOR;
          loopIteratorType = RANGE;
        }
      } /* firstArgCall is chpl_build_bounded_range */

      // ### Handles the 0..#10 by X case ###
      else if (firstArgCall->isNamed("#")) {
        // The last argument to "#" is the end of the range.
        rangeEnd = toExpr(firstArgCall->get(firstArgCall->argList.length));
        // Let's make sure that the first argument is to chpl_build_low_bounded_range
        if (CallExpr *countFirstArg = toCallExpr(firstArgCall->get(1))) {
          if (countFirstArg->isNamed("chpl_build_low_bounded_range")) {
            // The first argument to chpl_build_low_bounded_range is the range start
            rangeStart = toExpr(countFirstArg->get(1));
          }
        }
        if (rangeStart == NULL) { return; }
        
        loopIteratorType = RANGE;
        loopRangeOperator = COUNT_OPERATOR;
      } /* firstArgCall is "#" */

    } /* end iterCall's first arg is a CallExpr */   

    // ## Handles the 0...10 by X and 0..<10 by X case for for-loops
    // iterCall is chpl_direct_strided_range_iter
    else if (iterCall->isNamed("chpl_direct_strided_range_iter")) {
      rangeStart = toExpr(iterCall->get(1));
      rangeEnd = toExpr(iterCall->get(2));
      if (CallExpr *rangeOp = toCallExpr(rangeEnd)) {
        if (rangeOp->isNamed("chpl__nudgeHighBound")) {
          loopRangeOperator = NUDGE_HIGH_BOUND;
          loopIteratorType = RANGE;
        }
        else {
          // perhaps the end of the range is a function, like
          // for i 0..foo(); in any case, it isn't a <10 case
          loopRangeOperator = NO_OPERATOR;
          loopIteratorType = RANGE;
        }
      }
      else {
        loopRangeOperator = NO_OPERATOR;
        loopIteratorType = RANGE;
      }
    } /* end iterCall is chpl_direct_strided_range_iter */
      
    // ### Handles the forall i in A by X case ###
    else {
      // Here if the first argument to chpl_by is not a CallExpr.
      // It means the loop iterator sym is whatever the first arg to
      // chpl_by is
      loopIteratorSym = (toSymExpr(iterCall->get(1)))->symbol();
      if (loopIteratorSym == NULL) { return; }
      loopIteratorType = ARRAY_OR_DOMAIN;
    } 
  } /* iterCall->isNamed("chpl_by") or chpl_direct_strided_range_iter */

  //##############################################################
  //
  //  We DO NOT have a "by" clause in the iterator. This means we
  //  can only have ranges:
  //
  //      forall/for i in 0..10 (for-loop uses chpl_direct_range_iter)
  //      forall/for i in 0..<10
  //      forall/for i in 0..#10 (for-loop uses chpl_direct_counted_range_iter)
  //
  //##############################################################
  else {
    // ### Handle case for 0..10 and 0..<10 ###
    if (iterCall->isNamed("chpl_build_bounded_range") || iterCall->isNamed("chpl_direct_range_iter")) {
      // First argument to iterCall is the range start,
      // second arugment is the range end
      rangeStart = toExpr(iterCall->get(1));
      rangeEnd = toExpr(iterCall->get(2));
      // What kind of range operator do we have, "<" or nothing?
      // We look at rangeEnd and see if it is a call to chpl__nudgeHighBound
      // for "<". If it is not a call, then it is "nothing". If it is a call
      // but not the one for "<", then I am not sure what it is, so exit.
      if (CallExpr *rangeOp = toCallExpr(rangeEnd)) {
        if (rangeOp->isNamed("chpl__nudgeHighBound")) {
          loopRangeOperator = NUDGE_HIGH_BOUND;
          loopIteratorType = RANGE;
        }
        else {
          // perhaps the end of the range is a function, like
          // for i 0..foo(); in any case, it isn't a <10 case
          loopRangeOperator = NO_OPERATOR;
          loopIteratorType = RANGE;
        }
      }
      else {
        loopRangeOperator = NO_OPERATOR;
        loopIteratorType = RANGE;
      }
    } /* iterCall is chpl_build_bounded_range or chpl_direct_range_iter */

    // ### Handle case for 0..#10 ###
    else if (iterCall->isNamed("#") || iterCall->isNamed("chpl_direct_counted_range_iter")) {
      // The last argument to "#"/chpl_direct_counted_range_iter is the end of the range.
      rangeEnd = toExpr(iterCall->get(iterCall->argList.length));
      // Make sure first arg is call to chpl_build_low_bounded_range -- this is the forall case
      if (iterCall->isNamed("#")) {
        if (CallExpr *firstArgCall = toCallExpr(iterCall->get(1))) {
          if (firstArgCall->isNamed("chpl_build_low_bounded_range")) {
            rangeStart = toExpr(firstArgCall->get(1));
          }
        }
      }
      else {
        // for-loop case, the first arg to chpl_direct_counted_range_iter is the range start
        rangeStart = toExpr(iterCall->get(1));
      }
      if (rangeStart == NULL) { return; }
      loopIteratorType = RANGE;
      loopRangeOperator = COUNT_OPERATOR; 
    } /* iterCall is # operator */

  } /* end of else for forall not having a by clause */

  // If loopIteratorType is still INVALID_LOOP_TYPE, then we do not have a valid
  // candidate.
  if (loopIteratorType == INVALID_LOOP_TYPE) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t!!! loop containing irregular access has invalid structure\n");
    }
    return;
  }
  else {
    if (fReportIrregArrayAccesses) {
      printf("\t\t- loop containing irregular access has valid structure\n");
    }
  }
  // Otherwise, create the candidate and add it to the vector
  AdaptiveRemotePrefetchingCandidate candidate;
  candidate.forloop = forloop;
  candidate.byClauseStride = byClauseStride;
  candidate.loopIteratorType = loopIteratorType;
  candidate.loopIteratorSym = loopIteratorSym;
  candidate.parentCall = parentCall;
  candidate.call = call;
  candidate.loopRangeOperator = loopRangeOperator;
  candidate.rangeStart = rangeStart;
  candidate.rangeEnd = rangeEnd;
  candidate.prefetchIter_idx = NULL;
  candidate.originalIter_idx = loopIndexSym;
  candidate.prefetchDistance = NULL;
  candidates.push_back(candidate); 

  return;
} /* end of loopIteratesOverRangeOrUsesByClause */

//##################################################################################
/*
    When this function is called, we have at least one candidate for the adaptive
    remote prefetching (ARP) optimization. We now need to optimize the loop to 
    actually perform the optimization. We'll break this down in the following steps.
    Unless stated otherwise, when we say "the loop", we mean the loop that directly
    contains the candidate access (could be the forall, or a for-loop nested in the
    forall):

    1.) In some cases, we need to replace/update the loop's iterator so it yields
        the information we need. See updateLoopIteratorARP() for details.

    2.) Same as above, but now we need to update the loop index variable to receive
        a tuple, which is what the custom iterator from (1) yields. See
        updateLoopIndexVariableARP() for details.

    3.) Add the const declaration for the several relevant variables: number of sample 
        iterations we run before attempting to adjust the distance, the stride of the
        loop and the last valid index of the loop.

    4.) Add per-task variables to the forall: prefetch distance, count that tells us
        when to adjust the distance and a window count used in the distance adjustment.
        We add these variables for each prefetch candidate. 
    
    5.) Add an if-then structure that performs a param/static check to see whether we
        can do prefetching. All code generated after this step is placed within the
        then-block of this if statement.

    6.) Add an if-then-structure that checks if the count from (4) is greater than numSampleIterations
        from (3). If it isn't, increment the count by 1. If it is, add a call to the prefetch
        adjustment procedure and reset the count to 0.

    7.) Add an if-then structure, where we check whether our prefetch will be out-of-bounds
        w.r.t. the loop domain. If the prefetch will be in-bounds, we create a primitive
        in the then-block that will be replaced with the prefetch call during prefolding.
        If the prefetch will be out-of-bounds, we don't do anything special; it just falls
        through and does the access (i.e., there is no else-block).

    8.) Create an outer if-then structure that only takes the then-branch of prefetching
        is supported/valid. This is a param-guarded check so if the check is resolved to
        false, it will eliminate the code added from (4) above.

    9.) Replace the original A[B[i]] access with a primitive that will be caught and
        processed during prefolding.

    Arguments:
    forall -> the forall loop to analyze

    Return:
    None
*/
static void optimizeLoopARP(ForallStmt *forall)
{
  // For each candidate, do the transformations. Note that some things, like
  // modifying the loop iterator, do not need to be done "by" each candidate.
  // When candidates are directly nested in the forall, this is easy enough to keep
  // track of with a single flag. But the forall could have multiple for-loops
  // inside of it, each having more than one candidate. So we can just keep a
  // set of ForLoop* instances and we only change the iterator if a given ForLoop*
  // is not in the set.
  bool updatedForallIterator = false;
  bool updatedForallIndexVar = false;
  bool addedVarsForall = false;
  std::set<ForLoop *> updatedForLoopIterator;
  std::set<ForLoop *> updatedForLoopIndexVar;
  std::set<ForLoop *> addedVarsForLoop;
  int candidateID = 1;

  // Used in prefolding to keep track of what we've processed. Maps forall
  // IDs to a set of candidate IDs 
  std::set<int64_t> emptySet;
  gPrefetchCallProcessed[(int64_t)forall->optInfo.arpID] = emptySet;
  for (auto &candidate : forall->optInfo.adaptiveRemotePrefetchingCandidates) {
    candidate.ID = candidateID;
    // 1.) Update the loop iterator, if needed
    updateLoopIteratorARP(forall, 
                          candidate, 
                          updatedForallIterator, 
                          updatedForLoopIterator);

    // 2.) Update the loop index variable, if needed
    updateLoopIndexVariableARP(forall,
                               candidate,
                               updatedForallIndexVar,
                               updatedForLoopIndexVar);

    // 3.) Add const declarations for number of sample
    //     iterations, loop stride and last valid loop index.
    createConstVariablesARP(forall,
                            candidate,
                            addedVarsForall,
                            addedVarsForLoop);

    // 4.) Add task private variables for forall: distance, count, window
    addTaskPrivateVariablesToForallARP(forall,
                                       candidate);

    // 5.) Add if-then structure for the static check. This is a
    //     param check that will be resolved by the time we get to
    //     to prefolding.
    createStaticCheckARP(forall,
                         candidate);

    // 6.) Add if-then-else structure for adjusting the prefetch
    //     distance once we've executed the required number of iterations.
    createPrefetchAdjustmentCheck(forall,
                                  candidate);

    // 7.) Add if-then structure for the out-of-bounds check. This is
    //     a runtime check that will do the prefetch if we're in-bounds.
    createOutOfBoundsCheckARP(forall,
                              candidate);

    // 8.) Create the prefetch call and insert it in the proper locations.
    //     See createPrefetchCallARP() for details
    createPrefetchCallARP(forall,
                          candidate);

    // 9.) Create the primitive that we'll use to flag down each
    //     candidte during prefolding.
    createPrimitiveARP(forall,
                       candidate);
    
    candidateID++;
  } /* end of for each candidate loop */

  return;
} /* end of optimizeLoopARP */

//##################################################################################
/*
    This function updates the loop iterator for the given candidate to the
    adaptive remote prefetching (ARP) optimization. The candidate is either
    nested directly in forall or is nested in a for-loop that is within the
    forall. When we refer to "the loop" in the comments below, we mean whatever
    loop directly contains the candidate access.

    In some cases, we need to replace/update the loop's iterator so it yields
    the information we need for the ARP optimization. Consider these cases:

        (a) The loop is iterating over an array (for/forall elem in Arr). The
            custom iterator will yield "elem" still but also the corresponding
            index of "elem" in Arr. So we need to replace the iterator. But we don't know
            whether "Arr" is an array or a domain (or neither). Our custom iterator
            will match on the correct one at compile time. If "Arr" was a domain,
            we still yield the tuple but we just ignore the 2nd element in it (i.e.,
            the domain already gives us the index we want). If "Arr" is not an array
            or domain, we also just ignore the 2nd element of the tuple (and the
            optimization won't take place once we determine we don't have an array or
            domain in prefolding).

        (b) The loop is iterating over an explicit domain (for/forall i in A.domain).
            We know this by looking at our candidate(s), which kept notice of whether we
            had this situation. In this case, we don't need to use the custom iterator, as
            we know we have a domain.

        (c) The loop is iterating over a range (for/forall start..end). Like (b), we don't
        need to replace the iterator

    The custom iterator we have is called prefetchIter and it takes in the original "thing"
    that the loop is iterating over (the array or domain, assuming that is what it is).
    As mentioned above, we overloaded prfetchIter so it matches on arrays, domains or
    other. Also, recall that with ARP we require that we DO NOT iterate over an assocative
    domain or array. So prefetchIter also does a param check for that when matching the argument.

    Note that if multiple candidates are directly nested in the forall, we only need to update
    the forall once. So we use a passed-in flag to check to ensure we haven't already updated
    the iterator. For candidates that are instead nested in for-loops within the forall, we use
    a std::set to keep track of the loops we already modified via this function.

    The custom iteratpr mentioned above yields a tuple, so we will need to update the loop to
    receive that. We do that later in updateLoopIndexVariableARP().

    Arguments:
    forall -> the forall that contains the candidate access
    candidate -> the candidate access and associated info
    updatedForallIterator -> flag we check/set for updating the forall iterator
    updatedForLoopIterator -> set we check/add to for updating for-loop iterators

    Return:
    None; forall/for loop iterator is modified
*/
static void updateLoopIteratorARP(ForallStmt *forall,
                                  AdaptiveRemotePrefetchingCandidate &candidate,
                                  bool &updatedForallIterator,
                                  std::set<ForLoop *> &updatedForLoopIterator)
{
  // Is candidate in the forall or a forloop?
  if (candidate.forloop != NULL) {
    ForLoop *forloop = candidate.forloop;
    // Do we need to modify the loop iterator? First, if we already did so
    // via another candidate in this loop, then we don't. Otherwise, we also
    // don't need to do it if the loop iterator is a range or explicit domain.
    // Flipped around, we update the iterator if we haven't done so already AND
    // if the loop iterates other an array or domain variable.
    if (updatedForLoopIterator.count(forloop) == 0 && candidate.loopIteratorType == ARRAY_OR_DOMAIN) {
      updatedForLoopIterator.insert(forloop);
      Expr *origIterExpr = NULL;
      // get the iterator Symbol and find the PRIM_MOVE into it that calls _getIterator.
      // The _getIterator takes in the original loop iterator, in that it takes in
      // "A" from "for i in A". So we want to replace that argument to _getIterator
      // with a call to prefetchIter(A).
      Symbol *iterSym = forloop->iteratorGet()->symbol();
      if (iterSym == NULL) { return; }
      for_SymbolSymExprs(symexpr, iterSym) {
        if (CallExpr *symCall = toCallExpr(symexpr->parentExpr)) {
          if (symCall->isPrimitive(PRIM_MOVE) && symCall->get(1) == symexpr) {
            if (CallExpr *getIterCall = toCallExpr(symCall->get(2))) {
              if (getIterCall->isNamed("_getIterator")) {
                // make sure we have the right thing. getIterCall->get(1) should
                // be a SymExpr whose Symbol is the loop's iterator sym, or a CallExpr
                // to chpl_by, where the first argument there is the loop iterator sym.
                if (candidate.byClauseStride == NULL) {
                  origIterExpr = toExpr(getIterCall->get(1));
                  Symbol *iterSym = (toSymExpr(origIterExpr))->symbol();
                  INT_ASSERT(iterSym == candidate.loopIteratorSym);
                  break;
                }
                else {
                  CallExpr *byCall = toCallExpr(getIterCall->get(1));
                  if (byCall != NULL && byCall->isNamed("chpl_by")) {
                    Symbol *iterSym = (toSymExpr(byCall->get(1)))->symbol();
                    INT_ASSERT(iterSym == candidate.loopIteratorSym);
                    origIterExpr = toExpr(byCall);
                    break;
                  }
                }
              }
            }
          }
        }
      } /* end of for_SymbolSymExprs */     
      INT_ASSERT(origIterExpr != NULL);
      // If we had a by-clause, we need to basically "move" that into the custom
      // iterator. We have versions of prefetchIter that take in a by-clause. So
      // we simply just replace the "chpl_by" baseExpr with "prefetchIter", as the
      // arguments to both are the same.
      if (candidate.byClauseStride != NULL) {
        CallExpr *byCall = toCallExpr(origIterExpr);
        byCall->baseExpr->replace(new UnresolvedSymExpr("prefetchIter"));
      }
      else {
        // Otherwise, no by clause so replace the iterator as usual
        CallExpr *prefetchIter = new CallExpr("prefetchIter");
        origIterExpr->insertBefore(prefetchIter);
        prefetchIter->insertAtTail(origIterExpr->remove());
      }
    }
  } /* candidate is in a for loop */

  else {
    // Else, we have a forall. Do similar checks to see if we should update the iterator
    if (updatedForallIterator == false && candidate.loopIteratorType == ARRAY_OR_DOMAIN) {
      updatedForallIterator = true;
      Expr *origIterExpr = forall->firstIteratedExpr();
      // Do we have a by clause? If so, byClauseStride->parentExpr is
      // the chpl_by call. So do a similar replacement as we did for the for-loop case
      if (candidate.byClauseStride != NULL) {
        CallExpr *byCall = toCallExpr(candidate.byClauseStride->parentExpr);
        byCall->baseExpr->replace(new UnresolvedSymExpr("prefetchIter"));
      }
      else {
        CallExpr *prefetchIter = new CallExpr("prefetchIter");
        origIterExpr->insertBefore(prefetchIter);
        prefetchIter->insertAtTail(origIterExpr->remove());
      }
    }
  } /* candidate is in the forall loop */

} /* end of updateLoopIteratorARP */


//##################################################################################
/*
    This function updates the forall/for-loop index variable for the adaptive
    remote prefetching (ARP) optimization.

    From the outcome of updateLoopIteratorARP(), the loop that contains the candidate
    access for ARP may now yield a tuple (elem, idx) where "elem" is the original value
    yielded by the iterator and "idx" is a new value our custom iterator yields. Regardless
    of whether we are truly iterating over an array (which means we actually make use of "idx"),
    we need to update the loop index variable to receive the tuple.

    The way in which we do this transformation is different for forall loops and for-loop
    loops. So we need to break these into two cases. Also, like we did for updateLoopIteratorARP(),
    this transformation only needs to be applied to the forall/for-loop once, regardless of how
    many candidate accesses are in the loop.

    To ensure that the changes we make here are sane w.r.t. other optimizations that rely on
    looking at the forall/for loop meta data, we need to update the multiDIndices field for
    the loop we modified. Specifically, the loop will now be of the form 
    "for/forall (elem,idx) in prefetchIter(A)". The way that is parsed in gatherForallInfo()
    and gatherForLoopInfo() is that elem is added to multiDIndices[0] and idx is added to
    multiDIndices[1]. Again, this update only needs to happen once per loop.
    TODO: Currently not doing the above; doesn't seem to break anything if we don't do it.
   
    Finally, we want to extract out all index symbols used in the candidate access. This
    is for use in post resolution. We wait to do the extraction until the end of this
    function since we may have updated the index symbols used in the candidate access. 

    Arguments:
    forall -> the forall that contains the candidate access
    candidate -> the candidate access and associated info
    updatedForallIndexVar -> flag we check/set for updating the forall index variable
    updatedForLoopIndexVar -> set we check/add to for updating for-loop index variable

    Return:
    None; forall/for loop is modified   
*/
static void updateLoopIndexVariableARP(ForallStmt *forall,
                                       AdaptiveRemotePrefetchingCandidate &candidate,
                                       bool &updatedForallIndexVar,
                                       std::set<ForLoop *> &updatedForLoopIndexVar)
{
  // Is candidate in the forall or a forloop?
  if (candidate.forloop != NULL) {
    ForLoop *forloop = candidate.forloop;
    // First time updating this for-loop, and the iterator type is one where we would have
    // updated the iterator, and thus we need to update the index variable.
    if (updatedForLoopIndexVar.count(forloop) == 0 && candidate.loopIteratorType == ARRAY_OR_DOMAIN) {
      updatedForLoopIndexVar.insert(forloop);
      bool updateSuccess = false;
      // Create the call to _check_tuple_var_decl. The first argument is the indexOfInterest Symbol
      // and the second argument is the size of the tuple (2). So first, get the indexOfInterest Symbol
      Symbol *indexOfInterest = (forloop->indexGet())->symbol();
      INT_ASSERT(indexOfInterest != NULL);
      CallExpr *tupleCall = new CallExpr("_check_tuple_var_decl",
                                         new SymExpr(indexOfInterest),
                                         new_IntSymbol(2));
      // The tuple call needs to go at the very beginning of the for-loop
      AList &bodyExprs = forloop->body;
      Expr *firstExpr = toExpr(bodyExprs.get(1));
      firstExpr->insertBefore(tupleCall);

      // Now we need to add some PRIM_MOVEs to pull out the elements of the tuple
      // and store them into the loop index variables. The first element of the tuple
      // is always going to be the "original" loop index variable. The assumption is
      // that variable's DefExpr is now right after the tupleCall we just inserted.
      DefExpr *def = toDefExpr(tupleCall->next);
      INT_ASSERT(def != NULL);
      Symbol *origIndex = def->sym;
      INT_ASSERT(origIndex != NULL);
      // Right after this DefExpr, we should have a PRIM_MOVE into origIndex from
      // the indexOfInterest. We just need to modify this PRIM_MOVE so that the RHS is
      // a CallExpr that takes in the indexOfInterest and an integer "0", which says
      // pull out the first element of the tuple (indexOfInterest is now a tuple).
      // NOTE: since we are not creating a new loop index variable for the original
      // loop index (origIndex), we don't need to update the originalIter_idx field
      // for the candidate. However, that is not the case when we are dealing with a forall.
      if (CallExpr *moveCall = toCallExpr(def->next)) {
        if (moveCall->isPrimitive(PRIM_MOVE)) {
          Symbol *LHS = (toSymExpr(moveCall->get(1)))->symbol();
          Symbol *RHS = (toSymExpr(moveCall->get(2)))->symbol();
          INT_ASSERT(LHS == origIndex);
          INT_ASSERT(RHS == indexOfInterest);
          CallExpr *tupleAccess = new CallExpr(new SymExpr(indexOfInterest),
                                               new_IntSymbol(0));
          moveCall->get(2)->replace(tupleAccess);
          // While we are here, right after moveCall we need to define the second
          // element of the tuple. We'll call it prefetchIter_idx. After the DefExpr for
          // that, we also do a similar PRIM_MOVE as above
          VarSymbol *prefetchIdx = new VarSymbol("prefetchIter_idx");
          prefetchIdx->addFlag(FLAG_INDEX_VAR);
          prefetchIdx->addFlag(FLAG_INSERT_AUTO_DESTROY);
          DefExpr *idxDef = new DefExpr(prefetchIdx);
          moveCall->insertAfter(idxDef);
          CallExpr *moveCall2 = new CallExpr(PRIM_MOVE,
                                             new SymExpr(prefetchIdx),
                                             new CallExpr(new SymExpr(indexOfInterest),
                                                          new_IntSymbol(1)));
          idxDef->insertAfter(moveCall2);
          candidate.prefetchIter_idx = prefetchIdx;
          // Update the for-loop's multiDIndices info. Recall that multiDIndices
          // is a vector of vectors (for whatever reason). We know we already have
          // one vector added, and that will represent the original loop index variable.
          // We then create a new vector to hold the prefetch index we created above.
          // TODO: for now, we are not adding the new vector; we can revisit this if
          // we end up breaking something. As of now, no other code besides the code
          // I (tbrolin) wrote knows that a for-loop has the multiDIndices field.
          /*forloop->multiDIndices[0][0] = origIndex;
          std::vector<Symbol *> tempVec;
          tempVec.push_back(prefetchIdx);
          forloop->multiDIndices.push_back(tempVec);*/
          updateSuccess = true;
        }
      }
      if (updateSuccess != true) {
        INT_FATAL("failed to update for-loop index variable for ARP optimization");
      }
    }
  } /* end of candidate is in for loop */

  else {
    // Else, we have a forall. First, if the forall has already been updated, we
    // still need to grab the new loop index variable we created for the candidate.
    // When we process the forall for the first time, we create a new loop index
    // variable and stored it in forall->optInfo.multiDIndices[0][0].
    if (updatedForallIndexVar == true) {
      candidate.originalIter_idx = forall->optInfo.multiDIndices[0][0];
    }
    // Now, if we haven't updated the loop yet, do so.
    if (updatedForallIndexVar == false && candidate.loopIteratorType == ARRAY_OR_DOMAIN) {
      updatedForallIndexVar = true;
      // Things are a bit different for forall loops. While the for-loop just reuses
      // the existing indexOfInterest symbol, we need to basically create it. It goes
      // at the very beginning of the forall loop. We assume the first expression in
      // the forall is a DefExpr for the original loop index variable. Also, through this
      // process, we create a new original loop index variable, so we need to update our
      // candidate's field for that.
      Symbol *origIdxSym = forall->optInfo.multiDIndices[0][0];
      INT_ASSERT(origIdxSym != NULL);
      DefExpr *origIdxDef = toDefExpr(forall->getFirstExpr());
      // Make a copy of the original def expr; we'll replace it with the tuple def
      // below and then re-insert the copy back into the AST later.
      DefExpr *origIdxDef_copy = origIdxDef->copy();
      INT_ASSERT(origIdxDef != NULL);
      INT_ASSERT(origIdxSym == origIdxDef->sym);
      // Create the tuple variable and DefExpr for it.
      VarSymbol *chplIdx = new VarSymbol("chpl_idx_1");
      chplIdx->addFlag(FLAG_INDEX_VAR);
      chplIdx->addFlag(FLAG_INDEX_OF_INTEREST);
      chplIdx->addFlag(FLAG_TEMP);
      chplIdx->addFlag(FLAG_INSERT_AUTO_DESTROY);
      DefExpr *tupleDef = new DefExpr(chplIdx);
      // Replace the original index def with the tuple def
      origIdxDef->replace(tupleDef);

      // Now, create a BlockStmt that will contain the call to
      // _check_tuple_var_decl, the DefExprs for the loop index variables and
      // the PRIM_MOVEs into those. This new block stmt should go at the beginning of
      // the original body.
      BlockStmt *blockStmt = new BlockStmt();
      forall->loopBody()->insertAtHead(blockStmt);
      CallExpr *tupleCall = new CallExpr("_check_tuple_var_decl",
                                         new SymExpr(chplIdx),
                                         new_IntSymbol(2));
      blockStmt->insertAtHead(tupleCall);
      // Re-insert the copy of the original loop index DefExpr after tupleCall
      blockStmt->insertAtTail(origIdxDef_copy);
      // Now PRIM_MOVE into the original loop index from the tuple. However,
      // the insert we just did above with the def-copy creates a new origIdxSym.
      // We need to use that here, and then replace ALL uses of origIdxSym with
      // the new one
      Symbol *newIdxSym = origIdxDef_copy->sym;
      candidate.originalIter_idx = newIdxSym;
      CallExpr *moveCall1 = new CallExpr(PRIM_MOVE,
                                         new SymExpr(newIdxSym),
                                         new CallExpr(new SymExpr(chplIdx),
                                                      new_IntSymbol(0)));
      blockStmt->insertAtTail(moveCall1);
      // Do the find/replace for newIdxSym
      for_SymbolSymExprs(symexpr, origIdxSym) {
        symexpr->replace(new SymExpr(newIdxSym));
      }  
      // Now create a new DefExpr for the prefetch iterator index and the
      // corresponding PRIM_MOVE
      VarSymbol *prefetchIdx = new VarSymbol("prefetchIter_idx");
      prefetchIdx->addFlag(FLAG_INDEX_VAR);
      prefetchIdx->addFlag(FLAG_INSERT_AUTO_DESTROY);
      DefExpr *idxDef = new DefExpr(prefetchIdx);
      blockStmt->insertAtTail(idxDef);
      CallExpr *moveCall2 = new CallExpr(PRIM_MOVE,
                                         new SymExpr(prefetchIdx),
                                          new CallExpr(new SymExpr(chplIdx),
                                                       new_IntSymbol(1)));
      blockStmt->insertAtTail(moveCall2);
      candidate.prefetchIter_idx = prefetchIdx;
      // Update the forall's multiDIndices info. Recall that multiDIndices
      // is a vector of vectors (for whatever reason). We know we already have
      // one vector added, and that will represent the original loop index variable.
      // We then create a new vector to hold the prefetch index we created above.
      // TODO: for now, we are not adding the new vector; we can revisit this if
      // we end up breaking something.
      forall->optInfo.multiDIndices[0][0] = newIdxSym;
      /*std::vector<Symbol *> tempVec;
      tempVec.push_back(prefetchIdx);
      forall->optInfo.multiDIndices.push_back(tempVec);*/
    }
  } /* end of candidate is in forall loop */

  //Extract out all symbols used in parentCall so we can analyze them later
  // in post resolution. Ignore the A and B from parentCall and call (their call base).
  std::vector<SymExpr*> symexprs;
  collectSymExprs(candidate.parentCall, symexprs);
  Symbol *callBase = getCallBase(candidate.call);
  Symbol *parentCallBase = getCallBase(candidate.parentCall); 
  for (auto &symexpr : symexprs) {
    if (Symbol *sym = symexpr->symbol()) {
      // Ignore literals
      if (sym != callBase && sym != parentCallBase && !sym->isImmediate()) {
        candidate.prefetchIndexSymbols.insert(sym);
      }
    }
  }

} /* end of updateLoopIndexVariableARP */

//##################################################################################
/*
    Given a forall and a candidate access, create the few const variables that we'll
    need during the adaptive remote prefetching (ARP) optimization.

    Specifically, we create numSampleIterations, loopStride and lastValidIndex.
    If we've already processed a candidate in this forall (or for-loop), then we
    don't need to recreate the variables. We'll simply "get" them from the AST
    and add them to the candidate's info. This is because these variables are not
    specific to an individual candidate but rather the entire forall/loop.

    We use loopStride in both the out-of-bounds check we do as well as the prefetch
    call. It tells us how the loop index variable progresses between iterations.
    We get it by calling out to a Chapel function which will give us what we need.
    If the loop iterates over an array or domain, it give us back the underlying
    domain's stride. But if the loop had a by-clause, we factor that in as well
    by multiplying the domain's stride by the by-clause. Ranges without by-clause
    have an implied stride of 1.

    We use lastValidIndex in our out-of-bounds calculation. It tells us the
    value the loop index variable will have on the last iteration. If what we want
    to prefetch is greater than this, we know we are out of bounds. We again call out
    to a Chapel function to compute this. For domains and arrays, it is equal to
    .domain.high. For ranges, it depends on whether the range uses "#", "<" or no
    operator. We handle such cases separately.

    The numSampleIterations variable tells us how many iterations of the loop containing
    the candidate we need to execute before we attempt to adjust the prefetch distance.
    It relies on knowledge of the start/end bounds of the loop as well as the loop stride.

    Lastly, we insert a call to reset the prefetch counters. If we just have a forall
    loop, this is inserted right before the loop. If we have an inner for-loop, we
    insert it right before the for-loop.

    Arguments:
    forall -> the forall with the candidate
    candidate -> the candidate access
    updatedForallIndexVar -> flag we check/set for adding the variables for the forall.
    updatedForLoopIndexVar -> same as above for the for-loops. Since we could have
                              multiple for-loops in the forall, this is a std::set

    Return:
    None; AST around/in the forall is modified, and the candidate is updated.

*/
static void createConstVariablesARP(ForallStmt *forall,
                                    AdaptiveRemotePrefetchingCandidate &candidate,
                                    bool &addedVarsForall,
                                    std::set<ForLoop *> &addedVarsForLoop)
{
  // If we already processed the loop that contains the candidate, we don't need
  // to create the variables. Just pull them out and add them to the candidate.
  Expr *curr = NULL;
  if (candidate.forloop != NULL && addedVarsForLoop.count(candidate.forloop) > 0) {
    // candidate is in a for-loop that we already processed. So the variables have
    // already been added. Find their DefExpr above the for-loop and get their Symbols.
    curr = candidate.forloop->prev;
  }
  else if (candidate.forloop == NULL && addedVarsForall == true) {
    curr = forall->prev;
  }
  if (curr != NULL) {
    int found = 0;
    while (curr != NULL && found != 3) {
      if (DefExpr *def = toDefExpr(curr)) {
        if (CallExpr *call = toCallExpr(def->init)) {
          if (call->isNamed("getLastLoopIndex") ||
              call->isNamed("getLastLoopIndexSimpleRange") ||
              call->isNamed("getLastLoopIndexNudgeHigh") ||
              call->isNamed("getLastLoopIndexCountOp")) {
            candidate.lastValidIndex = toVarSymbol(def->sym);
            found++;
          }
          else if (call->isNamed("getLoopStride")) {
            candidate.loopStride = toVarSymbol(def->sym);
            found++;
          }
          else if (call->isNamed("getPrefetchSampleSizeForLoop") ||
                   call->isNamed("getPrefetchSampleSizeForall")) {
            candidate.numSampleIterations = toVarSymbol(def->sym);
            found++;
          }
        }
      }
      curr = curr->prev;
    } /* end while loop */
    INT_ASSERT(found == 3);
    return;
  } /* end  if curr != NULL */


  // Otherwise, create the variables
  if (candidate.forloop != NULL) {
    addedVarsForLoop.insert(candidate.forloop);
  }
  else {
    addedVarsForall = true;
  }

  std::string ID_str = std::to_string(candidate.ID);
  const char *ID = ID_str.c_str();
  VarSymbol *loopStride = new VarSymbol(astr("loopStride_", ID));
  VarSymbol *lastValidIndex = new VarSymbol(astr("lastValidIndex_", ID));
  VarSymbol *numSampleIterations = new VarSymbol(astr("numSampleIterations_", ID));

  candidate.loopStride = loopStride;
  candidate.lastValidIndex = lastValidIndex;
  candidate.numSampleIterations = numSampleIterations;

  loopStride->addFlag(FLAG_CONST);
  lastValidIndex->addFlag(FLAG_CONST);
  numSampleIterations->addFlag(FLAG_CONST);

  // Do the loopStride/lastValidIndex first
  CallExpr *getLoopStride = NULL;
  CallExpr *getLastValidIndex = NULL;
  // Handle case for for/forall i in A and for/forall i in A.domain (i.e., not a range)
  if (candidate.loopIteratorType != RANGE) {
    // Last-valid-index does not care about strides
    getLastValidIndex = new CallExpr("getLastLoopIndex",
                                     candidate.loopIteratorSym);
    // Handle case when we do not have a by-clause
    if (candidate.byClauseStride == NULL) {
      getLoopStride = new CallExpr("getLoopStride",
                                   candidate.loopIteratorSym);
    }
    else {
      // Handle case when we do have a by-clause
      getLoopStride = new CallExpr("getLoopStride",
                                   candidate.loopIteratorSym,
                                   candidate.byClauseStride->copy());
    }
  } /* end if candidate is not a range iterator */
  
  // Handle case for for/forall i in <range>
  else {
    // For last-valid-index, it depends on the range operator
    //  - no operator: last valid index is whatever the rangeEnd expression is.
    //  - high nudge: last valid index is rangeEnd -1
    //  - # operator: last valid index is (rangeStart+rangeEnd-1)
    if (candidate.loopRangeOperator == NO_OPERATOR) {
      getLastValidIndex = new CallExpr("getLastLoopIndexSimpleRange",
                                       candidate.rangeEnd->copy());
    }
    else if (candidate.loopRangeOperator == NUDGE_HIGH_BOUND) {
      getLastValidIndex = new CallExpr("getLastLoopIndexNudgeHigh",
                                       candidate.rangeEnd->copy());
    }
    else if (candidate.loopRangeOperator == COUNT_OPERATOR) {
      getLastValidIndex = new CallExpr("getLastLoopIndexCountOp",
                                       candidate.rangeStart->copy(),
                                       candidate.rangeEnd->copy());
    }
    // Without a by-clause, the implicit/default stride is 1
    if (candidate.byClauseStride == NULL) {
      getLoopStride = new CallExpr("getLoopStride");
    }
    else {
      // otherwise, just evaluate the by-clause and return it.
      getLoopStride = new CallExpr("getLoopStride",
                                   candidate.byClauseStride->copy());
    }
  } /* end of else branch for loop iterator type */
  
  // Now handle numSampleIterations. The call relies on knowing the start of the loop,
  // the last valid index and the stride. If we have a range, we have an Expr for the
  // start of the loop. Else, we have an array/domain, so the start is equal to domain.low,
  // which is extracted via getFirstLoopIndex
  CallExpr *getPrefetchSampleSize = NULL;
  if (candidate.forloop == NULL) {
    getPrefetchSampleSize = new CallExpr("getPrefetchSampleSizeForall");
  }
  else {
    getPrefetchSampleSize = new CallExpr("getPrefetchSampleSizeForLoop");
  }
  if (candidate.loopIteratorType != RANGE) {
    CallExpr *getFirstLoopIndex = new CallExpr("getFirstLoopIndex",
                                               candidate.loopIteratorSym);
    getPrefetchSampleSize->insertAtTail(getFirstLoopIndex);
  }
  else {
    getPrefetchSampleSize->insertAtTail(candidate.rangeStart->copy());
  }
  getPrefetchSampleSize->insertAtTail(candidate.lastValidIndex);
  getPrefetchSampleSize->insertAtTail(candidate.loopStride);
  // Now insert the calls before the loop that contains the access
  INT_ASSERT(getLoopStride != NULL);
  INT_ASSERT(getLastValidIndex != NULL);
  INT_ASSERT(getPrefetchSampleSize != NULL);
  // Calls go before loop that contains the access. getPrefetchSampleSize must
  // go after the the others, since it uses them. Also, reset the prefetch counter
  // for this task right before the for-loop.
  if (candidate.forloop != NULL) {
    candidate.forloop->insertBefore(new CallExpr("reset_per_cache_prefetch_counters"));
    candidate.forloop->insertBefore(new DefExpr(loopStride,
                                                getLoopStride));
    candidate.forloop->insertBefore(new DefExpr(lastValidIndex,
                                                getLastValidIndex));
    candidate.forloop->insertBefore(new DefExpr(numSampleIterations,
                                                getPrefetchSampleSize));
  }
  else {
    // if we just have a forall, we reset the counters for all tasks before
    // the forall loop
    forall->insertBefore(new CallExpr("reset_prefetch_counters"));
    forall->insertBefore(new DefExpr(loopStride,
                                     getLoopStride));
    forall->insertBefore(new DefExpr(lastValidIndex,
                                     getLastValidIndex));
    forall->insertBefore(new DefExpr(numSampleIterations,
                                     getPrefetchSampleSize));
  }

  return;
} /* end of createConstVariablesARP */

//##################################################################################
/*
    Given a candidate and the forall it is in, add a per-task prefetch distance
    variable to the forall. The distance is initialized to a default value (determined
    by whatever initPrefetchDistance() returns). Also add per-task count and window
    variables. Count is initialized to 0 and is incremented in each iteration of the
    loop that contains the candidate access; when it hits numSampleIterations, then
    we attempt to adjust the prefetch distance. The window variable is another prefetch 
    adjustment parameter that is used within adjustPrefetchDistance. It is initialized 
    to 0 as well.

    TODO: It may not be necessary to give each candidate its own count variable. If
    there are two candidates nested in the same forall (or for-loop), they can share
    the same count variable since they each share the same loop bounds, and hence will
    adjust their distances at the same interval. To do this, we'd need to keep track
    of whether a given forall or for-loop has been processed (and a count created). If
    we have already done so, instead of creating another count, we'll want to indicate
    in some way that we didn't, and ensure that when we call createPrefetchAdjustmentCheck(),
    we only generate a single if-check for those candidates and insert the appropriate
    calls to adjust the distances.

    Arguments:
    forall -> the forall with the candidate
    candidate -> the candidate access

    Return:
    None; the forall shadow variables are updated 
*/
static void addTaskPrivateVariablesToForallARP(ForallStmt *forall,
                                               AdaptiveRemotePrefetchingCandidate &candidate)
{
  std::string ID_str = std::to_string(candidate.ID);
  const char *ID = ID_str.c_str();
  UnresolvedSymExpr *distanceTmp = new UnresolvedSymExpr(astr("prefetchDist_", ID));
  UnresolvedSymExpr *countTmp = new UnresolvedSymExpr(astr("count_", ID));
  UnresolvedSymExpr *windowTmp = new UnresolvedSymExpr(astr("window_", ID));
  
  ShadowVarSymbol *prefetchDistance = ShadowVarSymbol::buildForPrefix(SVP_VAR,
                                                                      distanceTmp,
                                                                      NULL,
                                                                      new CallExpr("initPrefetchDistance"));
  ShadowVarSymbol *count = ShadowVarSymbol::buildForPrefix(SVP_VAR,
                                                           countTmp,
                                                           NULL,
                                                           new CallExpr("initCounts"));
  ShadowVarSymbol *window = ShadowVarSymbol::buildForPrefix(SVP_VAR,
                                                            windowTmp,
                                                            NULL,
                                                            new CallExpr("initCounts"));
  forall->shadowVariables().insertAtTail(prefetchDistance->defPoint);
  forall->shadowVariables().insertAtTail(count->defPoint);
  forall->shadowVariables().insertAtTail(window->defPoint);
  candidate.prefetchDistance = prefetchDistance;
  candidate.iterCount = count;
  candidate.window = window;

} /* end of addTaskPrivateVariablesToForallARP */

//##################################################################################
/*
    Creates the if-then static check for the adaptive remote prefetching (ARP)
    optimization. This will be a param-based check that resolves to either true
    or false by the time we get to prefolding. If the check is false, it will
    wipe out the entire then-block (i.e., the optimization/primitive). If it is
    true, it leaves the primitive and we will do further processing in prefolding.

    The check is whether the loop iterator Symbol is an array or domain, and whether
    it is associative. We can only do the prefetch if the loop iterator symbol is
    a non-associative array/domain. Note this loop iterator Symbol is for the loop
    that contains the candidate access. We also ensure that A and B from A[B[i]]
    are arrays.

    The staticCheck variable def and the check itself  should go right before the candidate.
    But the candidate could be nested in a CallExpr, like accum += foo * A[B[i]].
    So we need to look back from candidate.parentExpr until we hit something that
    is NOT a CallExpr. We then insert the code right before the last CallExpr we hit.

    Once we create the CondStmt for this, we add it to the candidate so it can be
    used in the next stages of code transformation.

    Arguments:
    forall -> the forall with the candidate
    candidate -> the candidate access

    Return:
    None, AST is updated and candidate is updated
*/
static void createStaticCheckARP(ForallStmt *forall,
                                 AdaptiveRemotePrefetchingCandidate &candidate)
{
  VarSymbol *staticCheck = new VarSymbol("staticPrefetchCheck");
  staticCheck->addFlag(FLAG_PARAM);
  // If we are iterating over a range, we just check for A and B to be arrays
  CallExpr *staticCall = new CallExpr("chpl__isPrefetchSupported");
  if (candidate.loopIteratorType != RANGE) {
    staticCall->insertAtTail(candidate.loopIteratorSym);
  }
  staticCall->insertAtTail(getCallBase(candidate.parentCall));
  staticCall->insertAtTail(getCallBase(candidate.call));
                                
  DefExpr *staticCheckDef = new DefExpr(staticCheck, staticCall);
  Expr *staticCond = new CallExpr("==", staticCheck, gTrue);
  candidate.staticCheck = staticCheck;

  // Find out where to do the insert for the staticCheckDef
  CallExpr *curr = candidate.parentCall;
  CallExpr *lastCall = NULL;
  while (curr != NULL) {
    lastCall = curr;
    curr = toCallExpr(curr->parentExpr);
  }
  INT_ASSERT(lastCall != NULL);
  // If we're here, then curr is the first "thing" above
  // parentCall that isn't a CallExpr. So insert the static check
  // def right before the last CallExpr we had. However, lastCall->parentExpr
  // could be a DefExpr; this happens when we have something like ref v = A[B[i]].
  // In that case, we need to insert before the DefExpr
  Expr *insertPoint = toExpr(lastCall);
  if (DefExpr *def = toDefExpr(lastCall->parentExpr)) {
    insertPoint = toExpr(def);
  }
  insertPoint->insertBefore(staticCheckDef);
  
  // Create the if-then structure
  BlockStmt *thenBlock = new BlockStmt();
  CondStmt *cond = new CondStmt(staticCond, thenBlock, NULL);
  insertPoint->insertBefore(cond);
  candidate.staticCond = cond;

} /* end of createStaticCheckARP */

//##################################################################################
/*
    This function adds an if-then-else structure that checks whether the count
    variable that was added to the forall's task-private variables is greater than
    numSampleIterations. If it isn't, we increment the count by 1. Else, we add a
    call to adjust the prefetch distance.

    Basically, we're creating the code that says "execute the specified number of
    iterations and then attempt to adjust the prefetch distance". The number of
    iterationst to perform was calculated and stored in the numSampleIteratons
    VarSymbol.

    This if-then-else structure will go at the very beginning of the then-block from
    createStaticCheckARP: candidate.staticCond->thenStmt.
    
    Arguments:
    forall -> the forall with the candidate
    candidate -> the candidate access

    Return:
    None, AST is updated and candidate is updated
*/
static void createPrefetchAdjustmentCheck(ForallStmt *forall,
                                          AdaptiveRemotePrefetchingCandidate &candidate)
{
  Expr *countCheck = new CallExpr("<",
                                  candidate.iterCount, 
                                  candidate.numSampleIterations);
  BlockStmt *thenBlock = new BlockStmt();
  BlockStmt *elseBlock = new BlockStmt();
  CondStmt *cond = new CondStmt(countCheck, thenBlock, elseBlock);

  // thenBlock increments count by 1
  thenBlock->insertAtHead(new CallExpr("+=", candidate.iterCount, new_IntSymbol(1)));

  // elseBlock calls adjustPrefetchDistance and then sets count to 0
  CallExpr *adjustDist = new CallExpr("adjustPrefetchDistance",
                                      candidate.prefetchDistance,
                                      candidate.window);
  elseBlock->insertAtHead(adjustDist);
  elseBlock->insertAtTail(new CallExpr("=", candidate.iterCount, new_IntSymbol(0)));

  // if-then-else goes at beginning of the staticCheck then-block
  candidate.staticCond->thenStmt->insertAtHead(cond);

} /* end of createPrefetchAdjustmentCheck */

//##################################################################################
/*
    This function generates a call to check for out-of-bounds prefetching for the 
    adaptive remote prefetching (ARP) optimization. It creates an if-then structure 
    so that if the prefetch is NOT out of bounds, we'll do the prefetch. We add calls 
    to do the prefetch in createPrefetchCallARP().

    Arguments:
    forall -> the forall with the candidate
    candidate -> the candidate access

    Return:
    None, AST is updated and candidate is updated
*/
static void createOutOfBoundsCheckARP(ForallStmt *forall,
                                      AdaptiveRemotePrefetchingCandidate &candidate)
{
  // 1.) We have the loopStride and lastValidIndex, but we need to compute 
  //     what the prefetch index will be. It will be equal to 
  //     i+(prefetchDistance * loopStride) assuming "i" is the loop index variable in 
  //     question. In that regard, we need to determine if we're using the original 
  //     loop index variable or the "new" one yielded by the custom iterator.
  Symbol *loopIndexSym = candidate.originalIter_idx;
  if (candidate.loopIteratorType == ARRAY_OR_DOMAIN) {
    loopIndexSym = toSymbol(candidate.prefetchIter_idx);
  }
  CallExpr *prefetchIndex = new CallExpr("+",
                                         loopIndexSym,
                                         new CallExpr("*",
                                                      candidate.prefetchDistance,
                                                      candidate.loopStride));

  // 2.) Create the if-then structure for the out of bounds check:
  //     if we're not out of bounds, do the prefetch. This goes in the then-block
  //     of our staticCheck from createStaticCheckARP(). The prefetch call itself
  //     will be added in createPrefetchCallARP()
  Expr *outOfBoundsCond = new CallExpr("<=", prefetchIndex, candidate.lastValidIndex);
  BlockStmt *thenBlock = new BlockStmt();
  CondStmt *cond = new CondStmt(outOfBoundsCond, thenBlock, NULL);
  candidate.staticCond->thenStmt->insertAtTail(cond);
  candidate.outOfBoundsCond = cond;

} /* end of createOutOfBoundsCheckARP */


//##################################################################################
/*
    This function creates the calls to prefetch() and inserts them into the proper
    locations for the adaptive remote prefetch (ARP) optimization.

    It isn't as straightforward as generating a single CallExpr and inserting it.
    The issue we have is that the loop may be of the form "for elem in A" where A
    is an array. However, at this point in compilation, we don't know that; it
    could just as well be a domain. In either case, we previously modified the
    loop so it looks like "for (elem,idx) in prefetchIter(A)". So if A is an array,
    we now have the corresponding index (idx) into A for a given elem. That is what
    we need to correctly generate the prefetch call.

    However, the way we generate the call is as follows: we look at parentCall, which
    is the entire A[B[]] access, and replace any use of the loop index variable i with
    i + (prefetchDistance * loopStride). This works just fine when we are iterating over
    a domain or range. But in the case mentioned above for an array, what we really want to
    do is replace any use of the loop index variable (call it elem now) with
    A[idx+(prefetchDistance*loopStride)]. This effectively gives us the value of "elem"
    that is the desired number of loop iterations ahead.

    The problem with the above is that we don't know whether we have an array or domain
    in the case of "for elem in A". If we try the approach mentioned where we assume the
    loop iterates over an array but it is in fact a domain, we'll get a compiler error
    (we cannot index into a domain like that).

    The solution is to create a static/param check that sees whether A is an array, and
    if so, performs the array-based prefetch. If it is not an array, or we know we have
    a range or explicit dot-domain, we do the "normal" prefetch. Since the call to 
    isArray() is resolved at compile-time, we don't run into errors trying to index
    into a domain or something.

    In the end, this function will create the following structure (the static check
    and out-of-bounds check already exist from prior steps):

        reset_prefetch_counters();
        const lastValidIndex = getLastLoopIndex(..);
        const loopStride = getLoopStride(..);
        const numSampleIterations = getPrefetchSampleSize(..);
        forall i in ... with (var prefetchDistance, var count, var window) {
            param staticPrefetchCheck = chpl__isPrefetchSupported(..);
            if staticPrefetchCheck == true {
                if count < numSampleIterations {
                    count += 1
                }
                else {
                    adjustPrefetchDistance(prefetchDistance, window);
                    count = 0;
                }
                if (i+(prefetchDistance * loopStride)) <= lastValidIndex {
                    if isArray(loopIteratorSym) {
                        prefetch for array
                    }
                    else {
                        prefetch for domains and ranges
                    }
                }
            }
            original access replaced with primitive
        }

    If we know we have a range or dot-domain, we don't need to generate the isArray if-then-else.

    Arguments:
    forall -> the forall with the candidate
    candidate -> the candidate access

    Return:
    None, AST is updated and candidate is updated
*/
static void createPrefetchCallARP(ForallStmt *forall,
                                  AdaptiveRemotePrefetchingCandidate &candidate)
{
  BlockStmt *thenBlock = NULL;
  BlockStmt *elseBlock = NULL;
  candidate.isArrayCond = NULL;
  // 1.) If we have potentially an array, generate the if isArray structure.
  //     This goes within the then-block of the out-of-bounds check.
  if (candidate.loopIteratorType == ARRAY_OR_DOMAIN) {
    Expr *isArrayCall = new CallExpr("isArray",
                                     candidate.loopIteratorSym);
    Expr *isArrayCond = new CallExpr("==",
                                     isArrayCall,
                                     gTrue);
    thenBlock = new BlockStmt();
    elseBlock = new BlockStmt();
    CondStmt *cond = new CondStmt(isArrayCond, thenBlock, elseBlock);
    candidate.isArrayCond = cond;
    candidate.outOfBoundsCond->thenStmt->insertAtHead(cond);
  }

  // 2.) Create the call to prefetch(). The first argument is the address
  //     to prefetch (i.e., A[B[]] offsetted by the prefetch distance).
  //     The key step here is constructing the proper expression
  //     to pass into the first argument. Assume that "i" is the loop index variable
  //     of interest. We want to find all uses of "i" in parentCall and replace it
  //     with "i+(prefetchDistance*loopStride)"; that effectively looks ahead
  //     the desired number of loop iterations. However, if the loop is iterating
  //     over an array, the loop index variable is an array element. So to effectively
  //     look ahead, we need to replace uses of that element with Arr[idx+offset] where
  //     offset is (prefetchDistance*loopStride) and "idx" is the prefetch index that
  //     our custom iterator yields us. That is why we needed the above param guard
  //     to figure out if we have an array or not.
  //
  // TODO: if we have a field access to A[B[i]], we can try to detect that and
  //       issue the prefetch from that field. May be a bit hard to nail this down
  //       during normalization, so maybe there will be a way to do it during prefolding
  //       and modify the prefetch call there.
  //
  // First, create the prefetch call assuming we don't have an array. Make a copy of parentCall
  // and look at all SymExprs that use candidate.originalIter_idx. Update those to be CallExprs
  // that factor in the prefetch distance and loop stride as discussed.
  CallExpr *parentCallDomainOrRange = candidate.parentCall->copy();
  ShadowVarSymbol *prefetchDistance = candidate.prefetchDistance;
  VarSymbol *loopStride = candidate.loopStride;
  std::vector<SymExpr *> symexprs;
  collectSymExprsFor(parentCallDomainOrRange, candidate.originalIter_idx, symexprs);
  for (auto &symexpr : symexprs) {
    Symbol *sym = symexpr->symbol();
    CallExpr *indexOffset = new CallExpr("+",
                                         sym,
                                         new CallExpr("*",
                                                      prefetchDistance,
                                                      loopStride));
    symexpr->replace(indexOffset);
  }
  CallExpr *prefetchCallDomainOrRange = new CallExpr("prefetch",
                                                     new_IntSymbol(candidate.ID),
                                                     parentCallDomainOrRange);

  // Now do the same but for the case where we may have an array as the iterator
  CallExpr *prefetchCallArray = NULL;
  if (candidate.loopIteratorType == ARRAY_OR_DOMAIN) {
    Symbol *A = getCallBase(candidate.parentCall);
    INT_ASSERT(A != NULL);
    CallExpr *parentCallCopy = candidate.parentCall->copy();
    VarSymbol *prefetchIter_idx = candidate.prefetchIter_idx;
    std::vector<SymExpr *> symexprs2;
    collectSymExprsFor(parentCallCopy, candidate.originalIter_idx, symexprs2);
    for (auto &symexpr : symexprs2) {
      // We want to replace symexpr with "A[prefetchIter_idx + (prefetchDistance*loopStride)]"
      // where A is the assumed array iterator symbol
      CallExpr *indexOffset = new CallExpr("+",
                                         prefetchIter_idx,
                                         new CallExpr("*",
                                                      prefetchDistance,
                                                      loopStride));
      CallExpr *arrayOffset = new CallExpr(A,
                                           indexOffset);
      symexpr->replace(arrayOffset);
    }
    prefetchCallArray = new CallExpr("prefetch",
                                     new_IntSymbol(candidate.ID),
                                     parentCallCopy);
  }

  // 3.) Now we can put the prefetch calls where they belong. If we had
  //     a potential array as the iterator, the array-specific prefetch
  //     goes in the then-block of the isArray() check, and the range/domain
  //     prefetch goes into the else-block. If we didn't have a potential
  //     array iterator, the range/domain prefetch goes into the then-block
  //     of the out-of-bounds check.
  if (prefetchCallArray != NULL) {
    thenBlock->insertAtHead(prefetchCallArray);
    elseBlock->insertAtHead(prefetchCallDomainOrRange);
  }
  else {
    // Didn't have ARRAY_OR_DOMAIN, so only need to worry about prefetchCallDomainOrRange.
    // It goes into the then-block for the out-of-bounds check
    candidate.outOfBoundsCond->thenStmt->insertAtTail(prefetchCallDomainOrRange);
  }
 
} /* end of createPrefetchCallARP */

//##################################################################################
/*
    This function creates the primitive for a candidate access as part of the
    adaptive remote prefetching (ARP) optimization.

    On the surface, we really don't need to pack much into this primitive, as we
    already generated the prefetch call. In other optimizations, we wait until
    prefolding to generate the optimization call and use info from the primitive
    to build that up.

    However, we do want to do one additional analysis during prefolding that does
    require some information. Specifically, we want to detect whether the array
    A from A[B[i]] holds records and note which fields are accessed within the
    loop. That way, we can issue our prefetches directly from the fields. In order
    to do this, we need to get access to the original A[B[i]] candidate so we can
    look for patterns like "ref t = A[B[i]]" or "var t = A[B[i]]", and then look
    for accesses like "t.field". So we will remove the original A[B[i]] access
    from the AST and replace it with the primitive, adding the A[B[i]] access to
    the primitive. During prefolding, we'll do our analysis and when we're done,
    we will replace the primitive with A[B[i]]. In this way, it is very similar
    to how we handle things for the IE optimization.

    Note we add in the gARPCandidateID int to the primitive. This is ONLY used
    in prefolding to keep track of which candidates we've processed. We can't
    use candidate.ID as that is relative to a given forall. So two "first"
    candidates in different foralls will have the same candidate.ID.

    Arguments:
    forall -> the forall with the candidate
    candidate -> the candidate access

    Return:
    None, AST is updated with the primitive
*/
static void createPrimitiveARP(ForallStmt *forall,
                               AdaptiveRemotePrefetchingCandidate &candidate)
{
  Symbol *A = getCallBase(candidate.parentCall);
  CallExpr *primitive = new CallExpr(PRIM_MAYBE_PREFETCH_CANDIDATE,
                                     new_IntSymbol(candidate.ID),
                                     new_IntSymbol(forall->optInfo.arpID),
                                     A,
                                     candidate.parentCall->copy(),
                                     candidate.staticCheck);

  // Add the symbols
  for (auto &sym : candidate.prefetchIndexSymbols) {
    primitive->insertAtTail(sym);
  }
    
  candidate.parentCall->replace(primitive);

} /* end of createPrimitiveARP */


///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                      Prefolding Related Functions                         //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
/*
    This is the function that gets called from prefold.cpp when it comes across
    a primitive we inserted for the adaptive remote prefetching (ARP) optimization.

    "call" is the primitive and it contains the following:

        candidateID, forallID, A, parentCall, staticCheck, sym1, sym2, ...
    
    The candidateID is just used for printing/logging purposes and the forall ID is
    used when/if we need to match the primitive to its enclosing forall. "A" is the 
    Symbol for the array "A" in "A[B[i]]"; we want to do some checks on that (see below). 
    "parentCall" is the actual A[B[i]] CallExpr. The primitive replaced that in the AST,
    so directly above parentCall should be the code we generated for the prefetching.
    This is important so we can find the prefetch call for the analysis described below.
    When we're done, we will replace the primitive with parentCall (or rather, preFold.cpp
    will do that). We pass in staticCheck which will be true or false, depending on whether
    prefetching was supported. If it is false, we don't do anything and just return normally.
    There is nothing to do since regardless if we were valid or not, the primitive is
    removed and replaced with the original access.

    We need to do processing of the prefetch index symbols in post resolution but they
    get lost during the generic-to-concrete creation when we are dealing with foralls
    in functions. So we brought them over in the primitive and we'll add them back to
    the forall candidate info.

    An additional check we do is to determine whether the array A from A[B[i]] stores
    records, and if so, whether specific fields of that record are accessed within the
    loop. The idea is that we should do our prefetch(es) from the fields, rather than
    just "A[B[i]]". If field1 is accessed and it is located at the very end of the
    record, our prefetch of "A[B[i]]" may miss that field. So we want to instead do
    prefetch(A[B[i]].field1). If there are multiple fields accessed, we insert a
    prefetch for each field. However, if a field that is accessed is an array, we
    will not attempt to prefetch that. In most cases, we will walk through that array
    in the code, and we have no hope (or desire) to prefetch the entire array. So
    we don't issue a prefetch for that field.

    Arguments:
    call -> the primitive for ARP

    Return:
    a NULL CallExpr; preFold.cpp takes care of things from that
*/
CallExpr *preFoldMaybePrefetchingCandidate(CallExpr *call)
{
  // Pull out the info
  int64_t ID, forallID;
  get_int(toSymExpr(call->get(1)), &ID);
  get_int(toSymExpr(call->get(2)), &forallID);
  VarSymbol *check = (VarSymbol *)(toSymExpr(call->get(5))->symbol());
  bool firstProcess = false;
  if (gPrefetchCallProcessed[forallID].count(ID) == 0) {
    gPrefetchCallProcessed[forallID].insert(ID);
    firstProcess = true;
  }

  if (fReportIrregArrayAccesses && firstProcess) {
    printf("\n+ [ADAPTIVE REMOTE PREFETCH] Pre-Folding Analyzing candidate #%ld in forall #%ld\n", ID, forallID);
  }

  // If check is false, we are done.
  if (check == gFalse) {
    if (fReportIrregArrayAccesses && firstProcess) {
      printf("\t!!! candidate is NOT valid; undoing optimization\n");
    }
  }
  else {
    if (fReportIrregArrayAccesses && firstProcess) {
      printf("\t- candidate is valid\n");
    }
    // Perform field access analysis, if needed
    fieldAccessAnalysisARP(call, firstProcess);
    // Copy over syms to candidate info. Need to get enclosing forall first
    compute_call_sites();
    ForallStmt *forall = findEnclosingForallLoop(call);
    INT_ASSERT(forall != NULL);
    // The whole reason for copying over the prefetch index symbols is when
    // the forall is copied due to a concrete instantiation of the function
    // that contains the forall. We know this happened if our candidate vector's
    // size is currently equal to our ID-1 (IDs are 1-based). Assumption is that
    // our candidates were processed and assigned IDs in the same order that we will
    // be processing them in preFolding.
    if ((ID-1) >= forall->optInfo.adaptiveRemotePrefetchingCandidates.size()) {
      AdaptiveRemotePrefetchingCandidate newCandidate;
      newCandidate.ID = (int)ID;
      for (int i = 6; i <= call->argList.length; i++) {
        newCandidate.prefetchIndexSymbols.insert((toSymExpr(call->get(i)))->symbol());
      }
      forall->optInfo.adaptiveRemotePrefetchingCandidates.push_back(newCandidate);
    }
  }

  if (fReportIrregArrayAccesses && firstProcess) {
    printf("+ [ADAPTIVE REMOTE PREFETCH] Pre-Folding Analysis Complete\n");
  }

  Expr *ret = call->get(4)->remove(); 
  return (CallExpr *)ret;

} /* end of preFoldMaybePrefetchingCandidate */


//##################################################################################
/*
    This function performs field access analysis for the adaptive remote prefetching
    (ARP) primitive/candidate "call".

    We look at the base array "A" from "A[B[i]]" and see whether it stores records.
    If it does, we look at whether specific record fields are accessed in the loop
    that contains call. For each unique field access we find, we will generate a
    prefetch call specifically for that field. This replaces the existing
    prefetch call we have for "A[B[i]]".
    
    However, we will not issue prefetches to fields that are arrays; those are not
    something we can hope to actually prefetch effectively.

    We could try to reuse the detectFieldAccesses() function for our purposes once
    we extract out the necessary info to pass into that. However, it does do things
    bit differently, as it exits early if it finds non-POD field accesses. So we'll
    copy it and make some changes.

    Arguments:
    call -> the ARP primitive
    doPrints -> if true we will do prints/logging here
    
    Return:
    None
*/
static void fieldAccessAnalysisARP(CallExpr *call,
                                  bool doPrints)
{
  int64_t ID;
  get_int(toSymExpr(call->get(1)), &ID);
  Symbol *A = (toSymExpr(call->get(3)))->symbol();
  Type *AeltType = arrayElementType(A->getValType());
  bool isRecordA = isRecord(AeltType);
  if (!isRecordA) {
    return;
  }

  if (fReportIrregArrayAccesses && doPrints) {
    printf("\t- base array %s stores records; will initiate prefetch from specific fields accessed\n", A->name);
  }

  AggregateType *at = toAggregateType(AeltType);
  // From parentCall, get "t" from "ref t = A[B[i]]" or "var t = A[B[i]]".
  Symbol *LHS = NULL;
  // Look for move(LHS, call)
  if (CallExpr *parent = toCallExpr(call->parentExpr)) {
    if (parent->isPrimitive(PRIM_MOVE)) {
      LHS = (toSymExpr(parent->get(1)))->symbol();
    }
  }
  INT_ASSERT(LHS);

  // Look for a move into a ref or var "t" where LHS from above
  // is on the RHS.
  Symbol *t = NULL;
  for_SymbolSymExprs(symexpr, LHS) {
    if (CallExpr *symCall = toCallExpr(symexpr->parentExpr)) {
      // Case 1: ref t = A[B[i]]
      if (symCall->isPrimitive(PRIM_ADDR_OF)) {
        if (CallExpr *moveCall = toCallExpr(symCall->parentExpr)) {
          if (moveCall->isPrimitive(PRIM_MOVE)) {
            // LHS of move is t
            t = (toSymExpr(moveCall->get(1)))->symbol();
            break;
          }
        }
      }
      // Case 2: var t = A[B[i]]
      else if (symCall->isPrimitive(PRIM_INIT_VAR)) {
        // Ensure that 2nd arg is symexpr
        if (symexpr == toSymExpr(symCall->get(2))) {
          // first arg is t
          t = (toSymExpr(symCall->get(1)))->symbol();
        }
      }
    }
  }
  INT_ASSERT(t);

  // Now from t, look for field accesses. Add their name
  // to the fieldNames vector.
  std::map<const char*, int> fieldInfo;
  findFieldAccessesARP(t,
                       at,
                       fieldInfo);

  if (fReportIrregArrayAccesses && doPrints) {
    printf("\t\t- the following non-array fields are accessed in the loop: ");
    for (auto &elem : fieldInfo) {
      printf("%s ", elem.first);
    }
    printf("\n");
  }

  // Now that we know the fields that are accessed, we can update our prefetch
  // call. For this candidate, we have a single prefetch call. We want to find that
  // and replace it with a call to prefetch that takes in the field position. We then add
  // additional prefetch calls after that if we have other fields. Finding it will
  // be easy because one of the arguments to prefetch is the candidate ID. So look
  // for all calls to "prefetch" in the forall loop that have a matching ID as the 
  // first argument.
  ForallStmt *forall = findEnclosingForallLoop(call);
  INT_ASSERT(forall);
  std::vector<CallExpr *> calls;
  std::vector<CallExpr *> prefetchCalls;
  collectCallExprs(forall->loopBody(), calls);
  for (auto &c : calls) {
    if (c->isNamed("prefetch")) {
      int64_t candidateID;
      get_int(toSymExpr(c->get(1)), &candidateID);
      if (candidateID == ID) {
        // this is a prefetch call to update. Add it the vector
        prefetchCalls.push_back(c);
      }
    }   
  }
  // For each prefetch call, remove/replace it with an identical call
  // but that specifies the index of the field to get. That will match
  // on the version of prefetch() that will then use getFieldRef().
  for (auto &prefetchCall : prefetchCalls) {
    BlockStmt *b = new BlockStmt();
    prefetchCall->insertAfter(b);
    for (auto &info : fieldInfo) {
      CallExpr *newCall = new CallExpr("prefetch");
      newCall->insertAtHead(prefetchCall->get(1)->copy());
      newCall->insertAtTail(prefetchCall->get(2)->copy());
      newCall->insertAtTail(new_IntSymbol(info.second));
      b->insertAtTail(newCall);
    }
    // Now remove prefetchCall
    prefetchCall->remove();
    // Normalize, resolve and flatten block that has new prefetch calls
    normalize(b);
    resolveBlockStmt(b);
    b->flattenAndRemove();
  }

} /* end of fieldAccessAnalysisARP */

//##################################################################################
/*
    Almost a copy of detectFieldAccesses() but modified for the adaptive remote
    prefetching (ARP) optimization. Look at all uses of the Symbol sym and detect
    accesses to fields of a record (i.e., t.field). For each field we find, add
    its name/index to the std::map. Skip over fields that are arrays.

    Arguments:
    sym -> the Symbol from "sym = A[B[i]]"
    at -> the record type that "A" from "A[B[i]]" holds
    fieldInfo -> stores names/index of fields that were accessed

    Return:
    None, fieldNamesARP is updated
*/
static void findFieldAccessesARP(Symbol *sym,
                                 AggregateType *at,
                                 std::map<const char *, int> &fieldInfo)
{
  // Look at each SymExpr that uses sym
  for_SymbolSymExprs(symexpr, sym) {
    if (CallExpr *symCall = toCallExpr(symexpr->parentExpr)) {
      if(Symbol *fieldSym = isFieldAccess(symCall, at)) {
        // fieldSym is a field from the record at that is accessed. 
        // Add its name/index to the map. Note that indices via Chapel's
        // Reflection module are 0 based but what we get from here is 1-based.
        // NOTE: skip the field if it is an array
        if (!fieldSym->getValType()->symbol->hasFlag(FLAG_ARRAY)) {
          fieldInfo[fieldSym->name] = at->getFieldPosition(fieldSym->name)-1;
        }
      }
      else {
        // is symCall a call to a function where t is an argument?
        if (toUnresolvedSymExpr(symCall->baseExpr)) {
          // TODO: not sure how best to detect whether we have a function call?
          // Are all UnresolvedSymExpr's function calls? For now, we'll be stupid
          // and assume it is. So find the arg pos of sym in the call so we can use
          // that when analyzing the function itself
          int argPos = -1;
          for (int i = 1 ; i <= symCall->argList.length ; i++) {
            if (symexpr == toSymExpr(symCall->get(i))) {
              argPos = i;
              break;
            }
          }
          INT_ASSERT(argPos > 0);
          forv_Vec(FnSymbol, fn, gFnSymbols) {
            if (symCall->isNamed(fn->name)) {
              // fn is the function that symCall calls
              // invoke this function on the formal
              Symbol *symFormal = NULL;
              int pos = 1;
              for_alist(formal, fn->formals) {
                if (pos == argPos) {
                  symFormal = toArgSymbol(toDefExpr(formal)->sym);
                  break;
                }
                pos++;
              }
              INT_ASSERT(symFormal != NULL);
              findFieldAccessesARP(symFormal, at, fieldInfo);
            }
          }
        }
      }
    }
  } /* end of for_SymbolSymExprs(symexpr, t) */
  return;

} /* end of findFieldAccessesARP*/

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                      Post Resolution Related Functions                    //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
/*
    Post resolution analysis for adaptive remote prefetching (ARP) is pretty
    straight forward, especially when compared to the inspector-executor
    optimization. During normalization we collected the Symbols used in the
    prefetch candidate access (ignoring the A and B arrays themselves). We
    want to ensure that each of these symbols is read-only within the loop
    that contains the prefetch itself. This is to further ensure that our
    prefetches are going to correspond to elements of the array that are
    actually accessed in future iterations.
    
    Consider A[B[i]+j] as our prefetch access, where "i" is the loop
    index variable. We account for "i" when we create the prefetch call,
    in that we compute the "future i" for the iteration we are prefetching
    for. But what about "j"? If "j" is constant within the loop, then we're
    OK. But if "j" is modified in the loop, like "j += foo", then we can't
    really make the assumption that A[B[i+dist]+j] is going to give us a
    valid future value. So we require that all symbols used in the prefetch
    call be read-only in the loop.

    If we find a candidate that does use read-only symbols, we invalidate it
    and remove it. This means just removing the "if out of bounds" CondStmt
    (only has a thenStmt).
*/
void adaptiveRemotePrefetchingPostAnalysis()
{
  // Look for calls to prefetch() and analyze the corresponding candidate.
  // Note that if we were dealing with records, we could have multiple
  // prefetch() calls for the same candidate. We use the 1st argument to
  // prefetch(), which is the candidateID, to know if we've processed the
  // candidate before; we don't need to do the processing for each call that
  // correspond to the same candidate
  bool firstPrint = true;
  std::map<int, std::set<int64_t>> processedCandidates;
  forv_Vec(CallExpr, call, gCallExprs) {
    if (call->parentExpr != NULL && call->theFnSymbol() && 
        call->theFnSymbol()->hasFlag(FLAG_REMOTE_CACHE_PREFETCH)) {
      if (firstPrint && fReportIrregArrayAccesses) {
        printf("\n+ [ADAPTIVE REMOTE PREFETCH] Post Analysis for adaptive remote prefetching candidates\n");
        firstPrint = false;
      }
      ForallStmt *forall = enclosingForallStmt(call);
      INT_ASSERT(forall != NULL);
      int forallID = forall->optInfo.arpID;
      int64_t candidateID;
      get_int(toSymExpr(call->get(1)), &candidateID);
      // have we seen this candidate in the forall before?
      bool processedAlready = true;
      // If we've never processed this forall before, it is a new candidate
      if (processedCandidates.count(forallID) == 0) {
        processedAlready = false;
      }
      else {
        // We've seen at least 1 candidate in this forall; is this one new?
        if (processedCandidates[forallID].count(candidateID) == 0) {
          processedAlready = false;
        }
      }
      if (processedAlready) { continue; }

      else {
        processedCandidates[forallID].insert(candidateID);
        if (fReportIrregArrayAccesses) {
          printf("\t- Analyzing candidate #%ld in forall #%d\n", candidateID, forallID);
        }
        if (postAnalyzePrefetchCandidate(call) == false) {
          if (fReportIrregArrayAccesses) {
            printf("\t\t- !!! candidate is invalid; removing optimization\n");
          }
          // Find the CondStmt above the prefetch call and remove it
          Expr *curr = call;
          CondStmt *cond = NULL;
          while (curr != NULL) {
            if (isCondStmt(curr)) {
              cond = toCondStmt(curr);
              break;
            }
            curr = curr->parentExpr;
          }
          INT_ASSERT(cond != NULL);
          cond->thenStmt->remove();
          cond->remove();
        }
        else {
          if (fReportIrregArrayAccesses) {
            printf("\t\t- candidate is valid\n");
          }
        }
      }
    }
  }
  if (!firstPrint && fReportIrregArrayAccesses) {
    printf("+ [ADAPTIVE REMOTE PREFETCH] Post Analysis for adaptive remote prefetching complete\n");
  }
} /* end of adaptiveRemotePrefetchingPostAnalysis */

//##################################################################################
/*
    Given a call to prefetch() for some candidate, do post analysis. This involves
    ensuring that the symbols used in the prefetch are read-only in the enclosing
    loop. If we find a symbol that is modified in the loop, we return false.

    Arguments:
    call -> the prefetch call to analyze
    
    Return:
    true if the candidate is valid, false otherwise
*/
static bool postAnalyzePrefetchCandidate(CallExpr *call)
{
  bool retval = true;
 
  // Get the first argument to prefetch(), which is the candidate ID
  int64_t candidateID;
  get_int(toSymExpr(call->get(1)), &candidateID);
  
  // Find the enclosing forall for this candidate
  ForallStmt *forall = enclosingForallStmt(call);
  INT_ASSERT(forall != NULL);

  // Get the candidate info
  AdaptiveRemotePrefetchingCandidate candidate = forall->optInfo.adaptiveRemotePrefetchingCandidates[candidateID-1];

  // Get the set of symbols used in the prefetch call
  std::set<Symbol *> syms = candidate.prefetchIndexSymbols;

  // For each symbol, we want to find all modifications that are made to it.
  // Then, for each modification, we ensure it is NOT within the scope of the
  // loop that contains the prefetch call. This is either the forall we found
  // above OR the enclosing for-loop if we had that type of structure. 
  // 
  // Just like we do for the inspector-executor, we also find any aliases
  // to these symbols and track their modifications. We also look across
  // function calls.
  //
  // This is works at identifying fields of records being used as a
  // symbol.
  std::map<Symbol *, std::map<CallExpr *, bool>> modifications;
  std::map<Symbol *, bool> aliasesAnalyzed;
  std::map<Symbol *, std::set<Symbol *>> aliasSymbols;
  compute_call_sites();
  for (auto &sym : syms) {
    aliasesAnalyzed.clear();
    aliasesAnalyzed[sym] = true;
    findAllModificationsToSymbol(sym,
                                 (Expr*)call->parentExpr,
                                 modifications,
                                 aliasesAnalyzed,
                                 aliasSymbols,
                                 false,
                                 NULL);
  }
  Expr *loop = (Expr *)forall;
  if (candidate.forloop != NULL) {
    loop = (Expr *)candidate.forloop;
  }
  // For each modification, see if it's in the scope of the loop
  for (auto &elem : modifications) {
    Symbol *sym = elem.first;
    // For every modification involing sym...
    for (auto &mods : elem.second) {
      CallExpr *mod = mods.first;
      // does forall/forloop contain the modification?
      if (doesExprContainExpr(mod, loop)) {
        retval = false;
        if (fReportIrregArrayAccesses) {
          // TODO: this will print call_tmp in the case of some alias
          printf("\t\t- !!! %s cannot be modified in loop\n", sym->name);
        }
        break;
      }
    }
  }

  return retval;
} /* end of postAnalyzePrefetchCandidate */







// Added by tbrolin 6/30/2022 - present
//
// Support for the irregular write aggregation (IWA) optimization.

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                      Normalization Related Functions                      //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
/*
    Entry function for the IWA optimization. We look specifically at accesses of
    the form "A[B[i]] op val" that are in forall loops. We do analysis to determine
    whether the operation can be aggregated and perform code transformations to
    replace the operation with an aggregator.

    Arguments:
    forall -> the ForallStmt to analyze

    Return:
    None
*/
void irregularWriteAggregation(ForallStmt *forall)
{
  // If this loop has already been checked for this optimization,
  // return. This happens when we make a clone of the forall via
  // other optimizations. This prevents an infinite loop.
  if (forall->optInfo.irregWriteAggregationChecked) {
    return;
  }
  forall->optInfo.irregWriteAggregationChecked = true;

  // Gather forall info. This gets us some information regarding the
  // loop's domain.
  if (!forall->optInfo.infoGathered) {
    gatherForallInfo(forall);
  }

  // Do not proceed if we can't determine the loop's domain statically.
  Symbol *loopDomain = canDetermineLoopDomainStatically(forall);
  if (loopDomain == NULL) {
    return;
  }

  // Step 1: look for candidates in the loop. A candidate is A[B[i]] that
  // is on the LHS of an operation (i.e., a write). We will do other checks
  // as well, such as whether there are data dependencies.
  //
  findCandidatesIWA(forall);

  // Only continue if we found candidates
  if (forall->optInfo.irregWriteAggrCandidates.size() == 0) {
    return;
  }

  // If we're here, then we have candidates. So generate the optimized
  // version of the forall loop. This does not do any loop cloning.
  optimizeLoopIWA(forall);

} /* end of irregularWriteAggregation */

//##################################################################################
/*
    Given a ForallStmt, look for candidates for the irregular write aggregation
    optimization. These are accesses of the form "A[B[i]] op val". In other words,
    indirect/irregular writes. We then do further analyze to ensure that "op" can
    be aggregated.

    The A[B[i]] pattern can be fairly complex/general. Unlike the IE optimization,
    we are not restricted to just expressions with binary operations. We can have
    function calls, tuple accesses, etc. Essentially, we just require that we have
    a CallExpr that has a call-base (call it B[expr]) and that is enclosed in some
    other CallExpr that has a call-base (call it A[expr(B[expr])]).

    Candidates that we find are added to the forall's optInfo vector of irregular
    write aggregation candidates.

    Arguments:
    forall -> the forall loop to analyze

    Return:
    None
*/
static void findCandidatesIWA(ForallStmt* forall)
{
  std::vector<CallExpr *> callExprs;
  collectCallExprs(forall->loopBody(), callExprs);

  for_vector(CallExpr, call, callExprs) {
    // 1.) Ensure that call has a call-base, which means we
    //     have something like B[expr].
    if (getCallBase(call)) {
      // Correctly handles triple nested things like A[B[C[i]]].
      // We will apply the optimization to C[i]/B[C[i]], but not
      // to B[C[i]]/A[B[C[i]].
      if (doesCallHaveNestedCallBaseIE(call)) {
        continue;
      }

      // 2.) From call, look "up" until we find a CallExpr that
      //     we can get the call-base for. That would be "A" from
      //     something like A[B[expr]]. We are more flexible here when
      //     compared to the IE optimization, as we are not limited to
      //     just binary operations. We only consider the candidate invalid
      //     if we hit something that isn't a CallExpr. Also stop if we're
      //     in a primitive.
      CallExpr *parentCall = NULL;
      CallExpr *curr = call;
      bool isValid = true;
      while (isValid) {
        if ((curr = toCallExpr(curr->parentExpr))) {
          if (curr->isPrimitive(PRIM_MAYBE_IRREG_ACCESS) ||
              curr->isPrimitive(PRIM_MAYBE_IRREG_AGGREGATE_WRITE) ||
              curr->isPrimitive(PRIM_MAYBE_PREFETCH_CANDIDATE)) {
            isValid = false;
          }
          else if (getCallBase(curr)) {
            parentCall = curr;
            break;
          }
        }
        else {
          isValid = false;
        }
      } /* end of while isValid */
      if (isValid == false) { continue; }
      INT_ASSERT(parentCall != NULL);

      // Ensure we're not nested in a primitive
      CallExpr *tmp = parentCall;
      while (tmp != NULL && tmp->parentExpr != NULL) {
        if (tmp->isPrimitive(PRIM_MAYBE_IRREG_ACCESS) ||
            tmp->isPrimitive(PRIM_MAYBE_IRREG_AGGREGATE_WRITE) ||
            tmp->isPrimitive(PRIM_MAYBE_PREFETCH_CANDIDATE)) {

          isValid = false;
          break;
        }
        else if (tmp->isNamed("prefetch")) {
          isValid = false;
          break;
        }
        tmp = toCallExpr(tmp->parentExpr);
      }
      if (isValid == false) { continue; }

      // Now we have call and parentCall, so do further
      // analysis
      analyzeCandidateIWA(call, parentCall, forall);
    } /* end of if getCallBase */
  } /* end of for_vector */
} /* end of findCandidatesIWA */

//##################################################################################
/*
    Given a potential candidate for the irregular write aggregation optimization,
    perform analysis to determine whether it is a valid candidate.

    If the candidate is valid, we add it to the forall's vector of candidates for
    the irregular write aggregation optimization.

    Arguments:
    call -> the B[i] in A[B[i]]
    parentCall -> A[B[i]]
    forall -> the forall that the candidate is in

    Return:
    true if a call is an assignment, false otherwise
*/
static void analyzeCandidateIWA(CallExpr *call,
                                CallExpr *parentCall,
                                ForallStmt *forall)
{
  Symbol *callBase = getCallBase(call);
  Symbol *parentCallBase = getCallBase(parentCall);

  // Only print info about this candidate if we haven't processed it before.
  bool oldFReport = fReportIrregArrayAccesses;
  if (gCandidatesAnalyzedIWA.count(parentCall->stringLoc()) != 0) {
    fReportIrregArrayAccesses = false;
  }
  else {
    gCandidatesAnalyzedIWA.insert(parentCall->stringLoc());
  }

  if (fReportIrregArrayAccesses) {
    printf("+ [IRREG WRITE AGGR] Considering candidate irregular access at %s (forall at %s)\n", parentCall->stringLoc(),
                                                                                forall->stringLoc());
    printf("\t- Parent: %s, Call: %s\n", parentCallBase->name, callBase->name);
  }

  // 0.) Ensure that the candidate is not nested in a call to prefetch(), which is part of the
  // prefetch optimization.
  CallExpr *tmp = parentCall;
  while (tmp != NULL && tmp->parentExpr != NULL) {
    if (tmp->isNamed("prefetch")) {
      if (fReportIrregArrayAccesses) {
        printf("\t\t !!! irregular access cannot be an argument to prefetch()\n");
      }
      fReportIrregArrayAccesses = oldFReport;
      return;
    }
    tmp = toCallExpr(tmp->parentExpr);
  }

  // 1.) A cannot be defined inside of the forall
  //
  if (forall->loopBody()->contains(parentCallBase->defPoint)) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t !!! %s cannot be defined inside of the forall\n", parentCallBase->name);
    }
    fReportIrregArrayAccesses = oldFReport;
    return;
  }

  // 2.) Ensure that A[B[i]] is on the LHS of an operation and that operation
  // is something we can aggregate.
  //
  // We need to ensure that A[B[i]] is on the LHS of an operation (i.e., a write).
  // These will look like the following:
  /*
    (182782 CallExpr
      (182783 UnresolvedSymExpr OP)
      (182785 CallExpr
        (398469 SymExpr 'unknown A')
        (182787 CallExpr
          (398470 SymExpr 'unknown B')
          (398471 SymExpr 'unknown i')))
      (182791 SymExpr ))
  */
  // So what we want to do is look at parentCall->parentExpr and ensure it is a CallExpr
  // and that it is an operation we can aggregate. We also want to make sure that parentCall
  // is the first argument to the CallExpr, which says it is on the LHS. For now, we support
  // aggregation for =, += and atomic adds. Later on, we will generalize it so we can aggregate
  // any operation that is deemed valid.
  //
  // For something like A[B[i]].add(1), opCall's parent is a CallExpr where the first argument
  // is opCall and the 2nd argument is the literal 1 passed into the add(). If A[B[i]].add(1)
  // is truly on the LHS, then opCall->parentExpr->parentExpr cannot be a CallExpr. If we
  // have something like A[B[i]] += 34, then the first argument to opCall must be parentCall.
  bool isOnLHS = false;
  if (CallExpr *opCall = toCallExpr(parentCall->parentExpr)) {
    CallExpr *opParent = toCallExpr(opCall->parentExpr);
    if (opParent == NULL) {
      // Ensure that the first argument to opCall is parentCall
      if (CallExpr *firstArg = toCallExpr(opCall->get(1))) {
        if (firstArg == parentCall) {
          isOnLHS = true;
        }
      }
    }
    else {
      if (toCallExpr(opParent->baseExpr) == opCall) {
        if(!isCallExpr(opParent->parentExpr)) {
          isOnLHS = true;
        }
      }
    }
  }
  if (isOnLHS == false) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t !!! irregular access is not on LHS of operation\n");
    }
    fReportIrregArrayAccesses = oldFReport;
    return;
  }
  else {
    if (fReportIrregArrayAccesses) {
      printf("\t\t- irregular access is on the LHS of the operation\n");
    }
  }
  // Now we know that we have A[B[i]] on the LHS; make sure there is
  // an aggregatable operation here.
  IrregWriteAggrOp opType = isOperationAggregatable(parentCall);
  if (opType == INVALID) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t !!! unsupported operation for aggregation\n");
    }
    fReportIrregArrayAccesses = oldFReport;
    return;
  }
  else {
    if (fReportIrregArrayAccesses) {
      printf("\t\t- Operation is aggregate-able\n");
    }
  }

  // 3.) Ensure that the RHS is local (for now, we do not do this; see below).
  //
  // Now we know we have an operation that we could aggregate, and A[B[i]] is on the LHS.
  // Ideally, we would ensure that the RHS is local but in most of our use-cases, that is
  // not easily done. For now, we will do aggregation regardless of whether the RHS is local.
  // TODO: for something like BFS, where we have A[B[i]] += v, and v is a loop index variable
  // yielded from V[u].neighbors, it will be tricky to determine that the neighbors array is
  // local. We could do it dynamically with a cost (i.e., check whether V[u].neighbors.locale.id
  // is the same as here.id).

  // 4.) Check whether A[B[i]] is in a for-loop, and ensure it is a foreach
  //
  // The next thing to check is whether the operation is order independent. If it is directly nested
  // in the forall, then that is true (thus far). But we want to support having the operation within
  // something like a for-loop within a forall. For now, we'll support that by enforcing that the for
  // loop is a foreach, which enforces order-independent properties like a forall. So first we see
  // whether the A[B[i]] is in a for-loop, which is itself nested in the forall. We call the
  // isOrderIndependent() method on the for-loop; if it returns true, then the for loop is a foreach.
  // Note that we do not look across function calls for the enclosing for/foreach loop. If we found
  // our candidate in a forall, it suggests that the relevant for/foreach loop is within the current
  // function scope.
  ForLoop *f = findEnclosingForLoop(call);
  compute_call_sites(); // needed by doesExprContainExpr
  if (f != NULL && doesExprContainExpr(f, forall)) {
    // f is a for-loop nested in the forall; is it a foreach loop?
    if (!f->isOrderIndependent()) {
      if (fReportIrregArrayAccesses) {
        printf("\t\t !!! irregular access is in a for-loop, but it needs to be a foreach loop\n");
      }
      fReportIrregArrayAccesses = oldFReport;
      return;
    }
    else {
      if (fReportIrregArrayAccesses) {
        printf("\t\t- irregular access is in a foreach loop\n");
      }
    }
  }

  // Another aspect of order independence is that there are no data dependencies on A that are in the
  // loop body. This could be the case if there is a read/write after the operation. Since the above
  // enforces that we have order indepedent iterations, there are no loop carry dependencies to worry
  // about. So we just focus on the loop body (i.e., an iteration) as a stand-alone serial basic block.
  // See the function we call below for more info about what we are looking for.
  //
  // We want to pass into aggregatedStmtHasDataDependencies the top-most CallExpr for the aggregated
  // statement. For something like A[B[i]].add(1), this will be opParent from earlier. Otherwise, it
  // will be opCall. We also pass in just parentCall, so we can extract the symbol A from A[B[i]].
  //
  // opCall cannot be NULL here since it was a condition to get past the above checks
  CallExpr *opCall = toCallExpr(parentCall->parentExpr);
  CallExpr *opParent = toCallExpr(opCall->parentExpr);
  CallExpr *aggrCall = opParent;
  if (aggrCall == NULL) {
    aggrCall = opCall;
  }
  if (aggregatedStmtHasDataDependencies(forall, aggrCall, parentCall)) {
    if (fReportIrregArrayAccesses) {
      printf("\t\t !!! cannot do aggregation; data dependencies exist\n");
    }
    fReportIrregArrayAccesses = oldFReport;
    return;
  }
  else {
    if (fReportIrregArrayAccesses) {
      printf("\t\t- no data dependencies detected\n");
    }
  }

  // At this point, the candidate is valid. We want to extract the LHS and RHS so we can
  // manipulate it easier later on. For the typical A[B[i]] op val, we will have
  // LHS = A[B[i]] and RHS = val. But the atomic adds are different, since there is no
  // official RHS. Instead, we need to pull out the argument to add().
  //
  Expr *LHS = NULL;
  Expr *RHS = NULL;
  if (opType != ATOMIC_ADD) {
    LHS = toExpr(opCall->get(1));
    RHS = toExpr(opCall->get(2));
  }
  else {
    LHS = toExpr(opCall->get(1));
    CallExpr *parentOpCall = toCallExpr(opCall->parentExpr);
    RHS = toExpr(parentOpCall->get(1));
  }
  INT_ASSERT(LHS != NULL);
  INT_ASSERT(RHS != NULL);

  // Add the candidate; all we need is the LHS, RHS and the operation
  std::tuple<Expr *, Expr *, IrregWriteAggrOp> candidate;
  std::get<0>(candidate) = LHS;
  std::get<1>(candidate) = RHS;
  std::get<2>(candidate) = opType;
  forall->optInfo.irregWriteAggrCandidates.push_back(candidate);

  if (fReportIrregArrayAccesses) {
    printf("\t\t- candidate is value so far. If no prefolding prints are shown later, it was invalid\n");
    printf("\t\t  due to a non-distributed parent array or non-supported aggregation.\n");
  }

  fReportIrregArrayAccesses = oldFReport;
} /* end of analyzeCandidateIWA */

//##################################################################################
/*
    Given a CallExpr that is the A[B[i]] we are analyzing, determine whether the
    operation performed on it is something we can aggregate. For now, we specifically
    look for +=, .add() and =.

    TODO: Going forward, we could relax this and just try to exclude operations that we
    know are not associative/safe to aggregate (like -=). But at the same time, the fact
    that the user put the operation in a forall is an assertion on their part that the
    iterations are order-independent. For now, we'll just stick with the operations above
    since those are the ones we have test-cases for.

    Arguments:
    call -> the CallExpr to analyze

    Return:
    IrregWriteAggrOp that represents the type of operation or INVALID if we
    cannot do aggregation.
*/
static IrregWriteAggrOp isOperationAggregatable(CallExpr *call)
{
  IrregWriteAggrOp opType = INVALID;
  if (CallExpr *opCall = toCallExpr(call->parentExpr)) {
    if (opCall->isNamedAstr(astrSassign) == true) {
      opType = ASSIGNMENT;
    }
    else if (opCall->isNamed("+=")  == true) {
      opType = PLUSEQ;
    }
    else if (opCall->isNamed(".")  == true) {
      // If here, then we have something like A[B[i]].op. This happens for
      // atomic adds. So let's look for the .add call. This is 2nd argument
      // to opCall.
      if (SymExpr *symexpr = toSymExpr(opCall->get(2))) {
        if (VarSymbol *var = toVarSymbol(symexpr->symbol())) {
          if (strcmp(var->immediate->v_string.c_str(), "add") == 0) {
            opType = ATOMIC_ADD;
          }
        }
      }
    }
  }
  return opType;
} /* end of isOperationAggregatable */

//##################################################################################
/*
    Given the forall of interest and the aggregation candidate call, where call's
    base is A from A[B[i]], determine whether there are any data dependencies that
    would invalidate the aggregation optimization. We have the following cases to
    consider:

    1.) There can be no reads or writes to A (and its aliases) after the aggregated
    statement. This only applies to statements within the forall loop's body. If the
    aggregated statement is in a foreach loop, it applies to the statements in that loop as
    well as those after the foreach loop (while still in the forall loop).

    2.) For any function calls made after the aggregated statement within the forall,
    we look for accesses made to A (and all of its aliases) in that function. If A is
    passed in as an argument, we don't need to do this. Otherwise, we are conservative
    and assume that A (and its aliases) is global and that there could be an access
    within the function. So we dive into that function and look for accesses to A
    and all of its aliases.

    3.) For any aliases derived from A (i.e., ref foo = A), we check the aliases for the
    situations described in (1).

    The way we will go about this is to first gather all the aliases to A and store them
    in a set. We then will perform (1) and (2) above, referring to each alias when
    doing the checks.

    If we find any data dependencies, we return false. Otherwise we return true.

    Arguments:
    forall -> the forall of interest that contains the aggregated statement
    aggrCall -> the "top" CallExpr that contains the A[B[i]] call
    call -> the A[B[i]] CallExpr

    Return:
    true if there are no data dependencies, false otherwise.
*/
static bool aggregatedStmtHasDataDependencies(ForallStmt *forall,
                                              CallExpr *aggrCall,
                                              CallExpr *call)
{
  // Extract out the Symbol for A in A[B[i]]
  Symbol *A = getCallBase(call);
  INT_ASSERT(A != NULL);

  // 1.) Find all aliases to A throughout the entire program.
  // This also finds any aliases to those aliases, etc.
  // Each alias we find is added to the set below.
  std::set<Symbol *> aliasSymbols;
  findAliasesForSymbol(A, aliasSymbols, toFnSymbol(forall->parentSymbol));

  // 2.) Starting from the forall's body, see whether any of the symbols in
  //     aliasSymbols are used AFTER the aggregation call. This indicates a
  //     data dependency.
  //
  BlockStmt *block = forall->loopBody();
  bool doDependencyCheck = false;
  bool foundDependency = false;
  std::set<FnSymbol *> fnProcessed;
  areSymbolsUsedInBlock(block,
                        aggrCall,
                        &doDependencyCheck,
                        &foundDependency,
                        aliasSymbols,
                        fnProcessed);

  return foundDependency;

} /* end of aggregatedStmtHasDataDependencies */

//##################################################################################
/*
    Given the Symbol sym, find all aliases made from it (i.e., ref foo = sym).
    This is recursive: as we find an alias, we will call this function on that
    alias symbol and look for aliases to it. Since we have a set to store the
    alias symbols, we avoid processing the same symbol twice by ensuring the
    symbol is not already in the set.

    We also handle the case where we have ref sym = foo, where we will look at foo
    and find any aliases made to it.

    If a given Symbol is a formal to a function, then we will look at all call sites
    of the function and analyze the actual from the call site.

    Arguments:
    sym -> the current symbol to find aliases for
    aliases -> set of alias Symbols we have found thus far
    fn -> FnSymbol of the current function we are in (NULL if we are not in a function).

    Return:
    None; aliases is updated
*/
static void findAliasesForSymbol(Symbol *sym,
                                 std::set<Symbol *> &aliases,
                                 FnSymbol *fn)
{
  // We always add sym to the set. Upon the very first call to this
  // function, sym is our A from A[B[i]]. When called recursively,
  // sym is the alias we just found. But we want to ensure that we
  // are not processing the same sym again, which will cause infinite
  // recursion.
  if (aliases.count(sym)) {
    // we've seen sym already, so don't process it
    return;
  }
  aliases.insert(sym);

  // 1.) Determine whether sym is an alias to something else.
  //     We can tell by looking at sym's defPoint and checking
  //     if it is a ref variable. We would see this for something
  //     like "ref sym = foo". In that case, we add foo to our
  //     aliases set and then call this function recursively on
  //     foo. So also check for "ref sym = foo[0..2]", which has
  //     a different structure from the simple assignment case, and
  //     "ref sym = foo.field".
  //
  Expr *expr = NULL;
  if (VarSymbol *var = toVarSymbol(sym->defPoint->sym)) {
    if (var->hasFlag(FLAG_REF_VAR)) {
      expr = sym->defPoint->init;
    }
  }
  // sym could be a formal to a function. If so, go to the call-sites
  // of the function and search from there until we find its declaration.
  // Only do this if we know the intent is REF
  else if (ArgSymbol *arg = toArgSymbol(sym->defPoint->sym)) {
    // Sanity check
    INT_ASSERT(fn != NULL);
    if (arg->intent == INTENT_FLAG_REF) {
      // Find call sites of fn. Since this is during normalization, we cannot use
      // compute_callsites()
      forv_Vec(CallExpr, call, gCallExprs) {
        if (call->isNamed(fn->name)) {
          // extract out the actual arg from the call site
          int argPos = -1, currPos = 0;
          for_alist(formal, fn->formals) {
            if(ArgSymbol* arg1 = toArgSymbol(toDefExpr(formal)->sym)) {
              if (arg1 == arg) {
                argPos = currPos;
                break;
              }
            }
            currPos++;
          }
          INT_ASSERT(argPos != -1);
          Symbol *callSiteSym = toSymExpr(call->get(argPos+1))->symbol();
          findAliasesForSymbol(callSiteSym, aliases, toFnSymbol(call->parentSymbol));
        }
      }
    }
  }
  if (expr != NULL) {
    Symbol *aliasSym = NULL;
    // Handle case when we have ref sym = foo.field. We want grab foo
    // and add that to the alias set
    if (CallExpr *call = toCallExpr(expr)) {
      if (call->isNamedAstr(astrSdot)) {
        aliasSym = (toSymExpr(call->get(1)))->symbol();
      }
      // Like we do below further below, we could have something like ref sym = foo[0..2].
      // In that case, call's baseExpr would be the symbol we want, and the first
      // argument to call is the call to chpl_build_bounded_range. So let's do these
      // checks to make sure that is what we see
      else if (CallExpr *sliceCall = toCallExpr(call->get(1))) {
        if (UnresolvedSymExpr *uSE = toUnresolvedSymExpr(sliceCall->baseExpr)) {
          if (strcmp(uSE->unresolved, "chpl_build_bounded_range") == 0) {
            // Ensure we have a DefExpr, ->sym is equal to sym and ->init is
            // equal to call. If that all matches, then the alias we want is
            // call's baseExpr
            if (DefExpr *defExpr = toDefExpr(call->parentExpr)) {
              if (defExpr->sym == sym && defExpr->init == call) {
                aliasSym = toSymExpr(call->baseExpr)->symbol();
              }
            }
          }
        }
      }
    }
    else {
      // Simple case of ref sym = foo
      aliasSym = (toSymExpr(sym->defPoint->init))->symbol();
    }
    INT_ASSERT(aliasSym != NULL);

    // Call this function recursively on aliasSym
    findAliasesForSymbol(aliasSym, aliases, fn);

  } /* end of if (expr != NULL) */

  // 2.) If sym is not an alias itself, it could be the "original"
  //     symbol, and there could be aliases to it. This would be
  //     something like "ref foo = sym". In that case, we want to add
  //     "foo" to our alias set and call this function on foo. Furthermore,
  //     sym could be used to create multiple aliases, so we need to find each
  //     one. We also handle "ref foo = sym[0..2]"
  for_SymbolSymExprs(symexpr, sym) {
    Symbol *aliasSym = NULL;
    // For something like ref alias = sym, it will be a DefExpr and the ->sym field
    // will be "alias". We only care about "alias" if it is a ref variable. Something
    // like "var alias = sym" is not something we care about.
    if (DefExpr *defExpr = toDefExpr(symexpr->parentExpr)) {
      aliasSym = defExpr->sym;
      INT_ASSERT(aliasSym != NULL);
    }
    // Another case is something like "ref alias = sym[0..2]". In that case,
    // symexpr->parentExpr is a call and the parentExpr of that is the DefExpr
    // we care about. Lets look fairly explicitly for what would be there when we
    // are taking a slice of sym.
    else if (CallExpr *call = toCallExpr(symexpr->parentExpr)) {
      // call->baseExpr should be symexpr
      if (call->baseExpr == symexpr) {
        // First argument to call is another CallExpr to chpl_build_bounded_range
        if (CallExpr *sliceCall = toCallExpr(call->get(1))) {
          if (UnresolvedSymExpr *uSE = toUnresolvedSymExpr(sliceCall->baseExpr)) {
            // Finally make sure uSE is chpl_build_bounded_range
            if (strcmp(uSE->unresolved, "chpl_build_bounded_range") == 0) {
              // Now we know we have "alias = sym[0..2]".
              if (DefExpr *defExpr = toDefExpr(call->parentExpr)) {
                // Same checks are before: get the symbol and make sure it is a ref
                aliasSym = defExpr->sym;
                INT_ASSERT(aliasSym != NULL);
              }
            }
          }
        }
      }
    }
    // If we found an alias, analyze it if it is a ref.
    if (aliasSym != NULL) {
      VarSymbol* var = toVarSymbol(aliasSym->defPoint->sym);
      if (var->hasFlag(FLAG_REF_VAR)) {
        findAliasesForSymbol(aliasSym, aliases, fn);
      }
    }
  } /* end of for_SymbolSymExprs */


  // No aliases found for sym
  return;
} /* end of findAliasesForSymbol */

//##################################################################################
/*
    Given a BlockStmt, iterate through its statements and look for one that matches
    the specified matchCall. This represents the aggregated statement of interest,
    and once we find it, we want to start analyzing subsequent statements. Specifically
    the analysis is whether any of the statements use any of the symbols contained in
    the symbols set.

    This is a recursive function, since we will come across other block statements that
    we need to "dive" into.

    We also correctly handle function calls. If the call uses one of the symbols as an
    argument, we will detect that. If it does not, we will dive into the function itself
    and see whether any of the symbols are used. This could happen if a symbol was a global
    variable.

    Arguments:
    block -> the current BlockStmt to inspect
    matchCall -> the CallExpr to look for initially
    doDependencyChecks -> true if we should be doing dependency checks
    foundDependency -> will be set to true if we found a data dependency
    symbols -> set of Symbols to check against
    fnProcessed -> set of FnSymbols that we've processed thus far

    Return:
    None; foundDependency will be set to true if we found a dependency
*/
static void areSymbolsUsedInBlock(BlockStmt * block,
                                  CallExpr *matchCall,
                                  bool *doDependencyChecks,
                                  bool *foundDependency,
                                  std::set<Symbol *> symbols,
                                  std::set<FnSymbol *> &fnProcessed)
{
  // If we have a dependency, there is no need to keep looking.
  if (*foundDependency == true) {
    return;
  }

  for_alist(node, block->body) {
    // If we haven't started the dependency checks yet, see if we have reached
    // the aggregated statement (matchCall). Once we find it, we analyze all subsequent
    // statements.
    if (!(*doDependencyChecks)) {
      // If we have a Forall, look into its body
      if (ForallStmt *forall = toForallStmt(node)) {
        areSymbolsUsedInBlock(forall->loopBody(), matchCall, doDependencyChecks, foundDependency, symbols, fnProcessed);
      }
      // If we have a for, while, do-while, etc.
      else if (LoopStmt* loop = toLoopStmt(node)) {
        // Find the BlockStmt in the body
        BlockStmt *b = NULL;
        for_alist(fnode, loop->body) {
          if (isBlockStmt(fnode)) {
            b = toBlockStmt(fnode);
            break;
          }
        }
        INT_ASSERT(b != NULL);
        areSymbolsUsedInBlock(b, matchCall, doDependencyChecks, foundDependency, symbols, fnProcessed);
      }
      // If we hit a BlockStmt, we need to dive into it
      else if (BlockStmt *b = toBlockStmt(node)) {
        areSymbolsUsedInBlock(b, matchCall, doDependencyChecks, foundDependency, symbols, fnProcessed);
      }
      // DeferStmts have a BlockStmt within them
      else if (DeferStmt *d = toDeferStmt(node)) {
        areSymbolsUsedInBlock(d->body(), matchCall, doDependencyChecks, foundDependency, symbols, fnProcessed);
      }
      // For CondStmts, look at the then and else blocks. We also need to consider the cond expr
      // itself.
      else if (CondStmt *c = toCondStmt(node)) {
        if (CallExpr *call = toCallExpr(c->condExpr)) {
          if (call == matchCall) {
            // Found the aggregated statement.
            *doDependencyChecks = true;
          }
        }
        if (c->thenStmt != NULL) {
          areSymbolsUsedInBlock(c->thenStmt, matchCall, doDependencyChecks, foundDependency, symbols, fnProcessed);
        }
        if (c->elseStmt != NULL) {
          areSymbolsUsedInBlock(c->elseStmt, matchCall, doDependencyChecks, foundDependency, symbols, fnProcessed);
        }
      }

      // Finally, if we just have a CallExpr, see if it is our matchCall.
      else if (CallExpr *call = toCallExpr(node)) {
        if (call == matchCall) {
          // Found the aggregated statement.
          *doDependencyChecks = true;
        }
      }
    } /* end of if !doDependencyCheck */

    else {
      // If here, then we will be checking these nodes for any use of the
      // Symbols.
      std::vector<SymExpr *> symExprs;
      collectSymExprs(node, symExprs);
      for (auto &se : symExprs) {
        if(Symbol *nodeSym = se->symbol()) {
          for (auto &sym : symbols) {
            if (nodeSym == sym) {
              *foundDependency = true;
              return;
            }
          }
        }
      }
      // Handle function calls that DO NOT pass in the symbols as arguments.
      // Dive into the function and see if the symbols are used. If a symbol was
      // global, this could be the case. For each function we process, add it to
      // the set fnProcessed so we don't recurse forever.
      if (CallExpr *call = toCallExpr(node)) {
        if (toUnresolvedSymExpr(call->baseExpr)) {
          forv_Vec(FnSymbol, fn, gFnSymbols) {
            // haven't processed this function yet
            if (fnProcessed.count(fn) == 0) {
              if (call->isNamed(fn->name)) {
                // fn is the function that node calls
                fnProcessed.insert(fn);
                areSymbolsUsedInBlock(fn->body, matchCall, doDependencyChecks, foundDependency, symbols, fnProcessed);
              }
            }
          }
        }
      }
    }
  } /* end of for_alist */

} /* end of areSymbolsUsedInBlock */

//##################################################################################
/*
    Given a forall that has candidates for the irregular write aggregation
    optimization, generate the optimized version of the forall. The end
    result of this function is to create the following:

        forall ... with (var agg1 = new Agg, var agg2 = new Agg) {
             ...
            param staticCheck1 : bool = chpl__isAggregationSupported(..)
            if staticCheck1 == true {
                agg1.bufferOp(..);
            }
            else {
                original op1
            }
            ...
            param staticCheck2 : bool = chpl__isAggregationSupported(..)
            if staticCheck2  == true {
                agg2.bufferOp(..);
            }
            else {
                original op2
            }
        }

    Because we may have more than one candidate in the forall, we need to protect each
    operation with its own static-check if-then-else. In the IE optimization, we put the
    entire forall in an if-then-else, since we only considered 1 candidate. But in this
    case, one candidate may end up being valid and the other invalid. So we need to a way
    to more carefully remove invalid aggregators. So we DO NOT create a clone of the forall
    here. Note that the static checks are params, since all checks we need to perform can
    be done via Chapel code at compile time (the call to chpl__isAggregationSupported). This
    way, the if or else will be eliminated depending on what the param check resolves to.
    We could not do this approach for the IE optimization because we had several checks
    that could not be done via Chapel code at compile time.

    Another thing we generate is a Record that has a single Type method that represents the
    operation we are aggregating. So something like this:

        record AggOp {
            inline proc type op(ref lhs, const rhs) {
                lhs <op> rhs;
            }
        }

    where <op> is the operator we extracted earlier for the candidate. We add this record
    declaration in the same module as the forall. When we generate the call to create the
    aggregator, we pass in AggOp (as a type). When the buffers are flushed, the Type method
    will be invoked.

    Arguments:
    forall -> the forall that the candidates are in

    Return:
    None; the forall is modified
*/

static void optimizeLoopIWA(ForallStmt *forall)
{
  SET_LINENO(forall);
  std::vector< std::tuple<Expr *, Expr *, IrregWriteAggrOp> > &candidates = forall->optInfo.irregWriteAggrCandidates;

  // For each candiate, we will do the following:
  //    1.) Create the record/Type method for the operator
  //    2.) Add the code that creates the aggregator and add it to the forall's shadow variables
  //    3.) Create a staticCheck param that will hold the result of chpl__isAggregationSupported and
  //        then set up the conditional that checks for staticCheck == true.
  //    4.) Generate the if-then-else structure for the aggregated operation
  //    5.) Replace the A[B[i]] op val expression in the "then" branch with the
  //        PRIM_MAYBE_IRREG_AGGREGATE_WRITE primitive

  for(auto &candidate : candidates) {
    int myID = gIWACandidateID++;
    // Used in prefolding so we don't redo things for a cloned loop.
    gIrregWriteAggLoopProcessed[(int64_t)myID] = false;

    // Pull out info for this candidate. LHS is A[B[i]] and we'll keep
    // it as a CallExpr. RHS may be an immediate, variable or a call, so
    // we keep it as an Expr.
    CallExpr *LHS = toCallExpr(std::get<0>(candidate));
    Expr *RHS = std::get<1>(candidate);
    IrregWriteAggrOp op = std::get<2>(candidate);
    Symbol *A = getCallBase(LHS);
    INT_ASSERT(A != NULL);

    // 1.) Create the AggOp record and Type method.
    TypeSymbol *aggType = generateAggregationRecord(forall,
                                                    myID,
                                                    op);

    // 2.) Create the Aggregator object and store it as part of the forall's
    //     shadow variables.
    CallExpr *genCall = new CallExpr("chpl__irregWriteAggregatorGeneral", A, aggType);
    UnresolvedSymExpr *aggTmp = new UnresolvedSymExpr("chpl_irregWrite_agg");
    ShadowVarSymbol *aggregator = ShadowVarSymbol::buildForPrefix(SVP_VAR,
                                                                  aggTmp,
                                                                  NULL,
                                                                  genCall);
    aggregator->addFlag(FLAG_COMPILER_ADDED_AGGREGATOR);
    forall->shadowVariables().insertAtTail(aggregator->defPoint);

    // 3.) Create staticCheck param variable
    VarSymbol *staticCheck = new VarSymbol("staticCheckIWA");
    staticCheck->addFlag(FLAG_PARAM);
    CallExpr *isAggSupported = new CallExpr("chpl__isAggregationSupported",
                                            A,
                                            aggregator);
    DefExpr *staticCheckDef = new DefExpr(staticCheck, isAggSupported);
    Expr *staticCond = new CallExpr("==", staticCheck, gTrue);
    
    // 4.) Create the if-then-else structure around the operation. The if-cond
    //     will be placed before the operation, so we need to look at the LHS
    //     and go "up" until we hit a block statement; the Expr before that is what we want.
    //     We will make a copy of this Expr and use that as the un-optimized version. The
    //     original will be modified to use the primitive.
    Expr *entryPoint = LHS->parentExpr;
    for (Expr* curr = LHS->parentExpr; curr; curr = curr->parentExpr) {
        if (isBlockStmt(curr)) {
            break;
        }
        entryPoint = curr;
    }
    INT_ASSERT(entryPoint != NULL);
    // Copy the Expr and use it as the un-optimized version
    Expr *exprCopy = entryPoint->copy();

    // 5.) Replace the operation in the original Expr with the primitive.
    //     Note that LHS and RHS are still pointers to what is in entryPoint.
    //     We return what createPrimitive() creates and store it in entryPoint,
    //     since we replaced it within createPrimitiveIWA(), so our pointer before
    //     is not useful.
    entryPoint = createPrimitiveIWA((Expr*)LHS,
                                    RHS,
                                    op,
                                    aggregator,
                                    myID);

    // Now fill in the if-then-else structure. The then-block will
    // contain the original Expr which has been modified via the primitive.
    // The else-block contains the original Expr.
    BlockStmt *thenBlock = new BlockStmt();
    BlockStmt *elseBlock = new BlockStmt();
    CondStmt *cond = new CondStmt(staticCond, thenBlock, elseBlock);
    entryPoint->insertAfter(cond);
    entryPoint->insertAfter(staticCheckDef);
    thenBlock->insertAtTail(entryPoint->remove());
    elseBlock->insertAtTail(exprCopy);
  } /* end of for(auto &candidate) */

} /* end of optimizeLoopIWA */

//##################################################################################
/*
    Creates a record for an aggregation candidate, where the record just have a
    type method to perform the specified operation op. The record is defined
    in the same module as the forall. We return the TypeSmbol for the record
    created.

    Essentially, this creates the following:

    record AggRec {
        inline proc type op(ref lhs, const rhs) {
            lhs <op> rhs
        }
    }

    where <op> is the operation denoted by op.

    Arguments:
    forall -> the forall of interest
    ID -> numeric ID for this aggregation candidate
    op -> the operation we are aggregating

    Return:
    TypeSymbol * -> the type of the created AggregateType
*/
static TypeSymbol *generateAggregationRecord(ForallStmt *forall,
                                             int ID,
                                              IrregWriteAggrOp op)
{
  AggregateType* aggRec = new AggregateType(AGGREGATE_RECORD);

  // Give the record a unique name by appending the ID
  auto recName = "__aggrRec_" + std::to_string(ID);
  TypeSymbol* aggOpType = new TypeSymbol(recName.c_str(), aggRec);

  // Create the type method with the proper arguments. It needs to
  // specify "this", "ref lhs" and "const rhs"
  FnSymbol* fn = new FnSymbol("op");
  fn->addFlag(FLAG_INLINE);
  fn->addFlag(FLAG_METHOD);
  fn->addFlag(FLAG_METHOD_PRIMARY);
  fn->addFlag(FLAG_VOID_NO_RETURN_VALUE);
  fn->insertFormalAtTail(new ArgSymbol(INTENT_BLANK, "_mt", dtMethodToken));
  fn->setMethod(true);
  Type* thisType = aggRec;
  ArgSymbol* _this = new ArgSymbol(INTENT_BLANK, "this", thisType);
  _this->addFlag(FLAG_TYPE_VARIABLE);
  _this->addFlag(FLAG_ARG_THIS);
  fn->insertFormalAtTail(_this);
  ArgSymbol *argLHS = new ArgSymbol(INTENT_REF, "lhs", dtAny);
  ArgSymbol *argRHS = new ArgSymbol(INTENT_CONST, "rhs", dtAny);
  fn->insertFormalAtTail(argLHS);
  fn->insertFormalAtTail(argRHS);

  // Create the body of the function: lhs op rhs
  CallExpr *opCall = NULL;
  switch (op) {
    case ASSIGNMENT:
      opCall = new CallExpr("=", argLHS, argRHS);
      break;
    case PLUSEQ:
      opCall = new CallExpr("+=", argLHS, argRHS);
      break;
    case ATOMIC_ADD: {
      Expr *callBase = buildDotExpr(argLHS, "add");
      opCall = new CallExpr(callBase, argRHS);
      break;
    }
    default:
      INT_ASSERT("unknown operation for irregular write aggregation");
  }
  INT_ASSERT(opCall != NULL);
  fn->insertAtTail(opCall);

  // Add the record to the forall's module
  FnSymbol *modInitFn = forall->getModule()->initFn;
  modInitFn->insertAtHead(new DefExpr(aggOpType));

  // Add the type method to the record
  DefExpr* fnDef = new DefExpr(fn);
  aggRec->symbol->defPoint->insertBefore(fnDef);
  aggRec->methods.add(fn);

  return aggOpType;
} /* end of generateAggregationRecord */

//##################################################################################
/*
    Creates the PRIM_MAYBE_IRREG_AGGREGATE_WRITE primitive and replaces LHS's parent
    with it. It will then be caught during prefolding for further analysis.

    What we pass onto prefolding are the LHS and RHS of the statement and the ID
    of the candidate. We also pass around the Aggregator object itself (well, 
    its Symbol). The actual replacement of the original operation/statement with 
    the call to the aggregator is done during prefolding. But we create the aggregator 
    during normalization since it is added as a task-private variable within the forall 
    (easier to do that during normalization).

    NOTE: Because the LHS and RHS already exists in the AST, when we add them to the
    primitive, we remove them from the AST at the same time.

    Arguments:
    LHS -> the LHS of the statement that is being aggregated (i.e., A[B[i]]).
    RHS -> the RHS of the statement that is being aggregated (an immediate, variable or call)
    op  -> the type of operation being aggregated (atomic add, +=, =, etc.).
    agg -> the Symbol corresponding to the task-private aggregator that we created.
    ID -> integer ID that uniquely identifies this candidate in the forall.

    Return:
    the aggregated statement that is now the PRIM_MAYBE_IRREG_AGGREGATE_WRITE primitive
*/
static CallExpr *createPrimitiveIWA(Expr *LHS,
                                    Expr *RHS,
                                    IrregWriteAggrOp op,
                                    ShadowVarSymbol *aggregator,
                                    int ID)
{
  // Save off LHS' parent, which is what we replace with the primitive.
  // Since we remove LHS below, we need to do this first.
  // NOTE: if the op is ATOMIC_ADD, then it's a bit different. We want to
  // get LHS->parentExpr->parentExpr, which is a CallExpr that seems to get
  // transformed into a MOVE after normalization and messes things up since
  // our bufferOp() call does not return anything.
  CallExpr *call = NULL;
  if (op != ATOMIC_ADD) {
    call = toCallExpr(LHS->parentExpr);
  }
  else {
    call = toCallExpr(LHS->parentExpr->parentExpr);
  }
  CallExpr *repl = new CallExpr(PRIM_MAYBE_IRREG_AGGREGATE_WRITE);
  repl->insertAtTail(LHS->remove());
  repl->insertAtTail(RHS->remove());
  repl->insertAtTail(new_IntSymbol(op));
  repl->insertAtTail(aggregator);
  repl->insertAtTail(new_IntSymbol(ID));
  call->replace(repl);
  return repl;
} /* end of createPrimitiveIWA */

///////////////////////////////////////////////////////////////////////////////
//                                                                           //
//                      Pre-folding Related Functions                        //
//                                                                           //
///////////////////////////////////////////////////////////////////////////////
/*
    The following functions perform further analysis/code-transformation for the
    irregular write aggregation optimization during pre-folding.

    The main task here is to catch the PRIM_MAYBE_IRREG_AGGREGATE_WRITE primitive
    and replace it with the actual aggregator call. We guarded the primitive with
    a param check, so if we find a primitive we know it is valid. Anything that
    would invalidate the optimization would result in the param check being false,
    and eliminating the primitive all together.
*/

//##################################################################################
/*
    This function is called from prefold.cpp when it processes a CallExpr that is
    the PRIM_MAYBE_IRREG_AGGREGATE_WRITE primitive.

    If the optimization is valid (if we're here, it is valid since we wouldn't have
    found the primitive if it was invalid), we replace the primitive with a call to agg.bufferOp()
    and return that.
*/
CallExpr *preFoldMaybeIrregWriteAggregation(CallExpr *call)
{
  CallExpr *repl = NULL;

  // Pull out what we need; we remove LHS and RHS since we may be
  // creating the bufferOp call with them. By removing them, our
  // indices change in the call->get() call.
  Expr *LHS = call->get(1)->remove();
  Expr *RHS = call->get(1)->remove();
  int64_t op, ID;
  get_int(toSymExpr(call->get(1)), &op);
  ShadowVarSymbol *agg = (ShadowVarSymbol *)(toSymExpr(call->get(2))->symbol());
  get_int(toSymExpr(call->get(3)), &ID);

  if (fReportIrregArrayAccesses && !gIrregWriteAggLoopProcessed[ID]) {
    printf("\n+ [IRREG WRITE AGGR] Pre-Folding Analyzing candidate #%ld\n", ID);
  }

  // Again, we're only here if we were valid, no need to check anything else.
  // Build the call agg.bufferOp(LHS, RHS)
  if (fReportIrregArrayAccesses && !gIrregWriteAggLoopProcessed[ID]) {
    printf("\t- inserting call to aggregator bufferOp() function\n");
  }
  Expr *callBase = buildDotExpr(agg, "bufferOp");
  repl = new CallExpr(callBase, LHS, RHS);

  if (fReportIrregArrayAccesses && !gIrregWriteAggLoopProcessed[ID]) {
    printf("### [IRREG WRITE AGGR] Pre-Folding Analysis Complete ###\n");
  }

  gIrregWriteAggLoopProcessed[ID] = true;

  return repl;
} /* end of preFoldMaybeIrregWriteAggregation */
