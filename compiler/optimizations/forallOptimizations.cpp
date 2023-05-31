/*
 * Copyright 2020-2023 Hewlett Packard Enterprise Development LP
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

// Added by tbrolin
#include "ForLoop.h"
#include "WhileStmt.h"
#include "wellknown.h"
#include "resolveFunction.h"
#include "DeferStmt.h"
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

// Utilities for prefetching
static bool doesCallHaveNestedCallBaseIE(CallExpr *call);
static ForLoop *findEnclosingForLoop(Expr *expr);
static void gatherForLoopInfo(ForLoop *f);
static void getForLoopIndexVars(ForLoop *f);
static std::vector<Symbol *> getForLoopIndexSymbols(ForLoop *f,
                                                    Symbol *baseSym);
static void getForLoopDomainInfo(ForLoop *f,
                                 Expr *expr);
static bool doesExprContainExpr(Expr *expr,
                                Expr *matchExpr);
static bool isAssignment(CallExpr *call);
static ForallStmt *findEnclosingForallLoop(Expr *expr);
static Symbol *isFieldAccess(CallExpr *call,
                             AggregateType *at);
static void findAllModificationsToSymbol(Symbol *sym,
                                         Expr *expr,
                                         std::map<Symbol *, std::map<CallExpr *, bool>> &modifications,
                                         std::map<Symbol *, bool> &aliasesAnalyzed,
                                         std::map<Symbol *, std::set<Symbol *>> &aliasSymbols,
                                         bool isRecordField,
                                         AggregateType *at);
static FnSymbol *isSymbolRecordField(Symbol *sym,
                                     Symbol *&fieldSym,
                                     AggregateType *&at);
static bool isCallExprValid(CallExpr *call);
static Symbol *detectAliasesInCall(CallExpr *call,
                                   SymExpr *symexpr,
                                   bool checkCase4);


/////////////////////////////////////
//                                 //
//  Utility vectors/maps/#defines  //
//                                 //
/////////////////////////////////////
int gARPForallID = 0;
// gArrFieldsToDomFields is defined in compiler/include/passes.h as
// extern
std::map<AggregateType *, std::map<int, int>> gArrFieldsToDomFields;
std::map<int64_t, std::set<int64_t>> gPrefetchCallProcessed;
std::set<const char *> gCandidatesAnalyzedARP;






void doPreNormalizeArrayOptimizations() {
  const bool anyAnalysisNeeded = fAutoLocalAccess ||
                                 fAutoAggregation ||
                                 !fNoFastFollowers;
  if (anyAnalysisNeeded) {
    forv_expanding_Vec(ForallStmt, forall, gForallStmts) {
      // added by tbrolin
      if (fOptimizeIrregularArrayAccesses) {
        if (forall->getModule()->modTag == MOD_USER) {
          adaptiveRemotePrefetching(forall);
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
          callExpr->isPrimitive(PRIM_MAYBE_AGGREGATE_ASSIGN)) {
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

  // added by tbrolin
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

  gatherForallInfo(forall);

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

// Added by tbrolin
//
// Support for the adaptive remote prefetching (ARP) optimization

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
  /*if (forall->optInfo.cloneTypeIE == INSPECTOR) {
    return;
  }*/

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
          /*if (curr->isPrimitive(PRIM_MAYBE_IRREG_ACCESS) ||
              curr->isPrimitive(PRIM_MAYBE_IRREG_AGGREGATE_WRITE) ||
              curr->isPrimitive(PRIM_MAYBE_PREFETCH_CANDIDATE)) {*/
          if (curr->isPrimitive(PRIM_MAYBE_PREFETCH_CANDIDATE)) {
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
        /*if (tmp->isPrimitive(PRIM_MAYBE_IRREG_ACCESS) ||
            tmp->isPrimitive(PRIM_MAYBE_IRREG_AGGREGATE_WRITE) ||
            tmp->isPrimitive(PRIM_MAYBE_PREFETCH_CANDIDATE)) {*/
          if (tmp->isPrimitive(PRIM_MAYBE_PREFETCH_CANDIDATE)) {
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
    printf("+ [ADAPTIVE REMOTE PREFETCH] Considering candidate irregular access at %s (forall at %s)\n", parentCall->stringLoc(), forall->stringLoc());
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

    // TODO NEW: create an if-then statement that checks whether the prefetch
    // distance is NOT -1. If it is not -1, then we'll do all the prefetching
    // stuff. Otherwise, we'll just do the original access. We are setting the distance
    // to -1 when we encounter too many useless prefetches.
    Expr *distCheck = new CallExpr(">", candidate.prefetchDistance, new_IntSymbol(0));
    BlockStmt *thenBlock = new BlockStmt();
    CondStmt *cond = new CondStmt(distCheck, thenBlock);
    candidate.staticCond->thenStmt->insertAtHead(cond);
    candidate.distCond = cond;

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
    to 0 as well. Finally, we add a stopCount variable initialized to 0. This is used
    to keep track of how many consecutive adjust intervals we've seen where we had
    too many useless prefetches.

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
  UnresolvedSymExpr *stopTmp = new UnresolvedSymExpr(astr("stopCount_", ID));

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
  ShadowVarSymbol *stopCount = ShadowVarSymbol::buildForPrefix(SVP_VAR,
                                                               stopTmp,
                                                               NULL,
                                                               new CallExpr("initCounts"));


  // I think this is here when gathering the prefetch usage patterns?
  /*UnresolvedSymExpr *distArrTmp = new UnresolvedSymExpr(astr("distArray_", ID));
  ShadowVarSymbol *distArr = ShadowVarSymbol::buildForPrefix(SVP_REF,
                                                            distArrTmp,
                                                            NULL,
                                                            new CallExpr("getDistArray"));
  forall->shadowVariables().insertAtTail(distArr->defPoint);
  //forall->insertAfter(new CallExpr("printDistanceStats"));
  //forall->insertAfter(new CallExpr("resetTaskIDs"));
  candidate.distArr = distArr;
  */

  forall->shadowVariables().insertAtTail(prefetchDistance->defPoint);
  forall->shadowVariables().insertAtTail(count->defPoint);
  forall->shadowVariables().insertAtTail(window->defPoint);
  forall->shadowVariables().insertAtTail(stopCount->defPoint);
  candidate.prefetchDistance = prefetchDistance;
  candidate.iterCount = count;
  candidate.window = window;
  candidate.stopCount = stopCount;

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
                                      candidate.window,
                                      candidate.stopCount);
  elseBlock->insertAtHead(adjustDist);
  elseBlock->insertAtTail(new CallExpr("=", candidate.iterCount, new_IntSymbol(0)));

  // if-then-else goes at beginning of the distCond then-block
  candidate.distCond->thenStmt->insertAtHead(cond);

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
  //     of our distance != -1 check/condition. The prefetch call itself
  //     will be added in createPrefetchCallARP()
  Expr *outOfBoundsCond = new CallExpr("<=", prefetchIndex, candidate.lastValidIndex);
  BlockStmt *thenBlock = new BlockStmt();
  CondStmt *cond = new CondStmt(outOfBoundsCond, thenBlock, NULL);
  candidate.distCond->thenStmt->insertAtTail(cond);
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
        forall i in ... with (var prefetchDistance, var count, var window, var stopCount) {
            param staticPrefetchCheck = chpl__isPrefetchSupported(..);
            if staticPrefetchCheck == true {
                if prefetchDistance > 0 {
                    if count < numSampleIterations {
                        count += 1
                    }
                    else {
                        adjustPrefetchDistance(prefetchDistance, window, stopCount);
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
    //elseBlock->insertAtHead(new CallExpr("logDistance", candidate.prefetchDistance, candidate.distArr));
  }
  else {
    // Didn't have ARRAY_OR_DOMAIN, so only need to worry about prefetchCallDomainOrRange.
    // It goes into the then-block for the out-of-bounds check
    candidate.outOfBoundsCond->thenStmt->insertAtTail(prefetchCallDomainOrRange);
    //candidate.outOfBoundsCond->thenStmt->insertAtTail(new CallExpr("logDistance", candidate.prefetchDistance, candidate.distArr));
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
  /*if (call->theFnSymbol()) {
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
  }*/
  return true;
} /* end of isCallExprValid */

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
