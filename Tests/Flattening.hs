{-# LANGUAGE OverloadedStrings #-}

module Tests.Flattening where

import CNP
import Language
import Saturation
import Helpers
import Flattening


import Tests.Shared
import Test.HUnit
import Test.HUnit.Base  ((~?=), Test(TestCase, TestList))
import Test.HUnit.Text (runTestTT)
import Test.HUnit.Tools (assertRaises)
import Text.PrettyPrint.HughesPJClass





--- CNF Transformation tests

testIDCallCNF =
  let program = noGoalProgram [PredicateDefinition "p" $ ["a", "b"] `from` "id"]
  in TestCase $ assertEqual "Predicate call id CNF"
                  "p(A,B) v ~id(A,B)"
                  (toCNFStr program)

testTrueCallCNF =
  let program = noGoalProgram [PredicateDefinition "t" $ [] `from` "true"]
  in TestCase $ assertEqual "Predicate call true CNF"
                  "t v ~true"
                  (toCNFStr program)

testUserPredicateCallCNF =
  let program = noGoalProgram [PredicateDefinition "p" $ ["a", "b"] `from` "id"
                         ,PredicateDefinition "q" $ ["a", "b"] `from` "p"]
  in TestCase $ assertEqual "Predicate call to user defined predicate CNF"
                  (multilineStr ["p(A,B) v ~id(A,B)"
                               ,"q(A,B) v ~p(A,B)"])
                  (toCNFStr program)

testProjSelectCNF =
  let program = noGoalProgram [PredicateDefinition "p" $ ["a"] `from` "id" // ["a"]]
  in TestCase $ assertEqual "Predicate definition with only select-projection CNF"
                  "p(A) v ~id(A,_B)"
                  (toCNFStr program)

testProjRenameCNF =
  let program = noGoalProgram [PredicateDefinition "p" $ ["x"] `from` "id" // ["a"|>"x"]]
  in TestCase $ assertEqual "Predicate definition with only rename-projection CNF"
                  "p(X) v ~id(X,_B)"
                  (toCNFStr program)

testProjSelectAndRenameCNF =
  let program = noGoalProgram [PredicateDefinition "p" $ ["a", "y"] `from` "id" // ["a", "b"|>"y"]]
  in TestCase $ assertEqual "Predicate definition with only select-and-rename-projection CNF"
                  "p(A,Y) v ~id(A,Y)"
                  (toCNFStr program)

testProjOfProjOfProjCNF =
  let program = noGoalProgram [PredicateDefinition "p" $ ["c", "d"] `from`
                  "id" // ["a", "b"|>"d"] // ["a"|>"c", "d"]]
  in TestCase $ assertEqual "Three levels of projections CNF"
                  "p(C,D) v ~id(C,D)"
                  (toCNFStr program)

testORofANDofORCNF =
  let program = noGoalProgram comprehensiveProgram
  in TestCase $ assertEqual "OR of AND of OR of  and b in CNF" 
                  (multilineStr [
                    "p(A) v ~id(_A,A)"
                   ,"q(B) v ~id(B,'bee')"
                   ,"r(C) v ~id(C,[3,2,1])"
                   ,"s(D) v ~id(D,_B)"
                   ,"t(A,B,C,D) v ~t_e(A,B,C,D)"
                   ,"t_e(A,B,C,D) v ~p(A)"
                   ,"t_e(A,B,C,D) v ~q(B) v ~t_e_2_2(C,D)"
                   ,"t_e_2_2(C,D) v ~r(C)"
                   ,"t_e_2_2(C,D) v ~s(D)"
                   ])
                  (toCNFStr program)

testOrInGoal =
  let program = Program [PredicateDefinition "p" $ [] `from` "true"
                        ,PredicateDefinition "r" $ [] `from` "cons"]
      goal = Or ["p", "r"]
      exec = Execution program goal
      correctCNF = multilineStr [
        "p v ~true"
       ,"r v ~cons(_HEAD,_TAIL,_LIST)"
       ,"$goal v ~p"
       ,"$goal v ~r"
       ,"~$goal"
       ]
  in TestCase $ assertEqual "OR operator in goal does not produce correct CNF"
                 correctCNF
                 (toCNFStr exec)


-- TEST APPEND CNF
{-
append = {xs, ys, list} from
         or(and(nil {nil->xs}
               ,id {a->xs, b->list})
           ,and(cons {list->xs, head->headx, tail->tailx}
               ,append {ys, xs->tailx, list->inlist}
               ,cons {list, head->headx, tail->inlist}))
-}

testAppendCNF =
  let appendPredicate = PredicateDefinition "append" (["xs", "ys", "list"] `from`
         (Or [And ["isNil" // ["nil" |> "xs"]
                  ,"id" // ["a" |> "ys","b" |> "list"]]
             ,And ["cons" // ["list" |> "xs", "head" |> "headx", "tail" |> "tailx"]
                  ,"append" // ["ys", "xs" |> "tailx", "list" |> "inlist"]
                  ,"cons" // ["list", "head" |> "headx", "tail" |> "inlist"]]]))   
      appendGoal = And ["append", ConsList "xs" [1], ConsList "ys" [2,3], ConsList "list" [1,2,3]] 
      appendProgram = Program [appendPredicate]
      executionAppend = Execution appendProgram appendGoal
      programAppendCNF = multilineStr [
         "append(XS,YS,LIST) v ~append_e(XS,YS,LIST,_HEADX,_TAILX,_INLIST)"
         ,"append_e(XS,YS,LIST,_HEADX,_TAILX,_INLIST) v ~isNil(XS) v ~id(YS,LIST)"
         ,"append_e(XS,YS,LIST,_HEADX,_TAILX,_INLIST) v ~cons(_HEADX,_TAILX,XS) v ~append(_TAILX,YS,_INLIST) v ~cons(_HEADX,_INLIST,LIST)"
         ,"~append(XS,YS,LIST) v ~id(XS,[1]) v ~id(YS,[2,3]) v ~id(LIST,[1,2,3])"
        ]
  in TestCase $ assertEqual "When converted to CNF" programAppendCNF (toCNFStr executionAppend)


-- TEST NAME CAPTURING CNF
{-
Named:
testNameCapturing = {a} from or(id, and(id{a}, cons{list->a}){})
Saturated:
testNameCapturing(a) =
    or(a, _b)
        [id(a, _b),
         and(_2a)
             [id(_2a, _21b), cons(_22head, _22tail, _2a)]]
-}
testNameCapturingCNF = 
  let nameCapturing :: NPredicateDefinition
      nameCapturing = PredicateDefinition "nameCapturing" $ ["a"] `from`
                          Or ["id"
                             ,And ["id" // ["a"]
                                  ,"cons" // ["list" |> "a"]
                              ] // []
                          ]
      programNameCapturing = noGoalProgram [nameCapturing]
      programNameCapturingCNF = multilineStr [
        "nameCapturing(A) v ~nameCapturing_e(A,_B)"
       ,"nameCapturing_e(A,_B) v ~id(A,_B)"
       ,"nameCapturing_e(A,_B) v ~id(_2A,_21B) v ~cons(_22HEAD,_22TAIL,_2A)"
        ]
  in TestCase $ assertEqual "Name capturing is not observed in CNF" programNameCapturingCNF (toCNFStr programNameCapturing)

testANDLinkedArgumentsCNF =
  let program = noGoalProgram [PredicateDefinition "t" $ ["a"] `from`
                                 And ["true", And ["id", "id" // ["a"|>"b", "b"|>"a"]]]] 
      programCNF = "t(A) v ~true v ~id(A,_B) v ~id(_B,A)"
  in TestCase $ assertEqual "Lined or-goal produces correct CNF"
                  programCNF (toCNFStr program)

testORLinkedArgumentsCNF =
  let program = noGoalProgram [PredicateDefinition "t" $ ["a"] `from`
                                 And ["true", Or ["id", "id" // ["a"|>"b", "b"|>"a"]]]] 
      programCNF = multilineStr [
                     "t(A) v ~true v ~t_e_2(A,_B)"
                    ,"t_e_2(A,_B) v ~id(A,_B)"
                    ,"t_e_2(A,_B) v ~id(_B,A)"
                    ]
  in TestCase $ assertEqual "Lined or-goal produces correct CNF"
                  programCNF (toCNFStr program)

testFlatteningOfFoldR =
  let program = noGoalProgram [
        PredicateDefinition "t" $ (["as", "folded"] `from`
          And [
            (FoldR ("cons" // ["head"|>"a", "tail"|>"b", "list"|>"folded"])
                   (Or [Id "b0" "folded", ConsList "folded" ["FirstList"]]))
          ,IsNil "b0"])
        ]
      programCNF = multilineStr ["t(AS,FOLDED) v ~t_e_1(AS,_B0,FOLDED) v ~isNil(_B0)"
                                ,"t_e_1(AS,B0,F) v ~isNil(AS) v ~t_e_1_b(B0,F)"
                                ,"t_e_1(AS,B0,F) v ~cons(A,AS_T,AS) v ~t_e_1(AS_T,B0,F_I) v ~t_e_1_r(A,F_I,F)"
                                ,"t_e_1_b(_B0,FOLDED) v ~t_e_1_b_1(_B0,FOLDED)"
                                ,"t_e_1_r(_1A,_1B,FOLDED) v ~cons(_1A,_1B,FOLDED)"
                                ,"t_e_1_b_1(_B0,FOLDED) v ~id(_B0,FOLDED)"
                                ,"t_e_1_b_1(_B0,FOLDED) v ~id(FOLDED,['FirstList'])"]
  in TestCase $ assertEqual "Flattening of FoldR produces correct CNF"
                  programCNF (toCNFStr program)

cnfTests  = TestList [TestLabel "IDCallCNF" testIDCallCNF
                     ,TestLabel "TrueCallCNF" testTrueCallCNF
                     ,TestLabel "UserPredicateCallCNF" testUserPredicateCallCNF
                     ,TestLabel "ProjectionOnlySelect" testProjSelectCNF
                     ,TestLabel "ProjectionOnlyRename" testProjRenameCNF
                     ,TestLabel "ProjectionSelectAndRename" testProjSelectAndRenameCNF
                     ,TestLabel "Proj of Proj of Proj in CNF" testProjOfProjOfProjCNF
                     ,TestLabel "Or of And of Or in CNF" testORofANDofORCNF
                     ,TestLabel "Or in goal" testOrInGoal
                     ,TestLabel "AppendCNF" testAppendCNF
                     ,TestLabel "NameCapturingCNF" testNameCapturingCNF
                     ,TestLabel "LinkedANDArgsCNF" testANDLinkedArgumentsCNF
                     ,TestLabel "LinkedORArgsCNF" testORLinkedArgumentsCNF
                     ,TestLabel "FoldRDeepBaseCNF" testFlatteningOfFoldR]
