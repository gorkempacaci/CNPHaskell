{-# LANGUAGE OverloadedStrings #-}

module Tests.Solver where

import CNP
import Solver
import Tests.Shared

import Test.HUnit
import Test.HUnit.Base  ((~?=), Test(TestCase, TestList))
import Test.HUnit.Text (runTestTT)
import Test.HUnit.Tools (assertRaises)



data SolveBoolTest = SolveBoolTest String Bool NExecution

appendPredicate = PredicateDefinition "append" (["xs", "ys", "list"] `from`
  Or
     [And [IsNil "xs", Id "ys" "list"]
     ,And ["cons" // ["list" |> "xs", "head" |> "headx", "tail" |> "tailx"]
            ,"append" // ["ys", "xs" |> "tailx", "list" |> "inlist"]
            ,"cons" // ["list", "head" |> "headx", "tail" |> "inlist"]]])

appendProgram = Program [appendPredicate]


appendPredicateViaFoldr = PredicateDefinition "append"
       (["as"|>"xs", "b0"|>"ys", "folded"|>"list"] `from` 
        (FoldR ("cons" // ["head"|>"a", "tail"|>"b", "list"|>"folded"])
        (Id "b0" "folded"))
       )
appendProgramViaFoldr = Program [appendPredicateViaFoldr]

reversePredicateViaFoldl = PredicateDefinition "reverse"
       (["as", "folded"|>"bs"] `from` 
        And [
          IsNil "b0"
         ,(FoldL ("cons" // ["head"|>"a", "tail"|>"b", "list"|>"folded"])
                 (Id "b0" "folded"))]
       )
reverseProgramViaFoldl = Program [reversePredicateViaFoldl]


{-
  parentage :: {parent, child}
  isMale :: {name}
  isParent :: {parent} = parentage{parent}
  isFather :: {name} = and(parentage{parent->name}, isMale{name})
  isGrandchild :: {name} = and(parentage{parent, child}, parentage{parent->gparent, child->parent})
-}

parentageProgram = Program [
  "parentage" -:- extensionally 
                   ["parent",   "child"]
                  [["Leonard",  "Aldous"]
                  ,["Julia",    "Aldous"]
                  ,["Aldous",   "Matthew"]
                  ,["Maria",    "Matthew"]]
 ,"isMale" -:- extensionally
                ["name"]
               [["Leonard"]
               ,["Aldous"]
               ,["Matthew"]]
 ,"isParent" -:- (["parent"|>"name"] `from` "parentage")
 ,"isFather" -:- (["name"] `from`
    And ["parentage" // ["parent"|>"name"]
        ,"isMale"
     ])
 ,"isGrandchild" -:- (["name"] `from`
    (And ["parentage" 
        ,"parentage" // ["parent"|>"child", "child"|>"name"]
     ]))
 ]

ballColorProgram = Program [
  "color" -:- extensionally ["color"] [["blue"], ["green"], ["white"], ["red"]]
 ,"threeDifferentBalls" -:- (["ball1", "ball2", "ball3"] `from`
    (And ["color" // ["color"|>"ball1"]
         ,"color" // ["color"|>"ball2"]
         ,"color" // ["color"|>"ball3"]
         ,(Diff "ball1" "ball2")
         ,(Diff "ball2" "ball3")
         ,(Diff "ball3" "ball1")
         ]))
 ]

testSolveBool :: SolveBoolTest -> Test
testSolveBool (SolveBoolTest caseLabel expectedResult exec) =
  TestLabel caseLabel $ TestCase $ assertEqual ("solveBool failed for:"++caseLabel) expectedResult (solveBool exec)


solveBoolTestCases = [
  SolveBoolTest "append true 1" True (Execution appendProgram 
    (And ["append", ConsList "xs" [1], ConsList "ys" [2,3], ConsList "list" [1,2,3]]))
 ,SolveBoolTest "append true 2" True (Execution appendProgram 
    (And ["append", ConsList "xs" [], ConsList "ys" [1,2,3], ConsList "list" [1,2,3]]))
 ,SolveBoolTest "append true 3" True (Execution appendProgram 
    (And ["append", ConsList "xs" [1,2,3], ConsList "ys" [], ConsList "list" [1,2,3]]))
 ,SolveBoolTest "append true 4" True (Execution appendProgram 
    (And ["append", ConsList "xs" [], ConsList "ys" [], ConsList "list" []]))

 ,SolveBoolTest "append false 1" False (Execution appendProgram 
    (And ["append", ConsList "xs" [], ConsList "ys" [], ConsList "list" [1,2,3]]))
 ,SolveBoolTest "append false 2" False (Execution appendProgram 
    (And ["append", ConsList "xs" [1], ConsList "ys" [2], ConsList "list" [1,2,3]]))
 ,SolveBoolTest "append false 3" False (Execution appendProgram 
    (And ["append", ConsList "xs" [1,2], ConsList "ys" [], ConsList "list" [1,2,3]]))
 ,SolveBoolTest "append false 3" False (Execution appendProgram 
    (And ["append", ConsList "xs" [], ConsList "ys" [2,3], ConsList "list" [1,2,3]]))

 ,SolveBoolTest "appendFoldr true 1" True (Execution appendProgramViaFoldr
    (And ["append", ConsList "xs" [1], ConsList "ys" [2,3], ConsList "list" [1,2,3]]))
 ,SolveBoolTest "appendFoldr true 2" True (Execution appendProgramViaFoldr 
    (And ["append", ConsList "xs" [], ConsList "ys" [1,2,3], ConsList "list" [1,2,3]]))
 ,SolveBoolTest "appendFoldr true 3" True (Execution appendProgramViaFoldr 
    (And ["append", ConsList "xs" [1,2,3], ConsList "ys" [], ConsList "list" [1,2,3]]))
 ,SolveBoolTest "appendFoldr true 4" True (Execution appendProgramViaFoldr 
    (And ["append", ConsList "xs" [], ConsList "ys" [], ConsList "list" []]))

 ,SolveBoolTest "appendFoldr false 1" False (Execution appendProgramViaFoldr 
    (And ["append", ConsList "xs" [], ConsList "ys" [], ConsList "list" [1,2,3]]))
 ,SolveBoolTest "appendFoldr false 2" False (Execution appendProgramViaFoldr 
    (And ["append", ConsList "xs" [1], ConsList "ys" [2], ConsList "list" [1,2,3]]))
 ,SolveBoolTest "appendFoldr false 3" False (Execution appendProgramViaFoldr 
    (And ["append", ConsList "xs" [1,2], ConsList "ys" [], ConsList "list" [1,2,3]]))
 ,SolveBoolTest "appendFoldr false 3" False (Execution appendProgramViaFoldr 
    (And ["append", ConsList "xs" [], ConsList "ys" [2,3], ConsList "list" [1,2,3]]))

 ,SolveBoolTest "reverseFoldl true 1" True (Execution reverseProgramViaFoldl
    (And ["reverse", ConsList "as" [], ConsList "bs" []]))
 ,SolveBoolTest "reverseFoldl true 2" True (Execution reverseProgramViaFoldl
    (And ["reverse", ConsList "as" [1], ConsList "bs" [1]]))
 ,SolveBoolTest "reverseFoldl true 3" True (Execution reverseProgramViaFoldl
    (And ["reverse", ConsList "as" [1,2,3,4], ConsList "bs" [4,3,2,1]]))

 ,SolveBoolTest "reverseFoldl false 1" False (Execution reverseProgramViaFoldl
    (And ["reverse", ConsList "as" [1], ConsList "bs" []]))
 ,SolveBoolTest "reverseFoldl false 2" False (Execution reverseProgramViaFoldl
    (And ["reverse", ConsList "as" [], ConsList "bs" [1]]))
 ,SolveBoolTest "reverseFoldl false 3" False (Execution reverseProgramViaFoldl
    (And ["reverse", ConsList "as" [1,2], ConsList "bs" [1,2]]))
 ,SolveBoolTest "reverseFoldl false 4" False (Execution reverseProgramViaFoldl
    (And ["reverse", ConsList "as" [1,2], ConsList "bs" [1,2,3]]))


 ,SolveBoolTest "parentage true 1" True (Execution parentageProgram
    (And ["isGrandchild", Constant "name" "Matthew"]))
 ,SolveBoolTest "parentage true 2" True (Execution parentageProgram
    (And ["isFather", Constant "name" "Leonard"]))
 ,SolveBoolTest "parentage true 3" True (Execution parentageProgram
    (And ["isFather", Constant "name" "Aldous"]))
 ,SolveBoolTest "parentage true 3" True (Execution parentageProgram
    (And ["isParent", Constant "name" "Julia"]))

 ,SolveBoolTest "parentage false 1" False (Execution parentageProgram
    (And ["isGrandchild", Constant "name" "Aldous"]))
 ,SolveBoolTest "parentage false 2" False (Execution parentageProgram
    (And ["isGrandchild", Constant "name" "Leonard"]))
 ,SolveBoolTest "parentage false 3" False (Execution parentageProgram
    (And ["isFather", Constant "name" "Matthew"]))
 ,SolveBoolTest "parentage false 4" False (Execution parentageProgram
    (And ["isFather", Constant "name" "Julia"]))
 ,SolveBoolTest "parentage false 6" False (Execution parentageProgram
    (And ["isParent", Constant "name" "Matthew"]))

 ,SolveBoolTest "threeDifferentBalls true 1" True (Execution ballColorProgram
    (And ["threeDifferentBalls", Constant "ball1" "green", Constant "ball2" "red", Constant "ball3" "white"]))

 ,SolveBoolTest "threeDifferentBalls false 1" False (Execution ballColorProgram
    (And ["threeDifferentBalls", Constant "ball1" "green", Constant "ball2" "red", Constant "ball3" "green"]))

 ,SolveBoolTest "threeDifferentBalls false 2" False (Execution ballColorProgram
    (And ["threeDifferentBalls", Constant "ball1" "green", Constant "ball2" "brun", Constant "ball3" "green"]))
 ,SolveBoolTest "threeDifferentBalls false 3" False (Execution ballColorProgram
    (And ["threeDifferentBalls", Constant "ball1" "green", Constant "ball2" "green", Constant "ball3" "green"]))
 ,SolveBoolTest "threeDifferentBalls false 4" False (Execution ballColorProgram
    (And ["threeDifferentBalls", Constant "ball1" "red", Constant "ball2" "green", Constant "ball3" "green"]))


 ]

solveBoolTests = TestList $ map testSolveBool solveBoolTestCases

solverTests = TestList [solveBoolTests]

