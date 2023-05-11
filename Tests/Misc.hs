{-# LANGUAGE OverloadedStrings #-}

module Tests.Misc where

import CNP
import Language
import Saturation
import Helpers
import Flattening

import Tests.Flattening
import Tests.Unification
import Tests.Shared
import Tests.Resolution
import Tests.Solver

import Helpers

import Control.Exception (ErrorCall(ErrorCall), evaluate)
import Test.HUnit
import Test.HUnit.Base  ((~?=), Test(TestCase, TestList))
import Test.HUnit.Text (runTestTT)
import Test.HUnit.Tools (assertRaises)
import Text.PrettyPrint.HughesPJClass


-- HELPER TESTS

helpersTests = TestList [
                 TestCase $ assertEqual "Sets are equal"
                   True
                   (setEquals ["a", "b", "c"] ["b", "c", "a"])
                ,TestCase $ assertEqual "Sets are equal (empty)"
                   True
                   (setEquals ([]::[Int]) ([]::[Int]))
                ,TestCase $ assertEqual "Sets are not equal-1"
                   False
                   (setEquals ["a", "b", "c"] ["b", "a"])
                ,TestCase $ assertEqual "Sets are not equal-2"
                   False
                   (setEquals ["a", "b"] ["b", "a", "c"])
                ,TestCase $ assertEqual "Sets are not equal-3"
                   False
                   (setEquals [] ["b", "a", "c"])
                ,TestCase $ assertEqual "Sets are not equal-3"
                   False
                   (setEquals ["a", "b"] [])
               ]





-- SATURATION TESTS

testProgramSaturation = TestCase $ assertEqual "Saturated program incorrect."
    (multilineStr [
      "p(a) := id(_a,a)"
     ,"q(b) := 'bee'::{b}"
     ,"r(c) := [3, 2, 1]::{c}"
     ,"s(d) := id(d,_b)"
     ,"t(a,b,c,d) := or(a,b,c,d)[p(a),and(b,c,d)[q(b),or(c,d)[r(c),s(d)]]]"
     ,"and()[]"
    ])
    (prettyShow (saturate (noGoalProgram comprehensiveProgram)))


saturationTests = TestList [testProgramSaturation]

---- VALIDATION TESTS

testErrNonexistingPredicateCallVAL =
  let program = noGoalProgram [PredicateDefinition "q" $ ["x"] `from` "p"]
  in assertError "Predicate call to nonexisting predicate raises error."
       "Predicate does not exist or ambiguous:p"
       (toCNFStr program)

testErrDuplicatePredicateVAL =
  let program = noGoalProgram [PredicateDefinition "p" $ ["a", "b"] `from` "id"
                              ,PredicateDefinition "p" $ ["a", "b"] `from` "id"]
  in assertError "More than one definitions for a predicate symbol not allowed."
       "Predicate is defined multiple times:p"
       (toCNFStr program)

testErrPredDoesNotBeginWithProjVAL =
  let program = noGoalProgram [PredicateDefinition "p" $ "id"]
  in assertError "Predicate definitions should start with a projection."
       "Predicate definition does not start with a projection:p"
       (toCNFStr program)

testErrProjNonexistingArg = 
  let errProgProjNonexistingArg = noGoalProgram [PredicateDefinition "err1" $ ["x", "y"] `from`
                                  Constant "y" "y"]
  in assertError "Nonexisting argument raises an error"
    "Projected argument does not exist:[\"x\"] not in [\"y\"]"
    (toCNFStr errProgProjNonexistingArg)

-- more than one source argument is mapped to one target name (implicit conjunction)
testErrProjNoninjective =
  let errProgProjNoninjective = noGoalProgram [PredicateDefinition "err2" $ ["x"] `from`
                                "id" // ["a"|>"x", "b"|>"x"]]
  in assertError "Noninjective projection raises an error."
    "Projection maps many arguments to one:[a|>x, b|>x]"
    (toCNFStr errProgProjNoninjective)

-- one source argument is mapped to more than one target name (implicit identity)
testErrProjOneToMany =
  let errProgProjOneToMany = noGoalProgram [PredicateDefinition "err3" $ ["x"] `from`
                             Constant "a" "a" // ["a"|>"x", "a"|>"y"]]
  in assertError "Projection from one argument to many raises an error"
    "Projection maps one argument to many:[a|>x, a|>y]"
    (toCNFStr errProgProjOneToMany)

validationTests = TestList [TestLabel "ErrNonexistingPredicateCall" testErrNonexistingPredicateCallVAL
                           ,TestLabel "ErrDuplicatePredicate" testErrDuplicatePredicateVAL
                           ,TestLabel "ErrPredDoesNotBeginWithProj" testErrPredDoesNotBeginWithProjVAL
                           ,TestLabel "testErrProjNonexistingArg" testErrProjNonexistingArg
                           ,TestLabel "testErrProjNoninjective" testErrProjNoninjective
                           ,TestLabel "testErrProjOneToMany" testErrProjOneToMany
                            ]


