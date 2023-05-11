{-# LANGUAGE OverloadedStrings #-}

module Tests.Shared where

import Control.Exception (ErrorCall(ErrorCall), evaluate)
import Test.HUnit
import Test.HUnit.Base  ((~?=), Test(TestCase, TestList))
import Test.HUnit.Text (runTestTT)
import Test.HUnit.Tools (assertRaises)
import Language

-- from http://stackoverflow.com/questions/13350164/how-do-i-test-for-an-error-in-haskell
assertError msg ex f = 
  TestCase $ assertRaises msg (ErrorCall ex) $ evaluate f


-- prepares an execution for a program with no goal. (validation)
noGoalProgram :: [NPredicateDefinition] -> NExecution
noGoalProgram predicates = Execution (Program predicates) (And [])


comprehensiveProgram = [PredicateDefinition "p" $ ["a"] `from` "id" // ["b"|>"a"]
                       ,PredicateDefinition "q" $ ["b"] `from` Constant "b" "bee"
                       ,PredicateDefinition "r" $ ["c"] `from` ConsList "c" [3,2,1]
                       ,PredicateDefinition "s" $ ["d"] `from` "id" // ["a"|>"d"]
                       ,PredicateDefinition "t" $ ["a", "b", "c", "d"] `from`
                           (Or ["p", And ["q", Or ["r", "s"]]])]