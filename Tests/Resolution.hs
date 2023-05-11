{-# LANGUAGE OverloadedStrings #-}

module Tests.Resolution where

import Flattening
import Unification
import Solver
import Tests.Shared

import Test.HUnit
import Test.HUnit.Base  ((~?=), Test(TestCase, TestList))
import Test.HUnit.Text (runTestTT)
import Test.HUnit.Tools (assertRaises)

data ResolutionRuleTestCase = ResolutionRuleTestCase String CFDisjunction CFDisjunction ResolutionResult

resolutionRuleTestCases = [
  ResolutionRuleTestCase "predicate symbols neg+pos resolve away"
    (Disjunction [Pos (Atom "q" []), Neg (Atom "p" [])])
    (Disjunction [Pos (Atom "p" [])])
    (ResolvesToClause (Disjunction [Pos (Atom "q" [])]))
 ,ResolutionRuleTestCase "predicate symbols neg+neg do NOT resolve away"
    (Disjunction [Pos (Atom "q" []), Neg (Atom "p" [])])
    (Disjunction [Neg (Atom "p" [])])
    DoesNotResolve
 ,ResolutionRuleTestCase "resolves with substitution - 1"
    (Disjunction [Pos (Atom "q" [VarTerm "x"]), Neg (Atom "p" [VarTerm "x"])])
    (Disjunction [Pos (Atom "p" [ConstantTerm 5])])
    (ResolvesToClause (Disjunction [(Pos (Atom "q" [ConstantTerm 5]))]))
 ,ResolutionRuleTestCase "neg+pos resolves to empty clause"
    (Disjunction [Pos (Atom "a" [VarTerm "x"])])
    (Disjunction [Neg (Atom "a" [VarTerm "y"])])
    (ResolvesToFalse)
 ,ResolutionRuleTestCase "resolves without substitution"
    (Disjunction [Pos (Atom "a" [])])
    (Disjunction [Neg (Atom "a" [])])
    (ResolvesToFalse)
 ]

testResolutionRule :: ResolutionRuleTestCase -> Test
testResolutionRule (ResolutionRuleTestCase caseMessage firstClause secondClause expectedResult) =
  TestLabel caseMessage $ TestCase $ assertEqual caseMessage expectedResult (resolveClauses firstClause secondClause)

testVarsInDisjunction :: Test
testVarsInDisjunction =
    TestLabel "correct variables are found in a disjunction" $ TestCase $ 
      assertEqual "incorrect variables are found in a disjunction"
        ["X", "Y", "Z"]
        (varNamesInLits
          ([
            Pos (Atom "a" [
                  VarTerm "x"
                 ,ConsTerm (Cons (ConstantTerm 5) (Cons (VarTerm "y") (Cons (VarTerm "x") (Cons (VarTerm "z") (ConsNil)))))
                 ]
                )
           ])
        )

testRenamingCommonVars :: Test
testRenamingCommonVars =
    TestLabel "common variables in two clauses are eliminated" $ TestCase $
      assertEqual "variable renaming incorrect"
        ([Neg (Atom "a" [VarTerm "aa", VarTerm "y", VarTerm "ab"])])
        (renameDuplicateVariables
            ([Neg (Atom "a" [VarTerm "x", VarTerm "y", VarTerm "z"])])
            ([Pos (Atom "a" [VarTerm "X", VarTerm "K", VarTerm "Z"])])
        )

resolutionRuleTests = TestList $ map testResolutionRule resolutionRuleTestCases

data GroundResolutionTestCase = GroundResolutionTestCase String CFDisjunction CFDisjunction


testCasesResolveWithGroundPredicates = 
  let consList123 = Cons (ConstantTerm 1) $ Cons (ConstantTerm 2) $ Cons (ConstantTerm 3) ConsNil
      consList23 = Cons (ConstantTerm 2) $ Cons (ConstantTerm 3) ConsNil
  in [
      GroundResolutionTestCase "id-negative unifies away"
        (Disjunction [Neg $ Atom "id" [ConstantTerm 5, ConstantTerm 5]])
        (Disjunction [])
     ,GroundResolutionTestCase "true-negative unifies away"
        (Disjunction [Neg $ Atom "true" []])
        (Disjunction [])
     ,GroundResolutionTestCase "id-positive does not unify"
        (Disjunction [Pos $ Atom "id" [ConstantTerm 5, ConstantTerm 5]])
        (Disjunction [Pos $ Atom "id" [ConstantTerm 5, ConstantTerm 5]])
     ,GroundResolutionTestCase "id-with vars unifies with substitutions"
        (Disjunction [Neg (Atom "id" [VarTerm "x", ConstantTerm 5]), Neg (Atom "a" [VarTerm "x"])])
        (Disjunction [Neg (Atom "a" [ConstantTerm 5])])

     ,GroundResolutionTestCase "diff of A, A unifies as false"
        (Disjunction [Neg (Atom "diff" [VarTerm "A", VarTerm "A"])])
        (Disjunction [Pos (Atom "true" [])])
     ,GroundResolutionTestCase "diff of A, B does not unify"
        (Disjunction [Neg (Atom "diff" [VarTerm "A", VarTerm "B"])])
        (Disjunction [Neg (Atom "diff" [VarTerm "A", VarTerm "B"])])
     ,GroundResolutionTestCase "diff of different constants unifies as true"
        (Disjunction [Neg (Atom "diff" [ConstantTerm 4, ConstantTerm 0])])
        (Disjunction [])
     ,GroundResolutionTestCase "diff of equal constants unifies as false"
        (Disjunction [Neg (Atom "diff" [ConstantTerm 0, ConstantTerm 0])])
        (Disjunction [Pos (Atom "true" [])])
     ,GroundResolutionTestCase "diff of var vs constant does not unify-1"
        (Disjunction [Neg (Atom "diff" [VarTerm "a", ConstantTerm 0])])
        (Disjunction [Neg (Atom "diff" [VarTerm "a", ConstantTerm 0])])
     ,GroundResolutionTestCase "diff of var vs constant does not unify-2"
        (Disjunction [Neg (Atom "diff" [ConstantTerm 0, VarTerm "a"])])
        (Disjunction [Neg (Atom "diff" [ConstantTerm 0, VarTerm "a"])])
     ,GroundResolutionTestCase "diff of single term does not unify."
        (Disjunction [Neg (Atom "diff" [ConstantTerm 0])])
        (Disjunction [Neg (Atom "diff" [ConstantTerm 0])])

     ,GroundResolutionTestCase "~isNil([]) unifies as false"
        (Disjunction [Neg (Atom "isNil" [ConsTerm ConsNil])])
        (Disjunction [])
     ,GroundResolutionTestCase "~isNil([1]) unifies as true"
        (Disjunction [Neg (Atom "isNil" [ConsTerm (Cons (ConstantTerm 1) ConsNil)])])
        (Disjunction [Pos (Atom "true" [])])

     ,GroundResolutionTestCase "id-cons-a unifies with substitutions"
        (Disjunction [Neg (Atom "id" [VarTerm "z", ConsTerm consList123])
         ,Neg (Atom "cons" [VarTerm "x", VarTerm "y", VarTerm "z"])
         ,Neg (Atom "a" [VarTerm "y"])])
        (Disjunction [Neg (Atom "a" [ConsTerm consList23])])
     ,GroundResolutionTestCase "a-cons-id unifies with substitutions"
        (Disjunction [Neg (Atom "a" [VarTerm "y"])
         ,Neg (Atom "cons" [VarTerm "x", VarTerm "y", VarTerm "z"])
         ,Neg (Atom "id" [VarTerm "z", ConsTerm consList123])])
        (Disjunction [Neg (Atom "a" [ConsTerm consList23])])
     ,GroundResolutionTestCase "cons with head mismatch unifies to false"
        (Disjunction [Neg (Atom "cons" [ConstantTerm 2, VarTerm "x", ConsTerm consList123])])
        (Disjunction [Pos (Atom "true" [])])
     ,GroundResolutionTestCase "Variable inside cons"
        (Disjunction [Neg $ Atom "id" [VarTerm "x", ConstantTerm 3]
        ,Neg $ Atom "cons" [VarTerm "h", VarTerm "t", ConsTerm (Cons (ConstantTerm 1) (Cons (ConstantTerm 2) (Cons (VarTerm "x") ConsNil)))]
        ,Pos $ Atom "r" [VarTerm "h", VarTerm "t"]])
        (Disjunction [Pos $ Atom "r" [ConstantTerm 1, ConsTerm consList23]])
     ]

testResolveWithGroundPredicates :: GroundResolutionTestCase -> Test
testResolveWithGroundPredicates (GroundResolutionTestCase caseMessage givenDisjunction expectedAfterRes) =
  TestLabel caseMessage $ TestCase $ assertEqual caseMessage expectedAfterRes (groundClauseExhaustively givenDisjunction)

groundResolutionTests = TestList $ map testResolveWithGroundPredicates testCasesResolveWithGroundPredicates


resolutionTests = TestList [resolutionRuleTests
                           ,testVarsInDisjunction
                           ,testRenamingCommonVars
                           ,groundResolutionTests]


