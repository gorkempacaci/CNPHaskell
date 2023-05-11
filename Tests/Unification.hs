module Tests.Unification where

import Flattening
import Unification
import Tests.Shared

import Test.HUnit
import Test.HUnit.Base  ((~?=), Test(TestCase, TestList))
import Test.HUnit.Text (runTestTT)
import Test.HUnit.Tools (assertRaises)

data UnifyAtomTestCase = UnifyAtomTestCase String CFAtom CFAtom UnificationResult

testValuesUnifyAtom = [
  UnifyAtomTestCase "Same predicate symbols should unify."
                    (Atom "a" [])
                    (Atom "a" [])
                    (UnifyWith [])
 ,UnifyAtomTestCase "Different predicate symbols should not unify."
                    (Atom "a" [])
                    (Atom "b" [])
                    DoNotUnify
 ,UnifyAtomTestCase "Empty term list should not unify with non-empty ones."
                    (Atom "a" [])
                    (Atom "a" [ConstantTerm 1])
                    DoNotUnify
 ,UnifyAtomTestCase "First item UnifyAsFalse then the rest doesnt"
                    (Atom "a" [ConstantTerm 1, ConstantTerm 5])
                    (Atom "a" [ConstantTerm 1, ConstantTerm 0])
                    DoNotUnify
 ,UnifyAtomTestCase "First item UnifyAsFalse then the rest UnifyWith"
                    (Atom "a" [ConstantTerm 1, VarTerm "x"])
                    (Atom "a" [ConstantTerm 1, ConstantTerm 0])
                    (UnifyWith [Substitution "x" (ConstantTerm 0)])
 ,UnifyAtomTestCase "First item DoNotUnify then the rest UnifyAsFalse"
                    (Atom "a" [ConstantTerm 0, ConstantTerm 5])
                    (Atom "a" [ConstantTerm 1, ConstantTerm 5])
                    DoNotUnify
 ,UnifyAtomTestCase "Non-empty term list should not unify with empty ones."
                    (Atom "a" [ConstantTerm 1])
                    (Atom "a" [])
                    DoNotUnify
 ,UnifyAtomTestCase "Variable substitution"
                    (Atom "a" [VarTerm "x"])
                    (Atom "a" [VarTerm "z"])
                    (UnifyWith [Substitution "x" (VarTerm "z")])
 ,UnifyAtomTestCase "Variable transitive substitution-1"
                    (Atom "a" [VarTerm "ax", VarTerm "ay"])
                    (Atom "a" [VarTerm "bz", VarTerm "bz"])
                    (UnifyWith [Substitution "ax" (VarTerm "bz")
                                 ,Substitution "ay" (VarTerm "bz")])
 ,UnifyAtomTestCase "Variable transitive substitution-2"
                    (Atom "a" [VarTerm "x", VarTerm "x"])
                    (Atom "a" [ConstantTerm 5, VarTerm "y"])
                    (UnifyWith [Substitution "x" (ConstantTerm 5)
                                 ,Substitution "y" (ConstantTerm 5)])
 ,UnifyAtomTestCase "Variable transitive substitution-3"
                    (Atom "a" [VarTerm "z"   , VarTerm "z", VarTerm "y"])
                    (Atom "a" [ConstantTerm 5, VarTerm "x", VarTerm "x"])
                    (UnifyWith [Substitution "z" (ConstantTerm 5)
                                 ,Substitution "x" (ConstantTerm 5)
                                 ,Substitution "y" (ConstantTerm 5)])
 ]


testAtomsUnify :: UnifyAtomTestCase -> Test
testAtomsUnify (UnifyAtomTestCase caseMessage firstAtom secondAtom expectedResult) =
  TestLabel caseMessage $ TestCase $ assertEqual caseMessage expectedResult (unifyContradictoryAtoms firstAtom secondAtom)



data UnifyGroundAtomTestCase = UnifyGroundAtomTestCase String CFAtom UnificationResult

testValuesUnifyGroundAtom = [
  UnifyGroundAtomTestCase "id-1 constants equal"
                 (Atom "id" [ConstantTerm 5, ConstantTerm 5])
                 (UnifyWith [])
 ,UnifyGroundAtomTestCase "id-2 constants nonequal"
                 (Atom "id" [ConstantTerm 5, ConstantTerm 0])
                 (UnifyAsTrue) 
 ,UnifyGroundAtomTestCase "id-3 constant subs for var"
                 (Atom "id" [ConstantTerm 5, VarTerm "x"])
                 (UnifyWith [Substitution "x" (ConstantTerm 5)])
 ,UnifyGroundAtomTestCase "id-4 constant subs for var"
                 (Atom "id" [VarTerm "x", ConstantTerm 5])
                 (UnifyWith [Substitution "x" (ConstantTerm 5)])
 ,UnifyGroundAtomTestCase "id-5 var subs for var"
                 (Atom "id" [VarTerm "x", VarTerm "y"])
                 (UnifyWith [Substitution "x" (VarTerm "y")])   
 ,UnifyGroundAtomTestCase "id-6 invalid terms"
                 (Atom "id" [])
                 (DoNotUnify)               
 ,UnifyGroundAtomTestCase "id-7 invalid terms"
                 (Atom "id" [VarTerm "x", VarTerm "y", VarTerm "z"])
                 (DoNotUnify)               
 ,UnifyGroundAtomTestCase "cons-constants true"
                 (Atom "cons" [ConstantTerm 1, ConsTerm (cfConsesFromList [2,3]), ConsTerm (cfConsesFromList [1,2,3])])
                 (UnifyAsFalse)
 ,UnifyGroundAtomTestCase "cons-constants false"
                 (Atom "cons" [ConstantTerm 1, ConsTerm (cfConsesFromList [2,3]), ConsTerm (cfConsesFromList [1,2,3,4])])
                 (UnifyAsTrue)
 ,UnifyGroundAtomTestCase "cons-unpack head"
                 (Atom "cons" [VarTerm "x", ConsTerm (cfConsesFromList [2,3]), ConsTerm (cfConsesFromList [1,2,3])])
                 (UnifyWith [Substitution "x" (ConstantTerm 1)])
 ,UnifyGroundAtomTestCase "cons-unpack tail"
                 (Atom "cons" [ConstantTerm 1, VarTerm "x", ConsTerm (cfConsesFromList [1,2,3])])
                 (UnifyWith [Substitution "x" (ConsTerm (cfConsesFromList [2,3]))])
 ,UnifyGroundAtomTestCase "cons-pack list"
                 (Atom "cons" [ConstantTerm 1, ConsTerm (cfConsesFromList [2,3]), VarTerm "x"])
                 (UnifyWith [Substitution "x" (ConsTerm (cfConsesFromList [1,2,3]))])   
 ,UnifyGroundAtomTestCase "true-1"
                 (Atom "true" [])
                 (UnifyAsFalse)
 ,UnifyGroundAtomTestCase "true-2"
                 (Atom "true" [ConstantTerm 1])
                 (DoNotUnify)              
 ]


testGroundAtomsUnify :: UnifyGroundAtomTestCase -> Test
testGroundAtomsUnify (UnifyGroundAtomTestCase caseMessage atom expectedResult) =
  TestLabel caseMessage $ TestCase $ assertEqual caseMessage expectedResult (unifyLiteralWithGround $ Neg atom)





testUnificationErrIfVarOccursInBoth =
  TestLabel "Common variable among atoms should raise error" $
    assertError "occurs check does not raise error"
      "Common vars exist in two sets of terms:[5, X]u[X, 5]"
      (unifyContradictoryAtoms (Atom "a" [ConstantTerm 5, VarTerm "x"])
                  (Atom "a" [VarTerm "x", ConstantTerm 5]))

atomUnificationTests = TestList $ map testAtomsUnify testValuesUnifyAtom

atomUnificationTestsErr = TestList [testUnificationErrIfVarOccursInBoth]

groundAtomUnificationTests = TestList $ map testGroundAtomsUnify testValuesUnifyGroundAtom



unificationTests = TestList [atomUnificationTests
                            ,atomUnificationTestsErr
                            ,groundAtomUnificationTests]

