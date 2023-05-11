{-# LANGUAGE OverloadedStrings #-}

{-|
Module: Solver
Description: Main execution module for CNP programs. Provides the solveBool method which takes
  an NExecution, and returns true if the given goal follows from the program given in the execution directive.
  Together with the Unification module, it provides an implementation of a Resolution Search.
-}
module Solver (solveBool
              ,varNamesInLits -- for tests
              ,resolveClauses -- for tests
              ,renameDuplicateVariables -- for tests
              ,groundClauseExhaustively -- for tests
              ,ResolutionResult(..) -- for tests
              ) where

import Unification
import Flattening
import Saturation
import Language
import Data.List (find, (\\), nub, intersect, sort, any)
import Text.PrettyPrint.HughesPJClass


-- to turn on console debugging
-- import Debug.Trace
-- to turn off console debugging
-- trace _ a = a

{-| Represents the result of a resolution attempt. -}
data ResolutionResult = ResolvesToFalse
                      | ResolvesToTrue
                      | ResolvesToClause {resolvent::CFDisjunction}
                      | DoesNotResolve
  deriving (Eq, Show)

-- | Returns true if the given goal (in execution) follows from the given program.
solveBool :: NExecution -> Bool
solveBool nExec =
  let cfProg = flatten $ saturate nExec
      kb = sort $ map groundClauseExhaustively (disjunctions $ cfKnowledgeBase cfProg)
      uGoal = groundClauseExhaustively $ cfUserGoal cfProg
  in not $ goalFollowsFromKB kb uGoal
--            (trace ("KB:\n" ++ (prettyShow kb) ++ "\n") kb)
--            (trace ("GOAL:" ++ (prettyShow uGoal) ++ "\n") uGoal) 

isTrueClause :: CFDisjunction -> Bool
isTrueClause disj = any ((==) literalTrue) (literals disj)

goalFollowsFromKB :: [CFDisjunction] -> CFDisjunction -> Bool
goalFollowsFromKB kb gl =
  let allResolutionAttempts = [(resolveClauses gl b) | b<-kb]
      falseResolventsNr = length $ filter (\u -> u == ResolvesToFalse) allResolutionAttempts
      newResolventsUnGr = [c | ResolvesToClause c <- allResolutionAttempts]
      newResolventsGr = map groundClauseExhaustively newResolventsUnGr
  in if isTrueClause gl then True
     else if gl == Disjunction [] then True
     else if not (falseResolventsNr == 0) then False
     else let forks = map (goalFollowsFromKB (gl:kb)) newResolventsGr
          in not $ any ((==) False) forks

instance Pretty ResolutionResult where
  pPrint (ResolvesToClause c) = text ("ResolvesTo ") <> pPrint c
  pPrint o = text (show o)

-- | attempts to resolve two clauses using the resolution rule. unifies on the first
--   found unifying literal only. 
resolveClauses :: CFDisjunction -> CFDisjunction -> ResolutionResult
resolveClauses (Disjunction []) _ = error "empty disjunction as #1 of resolveClauses"
resolveClauses _ (Disjunction []) = error "empty disjunction as #2 of resolveClauses"
resolveClauses (Disjunction leftLitsUnsafe) (Disjunction rightLits) =
  let leftLits = renameDuplicateVariables leftLitsUnsafe rightLits
      allUniAttempts = [(l1, l2, unifyLiterals l1 l2) | l1 <- leftLits, l2 <- rightLits]
      firstUnifying = find (\(_,_,u) -> not (u == DoNotUnify)) allUniAttempts
  in case firstUnifying of
    Nothing -> DoesNotResolve
    Just (l1, l2, uResult) ->
      let litsExceptResolved = (leftLits \\ [l1]) ++ (rightLits \\ [l2])
      in if null litsExceptResolved then ResolvesToFalse else
          case uResult of 
            UnifyWith subs -> ResolvesToClause $ Disjunction $ applySubstitutionsToLiterals subs litsExceptResolved


-- | Applies a repetitive search until none of the literals
--   of a disjunction unifies with ground atoms.
groundClauseExhaustively :: CFDisjunction -> CFDisjunction
groundClauseExhaustively disj =
  Disjunction $ groundLiteralsExhaustively $ literals disj

-- | Repeats unifying if at least one literal unifies with
--   a ground predicate. When no literal unifies, returns the 
--   remaining list of literals, modulo substitutions.
groundLiteralsExhaustively :: [CFLiteral] -> [CFLiteral]
groundLiteralsExhaustively [] = []
groundLiteralsExhaustively literals =
  let firstUnification = unifyOneLiteralWithGround literals
  in case firstUnification of 
    (DoNotUnify, _) -> literals -- none of the literals could be ground.
    (UnifyWith subs, litsRemaining) ->
      let newLits = applySubstitutionsToLiterals subs litsRemaining
      in groundLiteralsExhaustively newLits
    (UnifyAsFalse, litsNew) -> groundLiteralsExhaustively litsNew
    (UnifyAsTrue, _) -> [literalTrue]            

-- | renames conflicting variables in leftLits to [AA..ZZ] so none occur in rightLits. 
renameDuplicateVariables :: [CFLiteral] -> [CFLiteral] -> [CFLiteral]
renameDuplicateVariables leftLits rightLits =
  let candidateVarNames2 = [[x,y]|x<-['A'..'Z'], y<-['A'..'Z']]
      varsInLeft = varNamesInLits leftLits
      varsInRight = varNamesInLits rightLits
      varsCommon = intersect varsInLeft varsInRight
      varsFresh = candidateVarNames2 \\ (varsInLeft ++ varsInRight)
      substitutions = [Substitution a (VarTerm b) | (a,b) <- zip varsCommon varsFresh]
      newLiteralsLeft = applySubstitutionsToLiterals substitutions leftLits
  in if (length substitutions < length varsCommon)
     then error "While renaming duplicate variables, ran out of variable names in range 'AA'..'ZZ'."
     else newLiteralsLeft

-- | returns the complete unique list of variable names in a list of literals.
varNamesInLits :: [CFLiteral] -> [String]
varNamesInLits lits =
  let allAtoms = map atom lits
      allTerms = concat $ map atomTerms allAtoms
  in nub $ concat $ map varNamesInTerm allTerms

-- | returns the variable names in a term.
varNamesInTerm :: CFTerm -> [String]
varNamesInTerm term =
  case term of 
    (ConstantTerm _) -> []
    (VarTerm v) -> [show term]
    (ConsTerm c) -> varNamesInCons c

-- | returns the variable names in a cons list, recursively.
varNamesInCons :: CFCons -> [String]
varNamesInCons c =
  case c of 
    ConsNil -> []
    Cons h t -> (varNamesInTerm h) ++ (varNamesInCons t)
