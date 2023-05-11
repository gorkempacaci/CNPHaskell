{-|
Module: Unification
Description: An implementation of first-order unification over types defined in Flattening.
-}
module Unification (unifyLiterals
                   ,unifyOneLiteralWithGround
                   ,literalTrue
                   ,applySubstitutionsToLiterals
                   ,unifyContradictoryAtoms
                   ,unifyLiteralWithGround
                   ,UnificationResult(..)
                   ,Substitution(..)
                   ) where

import Flattening
import Helpers
import Data.List(intersect, (\\), find)
import Text.PrettyPrint.HughesPJClass

-- | represents substitution of a variable with a given term.
data Substitution = Substitution {subsVar::String, subsWith::CFTerm}
  deriving (Eq)

-- | unification result for unifying literals or clauses.
data UnificationResult = UnifyAsFalse
                       | UnifyWith [Substitution]
                       | DoNotUnify
                       | UnifyAsTrue
  deriving (Show)

-- | unification result for term unification
data TermUnificationResult = TermsUnifyWith {termsSubstitution::[Substitution]}
                           | TermsDoNotUnify

instance Show Substitution where
  show (Substitution var with) = var ++ "->" ++ (show with)

instance Eq UnificationResult where
  (UnifyWith ss1) == (UnifyWith ss2) = setEquals ss1 ss2
  UnifyAsFalse == UnifyAsFalse = True
  DoNotUnify == DoNotUnify = True
  UnifyAsTrue == UnifyAsTrue = True
  a == b = False

-- | defines a literal which is a positive literal with atom name "true", and no terms.
literalTrue :: CFLiteral
literalTrue = Pos $ Atom "true" []

-- | attempts to unify two literals. 
unifyLiterals :: CFLiteral -> CFLiteral -> UnificationResult
unifyLiterals lit1 lit2 =
  case (lit1, lit2) of
    (Pos atom1, Neg atom2) -> unifyContradictoryAtoms atom1 atom2
    (Neg atom1, Pos atom2) -> unifyContradictoryAtoms atom1 atom2
    otherwise -> DoNotUnify

-- | Atoms unify if their names are the same and if their terms unify.
unifyContradictoryAtoms :: CFAtom -> CFAtom -> UnificationResult
unifyContradictoryAtoms (Atom lName lTerms) (Atom rName rTerms) =
  if lName /= rName then DoNotUnify
  else case unifyTerms lTerms rTerms of 
    TermsDoNotUnify -> DoNotUnify
    TermsUnifyWith s -> UnifyWith s


-- | Given a list of literals, unifies the first one it can unify
--   with a ground predicate, and returns the unification result with
--   the list of literals except the one just unified.
--   The remaining literals have not been 
unifyOneLiteralWithGround :: [CFLiteral] -> (UnificationResult, [CFLiteral])
unifyOneLiteralWithGround [] = (DoNotUnify, [])
unifyOneLiteralWithGround lits@(firstLit:restLit) =
  let firstLitUni = unifyLiteralWithGround firstLit
  in case firstLitUni of
      UnifyAsFalse -> (UnifyAsFalse, restLit)
      UnifyWith _ -> (firstLitUni, restLit)
      DoNotUnify ->
        let (restUniResult, restUniRemaining) = unifyOneLiteralWithGround restLit
        in (restUniResult, firstLit:restUniRemaining)
      UnifyAsTrue -> (UnifyAsTrue, lits)

-- | attempts to unify a given literal with one of the ground predicates.
unifyLiteralWithGround :: CFLiteral -> UnificationResult
unifyLiteralWithGround (Pos _) = DoNotUnify
unifyLiteralWithGround (Neg (Atom name terms)) =
  case name of 
    "true" -> if null terms then UnifyAsFalse else DoNotUnify
    "isNil" -> unifyTermsOfGroundIsNil terms
    "id" -> unifyTermsOfGroundId terms
    "diff" -> unifyTermsOfGroundDiff terms
    "cons" -> unifyTermsOfGroundCons terms
    otherwise -> DoNotUnify

-- | attempts to unify as terms of ground predicate ~isNil([])
unifyTermsOfGroundIsNil :: [CFTerm] -> UnificationResult
unifyTermsOfGroundIsNil terms =
  case terms of
    [ConsTerm ConsNil] -> UnifyAsFalse
    [VarTerm vA] -> UnifyWith [Substitution vA (ConsTerm ConsNil)]
    otherwise -> UnifyAsTrue

-- | attempts to unify a given list of terms as arguments
-- | of the ground predicate ~id(X, X).
unifyTermsOfGroundId :: [CFTerm] -> UnificationResult
unifyTermsOfGroundId terms = 
  case terms of  --(tA:tB:[])
    [VarTerm vA, VarTerm vB] -> if vA == vB then UnifyAsFalse else UnifyWith [Substitution vA $ VarTerm vB]
    [VarTerm vA, tB] -> UnifyWith [Substitution vA tB]
    [tA, VarTerm vB] -> UnifyWith [Substitution vB tA]
    [tA, tB] -> let u = unifyTerm tA tB 
                in case u of 
                  TermsDoNotUnify -> UnifyAsTrue
                  TermsUnifyWith s -> UnifyWith s
    otherwise -> DoNotUnify

-- | attems to unify terms of ~diff(X, Y)
unifyTermsOfGroundDiff :: [CFTerm] -> UnificationResult
unifyTermsOfGroundDiff terms =
  case terms of 
    [VarTerm vA, VarTerm vB] -> if vA == vB then UnifyAsTrue else DoNotUnify
    [VarTerm _, _] -> DoNotUnify
    [_, VarTerm _] -> DoNotUnify
    [tA, tB] -> if tA == tB then UnifyAsTrue else UnifyAsFalse
    otherwise -> DoNotUnify

-- | attempts to unify a given list of terms as arguments
--   of the ground predicate ~cons(Head, Tail, List).
unifyTermsOfGroundCons :: [CFTerm] -> UnificationResult
unifyTermsOfGroundCons terms =
  case terms of
    -- case where List is empty
    [_,_,ConsTerm ConsNil] -> UnifyAsTrue
    headTerm:tailTerm:(ConsTerm (Cons hd tl)):[] ->
      let headUnifiesAs = unifyTerm headTerm hd
      in case headUnifiesAs of
        TermsDoNotUnify -> UnifyAsTrue
        TermsUnifyWith sHead ->
          let [newTailTerm] = applySubstitutionsToTerms sHead [tailTerm]
              [newConsTail] = applySubstitutionsToTerms sHead [ConsTerm $ tl]
              tailUResult = combineTermUnificationResults headUnifiesAs (unifyTerm newTailTerm newConsTail)
          in case tailUResult of 
              TermsDoNotUnify -> UnifyAsTrue
              TermsUnifyWith sComb -> if null sComb then UnifyAsFalse else UnifyWith sComb
    headTerm:(ConsTerm tailTerm):(VarTerm listVar):[] ->
      UnifyWith [Substitution listVar (ConsTerm $ Cons headTerm tailTerm)]
    otherwise -> DoNotUnify



-- | attempts to unify a list of terms.
unifyTerms :: [CFTerm] -> [CFTerm] -> TermUnificationResult
unifyTerms [ ] [ ] = TermsUnifyWith []
unifyTerms [ ]  _ = TermsDoNotUnify
unifyTerms  _  [ ] = TermsDoNotUnify
unifyTerms lTerms@(lTermsH:lTermsT) rTerms@(rTermsH:rTermsT) =
  if not $ verifyNoCommonVars lTerms rTerms
  then error $ "Common vars exist in two sets of terms:" ++ (prettyShow lTerms) ++ "u" ++ (prettyShow rTerms)
  else let headTermsU = unifyTerm lTermsH rTermsH
       in case headTermsU of
         TermsUnifyWith subs ->
           let lTermsTAfterSubs = applySubstitutionsToTerms subs lTermsT
               rTermsTAfterSubs = applySubstitutionsToTerms subs rTermsT
               restOfTermsU = unifyTerms lTermsTAfterSubs rTermsTAfterSubs
           in combineTermUnificationResults headTermsU restOfTermsU
         TermsDoNotUnify -> TermsDoNotUnify
           

-- | verifies that no variables occur in both lists of terms.
--   this is a prerequisite for unification to start between
--   two clauses.
verifyNoCommonVars :: [CFTerm] -> [CFTerm] -> Bool
verifyNoCommonVars terms1 terms2 =
  let vars1 = [VarTerm v | VarTerm v<-terms1]
      vars2 = [VarTerm v | VarTerm v<-terms2]
  in intersect vars1 vars2 == []

-- | attempts to unify two single terms. (not negated)
unifyTerm :: CFTerm -> CFTerm -> TermUnificationResult
unifyTerm (VarTerm lVar) rTerm@(VarTerm rVar) =
  if lVar == rVar then TermsUnifyWith [] else  TermsUnifyWith [Substitution lVar rTerm]
unifyTerm (VarTerm lVar) rTerm = TermsUnifyWith [Substitution lVar rTerm]
unifyTerm lTerm (VarTerm rVar) = TermsUnifyWith [Substitution rVar lTerm]
unifyTerm lTerm rTerm = if lTerm == rTerm then TermsUnifyWith [] else TermsDoNotUnify

-- | replaces all instances of a variable with the given term.
substituteVarWith :: String -> CFTerm -> CFTerm -> CFTerm
substituteVarWith varName subsTerm sourceTerm =
  case sourceTerm of 
    ConstantTerm _ -> sourceTerm
    VarTerm n -> if sourceTerm == (VarTerm varName) then subsTerm else sourceTerm
    ConsTerm cns -> ConsTerm (substituteVarInCons varName subsTerm cns)

-- | replaces all instances of a variable with the given term, recursively in a cons. 
substituteVarInCons :: String -> CFTerm -> CFCons -> CFCons
substituteVarInCons varName subsTerm sourceCons =
  case sourceCons of 
    ConsNil -> ConsNil
    Cons hd tl -> Cons {consHead=substituteVarWith varName subsTerm hd
                       ,consTail=substituteVarInCons varName subsTerm tl}

applySubstitutionToTerms :: [CFTerm] -> Substitution -> [CFTerm]
applySubstitutionToTerms inTerms subs@(Substitution varName withTerm) =
  map (substituteVarWith varName withTerm) inTerms

-- | Applies substitutions in the order they appear.
applySubstitutionsToTerms :: [Substitution] -> [CFTerm] -> [CFTerm]
applySubstitutionsToTerms subss terms =
  foldl applySubstitutionToTerms terms subss

applySubstitutionsToLiteral :: [Substitution] -> CFLiteral -> CFLiteral
applySubstitutionsToLiteral subs lit = 
  let anAtom = atom lit
      anAtomName = atomName anAtom
      newAtomTerms = applySubstitutionsToTerms subs (atomTerms anAtom)
  in lit {atom=Atom anAtomName newAtomTerms}

-- | applies given substitutions to all the literals, in the order they are given.
applySubstitutionsToLiterals :: [Substitution] -> [CFLiteral] -> [CFLiteral]
applySubstitutionsToLiterals subs lits =
  map (applySubstitutionsToLiteral subs) lits

-- | For combining term unification results
-- | Warning: only concatentates substitutions, does not aggregate them.
combineTermUnificationResults :: TermUnificationResult -> TermUnificationResult -> TermUnificationResult
combineTermUnificationResults uni1 uni2 =
  case (uni1, uni2) of 
    (TermsDoNotUnify, _) -> TermsDoNotUnify
    (_, TermsDoNotUnify) -> TermsDoNotUnify
    (TermsUnifyWith sA, TermsUnifyWith sB) -> TermsUnifyWith (sA ++ sB)




