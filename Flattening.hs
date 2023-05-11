{-|
Module: Flattening
Description: Profides the 'flatten' method and related data structures for 
  converting a saturated CNP expression tree into a flatter form which is
  definite clauses in Conjunction Normal Form.
-}
module Flattening (flatten
                  ,CFCons(..)
                  ,CFTerm(..)
                  ,CFAtom(..)
                  ,CFLiteral(..)
                  ,CFDisjunction(..)
                  ,CFConjunction(..)
                  ,CFExecution(..)
                  ,cfConsesFromList
                  ) where

import Data.List ((\\))

import Text.PrettyPrint.HughesPJClass
import Text.PrettyPrint.HughesPJClass as PP (empty)

import Language (Value(I, S))
import Saturation
import Helpers


-- | A functional Cons list of terms. This is the only function form.
data CFCons = Cons {consHead::CFTerm, consTail::CFCons} | ConsNil
  deriving(Show, Eq)
-- | A term that can be a constant, a variable or a const term.
data CFTerm = ConstantTerm {constValue::Value}
            | VarTerm String
            | ConsTerm CFCons
-- | An atom with terms as a list
data CFAtom = Atom {atomName::String, atomTerms::[CFTerm]}
  deriving(Show, Eq)
-- | A literal, which is either a Pos Atom or a Neg Atom.
data CFLiteral = Pos {atom::CFAtom} | Neg {atom::CFAtom}
  deriving(Show, Eq)
-- | A disjunction of literals
data CFDisjunction = Disjunction {literals::[CFLiteral]}
  deriving(Show, Eq)
-- | A conjunction of disjunctions
data CFConjunction = Conjunction {disjunctions::[CFDisjunction]}
  deriving(Show, Eq)
-- | An execution, which contains a conjunction as a knowledge base, and a disjunction as goal.
data CFExecution = CFExecution {cfKnowledgeBase::CFConjunction, cfUserGoal::CFDisjunction}
  deriving(Show, Eq)

instance Eq CFTerm where
  (==) (ConstantTerm v1) (ConstantTerm v2) = v1 == v2
  (==) (VarTerm v1) (VarTerm v2) = (toUpperStr v1 == toUpperStr v2)
  (==) (ConsTerm v1) (ConsTerm v2) = v1 == v2
  (==) a b = False

groundAtomId::(CFTerm, CFTerm) -> CFAtom
groundAtomId (firstTerm, secondTerm) =
  Atom {atomName="id", atomTerms=[firstTerm, secondTerm]}

-- | converts a saturated program into conjunctive normal form (conjunction of disjuncts)
flatten :: SExecution -> CFExecution
flatten (SExecution (SProgram pDefs) sGoal) =
  let goalFlattened = cfFromExpression "$goal" sGoal
      goalClause = goal goalFlattened
      goalClauseSupport = support goalFlattened
      originalKB = mergeConjunctions $ map cfFromSPredicate pDefs
      execKB = mergeConjunctions [originalKB, goalClauseSupport]
  in CFExecution {cfKnowledgeBase=execKB, cfUserGoal=goalClause}

-- returns a conjunction of disjunctions.
cfFromSPredicate :: SPredicateDefinition -> CFConjunction
cfFromSPredicate (SPredicateDefinition pDefName pDefSArgs pDefSExpr) =
  let predVars = map VarTerm $ (map commonName) pDefSArgs
      predAtom = Atom pDefName predVars
      goalAndSupport = cfFromExpression (pDefName ++ "_e") pDefSExpr
      implicationClause = addLiteralToBeginning (Pos predAtom) (goal goalAndSupport)
  in mergeConjunctions [(Conjunction [implicationClause]), (support goalAndSupport)]

-- generates (a) clause(s) with given fact and goals. since conjunctions result in multiple
-- clauses, and disjunctions in a single clause, the result is always a list.
addLiteralToBeginning :: CFLiteral -> CFDisjunction -> CFDisjunction
addLiteralToBeginning literal dis = Disjunction (literal:literals dis)

goalFromPredicateCall :: SExpression -> CFDisjunction
goalFromPredicateCall expr@(SPredicateCall name args) =
  Disjunction $ [Neg $ Atom name (varsFromArgs expr)]

mergeDisjunctions :: [CFDisjunction] -> CFDisjunction
mergeDisjunctions ds = Disjunction {literals=concat (map literals ds)}

mergeConjunctions :: [CFConjunction] -> CFConjunction
mergeConjunctions cs = Conjunction {disjunctions=concat (map disjunctions cs)}

varFromArg :: SArgument -> CFTerm
varFromArg sArg = VarTerm (commonName sArg)

{- returns variable names for an SExpression using common names. -}
varsFromArgs :: SExpression -> [CFTerm]
varsFromArgs exp = map VarTerm (commonArgNamesOf exp)

makeVars :: [String] -> [CFTerm]
makeVars = map VarTerm

-- unpacks common argument names of a saturated expression
commonArgNamesOf :: SExpression -> [String]
commonArgNamesOf expr = case expr of 
  SPredicateCall _ args -> map commonName args
  SOr _ args -> map commonName args
  SFoldR _ _ args -> map commonName args
  SFoldL _ _ args -> map commonName args

-- goals are always in the form of negated literals in disjunction.
data CFGoalWithSupport =
    GoalWithSupport {goal::CFDisjunction, support::CFConjunction}

-- | Takes a list of values and converts them into the CFCons list structure.
cfConsesFromList :: [Value] -> CFCons
cfConsesFromList vs = case vs of
            x:xs -> Cons (ConstantTerm x) (cfConsesFromList xs)
            [] -> ConsNil

{- merges all goals and all supports into one goal-and-support. -}
mergeGoalsAndSupport :: [CFGoalWithSupport] -> CFGoalWithSupport
mergeGoalsAndSupport gss =
  let allGoals = mergeDisjunctions (map goal gss)
      allSupport = mergeConjunctions (map support gss)
  in GoalWithSupport {goal=allGoals, support=allSupport}

-- linking. takes a list of goals, and a link atom and produces a goal-support pair as 
-- goal: -link
-- supp: +link v -goal1
--       +link v -goal2
--       +link v -goal3
-- these supporting clauses eventually unify with the linked goal.
linkGoalFromMultipleGoals :: [CFDisjunction] -> CFAtom -> CFGoalWithSupport
linkGoalFromMultipleGoals goals linkAtom =
  let goalLiteral = Neg linkAtom
      headLiteral = Pos linkAtom
      supportClauses = map (\g -> mergeDisjunctions [Disjunction [headLiteral], g]) goals
  in GoalWithSupport (Disjunction [goalLiteral]) (Conjunction supportClauses)


-- | flattens an SExpression, naming its and its subexpressions with the name prefix given.
cfFromExpression :: String -> SExpression -> CFGoalWithSupport
cfFromExpression prefix expr =
  let nameForSubexpr i = prefix ++ "_" ++ (show i)
      allSubgoalsWithSupport = map (\(e, i) -> cfFromExpression (nameForSubexpr i) e)
      singleGoalWithNoSupport atom = GoalWithSupport (Disjunction [Neg $ atom]) (Conjunction [])
  in case expr of 
    SPredicateCall predicateName args -> GoalWithSupport (goalFromPredicateCall expr) (Conjunction [])
    SProjection _ _ -> error "unexpected projection in saturated expression tree."
    -- for the 'and' operator, all subgoals and subsupports are combined into a single clause.
    SAnd subExprs args -> mergeGoalsAndSupport $ allSubgoalsWithSupport (withIndex subExprs)
    -- in case of an 'or' operator, all subgoals are evaluated, and all their goals are 
    -- transformed into separate disjunctive clauses with a positive 'link' literal. 
    -- the goal of 'or' is a negative 'link' literal, which eventually unifies with the positives.
    -- these new disjunctive clauses and all the existing support for subgoals become the new 
    -- combined support for 'or'.
    SOr subExprs args ->
      let allSubGoals = allSubgoalsWithSupport (withIndex subExprs)
          orAtom = Atom prefix (varsFromArgs expr)
          subGoalsOnly = map goal allSubGoals
          subSupportsOnly = map support allSubGoals
          linkedGoalAndSupport = linkGoalFromMultipleGoals subGoalsOnly orAtom
          orGoal = goal linkedGoalAndSupport
          supportForLinkedGoals = support linkedGoalAndSupport
          orCombinedSupport = mergeConjunctions (supportForLinkedGoals : subSupportsOnly)
      in GoalWithSupport orGoal orCombinedSupport
    SFoldR sRec sBas _ -> cfForFold FoldBottomUp prefix (varsFromArgs expr) sRec sBas
    SFoldL sRec sBas _ -> cfForFold FoldTopDown prefix (varsFromArgs expr) sRec sBas
    SConsList arg values ->
      singleGoalWithNoSupport $ groundAtomId (varFromArg arg, ConsTerm $ cfConsesFromList values)
    SConstant arg value -> singleGoalWithNoSupport $ groundAtomId (varFromArg arg, ConstantTerm value)

-- | for passing along the direction of FoldR(bottom-up) or FoldL (top-down)
data FoldDirection = FoldBottomUp | FoldTopDown
  deriving (Show)

cfForFold :: FoldDirection -> String -> [CFTerm] -> SExpression -> SExpression -> CFGoalWithSupport
cfForFold f prefix goalArgs sRec sBas =
  let foldAtomName = prefix
      foldBLinkName = prefix ++ "_b"
      foldRLinkName = prefix ++ "_r"
      basCaseGS = cfFromExpression (foldBLinkName ++ "_1") sBas
      recCaseGS = cfFromExpression (foldRLinkName ++ "_1") sRec
      basClause = Disjunction 
                    [Pos (Atom foldAtomName (makeVars ["as", "b0", "f"]))
                    ,Neg (Atom "isNil" (makeVars ["as"]))
                    ,Neg (Atom foldBLinkName (makeVars ["b0", "f"]))]
      recClause = case f of 
        FoldBottomUp -> Disjunction
                    [Pos (Atom foldAtomName (makeVars ["as", "b0", "f"]))
                    ,Neg (Atom "cons" (makeVars ["a", "as_t", "as"]))
                    ,Neg (Atom foldAtomName (makeVars ["as_t", "b0", "f_i"]))
                    ,Neg (Atom foldRLinkName (makeVars ["a", "f_i", "f"]))]
        FoldTopDown -> Disjunction
                    [Pos (Atom foldAtomName (makeVars ["as", "b0", "f"]))
                    ,Neg (Atom "cons" (makeVars ["a", "as_t", "as"]))                    
                    ,Neg (Atom foldRLinkName (makeVars ["a", "b0", "f_i"]))
                    ,Neg (Atom foldAtomName (makeVars ["as_t", "f_i", "f"]))]
      basAppClause = Disjunction
                       (Pos (Atom foldBLinkName (varsFromArgs sBas))
                       :literals (goal basCaseGS))
      recAppClause = Disjunction
                       (Pos (Atom foldRLinkName (varsFromArgs sRec))
                       :literals (goal recCaseGS))
      foldGoal = Disjunction [Neg (Atom foldAtomName goalArgs)]
      foldSupport = mergeConjunctions [
                      Conjunction [
                        basClause
                       ,recClause
                       ,basAppClause
                       ,recAppClause]
                     ,support basCaseGS
                     ,support recCaseGS]
  in GoalWithSupport foldGoal foldSupport



instance Show CFTerm where
  show = prettyShow

instance Ord CFDisjunction where
  (Disjunction dis1) `compare` (Disjunction dis2) = (length dis1) `compare` (length dis2)

instance  Pretty (CFExecution) where
  pPrint (CFExecution kb gl) = vcat [pPrint kb, pPrint gl]
instance Pretty (CFConjunction) where
  pPrint (Conjunction disjs) = vcat (map pPrint disjs)
instance Pretty (CFDisjunction) where
  pPrint (Disjunction lits) = prettyWithInbetween (text "v") (<+>) lits
instance Pretty (CFLiteral) where
  pPrint (lit) = case lit of
    Pos atom -> pPrint atom
    Neg atom -> text "~" <> pPrint atom
instance Pretty (CFAtom) where
  pPrint (Atom name vars) = text name <> parensIfNotEmpty vars
instance Pretty (CFTerm) where
  pPrint (ConstantTerm s) = pPrint s
  pPrint (VarTerm name) = text (toUpperStr name)
  pPrint (ConsTerm l) = pPrint l
instance Pretty (CFCons) where
  pPrint (ConsNil) = brackets empty
  pPrint lst@(Cons _ t) = 
    let listContents l@(Cons hd tl) = case tl of 
          ConsNil -> pPrint hd
          Cons _ _ -> pPrint hd <> comma <> listContents tl
    in brackets $ listContents lst





