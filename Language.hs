{-|
Module: Language
Description: Defines the fundamental data structures for composing programs in CNP.

  This module defines the syntax of CNP programs. It includes
  the data structures a user of CNP would utilize. A CNP program
  written in these terms is fed into the 'saturate' function from the
  Saturation module, which decides local and common names for every
  argument in the expression, where the common names are unique in
  predicate scope. he result of the 'saturate' function is an SExecution
  (as opposed to n NExecution defined here). Then, the 'flatten' function
  from the Flattening module transforms this SExecution into CNF form
  (represented by the CF* data types in the Flattening module.)
-}
module Language where

import Data.String


{-| A cnp expression -}
data NExpression =
    PredicateCall {predName::String} -- an activation of a predicate (can be recursive)
  | Projection {expr::NExpression, projList::[NProjectionItem]} -- projection of arguments
  | And {exprs::[NExpression]}
  | Or {exprs::[NExpression]} -- conjunction and disjunction. auto-expanding.
  | FoldR {recursive::NExpression, base::NExpression}
  | FoldL {recursive::NExpression, base::NExpression}
  | ConsList {listName::String, listValues::[Value]}
  | Constant {constName::String, constValue::Value}
  | Id String String
  | Diff String String
  | IsNil String
  deriving (Show, Eq)

{-| Constant terms can contain primitive types -}
data Value = I Int | S String
  deriving (Show, Eq)

{-| So we can use an Int and an I Int interchangeably. -}
instance Num Value where
    fromInteger = I . fromInteger
    I x + I y = I (x+y)
    I x * I y = I (x*y)
    abs (I x) = I (abs x)
    signum (I x) = I (signum x)
    negate (I x) = I (negate x)

{-| String and S String can be used interchangeably.-}
instance IsString Value where
    fromString = S

{-| so we can write "id" instead of PredicateCall "id" -}
instance IsString NExpression where
    fromString = PredicateCall

{-| shortcut for projection. -}
infixl 5 //                                -- infix shortcut for projection
(//) = Projection
{-| shortcut syntax for projection, different argument order
   (first projections, then expression). useful for the
   required top-level projection in each predicate definition.
   so we can write PredicateDefinition "p" [p's args...] `from` (expression)
        instead of PredicateDefinition "p" (expression // [p's args...])
-}
infixr 1 `from`
(from) = flip Projection

{-| Two kinds of projection may appear in a projection list. -}
data NProjectionItem =
    -- include the given arugment with its original name.
    -- it can be read as "with argument a"
    Arg {argName::String}
    -- a|>b can be read as "with a as b" or "with a renamed to b"
    -- include the argument name #1 as #2
  | ArgAs {oldName::String, newName::String}
  deriving (Show, Eq)

{-| Shortcut that converts "arg" to Arg "arg" -}
instance IsString NProjectionItem where
  fromString = Arg

{-| Shortcut that converts "a"|>"b" to ArgAs "a" "b" -}
infix 1 |>
(|>) a b = ArgAs a b

{-| A predicate definition.
   It is required by the saturation process that the expression tree
   begins with a projection, so a predicate-arguments index can be
   generated without performing a deep argument inference pass.
 -}
data NPredicateDefinition =
    PredicateDefinition {defName::String, defExpr::NExpression}
  deriving (Show, Eq)

{-| Infix operator for predicate definition. Shorthand for PredicateDefinition data constructor. -}
infix 9 -:-
(-:-) n e = PredicateDefinition n e

{-| A CNP program without a goal. This contains the predicate definitions in KB. -}
data NProgram = Program [NPredicateDefinition]

{-| used for built-in predicates and by also predicate argument indexing -}
data PredicateSignature =
  PredicateSignature {sigName::String, sigArgs::[String]}

{-| A CNP execution contains a program, and a goal -}
data NExecution = Execution {userProgram::NProgram, userGoal::NExpression}

{-| builtin predicates and their arguments. -}
builtinPredicateSignatures :: [PredicateSignature]
builtinPredicateSignatures =
  [PredicateSignature "true" []
  ,PredicateSignature "isNil" ["nil"]
  ,PredicateSignature "id" ["a", "b"]
  ,PredicateSignature "diff" ["a", "b"]
  ,PredicateSignature "cons" ["head", "tail", "list"]
  ]
