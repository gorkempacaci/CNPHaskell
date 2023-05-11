{-# LANGUAGE OverloadedStrings #-}

{-|
Module: CNP
Description: The main module which should be imported by the programs that will use 
  a CNP embedding and solver. Exports all the necessary data structures and functions
  for defining and executing a CNP program.
-}
module CNP (NExecution(..)
           ,NProgram(..)
           ,NPredicateDefinition(..)
           ,NExpression(..) 
           ,NProjectionItem(..)
           ,Value(..)
           ,(//)          -- projection shorthand expr // proj
           ,from          -- projection shorthand proj `from` expr
           ,(|>)          -- renaming argument "a"|>"b"
           ,(-:-)         -- shorthand for predicate definition name -:- expr
           ,solveBool
           ,extensionally -- function for defining predicates extensionally. stands for an expr.
           ,toCNF -- for tests
           ,toCNFStr -- for tests
           ,toSaturatedStr -- for tests
           )where

import Data.String (IsString(..))
import Data.List (union, all, elem, intercalate, intersperse, find, (\\))
import Data.Set (empty)
import Text.PrettyPrint.HughesPJClass (prettyShow)
import qualified Control.Exception as E

import Language
import Helpers
import Saturation
import Flattening
import Solver

{-

  General Description:

  NExecution p g = defines a program p (list of predicate definitions)
    and a goal g (a cnp expression).

  saturate nExec = saturates all the names in the projections and 
    produces predicate-scope unique names for every argument, and
    removes projections from the tree since they become redundant
    after saturation. This step practically converts all arguments
    to variables in the conventional sense.

  flatten sProg = takes a saturated program, and flattens it to CNF 
    form. 

-}

-- | converts an execution into CNF form execution
toCNF :: NExecution -> CFExecution
toCNF = flatten . saturate

-- | converts the given execution into CNF form execution and then prettifies it.
toCNFStr :: NExecution -> String
toCNFStr = prettyShow . toCNF

-- | saturates the given execution and prettifies the saturated program.
toSaturatedStr :: NExecution -> String
toSaturatedStr = prettyShow . saturate

-- | a shorthand for defining predicates via their extension. 
extensionally :: [String] -> [[Value]] -> NExpression
extensionally argNames tupleList =
  let numArgs = length argNames
      predArgsProj = map Arg argNames
  in if not $ all (\t -> length t == numArgs) tupleList
     then error "Number of arguments and number of values in a tuple do not match."
     else predArgsProj `from` Or (map (\t -> And (map (\(a,v)-> Constant a v) (zip argNames t))) tupleList )








