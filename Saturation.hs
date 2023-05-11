{-|
Module: Saturation
Description: Defines the function 'saturate', which takes an NProgram as an input,
  which is the initial method of writing programs in CNP, and returns an SProgram,
  which is the 'saturated' form of the same program, omitting projections,
  and for every argument place contains a pair of (common, local)
  names. The common names are quantified in the scope of a predicate definition, which
  allows the logical replacements of expressions during flattening.
-}
module Saturation (SExecution(..)
                  ,SProgram(..)
                  ,SPredicateDefinition(..)
                  ,SExpression(..)
                  ,SArgumentSet(..)
                  ,SArgument(..)
                  ,saturate
                  ,languageFoldArgs
                  ,languageFoldBasArgs
                  ,languageFoldRecArgs
                  ) where

import Data.List (intersect, union, all, elem, intercalate, intersperse, find, (\\))
import Data.Set (empty)
import Text.PrettyPrint.HughesPJClass
import Text.PrettyPrint.HughesPJClass as PP (empty)

import Language
import Helpers



{-| an execution that includes a saturated program and a saturated goal -}
data SExecution = SExecution {sUserProgram::SProgram, sUserGoal::SExpression}

{-| a name-saturated program -}
data SProgram = SProgram [SPredicateDefinition]

{-| a saturated predicate definition with a name, arguments (arising from the
  required top-level projection), and a predicate expression -}
data SPredicateDefinition =
    SPredicateDefinition {sDefName::String, sDefArgs::SArgumentSet, sDefExpr::SExpression}
  deriving (Show, Eq)


{-| saturated CNP expression -}
data SExpression =                       
    SPredicateCall {sPredName::String, sPredArgs::SArgumentSet}
  | SProjection {sExpr::SExpression, sProjList::[NProjectionItem]}
  | SAnd {sExprs::[SExpression], sArgs::SArgumentSet}
  | SOr {sExprs::[SExpression], sArgs::SArgumentSet}
  | SFoldR {sRecursive::SExpression, sBase::SExpression, sArgs::SArgumentSet}
  | SFoldL {sRecursive::SExpression, sBase::SExpression, sArgs::SArgumentSet}
  | SConsList {sListArg::SArgument, listValues::[Value]}
  | SConstant {sConstArg::SArgument, sConstValue::Value}
  deriving (Show, Eq)


{-| list of saturated argument names -}
type SArgumentSet = [SArgument]

{-| represents an argument name after saturation.
  localName is unique in the context, but commonName
  is unique in the predicate scope. -}
data SArgument =                            
    SArgument {commonName::String, localName::String}
  deriving (Show, Eq)

-- | a function takes a predicate name and returns its argument names.
type PredicateArgumentLookup = (String -> [String])

-- | name maps are used during saturation of names in an expression tree.
data NameMapEntry = NameMapEntry {mapCommonName::String, mapLocalName::String}
type NameMap = [NameMapEntry]

-- | The fixed argument names a FoldR or FoldL should have.
languageFoldArgs = ["as", "b0", "folded"]
-- | The fixed argument names for a base case for folds.
languageFoldBasArgs = ["b0", "folded"]
-- | The fixed argument names for a recursive case for folds.
languageFoldRecArgs = ["a", "b", "folded"]



{-| saturates a program.
 this is a transformation which decides unique global names for each argument,
 preparing the clauses for unification. calculated names are preserved as local names. -}
saturate :: NExecution -> SExecution
saturate (Execution (Program uDefinitions) uGoal) =
  let lookup = signatureLookup $ signaturesFromDefinitions uDefinitions
      sUProgram = SProgram (map (saturatePredicateDefinition lookup) uDefinitions)
      sUGoal = saturateExpression lookup [] "" uGoal
  in SExecution {sUserProgram=sUProgram, sUserGoal=sUGoal}

saturatePredicateDefinition :: PredicateArgumentLookup -> NPredicateDefinition -> SPredicateDefinition
saturatePredicateDefinition lookup (PredicateDefinition name expression) =
  let predArgumentNames = lookup name
      predArguments = sArgumentsFromArgNames predArgumentNames
      saturatedPredExpression = saturateExpression lookup predArgumentNames "_" expression
      predName = validatePredicateSymbol name
  in SPredicateDefinition predName predArguments saturatedPredExpression

{-| takes a predicate signature lookup function, the argument names existing in the context,
 a fresh name prefix for new common names,
 an NExpression, and returns an SExpression with saturated argument names. -}
saturateExpression :: PredicateArgumentLookup -> [String] -> String -> NExpression -> SExpression
saturateExpression lookup contextArgs freshArgNamePrefix expression =
  let initialNameMap = initNameMapFromArgs contextArgs
      localSaturated = saturateLocalNames lookup expression
      commonSaturated = saturateCommonNames initialNameMap freshArgNamePrefix localSaturated
  in commonSaturated

-- | replaces syntactic sugar such as Id a b with a predicate call and projection.
replaceSyntacticSugar :: NExpression -> NExpression
replaceSyntacticSugar exp =
  case exp of 
    Id a b -> Projection (PredicateCall "id") [ArgAs "a" a, ArgAs "b" b]
    Diff a b -> Projection (PredicateCall "diff") [ArgAs "a" a, ArgAs "b" b]
    IsNil a -> Projection (PredicateCall "isNil") [ArgAs "nil" a]
    otherwise -> error ("Syntactic sugar not implemented:" ++ (show exp))

-- | calculates local names, bottom-up.
saturateLocalNames :: PredicateArgumentLookup -> NExpression -> SExpression
saturateLocalNames lookup nexpr =
  let unionOfLocalArgNames sexprs = foldl union [] (map localArgNamesOf sexprs)
  in case nexpr of
    PredicateCall name -> SPredicateCall name (sArgumentsFromArgNames (lookup name))
    Projection expr projs -> let sexpr = saturateLocalNames lookup expr
                                 projsValidated = validatedProjectionsFor projs sexpr
                             in SProjection sexpr projsValidated
    And exprs -> let subExprs = map (saturateLocalNames lookup) exprs
                     andArgs = unionOfLocalArgNames subExprs
                 in SAnd subExprs (sArgumentsFromArgNames andArgs)
    Or exprs -> let subExprs = map (saturateLocalNames lookup) exprs
                    orArgs = unionOfLocalArgNames subExprs
                in SOr subExprs (sArgumentsFromArgNames orArgs)
    FoldR rec bas -> saturateLocalNamesForFold lookup SFoldR rec bas
    FoldL rec bas -> saturateLocalNamesForFold lookup SFoldL rec bas
    ConsList n l -> SConsList (sArgumentFromArgName n) l
    Constant n v -> SConstant (sArgumentFromArgName n) v
    Id _ _ -> saturateLocalNames lookup $ replaceSyntacticSugar nexpr
    Diff _ _ -> saturateLocalNames lookup $ replaceSyntacticSugar nexpr
    IsNil _ -> saturateLocalNames lookup $ replaceSyntacticSugar nexpr

saturateLocalNamesForFold :: PredicateArgumentLookup -> (SExpression -> SExpression -> SArgumentSet -> SExpression) -> NExpression -> NExpression -> SExpression 
saturateLocalNamesForFold lookup f rec bas =
  let sRec = saturateLocalNames lookup rec
      sBas = saturateLocalNames lookup bas
      sArgs = sArgumentsFromArgNames languageFoldArgs
      (sRec2, sBas2) = validateFold sRec sBas
  in f sRec2 sBas2 sArgs

{-| calculates common names top->down, applying projections in inverse.
 this essentially moves the universal (\forall) quantifiers to the topmost scope,
 preparing the form for CNF.
 requires that logical junctions (and, or) have no more than 9 components (indexing.) -}
saturateCommonNames :: NameMap -> String -> SExpression -> SExpression
saturateCommonNames nameMap freshPrefix sExpr =
  let exprArgs = localArgNamesOf sExpr
      -- only used for predicateCall, And and Or, not projection.  
      newNameMap = restrictAndExpandNameMap exprArgs freshPrefix nameMap
      -- helper methods for SAnd and SOr
      logicalJunctionSaturate logicOp exprs args =
        let sExprsWithIndices = zipWith (\a b->(a, b)) exprs [1..]
            saturateAllWithPrefixIndices (exp, ind) =
              saturateCommonNames newNameMap (freshPrefix++(show ind)) exp
            saturatedExpressions = map saturateAllWithPrefixIndices sExprsWithIndices
            newArgs = sArgsWithCommonNamesFromMap newNameMap args
        in logicOp saturatedExpressions newArgs
  in case sExpr of 
      SPredicateCall pName pArgs ->
        SPredicateCall pName (sArgsWithCommonNamesFromMap newNameMap pArgs)
      SProjection sExpr sProjList ->
        let projNameMap = nameMapInverseApplyProjections sProjList newNameMap
            saturatedExpression = saturateCommonNames projNameMap freshPrefix sExpr
        in saturatedExpression -- projections are no longer useful.
      SAnd sExprs sArgs -> logicalJunctionSaturate SAnd sExprs sArgs
      SOr sExprs sArgs -> logicalJunctionSaturate SOr sExprs sArgs
      SFoldR sRec sBas sArgs -> saturateCommonNamesForFold newNameMap freshPrefix SFoldR sRec sBas sArgs 
      SFoldL sRec sBas sArgs -> saturateCommonNamesForFold newNameMap freshPrefix SFoldL sRec sBas sArgs
      SConsList arg list -> SConsList (sArgWithCommonNameFromMap newNameMap arg) list
      SConstant arg val -> SConstant (sArgWithCommonNameFromMap newNameMap arg) val

saturateCommonNamesForFold :: NameMap -> String -> (SExpression -> SExpression -> SArgumentSet -> SExpression) -> SExpression -> SExpression -> SArgumentSet -> SExpression
saturateCommonNamesForFold nameMap prefix f sRec sBas sArgs =
  let sRec2 = saturateCommonNames nameMap prefix sRec
      sBas2 = saturateCommonNames nameMap prefix sBas
      sArgs2 = sArgsWithCommonNamesFromMap nameMap sArgs
  in f sRec2 sBas2 sArgs2  

-- returns the argument names of a predicate signature
signatureLookup :: [PredicateSignature] -> String -> [String]
signatureLookup signatures searchedName =
  let signaturesWithBuiltin = (builtinPredicateSignatures ++ signatures)
      matches = (filter (\ps -> ((sigName ps) == searchedName)) signaturesWithBuiltin)
      numMatches = length matches
  in if numMatches == 1
     then sigArgs (head matches)
     else error $ "Predicate does not exist or ambiguous:" ++ searchedName

-- extracts predicate name and argument names as a list from predicate definition
-- requires that predicate body begins with a projection so it can decide the predicate
-- arguments in constant time. otherwise an early pass of the expression tree would
-- have been necessary.
injectPredToSignatures :: [PredicateSignature] -> NPredicateDefinition -> [PredicateSignature]
injectPredToSignatures existingSigs (PredicateDefinition name expr) =
  case expr of 
    Projection _ projItems -> 
      let args = outerNamesFromProjs projItems
      in if not (elem name (map sigName existingSigs))
         then existingSigs ++ [PredicateSignature name args]
         else error $ "Predicate is defined multiple times:" ++ name
    otherwise -> error $ "Predicate definition does not start with a projection:" ++ name

signaturesFromDefinitions :: [NPredicateDefinition] -> [PredicateSignature]
signaturesFromDefinitions = foldl injectPredToSignatures [] 


-- unpacks or extracts(i.c.o. projections) local arguments of a saturated expression
localArgNamesOf :: SExpression -> [String]
localArgNamesOf expr = case expr of
  SPredicateCall _ args -> map localName args
  SProjection _ projs -> outerNamesFromProjs projs
  SAnd _ args -> map localName args
  SOr _ args -> map localName args
  SFoldR _ _ args -> map localName args
  SFoldL _ _ args -> map localName args
  SConsList arg _ -> [localName arg]
  SConstant arg _ -> [localName arg]

-- creates SArguments from a list of argument names.
-- writes local name, leaves global name empty.
sArgumentsFromArgNames :: [String] -> [SArgument]
sArgumentsFromArgNames = map sArgumentFromArgName
sArgumentFromArgName n = SArgument n n

-- extracts OUTER argument names from projection list
outerNamesFromProjs :: [NProjectionItem] -> [String]
outerNamesFromProjs = map outerNameFromProj

outerNameFromProj :: NProjectionItem -> String
outerNameFromProj proj =
  case proj of 
    Arg a -> a
    ArgAs _ a -> a

-- extracts SOURCE argument names from projections list
innerNamesFromProjs :: [NProjectionItem] -> [String]
innerNamesFromProjs = map innerNameFromProj

innerNameFromProj :: NProjectionItem -> String
innerNameFromProj proj =
  case proj of
    Arg a -> a
    ArgAs a _ -> a

{- takes a set of projections and returns them as they are if they are valid.
   1. all source arguments should actually exist as local args in the source
   2. every source argument is mapped to only one projected argument
   3. every projected argument is mapped to only one source argument
 -}
validatedProjectionsFor :: [NProjectionItem] -> SExpression -> [NProjectionItem]
validatedProjectionsFor projItems sourceExp =
  let argsFromSource = localArgNamesOf sourceExp
      innNames = innerNamesFromProjs projItems
      outNames = outerNamesFromProjs projItems
      nonexistingArgs = innNames \\ argsFromSource
  in if not (isDistinctSet innNames)
     then error ("Projection maps one argument to many:" ++ (prettyShow projItems))
     else if not (isDistinctSet outNames)
     then error ("Projection maps many arguments to one:" ++ (prettyShow projItems))
     else if  length nonexistingArgs > 0 --not (isSubsetOf innNames argsFromSource)
     then error ("Projected argument does not exist:" ++ (prettyShow nonexistingArgs) ++ " not in " ++ (prettyShow argsFromSource))
     else if any (elem '_') (innNames ++ outNames)
     then error ("Argument names should not contain underscore:" ++ (prettyShow projItems))
     else projItems    





-- | validates the argument mapping between base and recursive cases of a fold
validateFold :: SExpression -> SExpression -> (SExpression, SExpression)
validateFold sRec sBas =
  let recArgs = localArgNamesOf sRec
      basArgs = localArgNamesOf sBas
  in if not (setEquals recArgs languageFoldRecArgs)
     then error ("fold's recursive case argument names should be: "++(show languageFoldRecArgs)++", instead of:" ++ (prettyShow recArgs))
     else if not (setEquals basArgs languageFoldBasArgs)
     then error ("fold's base case argument names should be: "++(show languageFoldBasArgs)++", instead of:" ++ (prettyShow basArgs))
     else (sRec, sBas)

validatePredicateSymbol :: String -> String
validatePredicateSymbol s =
  if (elem '_' s)
  then error ("The predicate name " ++ (show s) ++ " is invalid because it contains an underscore.")
  else s

-- initializes a name map from a list of argument names that has 
-- both common and local names the same.
initNameMapFromArgs :: [String] -> NameMap
initNameMapFromArgs = map (\n -> NameMapEntry n n)

-- restricts the items in a name map to the items available in an argument context.
-- let's say there is and(or1, or2), length(arguments(and)) is larger than or1 or or2.
-- when saturation procedure steps into these branches, it needs to restrict the 
-- name mappings to prevent name clashes / capturing.
restrictNameMap :: [String] -> NameMap -> NameMap
restrictNameMap argsWanted =
  filter (\e -> elem (mapLocalName e) argsWanted)

-- during the saturation of common names, name mappings need to be expanded to contain new 
-- fresh common names for encapsulated arguments in the inner context. 
-- this takes a list of necessary arguments, a fresh argument prefix, and the old name map.
nameMapExpandWithFreshNames :: [String] -> String -> NameMap -> NameMap
nameMapExpandWithFreshNames argsWanted freshPrefix nameMap =
  let availableNamesInMap = map mapLocalName nameMap
      missingNames = argsWanted \\ availableNamesInMap
      newEntries = map (\n -> NameMapEntry {mapLocalName=n, mapCommonName=freshPrefix++n} ) missingNames
  in nameMap ++ newEntries

-- restricts the name mappings available in the map to those appearing
-- in the argument list. Then, introduces new name mappings with fresh
-- common names using the fresh name prefix. 
restrictAndExpandNameMap :: [String] -> String -> NameMap -> NameMap
restrictAndExpandNameMap argNames freshNamePrefix nameMap =
  nameMapExpandWithFreshNames argNames freshNamePrefix (restrictNameMap argNames nameMap)

-- inversely applies projections to local names in a map.
-- common names stay the same.
nameMapInverseApplyProjections :: [NProjectionItem] -> NameMap -> NameMap
nameMapInverseApplyProjections projItems nameMap =
  let outerNames = outerNamesFromProjs projItems
      localNamesInMap = map mapLocalName nameMap
  in if setEquals outerNames localNamesInMap
     then map (nameMapEntryInverseApplyProjections projItems) nameMap
     else error $ "Projections outer names and top-down calculated local names do not match."
                    ++ show outerNames ++ " vs " ++ show localNamesInMap

-- inversely applies projections to a single map entry.
nameMapEntryInverseApplyProjections :: [NProjectionItem] -> NameMapEntry -> NameMapEntry
nameMapEntryInverseApplyProjections projItems mapEntry =
  let maybeRelevantProjectionItem = find (\p -> outerNameFromProj p == mapLocalName mapEntry) projItems
  in case maybeRelevantProjectionItem of
    Nothing -> error "A local name in the name map could not be found as an outer name in a projection."
    Just projItem -> mapEntry {mapLocalName = innerNameFromProj projItem}

-- looks up a local name in a name map and returns the common name
nameMapCommonNameFor :: NameMap -> String -> String
nameMapCommonNameFor nameMap localName =
  case (find (\nme -> mapLocalName nme == localName) nameMap) of
    Nothing -> error "Cannot find local name in name map."
    Just entry -> mapCommonName entry

{- these two functions generate commonNames for saturated arguments
   using a name map. -}
sArgWithCommonNameFromMap :: NameMap -> SArgument -> SArgument
sArgWithCommonNameFromMap nameMap arg =
  arg {commonName=nameMapCommonNameFor nameMap (localName arg)}
sArgsWithCommonNamesFromMap :: NameMap -> SArgumentSet -> SArgumentSet
sArgsWithCommonNamesFromMap nameMap =
  map (sArgWithCommonNameFromMap nameMap)



{- Pretty printing for saturated programs -}
instance  Pretty (SExecution) where
  pPrint (SExecution kb gl) = vcat [pPrint kb, pPrint gl]

instance Pretty (SProgram) where
  pPrint (SProgram definitions) = vcat (map pPrint definitions)

instance Pretty (SPredicateDefinition) where
  pPrint (SPredicateDefinition name sargs sexpr) =
    text name <> parens( commaSeparated sargs ) <> text " := " <> (pPrint sexpr)

instance Pretty (SExpression) where
  pPrint (SPredicateCall name sargs) = text name <> parensIfNotEmpty sargs
  pPrint (SProjection sexpr projs) = pPrint sexpr <+> braces (commaSeparated projs)
  pPrint (SAnd exprs sargs) = text "and" <> parens( commaSeparated sargs ) <> brackets( commaSeparated exprs )
  pPrint (SOr exprs sargs) = text "or" <> parens( commaSeparated sargs ) <> brackets( commaSeparated exprs )
  pPrint (SFoldR rec bas args) = text "foldr" <> parens ( commaSeparated args ) <> brackets ( commaSeparated [rec, bas] ) 
  pPrint (SFoldL rec bas args) = text "foldl" <> parens ( commaSeparated args ) <> brackets ( commaSeparated [rec, bas] ) 
  pPrint (SConsList arg vals) = pPrint vals <> text "::" <> braces (pPrint arg) 
  pPrint (SConstant arg val) = pPrint val <> text "::" <> braces (pPrint arg)

instance Pretty (SArgument) where
  pPrint (SArgument common local) = text common

instance Pretty (Value) where
  pPrint (I i) = text (show i)
  pPrint (S s) = quotes $ text s

instance Pretty (NProjectionItem) where
  pPrint (Arg a) = text a
  pPrint (ArgAs a b) = text a <> text "|>" <> text b

