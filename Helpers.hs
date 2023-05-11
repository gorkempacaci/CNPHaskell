{-|
Module: Helpers

Shared helper functions useful for multiple modules but do not strictly belong to a specific module.
-}
module Helpers where

import Data.List (intercalate, intersperse, nub, union, (\\))
import Text.PrettyPrint.HughesPJClass
import Data.Char(toUpper)



-- | returns true if the set contains no duplicate items.
isDistinctSet :: (Eq a) => [a] -> Bool
isDistinctSet items = length (nub items) == length items

-- | returns true if the two lists are equal as sets.
setEquals :: (Eq a) => [a] -> [a] -> Bool
setEquals xs ys = null (xs \\ ys) && null (ys \\ xs)

-- | puts the given separator between every item in the list
--   and folds with the given glue (<+> or <>)
prettyWithInbetween :: (Pretty a) => Doc -> (Doc -> Doc -> Doc) -> [a] -> Doc
prettyWithInbetween separator glue docs =
  foldl glue empty (intersperse separator (map pPrint docs))

-- | concatenates the items with commas in between, and returns a Doc.
commaSeparated :: (Pretty a) => [a] -> Doc
commaSeparated = prettyWithInbetween comma (<>)

-- | places parantheses (items separated with commas) if the list isn't empty.
parensIfNotEmpty :: (Pretty a) => [a] -> Doc
parensIfNotEmpty items = if length items == 0 then empty else parens(commaSeparated items)

-- | places indices for every object in a list, returns a list of tuples (o, i)
withIndex :: [a] -> [(a, Int)]
withIndex xs = zipWith (\a b->(a, b)) xs [1..]

-- | places newline (\n) characters between every string in a list and returns one string.
multilineStr :: [String] -> String
multilineStr = intercalate "\n"

-- | converts a string to uppercase.
toUpperStr :: String -> String
toUpperStr = map toUpper


