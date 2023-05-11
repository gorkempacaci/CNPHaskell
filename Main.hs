{-# LANGUAGE OverloadedStrings #-}

module Main where

import CNP




main :: IO ()
main =
  let reversePredicate = PredicateDefinition "reverse" (["as", "folded"|>"bs"] `from` 
        And [
          (FoldL ("cons" // ["head"|>"a", "tail"|>"b", "list"|>"folded"])
                 (Id "b0" "folded"))
         ,IsNil "b0"]
       )
      reverseProgram = Program [reversePredicate]
      reverseGoal = And ["reverse", ConsList "as" [1,2,3,4,5,6,7], ConsList "bs" [7,6,5,4,3,2,1]]
      reverseExecution = Execution reverseProgram reverseGoal
  in print $ solveBool reverseExecution




