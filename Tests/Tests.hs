{-# LANGUAGE OverloadedStrings #-}


module Main where

import System.Exit (exitFailure, exitSuccess)

import Tests.Flattening
import Tests.Unification
import Tests.Shared
import Tests.Resolution
import Tests.Solver
import Tests.Misc

import Test.HUnit

allTests = TestList [helpersTests
                    ,saturationTests
                    ,validationTests
                    ,cnfTests
                    ,unificationTests
                    ,resolutionTests
                    ,solverTests]


main :: IO Counts
main = runTestTT allTests



