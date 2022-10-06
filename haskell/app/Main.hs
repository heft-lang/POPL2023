module Main where

import Examples.YieldOut
import Data.List

main :: IO ()
main = putStrLn $ intercalate "\n" $ testExample
