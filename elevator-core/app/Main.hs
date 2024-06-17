module Main where

import System.Environment             (getArgs)

import Data.Proxy                     (Proxy (Proxy))
import Elevator.ExampleModes.TwoModes
import Elevator.Top                   (interpreter, runElTopM, interpreterWithFile)

main :: IO ()
main = do
  args <- getArgs
  case args of
    []    -> runElTopM $ interpreter (Proxy :: Proxy TwoModes)
    [arg] -> runElTopM $ interpreterWithFile (Proxy :: Proxy TwoModes) arg
    _     -> print "Loading more than 1 module is not yet supported"
