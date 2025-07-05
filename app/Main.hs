module Main where

import Data.Maybe                       (maybeToList)
import System.Environment               (getArgs)

import Quilt.ExampleModes.ThreeModes
import Quilt.ExampleModes.TwoModes
import Quilt.Top

main :: IO ()
main = do
  args <- getArgs
  case args of
    []         -> usage $ Just "Not enough arguments"
    [arg]      -> execute arg Nothing
    [arg,arg2] -> execute arg (Just arg2)
    _
      | "--help" `elem` args -> usage Nothing
      | otherwise -> print "Loading more than 1 module is not yet supported"
  where
    execute _          (Just "--help") = usage Nothing
    execute "--help"   _ = usage Nothing
    execute "ThreeModes" mayFp = runElTopM $ interpreterWithMayFile threeModesProxy mayFp defaultOptions
    execute "TwoModes" mayFp = runElTopM $ interpreterWithMayFile twoModesProxy mayFp defaultOptions
    execute _ _ = usage $ Just "Invalid mode spec"

defaultOptions :: ElTopOptions
defaultOptions = ElTopOptions
  { optionShowType = True
  , optionShowMode = True
  , optionShowEnv = False
  }

usage :: Maybe String -> IO ()
usage err =
  putStrLn
  $ unlines
  $ maybeToList err <>
    [ "quilti <accessibility spec> [<optional module to load>]"
    , ""
    , "Required Arguments:"
    , "  <accessibility spec>"
    , "    Determines which accessibility spec one wants to use."
    , "    Currently we have the following built-in specs:"
    , "    - ThreeModes"
    , "    - TwoModes"
    , "    To use other specs, one can use the code base of this executable as a library"
    , "    and provide their own accessibility spec as an instance of \"ElModeSpec\" typeclass."
    , ""
    , "Optional Arguments:"
    , "  <optional module to load>"
    , "    If provided, interpreter loads the module and then"
    , "    run commands under the definitions in the module."
    , ""
    , "Other Options:"
    , "  --help"
    , "    If this option is there, this message is printed."
    ]
