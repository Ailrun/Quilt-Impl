module Main where

import System.Environment                  (getArgs)

import Data.Proxy                          (Proxy (Proxy))
import Elevator.ExampleModes.InfoFlowModes
import Elevator.ExampleModes.LinMeta
import Elevator.ExampleModes.TwoModes
import Elevator.Top                        (interpreter, interpreterWithFile,
                                            runElTopM)
import Data.Maybe (maybeToList)

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
    execute "TwoModes" Nothing = runElTopM $ interpreter (Proxy :: Proxy TwoModes)
    execute "LinMeta" Nothing = runElTopM $ interpreter (Proxy :: Proxy LinMeta)
    execute "InfoFlowModes" Nothing = runElTopM $ interpreter (Proxy :: Proxy InfoFlowModes)
    execute _          (Just "--help") = usage Nothing
    execute "TwoModes" (Just fp) = runElTopM $ interpreterWithFile (Proxy :: Proxy TwoModes) fp
    execute "LinMeta" (Just fp) = runElTopM $ interpreterWithFile (Proxy :: Proxy LinMeta) fp
    execute "InfoFlowModes" (Just fp) = runElTopM $ interpreterWithFile (Proxy :: Proxy InfoFlowModes) fp
    execute "--help" _ = usage Nothing
    execute _ _ = usage $ Just "Invalid mode spec"

usage :: Maybe String -> IO ()
usage err =
  putStrLn
  $ unlines
  $ maybeToList err <>
    [ "elevatori <mode spec> [<optional module to load>]"
    , ""
    , "Required Arguments:"
    , "  <mode spec>"
    , "    Determines which mode spec one wants to use."
    , "    Currently it can be one of"
    , "    - TwoModes"
    , "    - LinMeta"
    , "    - InfoFlowModes"
    , "    To use other modes, one can use the code base of this executable as a library"
    , "    and provide their own mode spec."
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
