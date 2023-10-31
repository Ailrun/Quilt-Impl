{-# LANGUAGE OverloadedStrings #-}
module Main where

import           Control.Monad.Extra              (concatForM, loopM)
import qualified Data.Text.IO                     as T
import           Elevator.Evaluator               (eval)
import           Elevator.PrettyPrinter           (showDoc, showPretty)
import           Elevator.Syntax                  (ElIProgram (..))
import           Elevator.TypeChecker             (typeCheckProg,
                                                   typeCheckProgIncremental,
                                                   typeInfer)
import           ElevatorExt.Linear.Compile       (compileProg, compileTerm,
                                                   compileTop, decompileTerm,
                                                   decompileType)
import           ElevatorExt.Linear.ModeSpec      (Mode (..))
import           ElevatorExt.Linear.Parser        (fullCommandParse,
                                                   fullFileParse)
import           ElevatorExt.Linear.PrettyPrinter (prettyType)
import           ElevatorExt.Linear.Syntax        (ElxTop (..))
import           System.Environment               (getArgs)
import           System.IO                        (hFlush, stdout)

mainLoop :: ElIProgram Mode -> Integer -> IO ()
mainLoop iprog@(ElIProgram itops) n = do
  putStr "> "
  hFlush stdout
  l <- T.getLine
  if l == "@"
  then do
    pl <- flip loopM "" $ \pl -> do
      l'' <- T.getLine
      pure
        $ if l'' == "@"
          then Right pl
          else Left $ pl <> "\n" <> l''
    mainFun pl
  else mainFun l
  where
    mainFun str =
      case fullCommandParse ("<line " <> show n <> ">") str of
        Right (Left top@(ElxDef x _ _)) ->
          case typeCheckProgIncremental iprog (compileTop top) of
            Right itop -> do
              putStrLn $ "Top-level definition " <> show x <> " is defined"
              mainLoop (ElIProgram $ itops <> [itop]) (n + 1)
            Left err -> do
              putStrLn $ "Error " <> "<line " <> show n <> "> : " <> err
              mainLoop iprog (n + 1)
        Right (Right tm) -> do
          case typeInfer iprog MLine (compileTerm tm) of
            Right (itm, ty) -> do
              case eval iprog MLine itm of
                Right r -> do
                  putStrLn $ showPretty 80 (decompileTerm r)
                  putStrLn . showDoc 80 $ "  : " <>  prettyType 0 (decompileType ty)
                Left err -> putStrLn $ "Error " <> "<line " <> show n <> "> : " <> err
            Left err -> putStrLn $ "Error " <> "<line " <> show n <> "> : " <> err
          mainLoop iprog (n + 1)
        Left err -> do
          putStrLn $ "Error " <> "<line " <> show n <> "> : " <> err
          mainLoop iprog (n + 1)

main :: IO ()
main = do
  args <- getArgs
  itops <- concatForM args $ \fp -> do
    txt <- T.readFile fp
    case fullFileParse fp txt of
      Right prog ->
        case typeCheckProg (compileProg prog) of
          Right (ElIProgram itops) -> pure itops
          Left err -> do
            putStrLn $ "Error " <> "<" <> fp <> ">" <> " : " <> err
            pure []
      Left err -> do
        putStrLn $ "Error " <> "<" <> fp <> ">" <> " : " <> err
        pure []
  mainLoop (ElIProgram itops) 0
