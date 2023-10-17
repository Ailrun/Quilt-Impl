{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Data.Hashable          (Hashable)
import Data.Text.IO           qualified as T
import Elevator.Evaluator     (eval)
import Elevator.ModeSpec      (ElModeSpec (..))
import Elevator.Parser        (fullParse)
import Elevator.PrettyPrinter (prettyMode, prettyTerm, prettyType)
import Elevator.Syntax        (ElProgram (..), ElTop (..))
import Elevator.TypeChecker   (typeCheckProgIncremental, typeInfer)
import GHC.Generics           (Generic)
import System.IO              (hFlush, stdout)

data TwoMode = MCode | MProg
  deriving (Eq, Show, Generic, Hashable)

instance ElModeSpec TwoMode where
  showMode MCode = "c"
  showMode MProg = "p"

  readModeEither "c" = Right MCode
  readModeEither "p" = Right MProg
  readModeEither _   = Left "Should be eitehr c or p"

  MProg <=!! MCode = True
  m     <=!! n     = m == n

  modeSt MProg _ = True
  modeSt MCode _ = True

  modeOp MProg _ = True
  modeOp MCode _ = True

mainLoop :: ElProgram TwoMode -> Integer -> IO ()
mainLoop prog@(ElProgram tops) n = do
  putStr "> "
  hFlush stdout
  l <- T.getLine
  if l == "@"
  then do
    l' <- T.getContents
    mainFun l'
  else mainFun l
  where
    mainFun str =
      case fullParse ("<line " <> show n <> ">") str of
        Right (Left (top@(ElDef x _ _ _) :: ElTop TwoMode)) ->
          case typeCheckProgIncremental prog top of
            Right () -> do
              putStrLn $ "Top-level definition " <> show x <> " is defined"
              mainLoop (ElProgram $ tops <> [top]) (n + 1)
            Left err -> do
              putStrLn $ "Error " <> "<line " <> show n <> " : " <> err
              mainLoop prog (n + 1)
        Right (Right tm) -> do
          case typeInfer prog MProg tm of
            Right ty -> do
              case eval prog MProg tm of
                Right r -> do
                  putStrLn $ show (prettyTerm 0 r) <> " : " <> show (prettyMode MProg) <> " " <> show (prettyType 0 ty)
                Left err -> putStrLn $ "Error " <> "<line " <> show n <> " : " <> err
            Left err -> putStrLn $ "Error " <> "<line " <> show n <> " : " <> err
          mainLoop prog (n + 1)
        Left err -> do
          putStrLn $ "Error " <> "<line " <> show n <> " : " <> err
          mainLoop prog (n + 1)

main :: IO ()
main = mainLoop (ElProgram []) 0
