{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import Control.Monad.Extra    (concatForM, loopM)
import Data.Hashable          (Hashable)
import Data.Text.IO           qualified as T
import Elevator.Evaluator     (eval)
import Elevator.ModeSpec      (ElModeSpec (..))
import Elevator.Parser        (fullCommandParse, fullFileParse)
import Elevator.PrettyPrinter (prettyMode, prettyType, showDoc, showPretty)
import Elevator.Syntax        (ElIProgram (..), ElTop (..))
import Elevator.TypeChecker   (typeCheckProg, typeCheckProgIncremental,
                               typeInfer)
import GHC.Generics           (Generic)
import System.Environment     (getArgs)
import System.IO              (hFlush, stdout)

data TwoMode = MCode | MProg
  deriving (Eq, Show, Generic, Hashable)

instance ElModeSpec TwoMode where
  showMode MCode = "c"
  showMode MProg = "p"

  readModeEither "c" = Right MCode
  readModeEither "p" = Right MProg
  readModeEither _   = Left "Should be either c or p"

  MProg <=!! MCode = True
  m     <=!! n     = m == n

  modeSt MProg _ = True
  modeSt MCode _ = True

  modeOp MProg _ = True
  modeOp MCode _ = True

mainLoop :: ElIProgram TwoMode -> Integer -> IO ()
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
        Right (Left (top@(ElDef x _ _ _) :: ElTop TwoMode)) ->
          case typeCheckProgIncremental iprog top of
            Right itop -> do
              putStrLn $ "Top-level definition " <> show x <> " is defined"
              mainLoop (ElIProgram $ itops <> [itop]) (n + 1)
            Left err -> do
              putStrLn $ "Error " <> "<line " <> show n <> "> : " <> err
              mainLoop iprog (n + 1)
        Right (Right tm) -> do
          case typeInfer iprog MProg tm of
            Right (itm, ty) -> do
              case eval iprog MProg itm of
                Right r -> do
                  putStrLn $ showPretty 80 r
                  putStrLn . showDoc 80 $ "  : " <> prettyMode MProg <> " " <> prettyType 0 ty
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
        case typeCheckProg prog of
          Right (ElIProgram itops) -> pure itops
          Left err -> do
            putStrLn $ "Error " <> "<" <> fp <> ">" <> " : " <> err
            pure []
      Left err -> do
        putStrLn $ "Error " <> "<" <> fp <> ">" <> " : " <> err
        pure []
  mainLoop (ElIProgram itops) 0
