{-# LANGUAGE DeriveAnyClass    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
module Main where

import Control.Monad.Extra (forM_, loopM)
import Data.Hashable       (Hashable)
import Data.Text           (Text)
import Data.Text           qualified as T
import Data.Text.IO        qualified as T
import GHC.Generics        (Generic)
import System.Environment  (getArgs)
import System.Exit         (exitSuccess)
import System.IO           (hFlush, stdout)

-- import Elevator.Evaluator     (eval)
import Elevator.ModeSpec   (ElModeSpec (..))
import Elevator.Parser     (readEitherCompleteCommand, readEitherCompleteFile)
-- import Elevator.PrettyPrinter (prettyMode, prettyType, showDoc, showPretty)
import Elevator.Syntax     (ElCommand (..), ElProgram (..), ElTop (..))
-- import Elevator.TypeChecker   (typeCheckProg, typeCheckProgIncremental,
--                                typeInfer)

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

main :: IO ()
main = do
  args <- getArgs
  forM_ args $ \fp -> do
    txt <- T.readFile fp
    case readEitherCompleteFile fp txt of
      Right (prog :: Elevator.Syntax.ElProgram TwoMode) -> print prog
      Left err -> putStrLn $ "Error " <> "<" <> fp <> ">" <> " : " <> err
  mainLoop 0

mainLoop :: Integer -> IO ()
mainLoop n = do
  forcePutStr "> "
  l <- getMultiLine
  mainFun l
  where
    isTerminationCommand str = not (T.null str) && (T.isPrefixOf str "quit" || T.isPrefixOf str "exit")

    mainFun (T.uncons -> Just ('@', str))
      | isTerminationCommand str = exitSuccess
      | otherwise = do
          putStrLn "Unexpected command"
          mainLoop (n + 1)
    mainFun str = do
      case readEitherCompleteCommand ("<line " <> show n <> ">") str of
        Right (Elevator.Syntax.ComTop (top :: Elevator.Syntax.ElTop TwoMode)) -> print top
        Right (Elevator.Syntax.ComTerm tm) -> print tm
        Left err -> putStrLn $ "Error " <> "<line " <> show n <> "> : " <> err
      mainLoop (n + 1)

getMultiLine :: IO Text
getMultiLine = do
  l <- T.getLine
  case l of
    "@@@" -> do
      flip loopM "" $ \pl -> do
        forcePutStr "... | "
        l'' <- T.getLine
        pure $ case l'' of
          "@@@" -> Right pl
          _     -> Left $ pl <> "\n" <> l''
    _ -> pure l

forcePutStr :: String -> IO ()
forcePutStr s = putStr s >> hFlush stdout

-- main :: IO ()
-- main = do
--   args <- getArgs
--   itops <- concatForM args $ \fp -> do
--     txt <- T.readFile fp
--     case fullFileParse fp txt of
--       Right prog ->
--         case typeCheckProg prog of
--           Right (ElIProgram itops) -> pure itops
--           Left err -> do
--             putStrLn $ "Error " <> "<" <> fp <> ">" <> " : " <> err
--             pure []
--       Left err -> do
--         putStrLn $ "Error " <> "<" <> fp <> ">" <> " : " <> err
--         pure []
--   mainLoop (ElIProgram itops) 0

-- mainLoop :: ElIProgram TwoMode -> Integer -> IO ()
-- mainLoop iprog@(ElIProgram itops) n = do
--   putStr "> "
--   hFlush stdout
--   l <- T.getLine
--   if l == "@"
--   then do
--     pl <- flip loopM "" $ \pl -> do
--       l'' <- T.getLine
--       pure
--         $ if l'' == "@"
--           then Right pl
--           else Left $ pl <> "\n" <> l''
--     mainFun pl
--   else mainFun l
--   where
--     mainFun str =
--       case fullCommandParse ("<line " <> show n <> ">") str of
--         Right (Left (top@(ElDef x _ _ _) :: ElTop TwoMode)) ->
--           case typeCheckProgIncremental iprog top of
--             Right itop -> do
--               putStrLn $ "Top-level definition " <> show x <> " is defined"
--               mainLoop (ElIProgram $ itops <> [itop]) (n + 1)
--             Left err -> do
--               putStrLn $ "Error " <> "<line " <> show n <> "> : " <> err
--               mainLoop iprog (n + 1)
--         Right (Right tm) -> do
--           case typeInfer iprog MProg tm of
--             Right (itm, ty) -> do
--               case eval iprog MProg itm of
--                 Right r -> do
--                   putStrLn $ showPretty 80 r
--                   putStrLn . showDoc 80 $ "  : " <> prettyMode MProg <> " " <> prettyType 0 ty
--                 Left err -> putStrLn $ "Error " <> "<line " <> show n <> "> : " <> err
--             Left err -> putStrLn $ "Error " <> "<line " <> show n <> "> : " <> err
--           mainLoop iprog (n + 1)
--         Left err -> do
--           putStrLn $ "Error " <> "<line " <> show n <> "> : " <> err
--           mainLoop iprog (n + 1)
