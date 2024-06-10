{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
module Elevator.Top where

import Control.Monad.Extra        (loopM)
import Control.Monad.State.Strict (StateT, mapStateT, evalStateT)
import Control.Monad.Trans        (MonadTrans (lift))
import Data.Functor.Identity      (runIdentity)
import Data.Proxy                 (Proxy)
import Data.Text                  (Text)
import Data.Text                  qualified as T
import Data.Text.IO               qualified as T
import Elevator.Evaluator
import Elevator.ModeSpec
import Elevator.Parser
import Elevator.PrettyPrinter
import Elevator.Syntax
import Elevator.TypeChecker
import System.Exit                (exitSuccess)
import System.IO                  (hFlush, stdout)

type ElTopM = StateT Integer IO

data ElTopErr m = TypeError (ElTypingError m) | EvalError String
  deriving (Show)

runElTopM :: ElTopM a -> IO a
runElTopM = flip evalStateT 0

interpreter :: (ElModeSpec m) => Proxy m -> ElTopM ()
interpreter (_ :: Proxy m) = interpreterLoop 0 (ElIModule [] [] :: ElIModule m)

interpreterWithFile :: (ElModeSpec m) => Proxy m -> FilePath -> ElTopM ()
interpreterWithFile (_ :: Proxy m) fp = do
  txt <- lift $ T.readFile fp
  case readEitherCompleteFile fp txt of
    Right (premodu :: ElModule m) -> do
      checkRes <- mapStateT (pure . runIdentity) $ fullRunElCheckM $ checkModule premodu
      flippedEither checkRes handleModuleCheckingError $ interpreterLoop 0
    Left err -> lift $ putStrLn $ "Error " <> "<" <> fp <> ">" <> " : " <> err
  where
    handleModuleCheckingError err = lift $ putStrLn  $ "TypeError " <> "<" <> fp <> "> : " <> show err

interpreterLoop :: (ElModeSpec m) => Integer -> ElIModule m -> ElTopM ()
interpreterLoop n modu = do
  lift $ forcePutStr "> "
  l <- lift getMultiLine
  helperLoop l modu
  where
    isTerminationCommand str = not (T.null str) && (T.isPrefixOf str "quit" || T.isPrefixOf str "exit")

    helperLoop (T.uncons -> Just ('@', str)) modu'
      | isTerminationCommand str = lift exitSuccess
      | otherwise = do
          lift $ putStrLn "Unexpected command"
          interpreterLoop (n + 1) modu'
    helperLoop str modu' = do
      case readEitherCompleteCommand ("<line " <> show n <> ">") str of
        Right com -> do
          mayModu'' <- fullCommandRun modu' n com
          case mayModu'' of
            Right modu'' -> interpreterLoop (n + 1) modu''
            Left err     -> do
              lift $ putStrLn $ "Error " <> "<line " <> show n <> "> : " <> show err
              interpreterLoop (n + 1) modu'
        Left err -> do
          lift $ putStrLn $ "Error " <> "<line " <> show n <> "> : " <> err
          interpreterLoop (n + 1) modu'

fullCommandRun :: (ElModeSpec m) => ElIModule m -> Integer -> ElCommand m -> ElTopM (Either (ElTopErr m) (ElIModule m))
fullCommandRun modu _n (ComTop top) = do
  checkRes <- mapStateT (pure . runIdentity) $ fullRunElCheckM $ checkTopUnderModule modu top
  flippedEither checkRes (pure . Left . TypeError) $ \modu' -> lift $ do
    putStrLn $ showPretty 80 top
    pure (Right modu')
fullCommandRun modu _n (ComTerm t) = do
  checkRes <- mapStateT (pure . runIdentity) $ fullRunElCheckM $ inferTypeUnderModule modu t
  flippedEither checkRes (pure . Left . TypeError) $ \(it, ity, k) -> do
    lift $ putStrLn "------ type checking result ------"
    lift $ putStrLn $ showPretty 80 (TmAnn (fromInternal it) (fromInternal ity))
    lift $ putStrLn $ "------ of mode " <> showPrettyMode 80 k <> " ------"
    evalRes <- mapStateT (pure . runIdentity) $ fullRunElEvalM $ evalUnderModule modu it
    flippedEither evalRes (pure . Left . EvalError) $ \(it', env) -> lift $ do
      putStrLn "------ evaluation result ------"
      putStrLn $ showPretty 80 it'
      putStrLn "------ under ------"
      print env
      pure (Right modu)

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

flippedEither :: Either err a -> (err -> b) -> (a -> b) -> b
flippedEither (Left e) fe _  = fe e
flippedEither (Right v) _ fv = fv v
