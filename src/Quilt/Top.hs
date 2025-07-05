{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns      #-}
module Quilt.Top where

import Control.Exception          (IOException, catch)
import Control.Monad.Extra        (loopM, when)
import Control.Monad.State.Strict (StateT, evalStateT, mapStateT)
import Control.Monad.Trans        (MonadTrans (lift))
import Data.Functor.Identity      (runIdentity)
import Data.Proxy                 (Proxy)
import Data.Text                  (Text)
import Data.Text                  qualified as T
import Data.Text.IO               qualified as T
import System.Exit                (exitFailure, exitSuccess)
import System.IO                  (hFlush, stdout)
import System.IO.Error            (isEOFError)

import Quilt.Evaluator
import Quilt.ModeSpec
import Quilt.Parser
import Quilt.PrettyPrinter
import Quilt.Syntax
import Quilt.TypeChecker

type ElTopM = StateT Integer IO

data ElTopErr m = TypeError (ElTypingError m) | EvalError (ElEvalError m)
  deriving (Show)

data ElTopOptions
  = ElTopOptions
    { optionShowType :: Bool
    , optionShowMode :: Bool
    , optionShowEnv  :: Bool
    }

runElTopM :: ElTopM a -> IO a
runElTopM = flip evalStateT 0

interpreterWithMayFile :: (ElModeSpec m) => Proxy m -> Maybe FilePath -> ElTopOptions -> ElTopM ()
interpreterWithMayFile proxy Nothing   = interpreter proxy
interpreterWithMayFile proxy (Just fp) = interpreterWithFile proxy fp

interpreter :: (ElModeSpec m) => Proxy m -> ElTopOptions -> ElTopM ()
interpreter (_ :: Proxy m) opt = interpreterLoop opt 0 (ElIModule [] [] :: ElIModule m)

interpreterWithFile :: (ElModeSpec m) => Proxy m -> FilePath -> ElTopOptions -> ElTopM ()
interpreterWithFile (_ :: Proxy m) fp opt = do
  txt <- lift $ T.readFile fp
  case readEitherCompleteFile fp txt of
    Right (premodu :: ElModule m) -> do
      checkRes <- mapStateT (pure . runIdentity) $ fullRunElCheckM $ checkModule premodu
      flippedEither checkRes handleModuleCheckingError $ interpreterLoop opt 0
    Left err -> lift $ putStrLn $ "ParseError <" <> fp <> ">:\n\n" <> unlines (("  " <>) <$> lines err)
  where
    handleModuleCheckingError te = lift $ putStrLn $ showPrettyError 80 Nothing te

interpreterLoop :: (ElModeSpec m) => ElTopOptions -> Integer -> ElIModule m -> ElTopM ()
interpreterLoop opt n modu = do
  lift $ forcePutStr "> "
  l <- lift $ catch getMultiLine ioExceptionHandler
  helperLoop l modu
  where
    isTerminationCommand str = not (T.null str) && (T.isPrefixOf str "quit" || T.isPrefixOf str "exit")

    helperLoop (T.uncons -> Just ('@', str)) modu'
      | isTerminationCommand str = lift exitSuccess
      | otherwise = do
          lift $ putStrLn "Unexpected command"
          interpreterLoop opt (n + 1) modu'
    helperLoop str modu' = do
      case readEitherCompleteCommand ("<interactive command " <> show n <> ">") str of
        Right com -> do
          mayModu'' <- fullCommandRun opt modu' n com
          case mayModu'' of
            Right modu'' -> interpreterLoop opt (n + 1) modu''
            Left err     -> do
              lift $ putStrLn $ showError n err
              interpreterLoop opt (n + 1) modu'
        Left err -> do
          lift $ putStrLn $ "ParseError <interactive command " <> show n <> ">:\n\n" <> unlines (("  " <>) <$> lines err)
          interpreterLoop opt (n + 1) modu'

    showError ln (TypeError te) = showPrettyError 80 (Just ln) te
    showError ln (EvalError ee) = showPrettyError 80 (Just ln) ee

    ioExceptionHandler :: IOException -> IO Text
    ioExceptionHandler e = do
      if isEOFError e
      then putChar '\n'
      else print e
      exitFailure

fullCommandRun :: (ElModeSpec m) => ElTopOptions -> ElIModule m -> Integer -> ElCommand m -> ElTopM (Either (ElTopErr m) (ElIModule m))
fullCommandRun _   modu _n (ComTop top) = do
  checkRes <- mapStateT (pure . runIdentity) $ fullRunElCheckM $ checkTopUnderModule modu top
  flippedEither checkRes (pure . Left . TypeError) $ \modu' -> lift $ do
    putStrLn $ showPretty 80 top
    pure (Right modu')
fullCommandRun opt modu _n (ComTerm t) = do
  checkRes <- mapStateT (pure . runIdentity) $ fullRunElCheckM $ inferTypeUnderModule modu t
  flippedEither checkRes (pure . Left . TypeError) $ \(it, ity, k) -> do
    when (optionShowType opt) $ do
      lift $ putStrLn "------ type checking result ------"
      lift $ putStrLn $ showPretty 80 (TmAnn (fromInternal it) (fromInternal ity))
    when (optionShowMode opt) $ do
      lift $ putStrLn $ "------ of mode " <> showPrettyMode 80 k <> " ------"
    evalRes <- mapStateT (pure . runIdentity) $ fullRunElEvalM $ evalUnderModule modu it
    flippedEither evalRes (pure . Left . EvalError) $ \(it', (env, _)) -> lift $ do
      putStrLn "------ evaluation result ------"
      putStrLn $ showPretty 80 it'
      when (optionShowEnv opt) $ do
        putStrLn "------ under ------"
        putStrLn $ showPrettyEnv 80 env
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
