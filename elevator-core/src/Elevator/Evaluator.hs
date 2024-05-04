{-# LANGUAGE DerivingStrategies #-}
module Elevator.Evaluator where

import Control.Applicative        (Applicative (liftA2), liftA3)
import Control.Monad.Except       (ExceptT, MonadError (..))
import Control.Monad.State.Strict (State)
import Data.Foldable              (toList)
import Data.HashMap.Strict        (HashMap)
import Data.HashMap.Strict        qualified as HashMap
import Data.List                  (foldl')
import Data.Sequence              qualified as Seq
import Elevator.ModeSpec
import Elevator.Substitution      (ElSubstM (..), applySubstTerm, freshTmVarInTerm, freshTyVarInTerm)
import Elevator.Syntax
import Control.Monad (foldM)
import Data.Traversable.Compat (mapAccumM)

newtype ElEnv m = ElEnv { getElEnv :: HashMap ElId (Maybe (ElITerm m)) }
  deriving stock Show

evalUnderModule :: (ElModeSpec m) => ElIModule m -> ElITerm m -> ElEvalM (ElITerm m)
evalUnderModule (ElIModule _imps tops) = eval $ buildEnv tops
  where
    buildEnv = ElEnv . foldl' envHelper HashMap.empty
    envHelper envMap (ITopTermDef x _ _ t) = HashMap.insert x (Just t) envMap
    envHelper envMap ITopTypeDef{}         = envMap

checkNormHead :: ElITerm m -> Bool
checkNormHead ITmTrue    = True
checkNormHead ITmFalse   = True
checkNormHead (ITmInt _) = True
checkNormHead ITmSusp{}  = True
checkNormHead ITmLam{}   = True
checkNormHead ITmTLam{}  = True
checkNormHead _          = False

eval :: (ElModeSpec m) => ElEnv m -> ElITerm m -> ElEvalM (ElITerm m)
eval env (ITmVar x) =
  case envLookup x env of
    Just (Just t) -> eval env t
    Just Nothing  -> pure $ ITmVar x
    Nothing       -> throwError $ "Variable \"" <> show x <> "\"" <> " has no reference"
eval env (ITmData c args) = ITmData c <$> traverse (eval env) args
eval _   ITmTrue = pure ITmTrue
eval _   ITmFalse = pure ITmFalse
eval env (ITmIte t t0 t1) = do
  r <- eval env t
  case r of
    ITmTrue   -> eval env t0
    ITmFalse  -> eval env t1
    _
      | checkNormHead r -> nonBooleanError r
      | otherwise -> pure $ ITmIte r t0 t1
  where
    nonBooleanError r = throwError $ "Non-boolean result from the condition \"" <> show r <> "\""
eval _   (ITmInt n) = pure $ ITmInt n
eval env (ITmBinOp bop t0 t1) = do
  r0 <- eval env t0
  r1 <- eval env t1
  case (r0, r1) of
    (ITmInt n0, ITmInt n1) -> pure $ computeBop bop n0 n1
    (ITmInt _,  _)
      | checkNormHead r1 -> throwError $ "Non-integer result for the second operand \"" <> show r1 <> "\""
    (_, _)
      | checkNormHead r1 -> throwError $ "Non-integer result for the first operands \"" <> show r0 <> "\""
      | otherwise -> pure $ ITmBinOp bop r0 r1
eval env (ITmTuple items) = ITmTuple <$> traverse (eval env) items
eval env (ITmMatch m t ty brs) = do
  r <- eval env t
  if checkNormHead r
  then do
    (env', b) <- firstMatchingBranch env brs t
    eval env' b
  else pure $ ITmMatch m t ty brs
eval env (ITmSusp m ctxh t) = do
  r <- refineTemplate (envExtend ctxh env) m t
  pure $ ITmSusp m ctxh r
eval env (ITmForce h t sub) = do
  r <- eval env t
  case r of
    ITmSusp _ ctxh t' -> do
      t'' <- substM2evalM $ applySubstTerm sub (icontextHat2contextHat ctxh) t'
      eval env t''
    _
      | checkNormHead r -> throwError $ "Non Template result \"" <> show r <> "\" for force"
      | otherwise -> pure $ ITmForce h r sub
eval env (ITmStore h t) = ITmStore h <$> eval env t
eval _   (ITmLam x ty t) = pure $ ITmLam x ty t
eval _   (ITmTLam x ki t) = pure $ ITmTLam x ki t
eval env (ITmApp t0 t1) = do
  r0 <- eval env t0
  r1 <- eval env t1
  case r0 of
    ITmLam pat _ t -> do
      (env', t') <- matching env pat r1 t
      eval env' t'
    _
      | checkNormHead r0 -> throwError $ "Non-function result \"" <> show r0 <> "\" for application"
      | otherwise -> pure $ ITmApp r0 r1
eval env (ITmTApp t0 ty1) = do
  r0 <- eval env t0
  case r0 of
    ITmTLam x _ t -> do
      t' <- substM2evalM $ applySubstTerm (Seq.singleton (ISEType ty1)) (Seq.singleton x) t
      eval env t'
    _
      | checkNormHead r0 -> throwError $ "Non-type-function result \"" <> show r0 <> "\" for application"
      | otherwise -> pure $ ITmTApp r0 ty1

firstMatchingBranch :: (ElModeSpec m) => ElEnv m -> [ElIBranch m] -> ElITerm m -> ElEvalM (ElEnv m, ElITerm m)
firstMatchingBranch _   []             _ = throwError "No matching clause"
firstMatchingBranch env ((pat, b):brs) t = catchError (matching env pat t b) $ \_ -> firstMatchingBranch env brs t

matching :: (ElModeSpec m) => ElEnv m -> ElPattern m -> ElITerm m -> ElITerm m -> ElEvalM (ElEnv m, ElITerm m)
matching env PatWild          _                 b = pure (env, b)
matching env (PatVar x)       tm                b = do
  (x', b') <- substM2evalM (freshTmVarInTerm x b)
  pure (envInsert x' tm env, b')
matching env PatTrue          ITmTrue           b = pure (env, b)
matching env PatFalse         ITmFalse          b = pure (env, b)
matching env (PatInt n)       (ITmInt n')       b
  | n == n'                                       = pure (env, b)
matching env (PatTuple pats)  (ITmTuple items)  b = foldM (\(env', b') (pat, item) -> matching env' pat item b') (env, b) $ zip pats items
matching env (PatLoad pat)    (ITmStore _ t)    b = matching env pat t b
matching env (PatData c pats) (ITmData c' args) b
  | c == c'                                       = foldM (\(env', b') (pat, arg) -> matching env' pat arg b') (env, b) $ zip pats args
matching _   _                _                 _ = throwError "Pattern mismatching"

refineTemplate :: (ElModeSpec m) => ElEnv m -> m -> ElITerm m -> ElEvalM (ElITerm m)
refineTemplate _   _ (ITmVar x)            = pure $ ITmVar x
refineTemplate env n (ITmData c args)      = ITmData c <$> traverse (refineTemplate env n) args
refineTemplate _   _ ITmTrue               = pure ITmTrue
refineTemplate _   _ ITmFalse              = pure ITmFalse
refineTemplate env n (ITmIte t t0 t1)      =
  liftA3
    ITmIte
    (refineTemplate env n t)
    (refineTemplate env n t0)
    (refineTemplate env n t1)
refineTemplate _   _ (ITmInt n)            = pure $ ITmInt n
refineTemplate env n (ITmBinOp bop t0 t1)  = do
  liftA2
    (ITmBinOp bop)
    (refineTemplate env n t0)
    (refineTemplate env n t1)
refineTemplate env n (ITmTuple items)      = ITmTuple <$> traverse (refineTemplate env n) items
refineTemplate env n (ITmMatch h t ty brs) = do
  r <- getScrRes
  ITmMatch h r ty <$> traverse (refineBranchTemplate env n) brs
  where
    getScrRes
      | h >=!! n = eval env t
      | otherwise = refineTemplate env n t
refineTemplate env n (ITmSusp m ctxh t)    = ITmSusp m ctxh <$> refineTemplate (envExtend ctxh env) n t
refineTemplate env n (ITmForce h t sub)
  | h >=!! n                           = eval env (ITmForce h t sub)
  | otherwise                          = flip (ITmForce h) sub <$> refineTemplate env n t
refineTemplate env n (ITmStore h t)
  | h >=!! n                           = ITmStore h <$> eval env t
  | otherwise                          = ITmStore h <$> refineTemplate env n t
refineTemplate env n (ITmLam pat ty t)     = do
  (env', pat', t') <- opaqueMatching env pat t
  ITmLam pat' ty <$> refineTemplate env' n t'
refineTemplate env n (ITmTLam x ki t)      = do
  (x', t') <- substM2evalM $ freshTyVarInTerm x t
  ITmTLam x' ki <$> refineTemplate env n t'
refineTemplate env n (ITmApp t0 t1)        =
  liftA2
    ITmApp
    (refineTemplate env n t0)
    (refineTemplate env n t1)
refineTemplate env n (ITmTApp t0 ty1)      = flip ITmTApp ty1 <$> refineTemplate env n t0

refineBranchTemplate :: (ElModeSpec m) => ElEnv m -> m -> ElIBranch m -> ElEvalM (ElIBranch m)
refineBranchTemplate env n (pat, b) = do
  (env', pat', b') <- opaqueMatching env pat b
  (pat',) <$> refineTemplate env' n b'

opaqueMatching :: (ElModeSpec m) => ElEnv m -> ElPattern m -> ElITerm m -> ElEvalM (ElEnv m, ElPattern m, ElITerm m)
opaqueMatching env (PatVar x)       b = do
  (x', b') <- substM2evalM (freshTmVarInTerm x b)
  pure (envEmptyInsert x' env, PatVar x', b')
opaqueMatching env (PatTuple pats)  b = (\((env', b'), pats') -> (env', PatTuple pats', b')) <$> mapAccumM (\(env', b') pat -> (\(env'', pat', b'') -> ((env'', b''), pat')) <$> opaqueMatching env' pat b') (env, b) pats
opaqueMatching env (PatLoad pat)    b = opaqueMatching env pat b
opaqueMatching env (PatData c pats) b = (\((env', b'), pats') -> (env', PatData c pats', b')) <$> mapAccumM (\(env', b') pat -> (\(env'', pat', b'') -> ((env'', b''), pat')) <$> opaqueMatching env' pat b') (env, b) pats
opaqueMatching env pat              b = pure (env, pat, b)

computeBop :: ElBinOp -> Integer -> Integer -> ElITerm m
computeBop OpAdd n0 n1 = ITmInt (n0 + n1)
computeBop OpSub n0 n1
  | n0 >= n1  = ITmInt (n0 - n1)
  | otherwise = ITmInt 0
computeBop OpMul n0 n1 = ITmInt (n0 * n1)
computeBop OpDiv n0 n1 = ITmInt (n0 `div` n1)
computeBop OpMod n0 n1 = ITmInt (n0 `mod` n1)
computeBop OpEq n0 n1
  | n0 == n1  = ITmTrue
  | otherwise = ITmFalse
computeBop OpNe n0 n1
  | n0 /= n1  = ITmTrue
  | otherwise = ITmFalse
computeBop OpLe n0 n1
  | n0 <= n1  = ITmTrue
  | otherwise = ITmFalse
computeBop OpLt n0 n1
  | n0 < n1   = ITmTrue
  | otherwise = ITmFalse
computeBop OpGe n0 n1
  | n0 >= n1  = ITmTrue
  | otherwise = ITmFalse
computeBop OpGt n0 n1
  | n0 > n1   = ITmTrue
  | otherwise = ITmFalse

envInsert :: ElId -> ElITerm m -> ElEnv m -> ElEnv m
envInsert x t env = ElEnv . HashMap.insert x (Just t) $ getElEnv env

envEmptyInsert :: ElId -> ElEnv m -> ElEnv m
envEmptyInsert x env = ElEnv . HashMap.insert x Nothing $ getElEnv env

envExtend :: ElIContextHat m -> ElEnv m -> ElEnv m
envExtend ctxh env = ElEnv . HashMap.union (HashMap.fromList . toList $ fmap ((, Nothing) . fst) ctxh) $ getElEnv env

envLookup :: ElId -> ElEnv m -> Maybe (Maybe (ElITerm m))
envLookup x = HashMap.lookup x . getElEnv

newtype ElEvalM a = ElEvalM { runElEvalM :: ExceptT String (State Integer) a }
  deriving newtype (Functor, Applicative, Monad, MonadError String)

substM2evalM :: ElSubstM a -> ElEvalM a
substM2evalM (ElSubstM v) = ElEvalM v
