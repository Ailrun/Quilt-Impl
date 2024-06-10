{-# LANGUAGE DerivingStrategies #-}
module Elevator.Evaluator where

import Control.Applicative        (Applicative (liftA2), liftA3)
import Control.Monad.Except       (ExceptT, MonadError (..), runExceptT)
import Control.Monad.State.Strict (MonadState (get), State, StateT (runStateT), modify)
import Control.Monad.Trans        (MonadTrans (lift))
import Data.Foldable              (toList, foldlM)
import Data.HashMap.Strict        (HashMap)
import Data.HashMap.Strict        qualified as HashMap
import Data.List                  (foldl')
import Data.Sequence              (Seq)
import Data.Sequence              qualified as Seq
import Data.Tuple.Extra           (fst3)
import Elevator.ModeSpec
import Elevator.Substitution
import Elevator.Syntax

newtype ElEnv m = ElEnv { getElEnv :: HashMap ElId (Maybe (ElITerm m)) }
  deriving stock Show

evalUnderModule :: (ElModeSpec m) => ElIModule m -> ElITerm m -> ElEvalM m (ElITerm m)
evalUnderModule (ElIModule _imps tops) t = do
  modify (const (buildEnv tops))
  eval t
  where
    buildEnv = ElEnv . foldl' envHelper HashMap.empty
    envHelper envMap (ITopTermDef x _ _ t') = HashMap.insert x (Just t') envMap
    envHelper envMap ITopTypeDef{}          = envMap

checkNormHead :: ElITerm m -> Bool
checkNormHead ITmData{}  = True
checkNormHead ITmTrue    = True
checkNormHead ITmFalse   = True
checkNormHead (ITmInt _) = True
checkNormHead ITmTuple{} = True
checkNormHead ITmSusp{}  = True
checkNormHead ITmStore{} = True
checkNormHead ITmLam{}   = True
checkNormHead ITmTLam{}  = True
checkNormHead _          = False

eval :: (ElModeSpec m) => ElITerm m -> ElEvalM m (ElITerm m)
eval (ITmVar x) = do
  env <- get
  case envLookup x env of
    Just (Just t) -> eval t
    Just Nothing  -> pure $ ITmVar x
    Nothing       -> throwError $ "Variable \"" <> show x <> "\" has no reference in " <> show env
eval (ITmData c cn args) = ITmData c cn <$> traverse eval args
eval ITmTrue = pure ITmTrue
eval ITmFalse = pure ITmFalse
eval (ITmIte t t0 t1) = do
  r <- eval t
  case r of
    ITmTrue   -> eval t0
    ITmFalse  -> eval t1
    _
      | checkNormHead r -> nonBooleanError r
      | otherwise -> pure $ ITmIte r t0 t1
  where
    nonBooleanError r = throwError $ "Non-boolean result from the condition \"" <> show r <> "\""
eval (ITmInt n) = pure $ ITmInt n
eval (ITmBinOp bop t0 t1) = do
  r0 <- eval t0
  r1 <- eval t1
  case (r0, r1) of
    (ITmInt n0, ITmInt n1) -> pure $ computeBop bop n0 n1
    (ITmInt _,  _)
      | checkNormHead r1 -> throwError $ "Non-integer result for the second operand \"" <> show r1 <> "\""
    (_, _)
      | checkNormHead r1 -> throwError $ "Non-integer result for the first operands \"" <> show r0 <> "\""
      | otherwise -> pure $ ITmBinOp bop r0 r1
eval (ITmTuple items) = ITmTuple <$> traverse eval items
eval (ITmMatch m t ty brs) = do
  r <- eval t
  if checkNormHead r
  then do
    b <- firstMatchingBranch brs r
    eval b
  else pure $ ITmMatch m t ty brs
eval (ITmSusp m ctxh t) = do
  (ctxh', t') <- substM2evalM $ freshIContextHatInTerm ctxh t
  envExtend ctxh'
  r <- refineTemplate m t'
  pure $ ITmSusp m ctxh' r
eval (ITmForce h t sub) = do
  r <- eval t
  case r of
    ITmSusp _ ctxh t' -> do
      t'' <- substM2evalM $ applySubstTerm sub (icontextHat2idomain ctxh) t'
      eval t''
    _
      | checkNormHead r -> throwError $ "Non Template result \"" <> show r <> "\" for force"
      | otherwise -> pure $ ITmForce h r sub
eval (ITmStore h t) = ITmStore h <$> eval t
eval (ITmLam x ty t) = pure $ ITmLam x ty t
eval (ITmTLam x ki t) = pure $ ITmTLam x ki t
eval (ITmApp t0 t1) = do
  r0 <- eval t0
  r1 <- eval t1
  case r0 of
    ITmLam pat _ t -> do
      t' <- matching pat r1 t
      eval t'
    _
      | checkNormHead r0 -> throwError $ "Non-function result " <> show r0 <> " for application"
      | otherwise -> pure $ ITmApp r0 r1
eval (ITmTApp t0 ty1) = do
  r0 <- eval t0
  case r0 of
    ITmTLam x _ t -> do
      t' <- substM2evalM $ applySubstTerm (Seq.singleton (ISEType ty1)) (Seq.singleton (x, True)) t
      eval t'
    _
      | checkNormHead r0 -> throwError $ "Non-type-function result \"" <> show r0 <> "\" for application"
      | otherwise -> pure $ ITmTApp r0 ty1

firstMatchingBranch :: (ElModeSpec m) => [ElIBranch m] -> ElITerm m -> ElEvalM m (ElITerm m)
firstMatchingBranch []             _ = throwError "No matching clause"
firstMatchingBranch ((pat, b):brs) t = catchError (matching pat t b) $ \_ -> firstMatchingBranch brs t

matching :: (ElModeSpec m) => ElIPattern m -> ElITerm m -> ElITerm m -> ElEvalM m (ElITerm m)
matching IPatWild             _                    b = pure b
matching (IPatVar x)          tm                   b = do
  (x', b') <- substM2evalM (freshTmVarInTerm x b)
  envInsert x' tm
  pure b'
matching IPatTrue             ITmTrue              b = pure b
matching IPatFalse            ITmFalse             b = pure b
matching (IPatInt n)          (ITmInt n')          b
  | n == n'                                          = pure b
matching (IPatTuple pats)     (ITmTuple items)     b = foldlM (\b' (pat, item) -> matching pat item b') b $ zip pats items
matching (IPatLoad pat)       (ITmStore _ t)       b = matching pat t b
matching (IPatData _ cn pats) (ITmData _ cn' args) b
  | cn == cn'                                        = foldlM (\b' (pat, arg) -> matching pat arg b') b $ zip pats args
matching _                    _                    _ = throwError "Pattern mismatching"

refineTemplate :: (ElModeSpec m) => m -> ElITerm m -> ElEvalM m (ElITerm m)
refineTemplate _ (ITmVar x)            = pure $ ITmVar x
refineTemplate n (ITmData c cn args)   = ITmData c cn <$> traverse (refineTemplate n) args
refineTemplate _ ITmTrue               = pure ITmTrue
refineTemplate _ ITmFalse              = pure ITmFalse
refineTemplate n (ITmIte t t0 t1)      =
  liftA3
    ITmIte
    (refineTemplate n t)
    (refineTemplate n t0)
    (refineTemplate n t1)
refineTemplate _ (ITmInt n)            = pure $ ITmInt n
refineTemplate n (ITmBinOp bop t0 t1)  = do
  liftA2
    (ITmBinOp bop)
    (refineTemplate n t0)
    (refineTemplate n t1)
refineTemplate n (ITmTuple items)      = ITmTuple <$> traverse (refineTemplate n) items
refineTemplate n (ITmMatch h t ty brs) = do
  r <- getScrRes
  ITmMatch h r ty <$> traverse (refineBranchTemplate n) brs
  where
    getScrRes
      | h >=!! n = eval t
      | otherwise = refineTemplate n t
refineTemplate n (ITmSusp m ctxh t)    = do
  (ctxh', t') <- substM2evalM $ freshIContextHatInTerm ctxh t
  envExtend ctxh'
  ITmSusp m ctxh' <$> refineTemplate n t'
refineTemplate n (ITmForce h t sub)
  | h >=!! n                           = do
    r <- eval t
    case r of
      ITmSusp _ ctxh t' -> do
        t'' <- substM2evalM $ applySubstTerm sub (icontextHat2idomain ctxh) t'
        refineTemplate n t''
      _
        | checkNormHead r -> throwError $ "Non Template result \"" <> show r <> "\" for force"
        | otherwise -> pure $ ITmForce h r sub
  | otherwise                          = flip (ITmForce h) sub <$> refineTemplate n t
refineTemplate n (ITmStore h t)
  | h >=!! n                           = ITmStore h <$> eval t
  | otherwise                          = ITmStore h <$> refineTemplate n t
refineTemplate n (ITmLam pat ty t)     = do
  (pat', r) <- refineBranchTemplate n (pat, t)
  pure $ ITmLam pat' ty r
refineTemplate n (ITmTLam x ki t)      = do
  (x', t') <- substM2evalM $ freshTyVarInTerm x t
  ITmTLam x' ki <$> refineTemplate n t'
refineTemplate n (ITmApp t0 t1)        =
  liftA2
    ITmApp
    (refineTemplate n t0)
    (refineTemplate n t1)
refineTemplate n (ITmTApp t0 ty1)      = flip ITmTApp ty1 <$> refineTemplate n t0

refineBranchTemplate :: (ElModeSpec m) => m -> ElIBranch m -> ElEvalM m (ElIBranch m)
refineBranchTemplate n (pat, b) = do
  (pat', b') <- opaqueMatching pat b
  (pat',) <$> refineTemplate n b'

opaqueMatching :: (ElModeSpec m) => ElIPattern m -> ElITerm m -> ElEvalM m (ElIPattern m, ElITerm m)
opaqueMatching pat b = do
  (xs, pat', b') <- substM2evalM $ freshPattern pat b
  envExtendWithIds xs
  pure (pat', b')
--   (x', b') <- substM2evalM (freshTmVarInTerm x b)
--   pure (envEmptyInsert x' env, PatVar x', b')
-- opaqueMatching env (PatTuple pats)  b = (\((env', b'), pats') -> (env', PatTuple pats', b')) <$> mapAccumM (\(env', b') pat -> (\(env'', pat', b'') -> ((env'', b''), pat')) <$> opaqueMatching env' pat b') (env, b) pats
-- opaqueMatching env (PatLoad pat)    b = opaqueMatching env pat b
-- opaqueMatching env (PatData c pats) b = (\((env', b'), pats') -> (env', PatData c pats', b')) <$> mapAccumM (\(env', b') pat -> (\(env'', pat', b'') -> ((env'', b''), pat')) <$> opaqueMatching env' pat b') (env, b) pats
-- opaqueMatching env pat              b = pure (env, pat, b)

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

envInsert :: ElId -> ElITerm m -> ElEvalM m ()
envInsert x t = modify (ElEnv . HashMap.insert x (Just t) . getElEnv)

envEmptyInsert :: ElId -> ElEvalM m ()
envEmptyInsert x = modify (ElEnv . HashMap.insert x Nothing . getElEnv)

envExtend :: ElIContextHat m -> ElEvalM m ()
envExtend ctxh = envExtendWithIds (fmap fst3 ctxh)

envExtendWithIds :: Seq ElId -> ElEvalM m ()
envExtendWithIds xs = modify (ElEnv . HashMap.union (HashMap.fromList . toList $ fmap (, Nothing) xs) . getElEnv)

envLookup :: ElId -> ElEnv m -> Maybe (Maybe (ElITerm m))
envLookup x = HashMap.lookup x . getElEnv

newtype ElEvalM m a = ElEvalM { runElEvalM :: StateT (ElEnv m) (ExceptT String (State Integer)) a }
  deriving newtype (Functor, Applicative, Monad, MonadState (ElEnv m), MonadError String)

substM2evalM :: ElSubstM a -> ElEvalM m a
substM2evalM = ElEvalM . lift . runElSubstM

fullRunElEvalM :: (ElModeSpec m) => ElEvalM m a -> State Integer (Either String (a, ElEnv m))
fullRunElEvalM = runExceptT . flip runStateT (ElEnv HashMap.empty) . runElEvalM
