{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedLists    #-}
module Quilt.Evaluator where

import Control.Applicative        (Applicative (liftA2), liftA3)
import Control.Monad.Except       (ExceptT, MonadError (..), mapExceptT,
                                   runExceptT)
import Control.Monad.State.Strict (MonadState (get), State, StateT (runStateT),
                                   modify)
import Control.Monad.Trans        (MonadTrans (lift))
import Data.Bifunctor             (first, second)
import Data.Foldable              (foldlM, toList)
import Data.HashMap.Strict        (HashMap)
import Data.HashMap.Strict        qualified as HashMap
import Data.List                  (foldl')
import Data.Sequence              (Seq (..))
import Data.Tuple.Extra           (fst3)
import Data.Vector                (Vector)
import Data.Vector                qualified as Vector

import Quilt.ModeSpec
import Quilt.Substitution
import Quilt.Syntax

newtype ElEnv m = ElEnv { getElEnv :: HashMap ElId (Maybe (ElITerm m)) }
  deriving stock Show

newtype ElHeap m = ElHeap { getElHeap :: (Integer, HashMap Integer (Vector (ElITerm m))) }
  deriving stock Show

evalUnderModule :: (ElModeSpec m) => ElIModule m -> ElITerm m -> ElEvalM m (ElITerm m)
evalUnderModule (ElIModule _imps tops) t = do
  modifyEnv (const (buildEnv tops))
  eval t
  where
    buildEnv = ElEnv . foldl' envHelper HashMap.empty
    envHelper envMap (ITopTermDef x _ _ t') = HashMap.insert x (Just t') envMap
    envHelper envMap ITopTypeDef{}          = envMap

checkNormHead :: ElITerm m -> Bool
checkNormHead ITmData{}     = True
checkNormHead ITmArrayTag{} = True
checkNormHead ITmTrue       = True
checkNormHead ITmFalse      = True
checkNormHead (ITmInt _)    = True
checkNormHead ITmTuple{}    = True
checkNormHead ITmSusp{}     = True
checkNormHead ITmStore{}    = True
checkNormHead ITmLam{}      = True
checkNormHead ITmTLam{}     = True
checkNormHead _             = False

eval :: (ElModeSpec m) => ElITerm m -> ElEvalM m (ElITerm m)
eval (ITmVar x) = do
  env <- getEnv
  case envLookup x env of
    Just (Just t) -> eval t
    Just Nothing  -> pure $ ITmVar x
    Nothing       -> throwError $ EEVariableNotInEnv x env -- "Variable \"" <> show x <> "\" has no reference in " <> show env
eval (ITmBuiltIn bi) = evalBuiltIn bi []
eval tm@(ITmArrayTag _) = pure tm
eval (ITmData c cn args) = ITmData c cn <$> traverse eval args
eval tm@ITmTrue = pure tm
eval tm@ITmFalse = pure tm
eval (ITmIte t t0 t1) = do
  r <- eval t
  case r of
    ITmTrue   -> eval t0
    ITmFalse  -> eval t1
    _
      | checkNormHead r -> nonBooleanError r
      | otherwise -> pure $ ITmIte r t0 t1
  where
    nonBooleanError = throwError . EENonBoolean -- "Non-boolean result from the condition \"" <> show r <> "\""
eval tm@(ITmInt _) = pure tm
eval (ITmBinOp bop t0 t1) = do
  r0 <- eval t0
  r1 <- eval t1
  case (r0, r1) of
    (ITmInt n0, ITmInt n1) -> pure $ computeBop bop n0 n1
    (ITmInt _,  _)
      | checkNormHead r1 -> throwError $ EENonInteger r1 "the second operand" -- "Non-integer result for the second operand \"" <> show r1 <> "\""
    (_, _)
      | checkNormHead r0 -> throwError $ EENonInteger r0 "the first operand" -- "Non-integer result for the first operands \"" <> show r0 <> "\""
      | otherwise -> pure $ ITmBinOp bop r0 r1
eval (ITmTuple items) = ITmTuple <$> traverse eval items
eval (ITmMatch m t ty brs) = do
  r <- eval t
  if checkNormHead r
  then do
    b <- firstMatchingBranch brs r
    eval b
  else pure $ ITmMatch m r ty brs
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
      | checkNormHead r -> throwError $ EENonTemplate r -- "Non Template result \"" <> show r <> "\" for force"
      | otherwise -> pure $ ITmForce h r sub
eval (ITmStore h t) = ITmStore h <$> eval t
eval tm@ITmLam{} = pure tm
eval tm@ITmTLam{} = pure tm
eval t
  | Just (bi, spine) <- findBuiltInSpine t = evalBuiltIn bi spine
eval (ITmApp t0 t1) = do
  r0 <- eval t0
  r1 <- eval t1
  case r0 of
    ITmLam pat _ t -> do
      t' <- matching pat r1 t
      eval t'
    _
      | checkNormHead r0 -> throwError $ EENonFunction r0 -- "Non-function result " <> show r0 <> " for application"
      | otherwise -> pure $ ITmApp r0 r1
eval (ITmTApp t0 ty1) = do
  r0 <- eval t0
  case r0 of
    ITmTLam x _ t -> do
      t' <- substM2evalM $ applySubstTerm [ISEType ty1] [(x, True)] t
      eval t'
    _
      | checkNormHead r0 -> throwError $ EENonTypeFunction r0 -- "Non-type-function result \"" <> show r0 <> "\" for application"
      | otherwise -> pure $ ITmTApp r0 ty1

firstMatchingBranch :: (ElModeSpec m) => [ElIBranch m] -> ElITerm m -> ElEvalM m (ElITerm m)
firstMatchingBranch []             t = throwError $ EENoMatchingClause t
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
matching pat                  t                    _ = throwError $ EESinglePatternMismatch pat t

findBuiltInSpine :: ElITerm m -> Maybe (ElBuiltIn, ElISubst m)
findBuiltInSpine (ITmApp t0 t1)  = fmap (:|> ISETerm t1) <$> findBuiltInSpine t0
findBuiltInSpine (ITmTApp t0 k1) = fmap (:|> ISEType k1) <$> findBuiltInSpine t0
findBuiltInSpine (ITmBuiltIn bi) = pure (bi, [])
findBuiltInSpine _               = Nothing

evalBuiltIn :: (ElModeSpec m) => ElBuiltIn -> ElISubst m -> ElEvalM m (ElITerm m)
evalBuiltIn BIWithAlloc [ISEType ty0, ISEType ty1, ISETerm t0, ISETerm t1, ISETerm t2] = do
  r0 <- eval t0
  r1 <- eval t1
  r2 <- eval t2
  case r0 of
    ITmInt n -> do
      tag <- heapAllocArray (fromInteger n) r1
      r <- eval (ITmApp r2 (ITmArrayTag tag))
      case r of
        ITmTuple [_, v] -> v <$ heapDeleteArrayOf tag
        _
          | checkNormHead r -> throwError $ EEInvalidArgumentOfBuiltIn BIWithAlloc r "the callback"
          | otherwise       -> pure r
    _
      | checkNormHead r0 -> throwError $ EEInvalidArgumentOfBuiltIn BIWithAlloc r0 "the size argument"
      | otherwise        -> pure $ buildBuiltInSpine BIWithAlloc [ISEType ty0, ISEType ty1, ISETerm r0, ISETerm r1, ISETerm r2]
evalBuiltIn BIWithAlloc spine                                                          = throwError $ EEInvalidCallForBuiltIn BIWithAlloc spine
evalBuiltIn BIWrite     [ISEType ty0, ISETerm t0, ISETerm t1, ISETerm t2]              = do
  r0 <- eval t0
  r1 <- eval t1
  r2 <- eval t2
  case r0 of
    ITmInt n ->
      case r2 of
        ITmArrayTag tag -> do
          heapModifyArray tag (`Vector.update` [(fromInteger n, r1)])
          pure r2
        _
          | checkNormHead r2 -> throwError $ EEInvalidArgumentOfBuiltIn BIWrite r2 "the array argument"
          | otherwise        -> pure $ buildBuiltInSpine BIWithAlloc [ISEType ty0, ISETerm r0, ISETerm r1, ISETerm r2]
    _
      | checkNormHead r0 -> throwError $ EEInvalidArgumentOfBuiltIn BIWrite r0 "the index argument"
      | otherwise        -> pure $ buildBuiltInSpine BIWithAlloc [ISEType ty0, ISETerm r0, ISETerm r1, ISETerm r2]
evalBuiltIn BIWrite     spine                                                          = throwError $ EEInvalidCallForBuiltIn BIWrite spine
evalBuiltIn BIRead      [ISEType ty0, ISETerm t0, ISETerm t1]                          = do
  r0 <- eval t0
  r1 <- eval t1
  case r0 of
    ITmInt n ->
      case r1 of
        ITmArrayTag tag -> do
          array <- heapGetArray tag
          pure $ ITmTuple [array Vector.! fromInteger n, r1]
        _
          | checkNormHead r1 -> throwError $ EEInvalidArgumentOfBuiltIn BIRead r1 "the array argument"
          | otherwise        -> pure $ buildBuiltInSpine BIWithAlloc [ISEType ty0, ISETerm r0, ISETerm r1]
    _
      | checkNormHead r0 -> throwError $ EEInvalidArgumentOfBuiltIn BIRead r0 "the index argument"
      | otherwise        -> pure $ buildBuiltInSpine BIWithAlloc [ISEType ty0, ISETerm r0, ISETerm r1]
evalBuiltIn BIRead      spine                                                          = throwError $ EEInvalidCallForBuiltIn BIRead spine

buildBuiltInSpine :: ElBuiltIn -> ElISubst m -> ElITerm m
buildBuiltInSpine bi = foldl app (ITmBuiltIn bi)
  where
    app t0 (ISETerm t1)  = ITmApp t0 t1
    app t0 (ISEType ty1) = ITmTApp t0 ty1

refineTemplate :: (ElModeSpec m) => m -> ElITerm m -> ElEvalM m (ElITerm m)
refineTemplate _ tm@(ITmVar _)         = pure tm
refineTemplate _ tm@(ITmBuiltIn _)     = pure tm
refineTemplate _ tm@(ITmArrayTag _)    = pure tm
refineTemplate n (ITmData c cn args)   = ITmData c cn <$> traverse (refineTemplate n) args
refineTemplate _ tm@ITmTrue            = pure tm
refineTemplate _ tm@ITmFalse           = pure tm
refineTemplate n (ITmIte t t0 t1)      =
  liftA3
    ITmIte
    (refineTemplate n t)
    (refineTemplate n t0)
    (refineTemplate n t1)
refineTemplate _ tm@(ITmInt _)         = pure tm
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
        | checkNormHead r -> throwError $ EENonTemplate r -- "Non Template result \"" <> show r <> "\" for force"
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

getEnv :: ElEvalM m (ElEnv m)
getEnv = fst <$> get

modifyEnv :: (ElEnv m -> ElEnv m) -> ElEvalM m ()
modifyEnv = modify . first

getHeap :: ElEvalM m (ElHeap m)
getHeap = snd <$> get

modifyHeap :: (ElHeap m -> ElHeap m) -> ElEvalM m ()
modifyHeap = modify . second

heapAllocArray :: Int -> ElITerm m -> ElEvalM m Integer
heapAllocArray n a = do
  modifyHeap (\(ElHeap (nid, h)) -> ElHeap (succ nid, HashMap.insert nid (Vector.replicate n a) h))
  ElHeap (snid, _) <- getHeap
  pure (snid - 1)

heapGetArray :: Integer -> ElEvalM m (Vector (ElITerm m))
heapGetArray tag = do
  ElHeap (_, h) <- getHeap
  case HashMap.lookup tag h of
    Just array -> pure array
    Nothing    -> throwError $ EEInvalidHeapLoc tag -- "Invalid heap location " <> show tag

heapModifyArray :: Integer -> (Vector (ElITerm m) -> Vector (ElITerm m)) -> ElEvalM m ()
heapModifyArray tag f = modifyHeap (\(ElHeap (nid, h)) -> ElHeap (nid, HashMap.adjust f tag h))

heapDeleteArrayOf :: Integer -> ElEvalM m ()
heapDeleteArrayOf tag = modifyHeap (\(ElHeap (nid, h)) -> ElHeap (nid, HashMap.delete tag h))

envInsert :: ElId -> ElITerm m -> ElEvalM m ()
envInsert x t = modifyEnv (ElEnv . HashMap.insert x (Just t) . getElEnv)

envEmptyInsert :: ElId -> ElEvalM m ()
envEmptyInsert x = modifyEnv (ElEnv . HashMap.insert x Nothing . getElEnv)

envExtend :: ElIContextHat m -> ElEvalM m ()
envExtend ctxh = envExtendWithIds (fmap fst3 ctxh)

envExtendWithIds :: Seq ElId -> ElEvalM m ()
envExtendWithIds xs = modifyEnv (ElEnv . HashMap.union (HashMap.fromList . toList $ fmap (, Nothing) xs) . getElEnv)

envLookup :: ElId -> ElEnv m -> Maybe (Maybe (ElITerm m))
envLookup x = HashMap.lookup x . getElEnv

newtype ElEvalM m a = ElEvalM { runElEvalM :: StateT (ElEnv m, ElHeap m) (ExceptT (ElEvalError m) (State Integer)) a }
  deriving newtype (Functor, Applicative, Monad, MonadState (ElEnv m, ElHeap m), MonadError (ElEvalError m))

substM2evalM :: ElSubstM m a -> ElEvalM m a
substM2evalM = ElEvalM . lift . mapExceptT (fmap (first EESubstitutionError)) . runElSubstM

fullRunElEvalM :: (ElModeSpec m) => ElEvalM m a -> State Integer (Either (ElEvalError m) (a, (ElEnv m, ElHeap m)))
fullRunElEvalM = runExceptT . flip runStateT (ElEnv HashMap.empty, ElHeap (0, HashMap.empty)) . runElEvalM

data ElEvalError m
  = EEVariableNotInEnv ElId (ElEnv m)
  | EENonBoolean (ElITerm m)
  | EENonInteger (ElITerm m) String
  | EENonTemplate (ElITerm m)
  | EENonFunction (ElITerm m)
  | EENonTypeFunction (ElITerm m)
  | EENoMatchingClause (ElITerm m)
  | EESinglePatternMismatch (ElIPattern m) (ElITerm m)
  | EEInvalidCallForBuiltIn ElBuiltIn (ElISubst m)
  | EEInvalidArgumentOfBuiltIn ElBuiltIn (ElITerm m) String
  | EEInvalidHeapLoc Integer
  | EESubstitutionError (ElSubstError m)
  deriving Show
