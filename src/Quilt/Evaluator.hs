{-# LANGUAGE CPP                #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedLists    #-}
module Quilt.Evaluator where

#if MIN_VERSION_base(4,18,0)
import Control.Applicative        (liftA3)
#else
import Control.Applicative        (liftA2, liftA3)
#endif
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

newtype QEnv m = QEnv { getQEnv :: HashMap QId (Maybe (QITerm m)) }
  deriving stock Show

newtype QHeap m = QHeap { getQHeap :: (Integer, HashMap Integer (Vector (QITerm m))) }
  deriving stock Show

evalUnderModule :: (QModeSpec m) => QIModule m -> QITerm m -> QEvalM m (QITerm m)
evalUnderModule (QIModule _imps tops) t = do
  modifyEnv (const (buildEnv tops))
  eval t
  where
    buildEnv = QEnv . foldl' envHelper HashMap.empty
    envHelper envMap (ITopTermDef x _ _ t') = HashMap.insert x (Just t') envMap
    envHelper envMap ITopTypeDef{}          = envMap

checkNormHead :: QITerm m -> Bool
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

eval :: (QModeSpec m) => QITerm m -> QEvalM m (QITerm m)
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

firstMatchingBranch :: (QModeSpec m) => [QIBranch m] -> QITerm m -> QEvalM m (QITerm m)
firstMatchingBranch []             t = throwError $ EENoMatchingClause t
firstMatchingBranch ((pat, b):brs) t = catchError (matching pat t b) $ \_ -> firstMatchingBranch brs t

matching :: (QModeSpec m) => QIPattern m -> QITerm m -> QITerm m -> QEvalM m (QITerm m)
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

findBuiltInSpine :: QITerm m -> Maybe (QBuiltIn, QISubst m)
findBuiltInSpine (ITmApp t0 t1)  = fmap (:|> ISETerm t1) <$> findBuiltInSpine t0
findBuiltInSpine (ITmTApp t0 k1) = fmap (:|> ISEType k1) <$> findBuiltInSpine t0
findBuiltInSpine (ITmBuiltIn bi) = pure (bi, [])
findBuiltInSpine _               = Nothing

evalBuiltIn :: (QModeSpec m) => QBuiltIn -> QISubst m -> QEvalM m (QITerm m)
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

buildBuiltInSpine :: QBuiltIn -> QISubst m -> QITerm m
buildBuiltInSpine bi = foldl app (ITmBuiltIn bi)
  where
    app t0 (ISETerm t1)  = ITmApp t0 t1
    app t0 (ISEType ty1) = ITmTApp t0 ty1

refineTemplate :: (QModeSpec m) => m -> QITerm m -> QEvalM m (QITerm m)
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

refineBranchTemplate :: (QModeSpec m) => m -> QIBranch m -> QEvalM m (QIBranch m)
refineBranchTemplate n (pat, b) = do
  (pat', b') <- opaqueMatching pat b
  (pat',) <$> refineTemplate n b'

opaqueMatching :: (QModeSpec m) => QIPattern m -> QITerm m -> QEvalM m (QIPattern m, QITerm m)
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

computeBop :: QBinOp -> Integer -> Integer -> QITerm m
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

getEnv :: QEvalM m (QEnv m)
getEnv = fst <$> get

modifyEnv :: (QEnv m -> QEnv m) -> QEvalM m ()
modifyEnv = modify . first

getHeap :: QEvalM m (QHeap m)
getHeap = snd <$> get

modifyHeap :: (QHeap m -> QHeap m) -> QEvalM m ()
modifyHeap = modify . second

heapAllocArray :: Int -> QITerm m -> QEvalM m Integer
heapAllocArray n a = do
  modifyHeap (\(QHeap (nid, h)) -> QHeap (succ nid, HashMap.insert nid (Vector.replicate n a) h))
  QHeap (snid, _) <- getHeap
  pure (snid - 1)

heapGetArray :: Integer -> QEvalM m (Vector (QITerm m))
heapGetArray tag = do
  QHeap (_, h) <- getHeap
  case HashMap.lookup tag h of
    Just array -> pure array
    Nothing    -> throwError $ EEInvalidHeapLoc tag -- "Invalid heap location " <> show tag

heapModifyArray :: Integer -> (Vector (QITerm m) -> Vector (QITerm m)) -> QEvalM m ()
heapModifyArray tag f = modifyHeap (\(QHeap (nid, h)) -> QHeap (nid, HashMap.adjust f tag h))

heapDeleteArrayOf :: Integer -> QEvalM m ()
heapDeleteArrayOf tag = modifyHeap (\(QHeap (nid, h)) -> QHeap (nid, HashMap.delete tag h))

envInsert :: QId -> QITerm m -> QEvalM m ()
envInsert x t = modifyEnv (QEnv . HashMap.insert x (Just t) . getQEnv)

envEmptyInsert :: QId -> QEvalM m ()
envEmptyInsert x = modifyEnv (QEnv . HashMap.insert x Nothing . getQEnv)

envExtend :: QIContextHat m -> QEvalM m ()
envExtend ctxh = envExtendWithIds (fmap fst3 ctxh)

envExtendWithIds :: Seq QId -> QEvalM m ()
envExtendWithIds xs = modifyEnv (QEnv . HashMap.union (HashMap.fromList . toList $ fmap (, Nothing) xs) . getQEnv)

envLookup :: QId -> QEnv m -> Maybe (Maybe (QITerm m))
envLookup x = HashMap.lookup x . getQEnv

newtype QEvalM m a = QEvalM { runQEvalM :: StateT (QEnv m, QHeap m) (ExceptT (QEvalError m) (State Integer)) a }
  deriving newtype (Functor, Applicative, Monad, MonadState (QEnv m, QHeap m), MonadError (QEvalError m))

substM2evalM :: QSubstM m a -> QEvalM m a
substM2evalM = QEvalM . lift . mapExceptT (fmap (first EESubstitutionError)) . runQSubstM

fullRunQEvalM :: (QModeSpec m) => QEvalM m a -> State Integer (Either (QEvalError m) (a, (QEnv m, QHeap m)))
fullRunQEvalM = runExceptT . flip runStateT (QEnv HashMap.empty, QHeap (0, HashMap.empty)) . runQEvalM

data QEvalError m
  = EEVariableNotInEnv QId (QEnv m)
  | EENonBoolean (QITerm m)
  | EENonInteger (QITerm m) String
  | EENonTemplate (QITerm m)
  | EENonFunction (QITerm m)
  | EENonTypeFunction (QITerm m)
  | EENoMatchingClause (QITerm m)
  | EESinglePatternMismatch (QIPattern m) (QITerm m)
  | EEInvalidCallForBuiltIn QBuiltIn (QISubst m)
  | EEInvalidArgumentOfBuiltIn QBuiltIn (QITerm m) String
  | EEInvalidHeapLoc Integer
  | EESubstitutionError (QSubstError m)
  deriving Show
