{-# LANGUAGE CPP                #-}
{-# LANGUAGE DerivingStrategies #-}
module Quilt.Substitution where

#if MIN_VERSION_base(4,18,0)
import Control.Applicative        (liftA3)
#else
import Control.Applicative        (liftA2, liftA3)
#endif
import Control.Monad.Except       (ExceptT, MonadError (..))
import Control.Monad.State.Strict (MonadState (..), State)
import Data.Sequence              (Seq)
import Data.Sequence              qualified as Seq
import Data.Traversable.Compat    (mapAccumM)
import Data.Tuple                 (swap)
import Data.Tuple.Extra           (second3)

import Quilt.ModeSpec
import Quilt.Syntax

applySubstKind :: (QModeSpec m) => QISubst m -> QIDomain m -> QIKind m -> QSubstM m (QIKind m)
applySubstKind _   _   (IKiType m) = pure $ IKiType m
applySubstKind sub dom (IKiUp m ctx ki) = do
  (ctx', ki') <- freshIContextInKind ctx ki
  liftA2
    (IKiUp m)
    (applySubstCtx sub dom ctx')
    (applySubstKind sub dom ki')

------------------------------------------------------------
-- @applySubstType@ should give a "normalized" kind/type/context/... as
-- the result assuming that input type (and substitution entries containing
-- types) is already normal.

applySubstType :: (QModeSpec m) => QISubst m -> QIDomain m -> QIType m -> QSubstM m (QIType m)
applySubstType sub dom (ITyVar x) =
  case lookupFromIsubIdomain sub dom x of
    Just (ISEType ty) -> pure ty
    Just (ISETerm t)  -> throwError $ SETermForTypeVariable x t -- "Type variable " <> show x <> " cannot be instantiated with a term\n" <> showPrettyIndent 80 4 t
    _                 -> pure $ ITyVar x
applySubstType sub dom (ITySusp m ctxh ty) = do
  (ctxh', ty') <- freshIContextHatInType ctxh ty
  ITySusp m ctxh' <$> applySubstType sub dom ty'
applySubstType sub dom (ITyForce h ty sub') = do
  rty <- applySubstType sub dom ty
  rsub' <- applySubstSubst sub dom sub'
  -- This part handles the hereditary nature of this substitution
  case rty of
    ITySusp _ ctxh ty' -> applySubstType rsub' (icontextHat2idomain ctxh) ty'
    _                  -> pure $ ITyForce h rty rsub'
applySubstType sub dom (ITyData argTys c) = flip ITyData c <$> traverse (applySubstType sub dom) argTys
applySubstType _   _   (ITyBool m) = pure $ ITyBool m
applySubstType _   _   (ITyInt m) = pure $ ITyInt m
applySubstType sub dom (ITyProd itemTys) = ITyProd <$> traverse (applySubstType sub dom) itemTys
applySubstType sub dom (ITyArray m ty) = ITyArray m <$> applySubstType sub dom ty
applySubstType sub dom (ITyUp m l ctx ty) = do
  (ctx', ty') <- freshIContextInType ctx ty
  liftA2
    (ITyUp m l)
    (applySubstCtx sub dom ctx')
    (applySubstType sub dom ty')
applySubstType sub dom (ITyDown m h ty) = ITyDown m h <$> applySubstType sub dom ty
applySubstType sub dom (ITyArr ty0 ty1) =
  liftA2
    ITyArr
    (applySubstType sub dom ty0)
    (applySubstType sub dom ty1)
applySubstType sub dom (ITyForall x ki0 ty1) = do
  (x', ty1') <- freshTyVarInType x ty1
  liftA2
    (ITyForall x')
    (applySubstKind sub dom ki0)
    (applySubstType sub dom ty1')

applySubstCtx :: (QModeSpec m) => QISubst m -> QIDomain m -> QIContext m -> QSubstM m (QIContext m)
applySubstCtx sub dom = traverse (\(x, m, ce) -> (x, m,) <$> applySubstCtxEntry sub dom ce)

applySubstCtxEntry :: (QModeSpec m) => QISubst m -> QIDomain m -> QIContextEntry m -> QSubstM m (QIContextEntry m)
applySubstCtxEntry sub dom (ICEKind ki) = ICEKind <$> applySubstKind sub dom ki
applySubstCtxEntry sub dom (ICEType ty) = ICEType <$> applySubstType sub dom ty

applySubstTerm :: (QModeSpec m) => QISubst m -> QIDomain m -> QITerm m -> QSubstM m (QITerm m)
applySubstTerm sub dom (ITmVar x)            =
  case lookupFromIsubIdomain sub dom x of
    Just (ISETerm t)  -> pure t
    Just (ISEType ty) -> throwError $ SETypeForTermVariable x ty -- "Term variable " <> show x <> " cannot be instantiated with a type\n" <> showPrettyIndent 80 4 ty
    _                 -> pure $ ITmVar x
applySubstTerm _   _   (ITmArrayTag n)       = pure $ ITmArrayTag n
applySubstTerm _   _   (ITmBuiltIn bi)       = pure $ ITmBuiltIn bi
applySubstTerm sub dom (ITmData c cn args)   = ITmData c cn <$> traverse (applySubstTerm sub dom) args
applySubstTerm _   _   ITmTrue               = pure ITmTrue
applySubstTerm _   _   ITmFalse              = pure ITmFalse
applySubstTerm sub dom (ITmIte t0 t1 t2)     =
  liftA3
    ITmIte
    (applySubstTerm sub dom t0)
    (applySubstTerm sub dom t1)
    (applySubstTerm sub dom t2)
applySubstTerm _   _   (ITmInt n)            = pure $ ITmInt n
applySubstTerm sub dom (ITmBinOp bop t0 t1)  =
  liftA2
    (ITmBinOp bop)
    (applySubstTerm sub dom t0)
    (applySubstTerm sub dom t1)
applySubstTerm sub dom (ITmTuple items)      = ITmTuple <$> traverse (applySubstTerm sub dom) items
applySubstTerm sub dom (ITmMatch m t ty brs) =
  liftA3
    (ITmMatch m)
    (applySubstTerm sub dom t)
    (applySubstType sub dom ty)
    (traverse (applySubstBranch sub dom) brs)
applySubstTerm sub dom (ITmSusp m ctxh t)    = do
  (ctxh', t') <- freshIContextHatInTerm ctxh t
  ITmSusp m ctxh' <$> applySubstTerm sub dom t'
applySubstTerm sub dom (ITmForce h t sub')   =
  liftA2
    (ITmForce h)
    (applySubstTerm sub dom t)
    (applySubstSubst sub dom sub')
applySubstTerm sub dom (ITmStore h t)        = ITmStore h <$> applySubstTerm sub dom t
applySubstTerm sub dom (ITmLam pat ty t)     = do
  (_, pat', t') <- freshPattern pat t
  liftA2
    (ITmLam pat')
    (applySubstType sub dom ty)
    (applySubstTerm sub dom t')
applySubstTerm sub dom (ITmTLam x ki t)      = do
  (x', t') <- freshTyVarInTerm x t
  liftA2
    (ITmTLam x')
    (applySubstKind sub dom ki)
    (applySubstTerm sub dom t')
applySubstTerm sub dom (ITmApp t0 t1)        =
  liftA2
    ITmApp
    (applySubstTerm sub dom t0)
    (applySubstTerm sub dom t1)
applySubstTerm sub dom (ITmTApp t0 ty1)      =
  liftA2
    ITmTApp
    (applySubstTerm sub dom t0)
    (applySubstType sub dom ty1)

applySubstBranch :: (QModeSpec m) => QISubst m -> QIDomain m -> QIBranch m -> QSubstM m (QIBranch m)
applySubstBranch sub dom (pat, b) = do
  (_, pat', b') <- freshPattern pat b
  (pat',) <$> applySubstTerm sub dom b'

applySubstSubst :: (QModeSpec m) => QISubst m -> QIDomain m -> QISubst m -> QSubstM m (QISubst m)
applySubstSubst sub dom = traverse (applySubstSubstEntry sub dom)

applySubstSubstEntry :: (QModeSpec m) => QISubst m -> QIDomain m -> QISubstEntry m -> QSubstM m (QISubstEntry m)
applySubstSubstEntry sub dom (ISEType ty) = ISEType <$> applySubstType sub dom ty
applySubstSubstEntry sub dom (ISETerm t)  = ISETerm <$> applySubstTerm sub dom t

------------------------------------------------------------
-- Fresh Variable Generation
------------------------------------------------------------

freshPattern :: (QModeSpec m) => QIPattern m -> QITerm m -> QSubstM m (Seq QId, QIPattern m, QITerm m)
freshPattern (IPatVar x)          b = do
  (x', b') <- freshTmVarInTerm x b
  pure (Seq.singleton x', IPatVar x', b')
freshPattern (IPatTuple pats)     b = (\(b', patEnvs') -> let (pats', envs') = unzip patEnvs' in (mconcat envs', IPatTuple pats', b')) <$> mapAccumM (\b' pat -> (\(env'', pat', b'') -> (b'', (pat', env''))) <$> freshPattern pat b') b pats
freshPattern (IPatLoad pat)       b = second3 IPatLoad <$> freshPattern pat b
freshPattern (IPatData c cn pats) b = (\(b', patEnvs') -> let (pats', envs') = unzip patEnvs' in (mconcat envs', IPatData c cn pats', b')) <$> mapAccumM (\b' pat -> (\(env'', pat', b'') -> (b'', (pat', env''))) <$> freshPattern pat b') b pats
freshPattern pat                  b = pure (Seq.empty, pat, b)

freshTmVarInTerm :: (QModeSpec m) => QId -> QITerm m -> QSubstM m (QId, QITerm m)
freshTmVarInTerm x t = do
  x' <- freshOf x
  (x',) <$> applySubstTerm (Seq.singleton (ISETerm (ITmVar x'))) (Seq.singleton (x, False)) t

freshTmVarsInTerm :: (QModeSpec m) => [QId] -> QITerm m -> QSubstM m ([QId], QITerm m)
freshTmVarsInTerm xs t = swap <$> mapAccumM ((fmap swap .) . flip freshTmVarInTerm) t xs

freshTyVarInTerm :: (QModeSpec m) => QId -> QITerm m -> QSubstM m (QId, QITerm m)
freshTyVarInTerm x t = do
  x' <- freshOf x
  (x',) <$> applySubstTerm (Seq.singleton (ISEType (ITyVar x'))) (Seq.singleton (x, True)) t

freshIContextHatInTerm :: (QModeSpec m) => QIContextHat m -> QITerm m -> QSubstM m (QIContextHat m, QITerm m)
freshIContextHatInTerm ctxh t = swap <$> mapAccumM helper t ctxh
  where
    helper t' (x', m', True)  = fmap (, m', True) . swap <$> freshTyVarInTerm x' t'
    helper t' (x', m', False) = fmap (, m', False) . swap <$> freshTmVarInTerm x' t'

freshTmVarInType :: (QModeSpec m) => QId -> QIType m -> QSubstM m (QId, QIType m)
freshTmVarInType x ty = do
  x' <- freshOf x
  (x',) <$> applySubstType (Seq.singleton (ISETerm (ITmVar x'))) (Seq.singleton (x, False)) ty

freshTyVarInType :: (QModeSpec m) => QId -> QIType m -> QSubstM m (QId, QIType m)
freshTyVarInType x ty = do
  x' <- freshOf x
  (x',) <$> applySubstType (Seq.singleton (ISEType (ITyVar x'))) (Seq.singleton (x, True)) ty

freshIContextInType :: (QModeSpec m) => QIContext m -> QIType m -> QSubstM m (QIContext m, QIType m)
freshIContextInType ctx ty = swap <$> mapAccumM helper ty ctx
  where
    helper ty' (x', m', ce)
      | isCEKind ce = fmap (, m', ce) . swap <$> freshTyVarInType x' ty'
      | otherwise   = fmap (, m', ce) . swap <$> freshTmVarInType x' ty'

freshIContextHatInType :: (QModeSpec m) => QIContextHat m -> QIType m -> QSubstM m (QIContextHat m, QIType m)
freshIContextHatInType ctxh ty = swap <$> mapAccumM helper ty ctxh
  where
    helper ty' (x', m', True)  = fmap (, m', True) . swap <$> freshTyVarInType x' ty'
    helper ty' (x', m', False) = fmap (, m', False) . swap <$> freshTmVarInType x' ty'

freshTmVarInKind :: (QModeSpec m) => QId -> QIKind m -> QSubstM m (QId, QIKind m)
freshTmVarInKind x ki = do
  x' <- freshOf x
  (x',) <$> applySubstKind (Seq.singleton (ISETerm (ITmVar x'))) (Seq.singleton (x, False)) ki

freshTyVarInKind :: (QModeSpec m) => QId -> QIKind m -> QSubstM m (QId, QIKind m)
freshTyVarInKind x ki = do
  x' <- freshOf x
  (x',) <$> applySubstKind (Seq.singleton (ISEType (ITyVar x'))) (Seq.singleton (x, True)) ki

freshIContextInKind :: (QModeSpec m) => QIContext m -> QIKind m -> QSubstM m (QIContext m, QIKind m)
freshIContextInKind ctx ki = swap <$> mapAccumM helper ki ctx
  where
    helper ki' (x', m', ce)
      | isCEKind ce = fmap (, m', ce) . swap <$> freshTyVarInKind x' ki'
      | otherwise   = fmap (, m', ce) . swap <$> freshTmVarInKind x' ki'

freshOf :: QId -> QSubstM m QId
freshOf x
  | isDecoratedQId x = freshOf (dropDecorationFromQId x)
  | otherwise = do
    n <- get
    put (succ n)
    pure $ decorateQId x (show n)

------------------------------------------------------------
-- Other Helpers
------------------------------------------------------------

lookupFromIsubIdomain :: (QModeSpec m) => QISubst m -> QIDomain m -> QId -> Maybe (QISubstEntry m)
lookupFromIsubIdomain isub idom x =
  case Seq.findIndexR (\(x', _) -> x == x') idom of
    Just i  ->
      let
        (_, isKi) = idom `Seq.index` i
      in
      case isub Seq.!? i of
        Just it -> Just it
        Nothing -> Just $ iSubEntryOfBool isKi
    Nothing -> Nothing
  where
    iSubEntryOfBool True  = ISEType (ITyVar x)
    iSubEntryOfBool False = ISETerm (ITmVar x)

------------------------------------------------------------
-- Substitution Monad
------------------------------------------------------------

newtype QSubstM m a = QSubstM { runQSubstM :: ExceptT (QSubstError m) (State Integer) a }
  deriving newtype (Functor, Applicative, Monad, MonadError (QSubstError m), MonadState Integer)

data QSubstError m
  = SETypeForTermVariable QId (QIType m)
  | SETermForTypeVariable QId (QITerm m)
  deriving Show
