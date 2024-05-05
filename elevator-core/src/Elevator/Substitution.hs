{-# LANGUAGE DerivingStrategies #-}
module Elevator.Substitution where

import Control.Applicative        (Applicative (liftA2), liftA3)
import Control.Monad.Except       (ExceptT, MonadError (..))
import Control.Monad.State.Strict (MonadState (..), State)
import Data.Sequence              (Seq)
import Data.Sequence              qualified as Seq
import Data.Traversable.Compat    (mapAccumM)
import Data.Tuple                 (swap)
import Elevator.ModeSpec
import Elevator.PrettyPrinter
import Elevator.Syntax

applySubstKind :: (ElModeSpec m) => ElISubst m -> ElIDomain m -> ElIKind m -> ElSubstM (ElIKind m)
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

applySubstType :: (ElModeSpec m) => ElISubst m -> ElIDomain m -> ElIType m -> ElSubstM (ElIType m)
applySubstType sub dom (ITyVar x) =
  case lookupFromIsubIdomain sub dom x of
    Just (ISEType ty) -> pure ty
    Just (ISETerm t)  -> throwError $ "Type variable " <> show x <> " cannot be instantiated with a term\n" <> showPrettyIndent 80 4 t
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
applySubstType sub dom (ITyUp m ctx ty) = do
  (ctx', ty') <- freshIContextInType ctx ty
  liftA2
    (ITyUp m)
    (applySubstCtx sub dom ctx')
    (applySubstType sub dom ty')
applySubstType sub dom (ITyDown m ty) = ITyDown m <$> applySubstType sub dom ty
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

applySubstCtx :: (ElModeSpec m) => ElISubst m -> ElIDomain m -> ElIContext m -> ElSubstM (ElIContext m)
applySubstCtx sub dom = traverse (\(x, m, ce) -> (x, m,) <$> applySubstCtxEntry sub dom ce)

applySubstCtxEntry :: (ElModeSpec m) => ElISubst m -> ElIDomain m -> ElIContextEntry m -> ElSubstM (ElIContextEntry m)
applySubstCtxEntry sub dom (ICEKind ki) = ICEKind <$> applySubstKind sub dom ki
applySubstCtxEntry sub dom (ICEType ty) = ICEType <$> applySubstType sub dom ty

applySubstTerm :: (ElModeSpec m) => ElISubst m -> ElIDomain m -> ElITerm m -> ElSubstM (ElITerm m)
applySubstTerm sub dom (ITmVar x)            =
  case lookupFromIsubIdomain sub dom x of
    Just (ISETerm t)  -> pure t
    Just (ISEType ty) -> throwError $ "Term variable " <> show x <> " cannot be instantiated with a type\n" <> showPrettyIndent 80 4 ty
    _                 -> pure $ ITmVar x
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

applySubstBranch :: (ElModeSpec m) => ElISubst m -> ElIDomain m -> ElIBranch m -> ElSubstM (ElIBranch m)
applySubstBranch sub dom (pat, b) = do
  (_, pat', b') <- freshPattern pat b
  (pat',) <$> applySubstTerm sub dom b'

applySubstSubst :: (ElModeSpec m) => ElISubst m -> ElIDomain m -> ElISubst m -> ElSubstM (ElISubst m)
applySubstSubst sub dom = traverse (applySubstSubstEntry sub dom)

applySubstSubstEntry :: (ElModeSpec m) => ElISubst m -> ElIDomain m -> ElISubstEntry m -> ElSubstM (ElISubstEntry m)
applySubstSubstEntry sub dom (ISEType ty) = ISEType <$> applySubstType sub dom ty
applySubstSubstEntry sub dom (ISETerm t)  = ISETerm <$> applySubstTerm sub dom t

------------------------------------------------------------
-- Fresh Variable Generation
------------------------------------------------------------

freshPattern :: (ElModeSpec m) => ElIPattern m -> ElITerm m -> ElSubstM (Seq ElId, ElIPattern m, ElITerm m)
freshPattern (IPatVar x)          b = do
  (x', b') <- freshTmVarInTerm x b
  pure (Seq.singleton x', IPatVar x', b')
freshPattern (IPatTuple pats)     b = (\(b', patEnvs') -> let (pats', envs') = unzip patEnvs' in (mconcat envs', IPatTuple pats', b')) <$> mapAccumM (\b' pat -> (\(env'', pat', b'') -> (b'', (pat', env''))) <$> freshPattern pat b') b pats
freshPattern (IPatLoad pat)       b = freshPattern pat b
freshPattern (IPatData c cn pats) b = (\(b', patEnvs') -> let (pats', envs') = unzip patEnvs' in (mconcat envs', IPatData c cn pats', b')) <$> mapAccumM (\b' pat -> (\(env'', pat', b'') -> (b'', (pat', env''))) <$> freshPattern pat b') b pats
freshPattern pat                  b = pure (Seq.empty, pat, b)

freshTmVarInTerm :: (ElModeSpec m) => ElId -> ElITerm m -> ElSubstM (ElId, ElITerm m)
freshTmVarInTerm x t = do
  x' <- freshOf x
  (x',) <$> applySubstTerm (Seq.singleton (ISETerm (ITmVar x'))) (Seq.singleton (x, False)) t

freshTmVarsInTerm :: (ElModeSpec m) => [ElId] -> ElITerm m -> ElSubstM ([ElId], ElITerm m)
freshTmVarsInTerm xs t = swap <$> mapAccumM ((fmap swap .) . flip freshTmVarInTerm) t xs

freshTyVarInTerm :: (ElModeSpec m) => ElId -> ElITerm m -> ElSubstM (ElId, ElITerm m)
freshTyVarInTerm x t = do
  x' <- freshOf x
  (x',) <$> applySubstTerm (Seq.singleton (ISEType (ITyVar x'))) (Seq.singleton (x, True)) t

freshIContextHatInTerm :: (ElModeSpec m) => ElIContextHat m -> ElITerm m -> ElSubstM (ElIContextHat m, ElITerm m)
freshIContextHatInTerm ctxh t = swap <$> mapAccumM helper t ctxh
  where
    helper t' (x', m', True)  = fmap (, m', True) . swap <$> freshTyVarInTerm x' t'
    helper t' (x', m', False) = fmap (, m', False) . swap <$> freshTmVarInTerm x' t'

freshTmVarInType :: (ElModeSpec m) => ElId -> ElIType m -> ElSubstM (ElId, ElIType m)
freshTmVarInType x ty = do
  x' <- freshOf x
  (x',) <$> applySubstType (Seq.singleton (ISETerm (ITmVar x'))) (Seq.singleton (x, False)) ty

freshTyVarInType :: (ElModeSpec m) => ElId -> ElIType m -> ElSubstM (ElId, ElIType m)
freshTyVarInType x ty = do
  x' <- freshOf x
  (x',) <$> applySubstType (Seq.singleton (ISEType (ITyVar x'))) (Seq.singleton (x, True)) ty

freshIContextInType :: (ElModeSpec m) => ElIContext m -> ElIType m -> ElSubstM (ElIContext m, ElIType m)
freshIContextInType ctx ty = swap <$> mapAccumM helper ty ctx
  where
    helper ty' (x', m', ce)
      | isCEKind ce = fmap (, m', ce) . swap <$> freshTyVarInType x' ty'
      | otherwise   = fmap (, m', ce) . swap <$> freshTmVarInType x' ty'

freshIContextHatInType :: (ElModeSpec m) => ElIContextHat m -> ElIType m -> ElSubstM (ElIContextHat m, ElIType m)
freshIContextHatInType ctxh ty = swap <$> mapAccumM helper ty ctxh
  where
    helper ty' (x', m', True)  = fmap (, m', True) . swap <$> freshTyVarInType x' ty'
    helper ty' (x', m', False) = fmap (, m', False) . swap <$> freshTmVarInType x' ty'

freshTmVarInKind :: (ElModeSpec m) => ElId -> ElIKind m -> ElSubstM (ElId, ElIKind m)
freshTmVarInKind x ki = do
  x' <- freshOf x
  (x',) <$> applySubstKind (Seq.singleton (ISETerm (ITmVar x'))) (Seq.singleton (x, False)) ki

freshTyVarInKind :: (ElModeSpec m) => ElId -> ElIKind m -> ElSubstM (ElId, ElIKind m)
freshTyVarInKind x ki = do
  x' <- freshOf x
  (x',) <$> applySubstKind (Seq.singleton (ISEType (ITyVar x'))) (Seq.singleton (x, True)) ki

freshIContextInKind :: (ElModeSpec m) => ElIContext m -> ElIKind m -> ElSubstM (ElIContext m, ElIKind m)
freshIContextInKind ctx ki = swap <$> mapAccumM helper ki ctx
  where
    helper ki' (x', m', ce)
      | isCEKind ce = fmap (, m', ce) . swap <$> freshTyVarInKind x' ki'
      | otherwise   = fmap (, m', ce) . swap <$> freshTmVarInKind x' ki'

freshOf :: ElId -> ElSubstM ElId
freshOf x
  | isDecoratedElId x = freshOf (dropDecorationFromElId x)
  | otherwise = do
    n <- get
    put (succ n)
    pure $ decorateElId x (show n)

------------------------------------------------------------
-- Other Helpers
------------------------------------------------------------

lookupFromIsubIdomain :: (ElModeSpec m) => ElISubst m -> ElIDomain m -> ElId -> Maybe (ElISubstEntry m)
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

newtype ElSubstM a = ElSubstM { runElSubstM :: ExceptT String (State Integer) a }
  deriving newtype (Functor, Applicative, Monad, MonadError String, MonadState Integer)
