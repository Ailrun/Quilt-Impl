{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE ImportQualifiedPost #-}
module Elevator.TypeChecker where

import Control.Monad        (unless)
import Data.Bifunctor       (bimap, first)
import Data.Functor.Compose (Compose (..))
import Data.Map             (Map)
import Data.Map             qualified as Map
import Elevator.ModeSpec
import Elevator.Syntax

type ElTCM = Either String

data ElUsage
  = ElUnused
  | ElUsed
  deriving stock (Eq)

type ElContextEntry m = (ElType m, ElUsage)

type ElContext m = Map (ElModeKey m) (ElLocalContext m)
type ElLocalContext m = Map ElId (ElContextEntry m)

typeInfer :: (ElModeSpec m) => ElTerm m -> ElTCM (ElType m)
typeInfer t = fst <$> typeInferImpl msinit mempty t

typeInferImpl :: (ElModeSpec m) => m -> ElContext m -> ElTerm m -> ElTCM (ElType m, ElContext m)
typeInferImpl m ctx (TmVar x) = getCompose $
  Map.alterF
    (Compose . localHelper . maybeToEither "")
    (mskey m)
    ctx
  where
    localHelper :: ElTCM (ElLocalContext m) -> ElTCM (ElType m, Maybe (ElLocalContext m))
    localHelper getLctx = do
      lctx <- getLctx
      getCompose $ Just <$> Map.alterF (Compose . entryHelper . maybeToEither "") x lctx

    entryHelper :: ElTCM (ElContextEntry m) -> ElTCM (ElType m, Maybe (ElContextEntry m))
    entryHelper getCtxEntry = do
      (ty, u) <- getCtxEntry
      u' <- u `useIn` m
      pure (ty, Just (ty, u'))
typeInferImpl _ ctx (TmNat _) = Right (TyNat, ctx)
typeInferImpl m ctx (TmLift n l t) = do
  unless (m == n) $ Left ""
  unless (l <!! n) $ Left ""
  first (TyUp n l) <$> typeInferImpl l ctx t
typeInferImpl m ctx (TmUnlift h n t) = do
  unless (m == n) $ Left ""
  unless (n <!! h) $ Left ""
  let
    (geCtx, ctx0) = splitContextGE h ctx
  (ty, ctx1) <- typeInferImpl h ctx0 t
  case ty of
    TyUp h' n' ty' -> do
      unless (h == h') $ Left ""
      unless (n == n') $ Left ""
      pure (ty', Map.union geCtx ctx1)
    _ -> Left ""
typeInferImpl m ctx (TmRet h n t) = do
  unless (m == n) $ Left ""
  unless (n <!! h) $ Left ""
  let
    (geCtx, ctx0) = splitContextGE h ctx
  bimap (TyDown h n) (Map.union geCtx) <$> typeInferImpl h ctx0 t
typeInferImpl m ctx (TmLetRet h n x t t0) = do
  unless (m == n) $ Left ""
  unless (n <!! h) $ Left ""
  (downLetTy, ctx') <- typeInferImpl n ctx t
  case downLetTy of
    TyDown h' n' letTy -> do
      unless (h == h') $ Left ""
      unless (n == n') $ Left ""
      (ty0, ctx'') <- typeInferImpl n (insertCtxEntry h x (letTy, ElUnused) ctx') t0
      (letTy', u) <- maybeToEither "" . lookupCtxEntry h x $ ctx''
      unless (letTy `typeEq` letTy') $ Left ""
      unless (u `isUsedIn` h) $ Left ""
      pure (ty0, rollbackCtxEntry h x ctx' ctx'')
    _ -> Left ""
typeInferImpl m ctx (TmLam n x argTy t) = do
  unless (m == n) $ Left ""
  (retTy, ctx') <- typeInferImpl n (insertCtxEntry m x (argTy, ElUnused) ctx) t
  (argTy', u) <- maybeToEither "" . lookupCtxEntry m x $ ctx'
  unless (argTy `typeEq` argTy') $ Left ""
  unless (u `isUsedIn` m) $ Left ""
  pure (TyArr argTy' retTy, rollbackCtxEntry m x ctx ctx')
typeInferImpl m ctx (TmApp t t0) = do
  (funTy, ctx') <- typeInferImpl m ctx t
  case funTy of
    TyArr argTy retTy -> do
      (argTy', ctx'') <- typeInferImpl m ctx' t0
      unless (argTy `typeEq` argTy') $ Left ""
      pure (retTy, ctx'')
    _ -> Left ""

typeEq :: (ElModeSpec m) => ElType m -> ElType m -> Bool
typeEq = (==)

rollbackCtxEntry :: (ElModeSpec m) => m -> ElId -> ElContext m -> ElContext m -> ElContext m
rollbackCtxEntry m x preCtx = Map.adjust (Map.update (const (lookupCtxEntry m x preCtx)) x) (mskey m)

insertCtxEntry :: (ElModeSpec m) => m -> ElId -> ElContextEntry m -> ElContext m -> ElContext m
insertCtxEntry m x e = Map.insertWith Map.union (mskey m) (Map.singleton x e)

lookupCtxEntry :: (ElModeSpec m) => m -> ElId -> ElContext m -> Maybe (ElContextEntry m)
lookupCtxEntry m x ctx = Map.lookup (mskey m) ctx >>= Map.lookup x

splitContextGE :: (ElModeSpec m) => m -> ElContext m -> (ElContext m, ElContext m)
splitContextGE m = Map.partitionWithKey (const . (m <=!!) . elKeyToMode)

isUsedIn :: (ElModeSpec m) => ElUsage -> m -> Bool
isUsedIn ElUnused m = elStWithWk (msst m)
isUsedIn ElUsed   _ = True

-- | This function takes care the cases requiring the contraction rule.
useIn :: (ElModeSpec m) => ElUsage -> m -> ElTCM ElUsage
useIn ElUnused _      = pure ElUsed
useIn ElUsed   m
  | elStWithCo (msst m) = pure ElUsed
  | otherwise           = Left ""

maybeToEither :: a -> Maybe b -> Either a b
maybeToEither a Nothing  = Left a
maybeToEither _ (Just b) = Right b
