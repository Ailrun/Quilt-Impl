{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE ImportQualifiedPost #-}
module Elevator.TypeChecker where

import Control.Monad     (unless)
import Data.Map          (Map)
import Data.Map          qualified as Map
import Elevator.ModeSpec
import Elevator.Syntax
import Data.Bifunctor (Bifunctor(first))

type ElTCM a = Either String a

data ElUsage
  = ElNotUsed
  | ElUsed
  deriving stock (Eq)

type ElContext m = Map (ElModeKey m) (ElLocalContext m)
type ElLocalContext m = Map ElId (ElType m, ElUsage)

typeInfer :: (ElModeSpec m) => ElTerm m -> ElTCM (ElType m)
typeInfer t = fst <$> typeInferImpl msinit mempty t

typeInferImpl :: (ElModeSpec m) => m -> ElContext m -> ElTerm m -> ElTCM (ElType m, ElContext m)
typeInferImpl m ctx (TmVar x) = do
  lctx <- maybeToEither "" $ Map.lookup (mskey m) ctx
  (ty, u) <- maybeToEither "" $ Map.lookup x lctx
  u' <- u `usingIn` m
  let
    ctx' = Map.insert (mskey m) (Map.insert x (ty, u') lctx) ctx
  pure (ty, ctx')
typeInferImpl _ ctx (TmNat _) = Right (TyNat, ctx)
typeInferImpl m ctx (TmLift n l t) = do
  unless (m == n) $ Left ""
  unless (l <!! n) $ Left ""
  first (TyUp n l) <$> typeInferImpl l ctx t
typeInferImpl m ctx (TmUnlift h n t) = do
  unless (m == n) $ Left ""
  unless (n <!! h) $ Left ""
  ctx' <- dropContextNotGE h ctx
  res <- typeInferImpl h ctx' t
  case fst res of
    TyUp h' n' ty' -> do
      unless (h == h') $ Left ""
      unless (n == n') $ Left ""
      pure (ty', snd res) -- should return full context, not dropped context
    _ -> Left ""
typeInferImpl m ctx (TmLam n x ty t) = do
  unless (m == n) $ Left ""
  res <- typeInferImpl n _newctx_handle_shadowing t
  _using_res_add_TyArr_ty

dropContextNotGE :: (ElModeSpec m) => m -> ElContext m -> ElTCM (ElContext m)
dropContextNotGE m ctx
  | isWkableCtx droppedCtx = Right ctx'
  | otherwise = Left ""
  where
    (ctx', droppedCtx) = Map.partitionWithKey (const . not . (m <=!!) . elKeyToMode) ctx

isWkableCtx :: (ElModeSpec m) => m -> ElContext m -> Bool
isWkableCtx = and . Map.mapWithKey (\k lctx -> elStWithWk (msst (elKeyToMode k)) || foldMap ((== ElUsed) . snd) lctx)

usingIn :: (ElModeSpec m) => ElUsage -> m -> ElTCM ElUsage
usingIn ElNotUsed _     = pure ElUsed
usingIn ElUsed    m
  | elStWithCo (msst m) = pure ElUsed
  | otherwise           = Left ""

maybeToEither :: a -> Maybe b -> Either a b
maybeToEither a Nothing  = Left a
maybeToEither _ (Just b) = Right b
