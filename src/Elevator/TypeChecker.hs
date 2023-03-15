{-# LANGUAGE DerivingVia #-}
module Elevator.TypeChecker where

import Control.Monad        (join, unless, when)
import Control.Monad.State  (MonadState (get, put), MonadTrans (lift),
                             StateT (StateT), evalStateT, gets, modify')
import Data.Functor.Compose (Compose (..))
import Data.Map             (Map)
import Data.Map             qualified as Map
import Data.Set             qualified as Set
import Elevator.ModeSpec
import Elevator.Syntax

type ElTCM m = StateT (ElContext m) (Either String)

data ElUsage
  = ElUnused
  | ElUsed
  deriving stock (Eq)

type ElContextEntry m = (ElType m, ElUsage)

type ElContext m = Map (ElModeKey m) (ElLocalContext m)
type ElLocalContext m = Map ElId (ElContextEntry m)

typeInfer :: (ElModeSpec m) => m -> ElTerm m -> Either String (ElType m)
typeInfer m t = typeInferImpl m t `evalStateT` mempty

typeInferImpl :: forall ms. (ElModeSpec ms) => ms -> ElTerm ms -> ElTCM ms (ElType ms)
typeInferImpl m (TmVar x) = StateT $ \ctx -> getCompose $
  Map.alterF
    (Compose . localHelper)
    (mskey m)
    ctx
  where
    localHelper :: Maybe (ElLocalContext m) -> Either String (ElType m, Maybe (ElLocalContext m))
    localHelper mayLctx = do
      lctx <- maybeToEither (ctxEntryError x m) mayLctx
      getCompose $ Just <$> Map.alterF (Compose . entryHelper) x lctx

    entryHelper :: Maybe (ElContextEntry m) -> Either String (ElType m, Maybe (ElContextEntry m))
    entryHelper mayCtxEntry = do
      (ty, u) <- maybeToEither (ctxEntryError x m) mayCtxEntry
      u' <- (x, u) `useIn` m
      pure (ty, Just (ty, u'))
typeInferImpl m TmTrue = do
  lift $ verifyModeOp MdOpBool m
  pure TyBool
typeInferImpl m TmFalse =  do
  lift $ verifyModeOp MdOpBool m
  pure TyBool
typeInferImpl m (TmIte t t0 t1) = do
  lift $ verifyModeOp MdOpBool m
  ty <- typeInferImpl m t
  case ty of
    TyBool -> do
      ty0 <- typeInferImpl m t0
      ty1 <- typeInferImpl m t1
      unifyType ty0 ty1
      pure ty1
    _ -> lift $ Left $ typeMismatchError "Bool" (show ty)
typeInferImpl m (TmNat _) = do
  lift $ verifyModeOp MdOpNat m
  pure TyNat
typeInferImpl m (TmBinOp op t t0) = do
  lift $ verifyModeOp MdOpNat m
  when (retTy == TyBool) $
    lift $ verifyModeOp MdOpBool m
  ty' <- typeInferImpl m t
  unifyType ty ty'
  ty0' <- typeInferImpl m t0
  unifyType ty0 ty0'
  pure retTy
  where
    (ty, ty0, retTy :: ElType ms) = elBinOpType op
typeInferImpl m (TmLift n l t) = do
  lift $ verifyModeEq m n
  lift $ verifyModeGt m l
  lift $ verifyModeOp MdOpUp m
  TyUp m l <$> typeInferImpl l t
typeInferImpl m (TmUnlift h n t) = do
  lift $ verifyModeEq m n
  lift $ verifyModeLt m h
  lift $ verifyModeOp MdOpUp h
  withNotGEContext h $ do
    upTy <- typeInferImpl h t
    case upTy of
      TyUp h' m' ty -> do
        lift $ verifyModeEq h h'
        lift $ verifyModeEq m m'
        pure ty
      _ -> lift $ Left $ typeMismatchError "Up _" (show upTy)
typeInferImpl m (TmRet h n t) = do
  lift $ verifyModeEq m n
  lift $ verifyModeLt m h
  lift $ verifyModeOp MdOpDown m
  withNotGEContext h $ do
    TyDown h m <$> typeInferImpl h t
typeInferImpl m (TmLetRet h n x t t0) = do
  lift $ verifyModeEq m n
  lift $ verifyModeLt m h
  lift $ verifyModeOp MdOpDown m
  downLetTy <- typeInferImpl m t
  case downLetTy of
    TyDown h' m' letTy -> do
      lift $ verifyModeEq h h'
      lift $ verifyModeEq m m'
      withCtxEntryOfType h x letTy $ typeInferImpl m t0
    _ -> lift $ Left $ typeMismatchError "Down _" (show downLetTy)
typeInferImpl m (TmLam x n argTy t) = do
  lift $ verifyModeEq m n
  lift $ verifyModeOp MdOpArr m
  lift $ checkMode n argTy
  withCtxEntryOfType m x argTy $ do
    TyArr argTy <$> typeInferImpl n t
typeInferImpl m (TmApp t t0) = do
  lift $ verifyModeOp MdOpArr m
  funTy <- typeInferImpl m t
  case funTy of
    TyArr argTy retTy -> do
      argTy' <- typeInferImpl m t0
      unifyType argTy argTy'
      pure retTy
    _ -> lift $ Left $ typeMismatchError "_ -> _" (show funTy)

checkMode :: (ElModeSpec m) => m -> ElType m -> Either String ()
checkMode m TyNat = verifyModeOp MdOpNat m
checkMode m TyBool = verifyModeOp MdOpBool m
checkMode m (TyArr ty ty0) = do
  verifyModeOp MdOpArr m
  checkMode m ty
  checkMode m ty0
checkMode m (TyUp n l ty) = do
  verifyModeEq m n
  verifyModeGt m l
  verifyModeOp MdOpUp m
  checkMode l ty
checkMode m (TyDown h n ty) = do
  verifyModeEq m n
  verifyModeLt m h
  verifyModeOp MdOpDown m
  checkMode h ty

verifyModeEq :: (ElModeSpec m) => m -> m -> Either String ()
verifyModeEq m n = unless (m == n) $ Left $ concat
  [ "Mode mismatch: expected <"
  , msshow m
  , "> but get <"
  , msshow n
  , ">"
  ]

verifyModeGt :: (ElModeSpec m) => m -> m -> Either String ()
verifyModeGt m n = unless (m >!! n) $ Left $ concat
  [ "Mode mismatch: expected a mode smaller than <"
  , msshow m
  , "> but get <"
  , msshow n
  , ">"
  ]

verifyModeLt :: (ElModeSpec m) => m -> m -> Either String ()
verifyModeLt m n = unless (m <!! n) $ Left $ concat
  [ "Mode mismatch: expected a mode greater than <"
  , msshow m
  , "> but get <"
  , msshow n
  , ">"
  ]

verifyModeOp :: (ElModeSpec m) => ElMdOp -> m -> Either String ()
verifyModeOp op m = unless (op `Set.member` msop m) $ Left $ concat
  [ "Opeartors related to the symbol ("
  , show op
  , ") are not allowed in the mode <"
  , msshow m
  , ">"
  ]

unifyType :: (ElModeSpec m) => ElType m -> ElType m -> ElTCM m ()
unifyType ty ty0 = unless (ty `typeEq` ty0) $ lift $ Left $
  typeMismatchError (show ty) (show ty0)

typeEq :: (ElModeSpec m) => ElType m -> ElType m -> Bool
typeEq = (==)

withCtxEntryOfType :: (ElModeSpec m) => m -> ElId -> ElType m -> ElTCM m a -> ElTCM m a
withCtxEntryOfType m x ty action = do
  ctx <- get
  modify' (Map.insertWith Map.union (mskey m) (Map.singleton x (ty, ElUnused)))
  a <- action
  (ty', u) <- join (gets (lift . maybeToEither (ctxEntryError x m) . lookupCtxEntry m x))
  unifyType ty ty'
  unless (u `isUsedIn` m) $ lift $ Left $ concat
    [ "Invalid unused variable: the mode <"
    , msshow m
    , "> does not allow weakening, but the variable "
    , show x
    , "<"
    , msshow m
    , "> is unused"
    ]
    
  modify' (rollbackCtxEntry m x ctx)
  pure a

withNotGEContext :: (ElModeSpec m) => m -> ElTCM m a -> ElTCM m a
withNotGEContext m action = do
  (geCtx, ctx0) <- gets (Map.partitionWithKey (const . (m <=!!) . elKeyToMode))
  put ctx0
  a <- action
  modify' (Map.union geCtx)
  pure a

rollbackCtxEntry :: (ElModeSpec m) => m -> ElId -> ElContext m -> ElContext m -> ElContext m
rollbackCtxEntry m x preCtx = Map.adjust (Map.update (const (lookupCtxEntry m x preCtx)) x) (mskey m)

lookupCtxEntry :: (ElModeSpec m) => m -> ElId -> ElContext m -> Maybe (ElContextEntry m)
lookupCtxEntry m x ctx = Map.lookup (mskey m) ctx >>= Map.lookup x

typeMismatchError :: String -> String -> String
typeMismatchError st st0 =
  concat
  [ "Type mismatch: expected ("
  , st
  , ") but get ("
  , st0
  , ")"
  ]

ctxEntryError :: (ElModeSpec m) => ElId -> m -> String
ctxEntryError x m =
  concat
  [ "Out of scope variable "
  , show x
  , "<"
  , msshow m
  , ">: the variable is not in the context"
  ]
  

isUsedIn :: (ElModeSpec m) => ElUsage -> m -> Bool
isUsedIn ElUnused m = elMdStWithWk (msst m)
isUsedIn ElUsed   _ = True

-- | This function takes care the cases requiring the contraction rule.
useIn :: (ElModeSpec m) => (ElId, ElUsage) -> m -> Either String ElUsage
useIn (_, ElUnused) _      = pure ElUsed
useIn (x, ElUsed)   m
  | elMdStWithCo (msst m) = pure ElUsed
  | otherwise             = Left $ concat
    [ "Invalid double use of a variable: the mode <"
    , msshow m
    , "> does not allow contraction, but the variable "
    , show x
    , "<"
    , msshow m
    , "> is used twice."
    ]

maybeToEither :: a -> Maybe b -> Either a b
maybeToEither a Nothing  = Left a
maybeToEither _ (Just b) = Right b
