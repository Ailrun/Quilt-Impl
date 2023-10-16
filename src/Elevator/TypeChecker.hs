{-# LANGUAGE DerivingVia #-}
module Elevator.TypeChecker where

import Control.Monad       (unless, void, when)
import Data.Foldable       (foldlM)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.List           (foldl')
import Elevator.ModeSpec
import Elevator.Syntax

data ElUsage
  = ElUnused
  | ElUsed
  deriving stock (Eq)

type ElContextEntry m = (ElType m, m)
type ElContext m = HashMap ElId (ElContextEntry m)

typeCheckProg :: (ElModeSpec m) => ElProgram m -> Either String ()
typeCheckProg (ElProgram tops) = void $ foldlM typeCheckAndAddTop HashMap.empty tops

typeCheckProgIncremental :: (ElModeSpec m) => ElProgram m -> ElTop m -> Either String ()
typeCheckProgIncremental (ElProgram tops) top = void $ typeCheckAndAddTop ctx top
  where
    ctx = foldl' (flip (\(ElDef x m ty _) -> HashMap.insert x (ty, m))) HashMap.empty tops

typeCheckAndAddTop :: (ElModeSpec m) => ElContext m -> ElTop m -> Either String (ElContext m)
typeCheckAndAddTop ctx (ElDef x m ty t) = do
  void $ typeCheckImpl m ctx' t ty
  pure ctx'
  where
    ctx' = HashMap.insert x (ty, m) ctx

typeInfer :: (ElModeSpec m) => ElProgram m -> m -> ElTerm m -> Either String (ElType m)
typeInfer (ElProgram tops) m = fmap snd . typeInferImpl m ctx
  where
    ctx = foldl' (flip (\(ElDef x m' ty _) -> HashMap.insert x (ty, m'))) HashMap.empty tops

typeInferImpl :: (ElModeSpec m) => m -> ElContext m -> ElTerm m -> Either String (ElContext m, ElType m)
typeInferImpl m ctx (TmVar x) =
  case HashMap.lookup x ctx of
    Just (ty, m') -> do
      verifyModeEq m m'
      pure (HashMap.singleton x (ty, m), ty)
    Nothing       -> Left $ "Variable \"" <> show x <> "\" is not in scope"
typeInferImpl m _ TmTrue = do
  verifyModeOp MdOpBool m
  pure (HashMap.empty, TyBool)
typeInferImpl m _ TmFalse = do
  verifyModeOp MdOpBool m
  pure (HashMap.empty, TyBool)
typeInferImpl m ctx (TmIte t t0 t1) = do
  verifyModeOp MdOpBool m
  usage <- typeCheckImpl m ctx t TyBool
  (usage0, ty0) <- typeInferImpl m ctx t0
  (usage1, ty1) <- typeInferImpl m ctx t1
  unifyType ty0 ty1
  (, ty0) <$> foldlM mergeUsage usage [usage0, usage1]
typeInferImpl m _ (TmNat _) = do
  verifyModeOp MdOpNat m
  pure (HashMap.empty, TyNat)
typeInferImpl m ctx (TmSucc t) = do
  verifyModeOp MdOpNat m
  (, TyNat) <$> typeCheckImpl m ctx t TyNat
typeInferImpl m ctx (TmNatCase t tz x ts) = do
  verifyModeOp MdOpNat m
  usage <- typeCheckImpl m ctx t TyNat
  (usagez, tyz) <- typeInferImpl m ctx tz
  (usages, tys) <- typeInferImpl m (HashMap.insert x (TyNat, m) ctx) ts
  usages' <- removeVarUsage usages x m
  unifyType tyz tys
  (, tyz) <$> foldlM mergeUsage usage [usagez, usages']
typeInferImpl m ctx (TmBinOp bop t0 t1) = do
  verifyModeOp MdOpNat m
  when (retTy == TyBool) $
    verifyModeOp MdOpBool m
  usage0 <- typeCheckImpl m ctx t0 ty0
  usage1 <- typeCheckImpl m ctx t1 ty1
  (, retTy) <$> mergeUsage usage0 usage1
  where
    (ty0, ty1, retTy) = elBinOpTypeWithMode m bop
typeInferImpl m ctx (TmLift l t) = do
  verifyModeGt m l
  verifyModeOp MdOpUp m
  fmap (TyUp l m) <$> typeInferImpl l ctx t
typeInferImpl m ctx (TmUnlift h t) = do
  verifyModeLt m h
  verifyModeOp MdOpUp h
  ctx' <- cutContext ctx h
  (usage, upTy) <- typeInferImpl h ctx' t
  case upTy of
    TyUp m' h' ty -> do
      verifyModeEq h h'
      verifyModeEq m m'
      pure (usage, ty)
    _ -> Left $ errTypeWrongForm upTy "Up _"
typeInferImpl m ctx (TmRet h t) = do
  verifyModeLt m h
  verifyModeOp MdOpDown m
  ctx' <- cutContext ctx h
  fmap (TyDown h m) <$> typeInferImpl h ctx' t
typeInferImpl m ctx (TmLetRet h x t t0) = do
  verifyModeLt m h
  verifyModeOp MdOpDown m
  (usage, downLetTy) <- typeInferImpl m ctx t
  case downLetTy of
    TyDown h' m' letTy -> do
      verifyModeEq h h'
      verifyModeEq m m'
      (usage0, ty) <- typeInferImpl m (HashMap.insert x (letTy, h) ctx) t0
      usage0' <- removeVarUsage usage0 x h
      (, ty) <$> mergeUsage usage usage0'
    _ -> Left $ errTypeWrongForm downLetTy "Down _"
typeInferImpl m ctx (TmLam x (Just argTy) t) = do
  verifyModeOp MdOpArr m
  (usage, ty) <- typeInferImpl m (HashMap.insert x (argTy, m) ctx) t
  (, TyArr argTy ty) <$> removeVarUsage usage x m
typeInferImpl _ _ (TmLam x Nothing _) =
  Left $ "variable \"" <> show x <> "\" should have a type annotation"
typeInferImpl m ctx (TmApp t0 t1) = do
  verifyModeOp MdOpArr m
  (usage0, funTy) <- typeInferImpl m ctx t0
  case funTy of
    TyArr argTy retTy -> do
      (usage1, argTy') <- typeInferImpl m ctx t1
      unifyType argTy argTy'
      (, retTy) <$> mergeUsage usage0 usage1
    _ -> Left $ errTypeWrongForm funTy "_ -> _"

typeCheckImpl :: (ElModeSpec m) => m -> ElContext m -> ElTerm m -> ElType m -> Either String (ElContext m)
typeCheckImpl m ctx (TmLam x Nothing t) (TyArr argTy retTy) = do
  verifyModeOp MdOpArr m
  usage <- typeCheckImpl m (HashMap.insert x (argTy, m) ctx) t retTy
  removeVarUsage usage x m
typeCheckImpl m ctx t ty = do
  (usage, ty') <- typeInferImpl m ctx t
  unifyType ty ty'
  pure usage

verifyModeEq :: (ElModeSpec m) => m -> m -> Either String ()
verifyModeEq m n = unless (m == n) $ Left $ concat
  [ "Mode mismatch: expected <"
  , show m
  , "> but get <"
  , show n
  , ">"
  ]

verifyModeGt :: (ElModeSpec m) => m -> m -> Either String ()
verifyModeGt m n = unless (m >!! n) $ Left $ concat
  [ "Mode mismatch: expected a mode smaller than <"
  , show m
  , "> but get <"
  , show n
  , ">"
  ]

verifyModeLt :: (ElModeSpec m) => m -> m -> Either String ()
verifyModeLt m n = unless (m <!! n) $ Left $ concat
  [ "Mode mismatch: expected a mode greater than <"
  , show m
  , "> but get <"
  , show n
  , ">"
  ]

verifyModeOp :: (ElModeSpec m) => ElMdOp -> m -> Either String ()
verifyModeOp op m = unless (modeOp m op) $ Left $ concat
  [ "Opeartors related to the symbol ("
  , show op
  , ") are not allowed in the mode <"
  , show m
  , ">"
  ]

unifyType :: (ElModeSpec m) => ElType m -> ElType m -> Either String ()
unifyType ty ty0 = unless (ty `typeEq` ty0) $
  Left $ errTypeMismatch ty ty0

typeEq :: (ElModeSpec m) => ElType m -> ElType m -> Bool
typeEq = (==)

cutContext :: (ElModeSpec m) => ElContext m -> m -> Either String (ElContext m)
cutContext ctx m = do
  unless (isAllWeakenable (HashMap.filter (not . (>=!! m). snd) ctx)) $
    Left "A variable is not used but its mode does not allow weakening"
  pure (HashMap.filter ((>=!! m) . snd) ctx)
  where
    isAllWeakenable :: (ElModeSpec m) => ElContext m -> Bool
    isAllWeakenable = foldl helper True

    helper :: (ElModeSpec m) => Bool -> ElContextEntry m -> Bool
    helper False _       = False
    helper True  (_, m') = modeSt m' MdStWk

mergeUsage :: (ElModeSpec m) => ElContext m -> ElContext m -> Either String (ElContext m)
mergeUsage ctx0 ctx1 = do
  unless (isAllContractible (HashMap.intersection ctx0 ctx1)) $
    Left "A variable is used twice but its mode does not allow contraction"
  pure (HashMap.union ctx0 ctx1)
  where
    isAllContractible :: (ElModeSpec m) => ElContext m -> Bool
    isAllContractible = foldl helper True

    helper :: (ElModeSpec m) => Bool -> ElContextEntry m -> Bool
    helper False _      = False
    helper True  (_, m) = modeSt m MdStCo

removeVarUsage :: (ElModeSpec m) => ElContext m -> ElId -> m -> Either String (ElContext m)
removeVarUsage ctx x m = do
  unless (modeSt m MdStWk || HashMap.member x ctx) $
    Left $ "Variable \"" <> show x <> "\" is not used but its mode requires an usage"
  pure $ HashMap.delete x ctx

errTypeMismatch :: (ElModeSpec m) => ElType m -> ElType m -> String
errTypeMismatch ty0 ty1 =
  concat
  [ "Type mismatch: expected ("
  , show ty0
  , ") but get ("
  , show ty1
  , ")"
  ]

errTypeWrongForm :: (ElModeSpec m) => ElType m -> String -> String
errTypeWrongForm ty form =
  concat
  [ "Type mismatch: expected ("
  , form
  , ") but get ("
  , show ty
  , ")"
  ]
