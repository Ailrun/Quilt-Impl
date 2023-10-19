{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE OverloadedStrings #-}
module Elevator.TypeChecker where

import Control.Monad       (unless, when)
import Data.Foldable       (foldlM)
import Data.HashMap.Strict (HashMap)
import Data.HashMap.Strict qualified as HashMap
import Data.List           (foldl')
import Elevator.ModeSpec
import Elevator.Syntax
import Elevator.PrettyPrinter (prettyMode, showPrettyIndent)
import Prettyprinter
import Control.Monad.Extra (whenJust)
import Data.Traversable.Compat (mapAccumM)

data ElUsage
  = ElUnused
  | ElUsed
  deriving stock (Eq)

type ElContextEntry m = (ElType m, m)
type ElContext m = HashMap ElId (ElContextEntry m)

typeCheckProg :: (ElModeSpec m) => ElProgram m -> Either String (ElIProgram m)
typeCheckProg (ElProgram tops) = ElIProgram . snd <$> mapAccumM typeCheckAndAddTop HashMap.empty tops

typeCheckProgIncremental :: (ElModeSpec m) => ElIProgram m -> ElTop m -> Either String (ElITop m)
typeCheckProgIncremental (ElIProgram tops) top = snd <$> typeCheckAndAddTop ctx top
  where
    ctx = foldl' (flip (\(ElIDef x m ty _) -> HashMap.insert x (ty, m))) HashMap.empty tops

typeCheckAndAddTop :: (ElModeSpec m) => ElContext m -> ElTop m -> Either String (ElContext m, ElITop m)
typeCheckAndAddTop ctx (ElDef x m ty t) = do
  (_, it) <- typeCheckImpl m ctx' t ty
  pure (ctx', ElIDef x m ty it)
  where
    ctx' = HashMap.insert x (ty, m) ctx

typeInfer :: (ElModeSpec m) => ElIProgram m -> m -> ElTerm m -> Either String (ElITerm m, ElType m)
typeInfer (ElIProgram tops) m = fmap (\(_, it, ty) -> (it, ty)) . typeInferImpl m ctx
  where
    ctx = foldl' (flip (\(ElIDef x m' ty _) -> HashMap.insert x (ty, m'))) HashMap.empty tops

typeInferImpl :: (ElModeSpec m) => m -> ElContext m -> ElTerm m -> Either String (ElContext m, ElITerm m, ElType m)
typeInferImpl m ctx (TmVar x) =
  case HashMap.lookup x ctx of
    Just (ty, m') -> do
      verifyModeEq m m'
      pure (HashMap.singleton x (ty, m), ITmVar x, ty)
    Nothing       -> Left $ "Variable " <> show x <> " is not in scope"
typeInferImpl m _ TmTrue = do
  verifyModeOp MdOpBool m
  pure (HashMap.empty, ITmTrue, TyBool)
typeInferImpl m _ TmFalse = do
  verifyModeOp MdOpBool m
  pure (HashMap.empty, ITmFalse, TyBool)
typeInferImpl m ctx (TmIte t t0 t1) = do
  verifyModeOp MdOpBool m
  (usage, it) <- typeCheckImpl m ctx t TyBool
  (usage0, it0, ty) <- typeInferImpl m ctx t0
  (usage1, it1) <- typeCheckImpl m ctx t1 ty
  (, ITmIte it it0 it1, ty) <$> foldlM mergeUsage usage [usage0, usage1]
typeInferImpl m _ (TmNat n) = do
  verifyModeOp MdOpNat m
  pure (HashMap.empty, ITmNat n, TyNat)
typeInferImpl m ctx (TmSucc t) = do
  verifyModeOp MdOpNat m
  (usage, it) <- typeCheckImpl m ctx t TyNat
  pure (usage, ITmSucc it, TyNat)
typeInferImpl m ctx (TmNatCase t tz x ts) = do
  verifyModeOp MdOpNat m
  (usage, it) <- typeCheckImpl m ctx t TyNat
  (usagez, itz, ty) <- typeInferImpl m ctx tz
  (usages, its) <- typeCheckImpl m (HashMap.insert x (TyNat, m) ctx) ts ty
  usages' <- removeVarUsage usages x m
  (, ITmNatCase it itz x its, ty) <$> foldlM mergeUsage usage [usagez, usages']
typeInferImpl m ctx (TmBinOp bop t0 t1) = do
  verifyModeOp MdOpNat m
  when (retTy == TyBool) $
    verifyModeOp MdOpBool m
  (usage0, it0) <- typeCheckImpl m ctx t0 ty0
  (usage1, it1) <- typeCheckImpl m ctx t1 ty1
  (, ITmBinOp bop it0 it1, retTy) <$> mergeUsage usage0 usage1
  where
    (ty0, ty1, retTy) = elBinOpTypeWithMode m bop
typeInferImpl m ctx (TmLift (Just l) t) = do
  verifyModeGt m l
  verifyModeOp MdOpUp m
  (usage, it, ty) <- typeInferImpl l ctx t
  pure (usage, ITmLift l it, TyUp l m ty)
typeInferImpl _ _ (TmLift Nothing t) =
  Left $ "term\n" <> showPrettyIndent 80 2 (TmLift Nothing t) <> "\nshould have a mode annotation"
typeInferImpl m ctx (TmUnlift h t) = do
  verifyModeLt m h
  verifyModeOp MdOpUp h
  ctx' <- cutContext ctx h
  (usage, it, upTy) <- typeInferImpl h ctx' t
  case upTy of
    TyUp m' h' ty -> do
      verifyModeEq h h'
      verifyModeEq m m'
      pure (usage, ITmUnlift h it, ty)
    _ -> Left $ errTypeWrongForm upTy ("Up " <> show (prettyMode m <+> "=>" <+> prettyMode h) <> " _")
typeInferImpl m ctx (TmRet (Just h) t) = do
  verifyModeLt m h
  verifyModeOp MdOpDown m
  ctx' <- cutContext ctx h
  (usage, it, ty) <- typeInferImpl h ctx' t
  pure (usage, ITmRet h it, TyDown h m ty)
typeInferImpl _ _ (TmRet Nothing t) = do
  Left $ "term\n" <> showPrettyIndent 78 2 (TmRet Nothing t) <> "\nshould have a mode annotation"
typeInferImpl m ctx (TmLetRet h x t t0) = do
  whenJust h (verifyModeLt m)
  verifyModeOp MdOpDown m
  (usage, it, downLetTy) <- typeInferImpl m ctx t
  case downLetTy of
    TyDown h' m' letTy -> do
      whenJust h (`verifyModeEq` h')
      verifyModeEq m m'
      (usage0, it0, ty) <- typeInferImpl m (HashMap.insert x (letTy, h') ctx) t0
      usage0' <- removeVarUsage usage0 x h'
      (, ITmLetRet h' x it it0, ty) <$> mergeUsage usage usage0'
    _ -> Left $ errTypeWrongForm downLetTy ("Down " <> show (maybe "<_>" prettyMode h <+> "=>" <+> prettyMode m) <> " _")
typeInferImpl m ctx (TmLam x (Just argTy) t) = do
  verifyModeOp MdOpArr m
  (usage, it, ty) <- typeInferImpl m (HashMap.insert x (argTy, m) ctx) t
  (, ITmLam x argTy it, TyArr argTy ty) <$> removeVarUsage usage x m
typeInferImpl _ _ (TmLam x Nothing _) =
  Left $ "variable " <> show x <> " should have a type annotation"
typeInferImpl m ctx (TmApp t0 t1) = do
  verifyModeOp MdOpArr m
  (usage0, it0, funTy) <- typeInferImpl m ctx t0
  case funTy of
    TyArr argTy retTy -> do
      (usage1, it1) <- typeCheckImpl m ctx t1 argTy
      (, ITmApp it0 it1, retTy) <$> mergeUsage usage0 usage1
    _ -> Left $ errTypeWrongForm funTy "_ -> _"
typeInferImpl m ctx (TmAnn t ty) = (\(usage, it) -> (usage, it, ty)) <$> typeCheckImpl m ctx t ty

typeCheckImpl :: (ElModeSpec m) => m -> ElContext m -> ElTerm m -> ElType m -> Either String (ElContext m, ElITerm m)
typeCheckImpl m ctx (TmIte t t0 t1) ty = do
  verifyModeOp MdOpBool m
  (usage, it) <- typeCheckImpl m ctx t TyBool
  (usage0, it0) <- typeCheckImpl m ctx t0 ty
  (usage1, it1) <- typeCheckImpl m ctx t1 ty
  (, ITmIte it it0 it1) <$> foldlM mergeUsage usage [usage0, usage1]
typeCheckImpl m ctx (TmSucc t) ty = do
  verifyModeOp MdOpNat m
  unifyType TyNat ty
  fmap ITmSucc <$> typeCheckImpl m ctx t TyNat
typeCheckImpl m ctx (TmNatCase t tz x ts) ty = do
  verifyModeOp MdOpNat m
  (usage, it) <- typeCheckImpl m ctx t TyNat
  (usagez, itz) <- typeCheckImpl m ctx tz ty
  (usages, its) <- typeCheckImpl m (HashMap.insert x (TyNat, m) ctx) ts ty
  usages' <- removeVarUsage usages x m
  (, ITmNatCase it itz x its) <$> foldlM mergeUsage usage [usagez, usages']
typeCheckImpl m ctx (TmLift l t) ty = do
  whenJust l (verifyModeGt m)
  verifyModeOp MdOpUp m
  case ty of
    TyUp l' m' ty' -> do
      whenJust l (`verifyModeEq` l')
      verifyModeEq m m'
      fmap (ITmLift l') <$> typeCheckImpl l' ctx t ty'
    _ -> Left $ errTypeWrongForm ty ("Up " <> show (maybe "<_>" prettyMode l <+> "=>" <+> prettyMode m) <> " _")
typeCheckImpl m ctx (TmUnlift h t) ty = do
  verifyModeLt m h
  verifyModeOp MdOpUp h
  ctx' <- cutContext ctx h
  fmap (ITmUnlift h) <$> typeCheckImpl h ctx' t (TyUp m h ty)
typeCheckImpl m ctx (TmRet h t) ty = do
  whenJust h (verifyModeLt m)
  verifyModeOp MdOpDown m
  case ty of
    TyDown h' m' ty' -> do
      whenJust h (`verifyModeEq` h')
      verifyModeEq m m'
      ctx' <- cutContext ctx h'
      fmap (ITmRet h') <$> typeCheckImpl h' ctx' t ty'
    _ -> Left $ errTypeWrongForm ty ("Down " <> show (maybe "<_>" prettyMode h <+> "=>" <+> prettyMode m) <> " _")
typeCheckImpl m ctx (TmLetRet h x t t0) ty = do
  whenJust h (verifyModeLt m)
  verifyModeOp MdOpDown m
  (usage, it, downLetTy) <- typeInferImpl m ctx t
  case downLetTy of
    TyDown h' m' letTy -> do
      whenJust h (`verifyModeEq` h')
      verifyModeEq m m'
      (usage0, it0) <- typeCheckImpl m (HashMap.insert x (letTy, h') ctx) t0 ty
      usage0' <- removeVarUsage usage0 x h'
      (, ITmLetRet h' x it it0) <$> mergeUsage usage usage0'
    _ -> Left $ errTypeWrongForm downLetTy ("Down " <> show (maybe "<_>" prettyMode h <+> "=>" <+> prettyMode m) <> " _")
typeCheckImpl m ctx (TmLam x mayArgTy t) ty = do
  verifyModeOp MdOpArr m
  case ty of
    TyArr argTy' retTy -> do
      whenJust mayArgTy (unifyType argTy')
      (usage, it) <- typeCheckImpl m (HashMap.insert x (argTy', m) ctx) t retTy
      (, ITmLam x argTy' it) <$> removeVarUsage usage x m
    _ -> Left $ errTypeWrongForm ty "_ -> _"
typeCheckImpl m ctx t ty = do
  (usage, it, ty') <- typeInferImpl m ctx t
  unifyType ty ty'
  pure (usage, it)

verifyModeEq :: (ElModeSpec m) => m -> m -> Either String ()
verifyModeEq m n = unless (m == n) $ Left $ concat
  [ "Mode mismatch: expected "
  , show (prettyMode m)
  , " but get "
  , show (prettyMode n)
  ]

verifyModeGt :: (ElModeSpec m) => m -> m -> Either String ()
verifyModeGt m n = unless (m >!! n) $ Left $ concat
  [ "Mode mismatch: expected a mode smaller than "
  , show (prettyMode m)
  , " but get "
  , show (prettyMode n)
  ]

verifyModeLt :: (ElModeSpec m) => m -> m -> Either String ()
verifyModeLt m n = unless (m <!! n) $ Left $ concat
  [ "Mode mismatch: expected a mode greater than "
  , show (prettyMode m)
  , " but get "
  , show (prettyMode n)
  ]

verifyModeOp :: (ElModeSpec m) => ElMdOp -> m -> Either String ()
verifyModeOp op m = unless (modeOp m op) $ Left $ concat
  [ "Opeartors related to the symbol ("
  , show op
  , ") are not allowed in the mode "
  , show (prettyMode m)
  ]

unifyType :: (ElModeSpec m) => ElType m -> ElType m -> Either String ()
unifyType ty0 ty1 = unless (ty0 `typeEq` ty1) $
  Left $ errTypeMismatch ty0 ty1

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
    Left $ "Variable " <> show x <> " is not used but its mode requires an usage"
  pure $ HashMap.delete x ctx

errTypeMismatch :: (ElModeSpec m) => ElType m -> ElType m -> String
errTypeMismatch ty0 ty1 =
  unlines
  [ "Type mismatch: expected "
  , showPrettyIndent 80 2 ty0
  , " but get "
  , showPrettyIndent 80 2 ty1
  ]

errTypeWrongForm :: (ElModeSpec m) => ElType m -> String -> String
errTypeWrongForm ty form =
  unlines
  [ "Type mismatch: expected "
  , "  " <> form
  , " but get "
  , showPrettyIndent 80 2 ty
  ]
