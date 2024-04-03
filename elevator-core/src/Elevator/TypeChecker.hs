{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE ViewPatterns      #-}
module Elevator.TypeChecker where

import Control.Applicative        (Applicative (..))
import Control.Monad              (unless)
import Control.Monad.Error.Class  (MonadError (..), withError)
import Control.Monad.Reader.Class (MonadReader (..))
import Data.Bifunctor             (Bifunctor (..))
import Data.Foldable              (foldrM, traverse_)
import Data.Sequence              (Seq (..), pattern (:|>))
import Data.Sequence              qualified as Seq
import Elevator.ModeSpec
import Elevator.PrettyPrinter     (prettyContext, prettyMode, showDoc,
                                   showPrettyIndent)
import Elevator.Syntax

inferModeOfKind :: (ElModeSpec m) => ElKind m -> ElCheckM m (ElIKind m, m)
inferModeOfKind (KiType k)      = pure (IKiType k, k)
inferModeOfKind (KiUp k ctx ki) = do
  ictx <- inferContext ctx
  (iki, l) <- inferModeOfKind ki
  checkIsGTMode k l
  checkContextRange (Just l) (Just k) ictx
  pure (IKiUp k ictx iki, k)

inferModeOfKind_ :: (ElModeSpec m) => ElKind m -> ElCheckM m (ElIKind m)
inferModeOfKind_ = fmap fst . inferModeOfKind

getModeOfKind :: (ElModeSpec m) => ElIKind m -> m
getModeOfKind (IKiType k)   = k
getModeOfKind (IKiUp k _ _) = k

checkIsTypeKind :: (ElModeSpec m) => ElIKind m -> ElCheckM m m
checkIsTypeKind (IKiType k) = pure k
checkIsTypeKind iki         = throwError (TypingErrorInvalidKind iki)

inferKind :: (ElModeSpec m) => ElType m -> ElCheckM m (ElIType m, ElIKind m)
inferKind (TyVar _x)           = undefined
inferKind (TySusp _ctxh _ty)   = undefined
inferKind (TyForce _ctxh _ty)  = undefined
inferKind (TyData _tys _x)     = undefined
inferKind (TyBool k)           = pure (ITyBool k, IKiType k)
inferKind (TyInt k)            = pure (ITyInt k, IKiType k)
inferKind (TyProd _tys)        = undefined
inferKind (TyUp k ctx ty)      = do
  ictx <- inferContext ctx
  (ity, iki) <- inferKind ty
  l <- checkIsTypeKind iki
  checkIsLEMode l k
  pure (ITyUp k ictx ity, IKiType k)
inferKind (TyDown k ty)        = do
  (ity, iki) <- inferKind ty
  m <- checkIsTypeKind iki
  checkIsLEMode k m
  pure (ITyDown k ity, IKiType k)
inferKind (TyArr ty0 ty1)      = do
  (ity0, iki0) <- inferKind ty0
  (ity1, iki1) <- inferKind ty1
  k <- checkIsTypeKind iki0
  k' <- checkIsTypeKind iki1
  checkIsEQMode k k'
  pure (ITyArr ity0 ity1, iki1)
inferKind (TyForall x ki0 ty1) = do
  (iki0, m) <- inferModeOfKind ki0
  (ity1, iki1) <- local (:|> (x, m, ICEKind iki0)) $ inferKind ty1
  k <- checkIsTypeKind iki1
  checkIsGTMode m k
  pure (ITyForall x iki0 ity1, iki1)
inferKind (TyAnn _ty _ki) = undefined

checkKind :: (ElModeSpec m) => ElIKind m -> ElType m -> ElCheckM m (ElIType m)
checkKind ki          (TyVar _x)           = undefined
checkKind ki          (TySusp _ctxh _ty)   = undefined
checkKind ki          (TyForce _ctxh _ty)  = undefined
checkKind ki          (TyData _tys _x)     = undefined
checkKind (IKiType k) (TyBool k')          = pure (ITyBool k)
checkKind (IKiType k) (TyInt k')           = pure (ITyInt k)
checkKind ki          (TyProd _tys)        = undefined
checkKind ki          (TyUp k ctx ty)      = do
  ictx <- inferContext ctx
  (ity, iki) <- checkKind ty
  l <- checkIsTypeKind iki
  checkIsLEMode l k
  pure (ITyUp k ictx ity, IKiType k)
checkKind (IKiType k) (TyDown k' ty)       = do
  checkIsEQMode k k'
  (ity, iki) <- checkKind ty (IKiType k)
  m <- checkIsTypeKind iki
  checkIsLEMode k m
  checkIsLEMode k m
  pure (ITyDown k ity)
checkKind (IKiType k) (TyArr ty0 ty1)      = do
  ity0 <- checkKind (IKiType k) ty0
  ity1 <- checkKind (IKiType k) ty1
  pure (ITyArr ity0 ity1)
checkKind (IKiType k) (TyForall x ki0 ty1) = do
  (iki0, m) <- inferModeOfKind ki0
  checkIsGTMode m k
  ity1 <- local (:|> (x, m, ICEKind iki0)) $ checkKind (IKiType k) ty1
  pure (ITyForall x iki0 ity1)
checkKind ki          (TyAnn _ty _ki) = undefined

inferKind' :: (ElModeSpec m) => ElType m -> ElCheckM m (ElIType m, m)
inferKind' ty = do
  (ity, iki) <- inferKind ty
  pure (ity, getModeOfKind iki)

checkContextRange :: (ElModeSpec m) => Maybe m -> Maybe m -> ElIContext m -> ElCheckM m ()
checkContextRange mayL mayM ictx =
  withError (TypingErrorFor $ "context " <> showDoc 80 (prettyContext ((\(x, _, entry) -> (x, fromInternal entry)) <$> ictx)))
  . traverse_ checker
  $ ictx
  where
    checker =
      case (mayL, mayM) of
        (Just l, Just m) -> \(x, k, _) -> withError (TypingErrorFor $ "variable " <> show x) $ checkIsLEMode l k >> checkIsGTMode m k
        (_,      Just m) -> \(x, k, _) -> withError (TypingErrorFor $ "variable " <> show x) $ checkIsGTMode m k
        (Just l, _)      -> \(x, k, _) -> withError (TypingErrorFor $ "variable " <> show x) $ checkIsLEMode l k
        _                -> const (pure ())

inferContextEntry :: (ElModeSpec m) => ElContextEntry m -> ElCheckM m (ElIContextEntry m, m)
inferContextEntry (CEKind ki) = first ICEKind <$> inferModeOfKind ki
inferContextEntry (CEType ty) = first ICEType <$> inferKind' ty

inferContext :: (ElModeSpec m) => ElContext m -> ElCheckM m (ElIContext m)
inferContext = foldrM folder Seq.empty
  where
    folder (x, entry) ictx =
      (ictx :|>) . uncurry (flip (x,,))
      <$> local (<> ictx) (inferContextEntry entry)

checkIsGTMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> m -> em ()
checkIsGTMode m k = unless (m >!! k) $ throwError $ TypingErrorModeOrderMismatch "GT" m k

checkIsLEMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> m -> em ()
checkIsLEMode l k = unless (l <=!! k) $ throwError $ TypingErrorModeOrderMismatch "LE" l k

checkIsEQMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> m -> em ()
checkIsEQMode l k = unless (l == k) $ throwError $ TypingErrorModeOrderMismatch "EQ" l k

checkIsCoMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> em ()
checkIsCoMode k = unless (modeSt k MdStCo) $ throwError $ TypingErrorModeStructuralRule MdStCo k

-- typeCheckProg :: (ElModeSpec m) => ElProgram m -> Either String (ElIProgram m)
-- typeCheckProg (ElProgram tops) = ElIProgram . snd <$> mapAccumM typeCheckAndAddTop HashMap.empty tops

-- typeCheckProgIncremental :: (ElModeSpec m) => ElIProgram m -> ElTop m -> Either String (ElITop m)
-- typeCheckProgIncremental (ElIProgram tops) top = snd <$> typeCheckAndAddTop ctx top
--   where
--     ctx = foldl' (flip (\(ElIDef x m ty _) -> HashMap.insert x (ty, m))) HashMap.empty tops

-- typeCheckAndAddTop :: (ElModeSpec m) => ElContext m -> ElTop m -> Either String (ElContext m, ElITop m)
-- typeCheckAndAddTop ctx (ElDef x m ty t) = do
--   (_, it) <- typeCheckImpl m ctx' t ty
--   pure (ctx', ElIDef x m ty it)
--   where
--     ctx' = HashMap.insert x (ty, m) ctx

-- typeInfer :: (ElModeSpec m) => ElIProgram m -> m -> ElTerm m -> Either String (ElITerm m, ElType m)
-- typeInfer (ElIProgram tops) m = fmap (\(_, it, ty) -> (it, ty)) . typeInferImpl m ctx
--   where
--     ctx = foldl' (flip (\(ElIDef x m' ty _) -> HashMap.insert x (ty, m'))) HashMap.empty tops

-- typeInferImpl :: (ElModeSpec m) => m -> ElContext m -> ElTerm m -> Either String (ElContext m, ElITerm m, ElType m)
-- typeInferImpl m ctx (TmVar x) =
--   case HashMap.lookup x ctx of
--     Just (ty, m') -> do
--       verifyModeEq m m'
--       pure (HashMap.singleton x (ty, m), ITmVar x, ty)
--     Nothing       -> Left $ "Variable " <> show x <> " is not in scope"
-- typeInferImpl m _ TmTrue = do
--   verifyModeOp MdOpBool m
--   pure (HashMap.empty, ITmTrue, TyBool)
-- typeInferImpl m _ TmFalse = do
--   verifyModeOp MdOpBool m
--   pure (HashMap.empty, ITmFalse, TyBool)
-- typeInferImpl m ctx (TmIte t t0 t1) = do
--   verifyModeOp MdOpBool m
--   (usage, it) <- typeCheckImpl m ctx t TyBool
--   (usage0, it0, ty) <- typeInferImpl m ctx t0
--   (usage1, it1) <- typeCheckImpl m ctx t1 ty
--   (, ITmIte it it0 it1, ty) <$> foldlM mergeUsage usage [usage0, usage1]
-- typeInferImpl m _ (TmNat n) = do
--   verifyModeOp MdOpNat m
--   pure (HashMap.empty, ITmNat n, TyNat)
-- typeInferImpl m ctx (TmSucc t) = do
--   verifyModeOp MdOpNat m
--   (usage, it) <- typeCheckImpl m ctx t TyNat
--   pure (usage, ITmSucc it, TyNat)
-- typeInferImpl m ctx (TmNatCase t tz x ts) = do
--   verifyModeOp MdOpNat m
--   (usage, it) <- typeCheckImpl m ctx t TyNat
--   (usagez, itz, ty) <- typeInferImpl m ctx tz
--   (usages, its) <- typeCheckImpl m (HashMap.insert x (TyNat, m) ctx) ts ty
--   usages' <- removeVarUsage usages x m
--   (, ITmNatCase it itz x its, ty) <$> foldlM mergeUsage usage [usagez, usages']
-- typeInferImpl m ctx (TmBinOp bop t0 t1) = do
--   verifyModeOp MdOpNat m
--   when (retTy == TyBool) $
--     verifyModeOp MdOpBool m
--   (usage0, it0) <- typeCheckImpl m ctx t0 ty0
--   (usage1, it1) <- typeCheckImpl m ctx t1 ty1
--   (, ITmBinOp bop it0 it1, retTy) <$> mergeUsage usage0 usage1
--   where
--     (ty0, ty1, retTy) = elBinOpTypeWithMode m bop
-- typeInferImpl m ctx (TmLift (Just l) t) = do
--   verifyModeGt m l
--   verifyModeOp MdOpUp m
--   (usage, it, ty) <- typeInferImpl l ctx t
--   pure (usage, ITmLift l it, TyUp l m ty)
-- typeInferImpl _ _ (TmLift Nothing t) =
--   Left $ "term\n" <> showPrettyIndent 80 2 (TmLift Nothing t) <> "\nshould have a mode annotation"
-- typeInferImpl m ctx (TmUnlift h t) = do
--   verifyModeLt m h
--   verifyModeOp MdOpUp h
--   ctx' <- cutContext ctx h
--   (usage, it, upTy) <- typeInferImpl h ctx' t
--   case upTy of
--     TyUp m' h' ty -> do
--       verifyModeEq h h'
--       verifyModeEq m m'
--       pure (usage, ITmUnlift h it, ty)
--     _ -> Left $ errTypeWrongForm upTy ("Up " <> show (prettyMode m <+> "=>" <+> prettyMode h) <> " _")
-- typeInferImpl m ctx (TmRet (Just h) t) = do
--   verifyModeLt m h
--   verifyModeOp MdOpDown m
--   ctx' <- cutContext ctx h
--   (usage, it, ty) <- typeInferImpl h ctx' t
--   pure (usage, ITmRet h it, TyDown h m ty)
-- typeInferImpl _ _ (TmRet Nothing t) = do
--   Left $ "term\n" <> showPrettyIndent 78 2 (TmRet Nothing t) <> "\nshould have a mode annotation"
-- typeInferImpl m ctx (TmLetRet h x t t0) = do
--   whenJust h (verifyModeLt m)
--   verifyModeOp MdOpDown m
--   (usage, it, downLetTy) <- typeInferImpl m ctx t
--   case downLetTy of
--     TyDown h' m' letTy -> do
--       whenJust h (`verifyModeEq` h')
--       verifyModeEq m m'
--       (usage0, it0, ty) <- typeInferImpl m (HashMap.insert x (letTy, h') ctx) t0
--       usage0' <- removeVarUsage usage0 x h'
--       (, ITmLetRet h' x it it0, ty) <$> mergeUsage usage usage0'
--     _ -> Left $ errTypeWrongForm downLetTy ("Down " <> show (maybe "<_>" prettyMode h <+> "=>" <+> prettyMode m) <> " _")
-- typeInferImpl m ctx (TmLam x (Just argTy) t) = do
--   verifyModeOp MdOpArr m
--   (usage, it, ty) <- typeInferImpl m (HashMap.insert x (argTy, m) ctx) t
--   (, ITmLam x argTy it, TyArr argTy ty) <$> removeVarUsage usage x m
-- typeInferImpl _ _ (TmLam x Nothing _) =
--   Left $ "variable " <> show x <> " should have a type annotation"
-- typeInferImpl m ctx (TmApp t0 t1) = do
--   verifyModeOp MdOpArr m
--   (usage0, it0, funTy) <- typeInferImpl m ctx t0
--   case funTy of
--     TyArr argTy retTy -> do
--       (usage1, it1) <- typeCheckImpl m ctx t1 argTy
--       (, ITmApp it0 it1, retTy) <$> mergeUsage usage0 usage1
--     _ -> Left $ errTypeWrongForm funTy "_ -> _"
-- typeInferImpl m ctx (TmAnn t ty) = (\(usage, it) -> (usage, it, ty)) <$> typeCheckImpl m ctx t ty

-- typeCheckImpl :: (ElModeSpec m) => m -> ElContext m -> ElTerm m -> ElType m -> Either String (ElContext m, ElITerm m)
-- typeCheckImpl m ctx (TmIte t t0 t1) ty = do
--   verifyModeOp MdOpBool m
--   (usage, it) <- typeCheckImpl m ctx t TyBool
--   (usage0, it0) <- typeCheckImpl m ctx t0 ty
--   (usage1, it1) <- typeCheckImpl m ctx t1 ty
--   (, ITmIte it it0 it1) <$> foldlM mergeUsage usage [usage0, usage1]
-- typeCheckImpl m ctx (TmSucc t) ty = do
--   verifyModeOp MdOpNat m
--   unifyType TyNat ty
--   fmap ITmSucc <$> typeCheckImpl m ctx t TyNat
-- typeCheckImpl m ctx (TmNatCase t tz x ts) ty = do
--   verifyModeOp MdOpNat m
--   (usage, it) <- typeCheckImpl m ctx t TyNat
--   (usagez, itz) <- typeCheckImpl m ctx tz ty
--   (usages, its) <- typeCheckImpl m (HashMap.insert x (TyNat, m) ctx) ts ty
--   usages' <- removeVarUsage usages x m
--   (, ITmNatCase it itz x its) <$> foldlM mergeUsage usage [usagez, usages']
-- typeCheckImpl m ctx (TmLift l t) ty = do
--   whenJust l (verifyModeGt m)
--   verifyModeOp MdOpUp m
--   case ty of
--     TyUp l' m' ty' -> do
--       whenJust l (`verifyModeEq` l')
--       verifyModeEq m m'
--       fmap (ITmLift l') <$> typeCheckImpl l' ctx t ty'
--     _ -> Left $ errTypeWrongForm ty ("Up " <> show (maybe "<_>" prettyMode l <+> "=>" <+> prettyMode m) <> " _")
-- typeCheckImpl m ctx (TmUnlift h t) ty = do
--   verifyModeLt m h
--   verifyModeOp MdOpUp h
--   ctx' <- cutContext ctx h
--   fmap (ITmUnlift h) <$> typeCheckImpl h ctx' t (TyUp m h ty)
-- typeCheckImpl m ctx (TmRet h t) ty = do
--   whenJust h (verifyModeLt m)
--   verifyModeOp MdOpDown m
--   case ty of
--     TyDown h' m' ty' -> do
--       whenJust h (`verifyModeEq` h')
--       verifyModeEq m m'
--       ctx' <- cutContext ctx h'
--       fmap (ITmRet h') <$> typeCheckImpl h' ctx' t ty'
--     _ -> Left $ errTypeWrongForm ty ("Down " <> show (maybe "<_>" prettyMode h <+> "=>" <+> prettyMode m) <> " _")
-- typeCheckImpl m ctx (TmLetRet h x t t0) ty = do
--   whenJust h (verifyModeLt m)
--   verifyModeOp MdOpDown m
--   (usage, it, downLetTy) <- typeInferImpl m ctx t
--   case downLetTy of
--     TyDown h' m' letTy -> do
--       whenJust h (`verifyModeEq` h')
--       verifyModeEq m m'
--       (usage0, it0) <- typeCheckImpl m (HashMap.insert x (letTy, h') ctx) t0 ty
--       usage0' <- removeVarUsage usage0 x h'
--       (, ITmLetRet h' x it it0) <$> mergeUsage usage usage0'
--     _ -> Left $ errTypeWrongForm downLetTy ("Down " <> show (maybe "<_>" prettyMode h <+> "=>" <+> prettyMode m) <> " _")
-- typeCheckImpl m ctx (TmLam x mayArgTy t) ty = do
--   verifyModeOp MdOpArr m
--   case ty of
--     TyArr argTy' retTy -> do
--       whenJust mayArgTy (unifyType argTy')
--       (usage, it) <- typeCheckImpl m (HashMap.insert x (argTy', m) ctx) t retTy
--       (, ITmLam x argTy' it) <$> removeVarUsage usage x m
--     _ -> Left $ errTypeWrongForm ty "_ -> _"
-- typeCheckImpl m ctx t ty = do
--   (usage, it, ty') <- typeInferImpl m ctx t
--   unifyType ty ty'
--   pure (usage, it)

data ElTypingError m
  = TypingErrorInvalidKind (ElIKind m)
  | TypingErrorInvalidMultipleUsage ElId m
  | TypingErrorModeOrderMismatch String m m
  | TypingErrorModeStructuralRule ElMdSt m
  | TypingErrorFor String (ElTypingError m)
  deriving stock (Eq)

newtype ElUsage m = ElUsage { getElUsage :: Seq (ElId, m) }

newtype ElCheckM m a
  = ElCheckM
    { runElCheckM :: ElIContext m -> Either (ElTypingError m) (ElUsage m, a)
    }
  deriving (Functor)

pattern UEmpty :: ElUsage m
pattern UEmpty = ElUsage Empty

pattern (:+!) :: ElUsage m -> (ElId, m) -> ElUsage m
pattern (:+!) xs p <- ElUsage ((ElUsage -> xs) :|> p) where
  (:+!) xs p = ElUsage (getElUsage xs :|> p)

{-# COMPLETE UEmpty, (:+!) #-}

instance (ElModeSpec m) => Applicative (ElCheckM m) where
  pure = ElCheckM . const . pure . (UEmpty,)
  fm <*> am = ElCheckM $ \tctx -> do
    (fuse, f) <- runElCheckM fm tctx
    (ause, a) <- runElCheckM am tctx
    (, f a) <$> mergeUsage fuse ause
  liftA2 f am bm = ElCheckM $ \tctx -> do
    (ause, a) <- runElCheckM am tctx
    (buse, b) <- runElCheckM bm tctx
    (, f a b) <$> mergeUsage ause buse

instance (ElModeSpec m) => Monad (ElCheckM m) where
  am >>= f = ElCheckM $ \tctx -> do
    (ause, a) <- runElCheckM am tctx
    (buse, b) <- runElCheckM (f a) tctx
    (, b) <$> mergeUsage ause buse

instance (ElModeSpec m) => Control.Monad.Reader.Class.MonadReader (ElIContext m) (ElCheckM m) where
  ask = ElCheckM $ pure . (UEmpty,)
  local f am = ElCheckM $ runElCheckM am . f

instance (ElModeSpec m) => MonadError (ElTypingError m) (ElCheckM m) where
  throwError = ElCheckM . const . Left
  catchError am f = ElCheckM $ \tctx -> catchError (runElCheckM am tctx) (flip runElCheckM tctx . f)

mergeUsage :: (ElModeSpec m) => ElUsage m -> ElUsage m -> Either (ElTypingError m) (ElUsage m)
mergeUsage UEmpty            use1 = pure use1
mergeUsage (use0 :+! (x, k)) use1
  | Just i <- Seq.findIndexR ((x ==) . fst) (getElUsage use1) = do
      let (_, k') = getElUsage use1 `Seq.index` i
      checkIsEQMode k k'
      checkIsCoMode k
      use <- mergeUsage use0 . ElUsage . Seq.deleteAt i $ getElUsage use1
      pure $ use :+! (x, k)
  | otherwise = do
      use <- mergeUsage use0 use1
      pure $ use :+! (x, k)

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

typeEq :: (ElModeSpec m) => ElType m -> ElType m -> Bool
typeEq = undefined

-- cutContext :: (ElModeSpec m) => ElContext m -> m -> Either String (ElContext m)
-- cutContext ctx m = do
--   unless (isAllWeakenable (HashMap.filter (not . (>=!! m). snd) ctx)) $
--     Left "A variable is not used but its mode does not allow weakening"
--   pure (HashMap.filter ((>=!! m) . snd) ctx)
--   where
--     isAllWeakenable :: (ElModeSpec m) => ElContext m -> Bool
--     isAllWeakenable = foldl helper True

--     helper :: (ElModeSpec m) => Bool -> ElContextEntry m -> Bool
--     helper False _       = False
--     helper True  (_, m') = modeSt m' MdStWk

-- mergeUsage :: (ElModeSpec m) => ElContext m -> ElContext m -> Either String (ElContext m)
-- mergeUsage ctx0 ctx1 = do
--   unless (isAllContractible (HashMap.intersection ctx0 ctx1)) $
--     Left "A variable is used twice but its mode does not allow contraction"
--   pure (HashMap.union ctx0 ctx1)
--   where
--     isAllContractible :: (ElModeSpec m) => ElContext m -> Bool
--     isAllContractible = foldl helper True

--     helper :: (ElModeSpec m) => Bool -> ElContextEntry m -> Bool
--     helper False _      = False
--     helper True  (_, m) = modeSt m MdStCo

-- removeVarUsage :: (ElModeSpec m) => ElContext m -> ElId -> m -> Either String (ElContext m)
-- removeVarUsage ctx x m = do
--   unless (modeSt m MdStWk || HashMap.member x ctx) $
--     Left $ "Variable " <> show x <> " is not used but its mode requires an usage"
--   pure $ HashMap.delete x ctx

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
