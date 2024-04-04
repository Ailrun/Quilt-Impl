{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE ViewPatterns      #-}
module Elevator.TypeChecker where

import Control.Applicative        (Applicative (..))
import Control.Monad              (unless, void)
import Control.Monad.Error.Class  (MonadError (..), withError)
import Control.Monad.Reader.Class (MonadReader (..))
import Data.Bifunctor             (Bifunctor (..))
import Data.Foldable              (foldrM, traverse_)
import Data.Sequence              (Seq (..), pattern (:|>))
import Data.Sequence              qualified as Seq
import Data.Tuple.Extra           (fst3)
import Elevator.ModeSpec
import Elevator.Syntax

checkWFOfKind :: (ElModeSpec m) => ElKind m -> ElCheckM m (ElIKind m, m)
checkWFOfKind (KiType k)          = pure (IKiType k, k)
checkWFOfKind ki@(KiUp k ctx ki') = do
  ictx <- checkContext ctx
  (iki', l) <- checkWFOfKind ki'
  testIsGTMode k l
  withError (TEFor $ TETKind ki) $ checkContextRange (Just l) (Just k) ictx
  pure (IKiUp k ictx iki', k)

checkWFOfKind_ :: (ElModeSpec m) => ElKind m -> ElCheckM m (ElIKind m)
checkWFOfKind_ = fmap fst . checkWFOfKind

getModeOfIKind :: (ElModeSpec m) => ElIKind m -> m
getModeOfIKind (IKiType k)   = k
getModeOfIKind (IKiUp k _ _) = k

testIsKindType :: (ElModeSpec m) => ElIKind m -> ElCheckM m m
testIsKindType (IKiType k) = pure k
testIsKindType iki         = throwError (TEInvalidKind iki)

checkWFOfType :: (ElModeSpec m) => ElType m -> ElCheckM m (ElIType m, m)
checkWFOfType (TyVar x)            = do
  (m, ientry) <- lookupTypeAndUseInIctx x
  case ientry of
    ICEKind iki -> do
      void $ testIsKindType iki
      pure (ITyVar x, m)
    ICEType _ -> throwError $ TEInvalidEntryForTypeVariable x ientry
checkWFOfType (TySusp _ctxh _ty)   = undefined
checkWFOfType (TyForce _ctxh _ty)  = undefined
-- TODO: Add kind annotation to type arguments
checkWFOfType (TyData _tys _x)     = undefined
checkWFOfType (TyBool k)           = pure (ITyBool k, k)
checkWFOfType (TyInt k)            = pure (ITyInt k, k)
checkWFOfType (TyProd [])          = throwError TEInvalidEmptyProd
checkWFOfType (TyProd (ty:tys))    = do
  (ity, k) <- checkWFOfType ty
  (itys, ks) <- unzip <$> traverse checkWFOfType tys
  traverse_ (testIsSameMode k) ks
  pure (ITyProd (ity:itys), k)
checkWFOfType (TyUp k ctx ty)      = do
  ictx <- checkContext ctx
  (ity, l) <- checkWFOfType ty
  testIsLEMode l k
  pure (ITyUp k ictx ity, k)
checkWFOfType (TyDown k ty)        = do
  (ity, m) <- checkWFOfType ty
  -- We should test that ty only use entries >= m
  testIsLEMode k m
  pure (ITyDown k ity, k)
checkWFOfType (TyArr ty0 ty1)      = do
  (ity0, k0) <- checkWFOfType ty0
  (ity1, k1) <- checkWFOfType ty1
  testIsSameMode k0 k1
  pure (ITyArr ity0 ity1, k1)
checkWFOfType (TyForall x ki0 ty1) = do
  (iki0, m) <- checkWFOfKind ki0
  (ity1, k) <- local (:|> (x, m, ICEKind iki0)) $ checkWFOfType ty1
  testIsGTMode m k
  pure (ITyForall x iki0 ity1, k)
checkWFOfType (TyAnn ty ki)        = do
  (iki, k) <- checkWFOfKind ki
  void $ testIsKindType iki
  ity <- checkKind iki ty
  pure (ity, k)

checkKind :: (ElModeSpec m) => ElIKind m -> ElType m -> ElCheckM m (ElIType m)
checkKind iki (TyVar x)        = do
  (_, ientry) <- lookupTypeAndUseInIctx x
  case ientry of
    ICEKind iki' -> do
      unifyIKind iki iki'
      pure (ITyVar x)
    ICEType _ -> throwError $ TEInvalidEntryForTypeVariable x ientry
checkKind iki (TySusp ctxh ty)
  | IKiUp m ictx iki' <- iki   = do
    ictxh <- checkContextHat ctxh ictx
    ity <- local (<> ictx) $ checkKind iki' ty
    pure $ ITySusp m ictxh ity
  | otherwise                  = throwError $ TEInvalidKindForSusp iki
checkKind iki (TyForce ty sub) = undefined
checkKind iki (TyAnn _ty _ki)  = undefined
checkKind iki ty               = do
  k' <- testIsKindType iki
  (ity, k) <- checkWFOfType ty
  testIsSameMode k k'
  pure ity

inferKind :: (ElModeSpec m) => ElType m -> ElCheckM m (ElIType m, ElIKind m)
inferKind (TyVar _x)           = undefined
inferKind (TySusp _ctxh _ty)   = undefined
inferKind (TyForce _ctxh _ty)  = undefined
inferKind (TyData _tys _x)     = undefined
inferKind (TyBool k)           = pure (ITyBool k, IKiType k)
inferKind (TyInt k)            = pure (ITyInt k, IKiType k)
inferKind (TyProd _tys)        = undefined
inferKind (TyUp k ctx ty)      = do
  ictx <- checkContext ctx
  (ity, iki) <- inferKind ty
  l <- testIsKindType iki
  testIsLEMode l k
  pure (ITyUp k ictx ity, IKiType k)
inferKind (TyDown k ty)        = do
  (ity, iki) <- inferKind ty
  m <- testIsKindType iki
  testIsLEMode k m
  pure (ITyDown k ity, IKiType k)
inferKind (TyArr ty0 ty1)      = do
  (ity0, iki0) <- inferKind ty0
  (ity1, iki1) <- inferKind ty1
  k <- testIsKindType iki0
  k' <- testIsKindType iki1
  testIsSameMode k k'
  pure (ITyArr ity0 ity1, iki1)
inferKind (TyForall x ki0 ty1) = do
  (iki0, m) <- checkWFOfKind ki0
  (ity1, iki1) <- local (:|> (x, m, ICEKind iki0)) $ inferKind ty1
  k <- testIsKindType iki1
  testIsGTMode m k
  pure (ITyForall x iki0 ity1, iki1)
inferKind (TyAnn _ty _ki) = undefined

inferKind' :: (ElModeSpec m) => ElType m -> ElCheckM m (ElIType m, m)
inferKind' ty = do
  (ity, iki) <- inferKind ty
  pure (ity, getModeOfIKind iki)

checkContextRange :: (ElModeSpec m) => Maybe m -> Maybe m -> ElIContext m -> ElCheckM m ()
checkContextRange mayL mayM ictx =
  withError (TEFor $ TETContext $ (\(x, _, entry) -> (x, fromInternal entry)) <$> ictx)
  . traverse_ checker
  $ ictx
  where
    checker =
      case (mayL, mayM) of
        (Just l, Just m) -> \(x, k, _) -> withError (TEFor $ TETVariable x) $ testIsLEMode l k >> testIsGTMode m k
        (_,      Just m) -> \(x, k, _) -> withError (TEFor $ TETVariable x) $ testIsGTMode m k
        (Just l, _)      -> \(x, k, _) -> withError (TEFor $ TETVariable x) $ testIsLEMode l k
        _                -> const (pure ())

checkContextEntry :: (ElModeSpec m) => ElContextEntry m -> ElCheckM m (ElIContextEntry m, m)
checkContextEntry (CEKind ki) = first ICEKind <$> checkWFOfKind ki
checkContextEntry (CEType ty) = first ICEType <$> checkWFOfType ty

-- This works only when all entries in input context have lower modes
-- than any entry in the ambient context.
checkContext :: (ElModeSpec m) => ElContext m -> ElCheckM m (ElIContext m)
checkContext = foldrM folder Seq.empty
  where
    folder (x, entry) ictx =
      (ictx :|>) . uncurry (flip (x,,))
      <$> local (<> ictx) (checkContextEntry entry)

checkContextHat :: (ElModeSpec m) => ElContextHat m -> ElIContext m -> ElCheckM m (ElIContextHat m)
checkContextHat ctxh ictx = do
  unless (ctxh == fmap fst (putIHat ictx)) $ throwError $ TEContextHatConflict ctxh ictx
  pure $ putIHat ictx

testIsGTMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> m -> em ()
testIsGTMode m k = unless (m >!! k) $ throwError $ TEModeOrderFailure TEMOGT m k

testIsLEMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> m -> em ()
testIsLEMode l k = unless (l <=!! k) $ throwError $ TEModeOrderFailure TEMOLE l k

testIsSameMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> m -> em ()
testIsSameMode k0 k1 = unless (k0 == k1) $ throwError $ TEModeNotEqual k0 k1

testIsCoMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> em ()
testIsCoMode k = unless (modeSt k MdStCo) $ throwError $ TEModeStructuralRule MdStCo k

testIsWkMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> em ()
testIsWkMode k = unless (modeSt k MdStWk) $ throwError $ TEModeStructuralRule MdStWk k

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
--   unifyIType TyNat ty
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
--       whenJust mayArgTy (unifyIType argTy')
--       (usage, it) <- typeCheckImpl m (HashMap.insert x (argTy', m) ctx) t retTy
--       (, ITmLam x argTy' it) <$> removeVarUsage usage x m
--     _ -> Left $ errTypeWrongForm ty "_ -> _"
-- typeCheckImpl m ctx t ty = do
--   (usage, it, ty') <- typeInferImpl m ctx t
--   unifyIType ty ty'
--   pure (usage, it)

data ElTypingErrorModeOrdering
  = TEMOGT
  | TEMOGE
  | TEMOLT
  | TEMOLE

data ElTypingErrorTarget m
  = TETContext (ElContext m)
  | TETVariable ElId
  | TETMode m
  | TETTerm (ElTerm m)
  | TETType (ElType m)
  | TETKind (ElKind m)
  | TETIKindUnification (ElIKind m) (ElIKind m)
  | TETITypeUnification (ElIType m) (ElIType m)
  | TETIContextUnification (ElIContext m) (ElIContext m)

data ElTypingError m
  = TEInvalidKind (ElIKind m)
  | TENotInScope ElId
  | TEVariableClassMismatch ElId
  | TEInvalidEntryForTypeVariable ElId (ElIContextEntry m)
  | TEInvalidMultipleUsage ElId m
  | TEInvalidEmptyProd
  | TEInvalidKindForSusp (ElIKind m)
  | TEIdentifierMismatch ElId ElId
  | TEUnunifiableIKinds (ElIKind m) (ElIKind m)
  | TEUnunifiableITypes (ElIType m) (ElIType m)
  | TEUnunifiableIContexts (ElIContext m) (ElIContext m)
  | TEContextHatConflict (ElContextHat m) (ElIContext m)
  | TEModeOrderFailure ElTypingErrorModeOrdering m m
  | TEModeNotEqual m m
  | TEModeStructuralRule ElMdSt m
  | TEFor (ElTypingErrorTarget m) (ElTypingError m)
  | TEUnunifiableEntry (ElIContextEntry m) (ElIContextEntry m)

newtype ElUsage m = ElUsage { getElUsage :: Seq (ElId, Maybe m) }

newtype ElCheckM m a
  = ElCheckM
    { runElCheckM :: ElIContext m -> Either (ElTypingError m) (ElUsage m, a)
    }
  deriving (Functor)

pattern UEmpty :: ElUsage m
pattern UEmpty = ElUsage Empty

pattern (:+!) :: ElUsage m -> (ElId, Maybe m) -> ElUsage m
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

instance (ElModeSpec m) => MonadReader (ElIContext m) (ElCheckM m) where
  ask = ElCheckM $ pure . (UEmpty,)
  local f am = ElCheckM $ runElCheckM am . f

instance (ElModeSpec m) => MonadError (ElTypingError m) (ElCheckM m) where
  throwError = ElCheckM . const . Left
  catchError am f = ElCheckM $ \tctx -> catchError (runElCheckM am tctx) (flip runElCheckM tctx . f)

mergeUsage :: (ElModeSpec m) => ElUsage m -> ElUsage m -> Either (ElTypingError m) (ElUsage m)
mergeUsage UEmpty            use1 = pure use1
mergeUsage (use0 :+! (x, mayK)) use1
  | Just i <- Seq.findIndexR ((x ==) . fst) (getElUsage use1) = do
      let (_, mayK') = getElUsage use1 `Seq.index` i
      case (mayK, mayK') of
        (Just k, Just k') -> do
          testIsSameMode k k'
          testIsCoMode k
        (Nothing, Nothing) -> pure ()
        _ -> throwError $ TEVariableClassMismatch x
      use <- mergeUsage use0 . ElUsage . Seq.deleteAt i $ getElUsage use1
      pure $ use :+! (x, mayK)
  | otherwise = do
      use <- mergeUsage use0 use1
      pure $ use :+! (x, mayK)

useTypeVariable :: ElId -> ElCheckM m ()
useTypeVariable x = ElCheckM . const $ pure (UEmpty :+! (x, Nothing), ())

useTermVariable :: ElId -> m -> ElCheckM m ()
useTermVariable x m = ElCheckM . const $ pure (UEmpty :+! (x, Just m), ())

lookupTypeAndUseInIctx :: (ElModeSpec m) => ElId -> ElCheckM m (m, ElIContextEntry m)
lookupTypeAndUseInIctx x = do
  (m, ientry) <- lookupInIctx x
  case ientry of
    ICEKind _ -> do
      useTypeVariable x
      pure (m, ientry)
    ICEType _ -> throwError $ TEVariableClassMismatch x

lookupInIctx :: (ElModeSpec m) => ElId -> ElCheckM m (m, ElIContextEntry m)
lookupInIctx x = do
  ictx <- ask
  let mayI = Seq.findIndexR ((x ==) . fst3) ictx
  case mayI of
    Just i  -> let (_, m, ientry) = ictx `Seq.index` i in pure (m, ientry)
    Nothing -> throwError $ TENotInScope x

unifyIKind :: (ElModeSpec m) => ElIKind m -> ElIKind m -> ElCheckM m ()
unifyIKind iki0@(IKiType k0)      iki1@(IKiType k1)      = withError (TEFor $ TETIKindUnification iki0 iki1) $ testIsSameMode k0 k1
unifyIKind (IKiUp k0 ictx0 iki0') (IKiUp k1 ictx1 iki1') = do
  testIsSameMode k0 k1
  unifyIContext ictx0 ictx1
  unifyIKind iki0' iki1'
unifyIKind iki0                   iki1                   = throwError $ TEUnunifiableIKinds iki0 iki1

unifyIType :: (ElModeSpec m) => ElIType m -> ElIType m -> ElCheckM m ()
unifyIType _ity0 _ity1 = undefined

unifyIContext :: (ElModeSpec m) => ElIContext m -> ElIContext m -> ElCheckM m ()
unifyIContext ictx0 ictx1 = do
  unless (length ictx0 == length ictx1) $ throwError $ TEUnunifiableIContexts ictx0 ictx1
  withError (TEFor $ TETIContextUnification ictx0 ictx1) $ traverse_ (uncurry helper) $ Seq.zip ictx0 ictx1
  where
    helper :: (ElModeSpec m) => (ElId, m, ElIContextEntry m) -> (ElId, m, ElIContextEntry m) -> ElCheckM m ()
    helper (x0, m0, entry0) (x1, m1, entry1) = do
      unless (x0 == x1) $ throwError $ TEIdentifierMismatch x0 x1
      testIsSameMode m0 m1
      unifyIContextEntry entry0 entry1

unifyIContextEntry :: (ElModeSpec m) => ElIContextEntry m -> ElIContextEntry m -> ElCheckM m ()
unifyIContextEntry (ICEKind iki0) (ICEKind iki1) = unifyIKind iki0 iki1
unifyIContextEntry (ICEType ity0) (ICEType ity1) = unifyIType ity0 ity1
unifyIContextEntry entry0         entry1         = throwError $ TEUnunifiableEntry entry0 entry1

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

-- errTypeMismatch :: (ElModeSpec m) => ElType m -> ElType m -> String
-- errTypeMismatch ty0 ty1 =
--   unlines
--   [ "Type mismatch: expected "
--   , showPrettyIndent 80 2 ty0
--   , " but get "
--   , showPrettyIndent 80 2 ty1
--   ]

-- errTypeWrongForm :: (ElModeSpec m) => ElType m -> String -> String
-- errTypeWrongForm ty form =
--   unlines
--   [ "Type mismatch: expected "
--   , "  " <> form
--   , " but get "
--   , showPrettyIndent 80 2 ty
--   ]

-- verifyModeEq :: (ElModeSpec m) => m -> m -> Either String ()
-- verifyModeEq m n = unless (m == n) $ Left $ concat
--   [ "Mode mismatch: expected "
--   , show (prettyMode m)
--   , " but get "
--   , show (prettyMode n)
--   ]

-- verifyModeGt :: (ElModeSpec m) => m -> m -> Either String ()
-- verifyModeGt m n = unless (m >!! n) $ Left $ concat
--   [ "Mode mismatch: expected a mode smaller than "
--   , show (prettyMode m)
--   , " but get "
--   , show (prettyMode n)
--   ]

-- verifyModeLt :: (ElModeSpec m) => m -> m -> Either String ()
-- verifyModeLt m n = unless (m <!! n) $ Left $ concat
--   [ "Mode mismatch: expected a mode greater than "
--   , show (prettyMode m)
--   , " but get "
--   , show (prettyMode n)
--   ]
