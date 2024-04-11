{-# LANGUAGE CPP             #-}
{-# LANGUAGE DerivingVia     #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns    #-}
module Elevator.TypeChecker where

import Control.Applicative        (Applicative (..))
import Control.Comonad            (Comonad (duplicate))
import Control.Monad              (forM, unless, forM_)
import Control.Monad.Error.Class  (MonadError (..), withError)
import Control.Monad.Reader.Class (MonadReader (..))
import Data.Bifunctor             (Bifunctor (..))
import Data.Foldable              (foldrM, traverse_, Foldable (toList))
import Data.Sequence              (Seq (..), pattern (:|>))
import Data.Sequence              qualified as Seq
import Data.Traversable.Compat    (mapAccumM)
import Elevator.ModeSpec
import Elevator.Syntax
import Safe.Exact                 (zipExactMay)
import Control.Monad.Extra (whenJustM)
import qualified Data.Set as Set
import Data.Tuple.Extra (fst3)

checkModule :: (ElModeSpec m) => ElModule m -> ElCheckM m (ElIModule m)
checkModule (ElModule [] tops) = do
  (typeEnv, mayAnnTops) <- underEnv mempty $ buildTypeEnv tops
  (termEnv, annTops) <- underEnv typeEnv $ buildTermEnv mayAnnTops
  underEnv (typeEnv <> termEnv) $ ElIModule [] <$> traverse checkAnnTop annTops
checkModule (ElModule _ _)     = throwError $ TENotYetSupported "module dependence"

buildTypeEnv :: (ElModeSpec m) => [ElTop m] -> ElCheckM m (ElTypingEnvironment m, [ElPostTypeEnvTop m])
buildTypeEnv = mapAccumM buildForTop mempty
  where
    buildForTop env (TopTermDef x ty t)        = pure (env, PTETopTermDef x ty t)
    buildForTop env (TopTypeDef args x k cons) = do
      whenJustM (lookupTypeDecl x) $ const $ throwError $ TEDuplicatedTypeName x
      iargs <- forM args $ \(y, yki) ->
        (y,) <$> maybe (pure $ IKiType k) (fmap fst . checkWFOfKind) yki
      let env' = env <> ElTypingEnvironment (Seq.singleton (x, k, TEETypeDecl iargs))
      pure (env', PTETopTypeDef iargs x k cons)

buildTermEnv :: (ElModeSpec m) => [ElPostTypeEnvTop m] -> ElCheckM m (ElTypingEnvironment m, [ElPostEnvTop m])
buildTermEnv = mapAccumM buildForMayAnnTop mempty
  where
    buildForMayAnnTop env (PTETopTypeDef iargs x k cons) = do
      forM_ cons $ \(c, _) ->
        whenJustM (lookupConDecl x c) $ const $ throwError $ TEDuplicatedConName c
      icons <- checkCons iargs cons
      let env' = env <> ElTypingEnvironment (Seq.fromList (fmap (\(c, itys) -> (c, k, TEEConDecl (fst <$> iargs) itys x)) icons))
      pure (env', PETopTypeDef iargs x k icons)
    buildForMayAnnTop env (PTETopTermDef x ty t)         = do
      whenJustM (lookupTermDecl x) $ const $ throwError $ TEDuplicatedConName x
      (ity, k) <- checkWFOfType ty
      let env' = env <> ElTypingEnvironment (Seq.singleton (x, k, TEETermDecl ity))
      pure (env', PETopTermDef x ity t)

checkAnnTop :: (ElModeSpec m) => ElPostEnvTop m -> ElCheckM m (ElITop m)
checkAnnTop (PETopTypeDef iargs x k icons) = pure $ ITopTypeDef iargs x k icons
checkAnnTop (PETopTermDef x ity t)         = ITopTermDef x ity <$> checkType ity t

checkCons :: (ElModeSpec m) => [(ElId, ElIKind m)] -> [(ElId, [ElType m])] -> ElCheckM m [(ElId, [ElIType m])]
checkCons iargs = traverse checkCon
  where
    checkCon (c, argTys) = (c,) <$> traverse (local (<> iargsctx) . checkWFOfType_) argTys
    iargsctx = Seq.fromList ((\(y, yiki) -> (y, getModeOfIKind yiki, ICEKind yiki)) <$> iargs)

------------------------------------------------------------
-- "checkWFOfKind", "checkWFOfKind_",
-- "checkWFOfType", "checkWFOfType_",
-- "checkWFOfContext", ...
-- all should give a "normalized" kind/type/context/... as the result.
-- Note that "checkContext" (that checks a substitution against a context)
-- normalizes only the type part so that we can avoid unnecessary computations
-- and guarantee the termination of type checking.

checkWFOfKind :: (ElModeSpec m) => ElKind m -> ElCheckM m (ElIKind m, m)
checkWFOfKind (KiType k)          = pure (IKiType k, k)
checkWFOfKind ki@(KiUp k ctx ki') = do
  ictx <- checkWFOfContext ctx
  (iki', l) <- checkWFOfKind ki'
  testIsLEMode l k
  withError (TEFor $ TETKind ki) $ checkRangeOfContext (Just l) (Just k) ictx
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
checkWFOfType (TyBool k)           = pure (ITyBool k, k)
checkWFOfType (TyInt k)            = pure (ITyInt k, k)
checkWFOfType (TyData tys x)       = do
  (k, iargs) <- getTypeDecl x
  case zipExactMay (snd <$> iargs) tys of
    Just ikiTys -> do
      itys <- forM ikiTys $ \(iki, ty) ->
        checkContextUsageGE (getModeOfIKind iki) $ checkKind iki ty
      pure (ITyData itys x, k)
    Nothing    -> throwError $ TETypeArgNumberMismatch (length iargs) tys
checkWFOfType (TyProd [])          = throwError TEInvalidEmptyProd
checkWFOfType (TyProd (ty:tys))    = do
  (ity, k) <- checkWFOfType ty
  (itys, ks) <- unzip <$> traverse checkWFOfType tys
  traverse_ (testIsSameMode k) ks
  pure (ITyProd (ity:itys), k)
checkWFOfType ty@(TyUp k ctx ty')  = do
  ictx <- checkWFOfContext ctx
  (ity, l) <- checkWFOfType ty'
  testIsLEMode l k
  withError (TEFor $ TETType ty) $ checkRangeOfContext (Just l) (Just k) ictx
  pure (ITyUp k ictx ity, k)
checkWFOfType (TyDown k ty)        = do
  (ity, m) <- checkContextUsageGEBy snd $ checkWFOfType ty
  testIsLEMode k m
  pure (ITyDown k ity, k)
checkWFOfType (TyArr ty0 ty1)      = do
  (ity0, k0) <- checkWFOfType ty0
  (ity1, k1) <- checkWFOfType ty1
  testIsSameMode k0 k1
  pure (ITyArr ity0 ity1, k1)
checkWFOfType (TyForall x ki0 ty1) = do
  (iki0, m) <- checkContextUsageGEBy snd $ checkWFOfKind ki0
  (ity1, k) <- local (:|> (x, m, ICEKind iki0)) $ checkWFOfType ty1
  testIsGTMode m k
  pure (ITyForall x iki0 ity1, k)
checkWFOfType (TySusp {})          = throwError TEInvalidKindTypeForSusp
checkWFOfType ty                   = do
  (ity, iki') <- inferKind ty
  (ity,) <$> testIsKindType iki'

checkWFOfType_ :: (ElModeSpec m) => ElType m -> ElCheckM m (ElIType m)
checkWFOfType_ = fmap fst . checkWFOfType

checkKind :: (ElModeSpec m) => ElIKind m -> ElType m -> ElCheckM m (ElIType m)
checkKind iki (TySusp ctxh ty)
  | IKiUp m ictx iki' <- iki   = do
    ictxh <- checkWFOfContextHat ctxh ictx
    local (<> ictx) $ ITySusp m ictxh <$> checkKind iki' ty
  | otherwise                  = throwError $ TEInvalidKindForSusp iki
checkKind iki ty@(TyVar {})    = checkKindByInfer iki ty
checkKind iki ty@(TyForce {})  = checkKindByInfer iki ty
checkKind iki ty@(TyAnn {})    = checkKindByInfer iki ty
checkKind iki ty               = do
  k' <- testIsKindType iki
  (ity, k) <- checkWFOfType ty
  testIsSameMode k k'
  pure ity

checkKindByInfer :: (ElModeSpec m) => ElIKind m -> ElType m -> ElCheckM m (ElIType m)
checkKindByInfer iki ty = do
  (ity, iki') <- inferKind ty
  unifyIKind iki iki'
  pure ity

inferKind :: (ElModeSpec m) => ElType m -> ElCheckM m (ElIType m, ElIKind m)
inferKind (TyVar x)            = (ITyVar x,) . snd <$> getTypeAndUse x
inferKind (TyForce ty sub)     = do
  (ity, iki) <- checkContextUsageGEBy (getModeOfIKind . snd) $ inferKind ty
  case iki of
    IKiUp _ ictx iki' -> do
      isub <- checkContext ictx sub
      let k = getModeOfIKind iki'
      case ity of
        ITySusp _ _ ity' -> pure (applyTypeSubst ity' isub ictx, iki')
        _                -> pure (ITyForce k ity isub, iki')
    _                 -> throwError $ TEInvalidKindForForce iki
inferKind (TyAnn ty ki)        = do
  iki <- checkWFOfKind_ ki
  (, iki) <$> checkKind iki ty
inferKind ty@(TySusp _ _)      = throwError $ TENoninferableType ty
inferKind ty                   = fmap IKiType <$> checkWFOfType ty

checkRangeOfContext :: (ElModeSpec m) => Maybe m -> Maybe m -> ElIContext m -> ElCheckM m ()
checkRangeOfContext mayL mayM ictx =
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

checkWFOfContextEntry :: (ElModeSpec m) => ElContextEntry m -> ElCheckM m (ElIContextEntry m, m)
checkWFOfContextEntry (CEKind ki) = first ICEKind <$> checkWFOfKind ki
checkWFOfContextEntry (CEType ty) = first ICEType <$> checkWFOfType ty

-- This works only when all entries in input context have lower modes
-- than any entry in the ambient context.
checkWFOfContext :: (ElModeSpec m) => ElContext m -> ElCheckM m (ElIContext m)
checkWFOfContext = foldrM folder Seq.empty
  where
    folder (x, entry) ictx =
      (ictx :|>) . uncurry (flip (x,,))
      <$> local (<> ictx) (checkWFOfContextEntry entry)

checkWFOfContextHat :: (ElModeSpec m) => ElContextHat m -> ElIContext m -> ElCheckM m (ElIContextHat m)
checkWFOfContextHat ctxh ictx = do
  unless (ctxh == fmap fst (putIHat ictx)) $ throwError $ TEContextHatConflict ctxh ictx
  pure $ putIHat ictx

checkType :: (ElModeSpec m) => ElIType m -> ElTerm m -> ElCheckM m (ElITerm m)
checkType = undefined

inferType :: (ElModeSpec m) => ElTerm m -> ElCheckM m (ElITerm m, ElIType m)
inferType = undefined

checkContext :: (ElModeSpec m) => ElIContext m -> ElSubst m -> ElCheckM m (ElISubst m)
checkContext ictx subst
  | weakeningLen >= 0 = do
      let (ictxFromWeakening, subIctx) = Seq.splitAt weakeningLen ictx
      isubst <- traverse checkHelper $ Seq.zip subIctx subst
      checkContextWeakening ictxFromWeakening
      pure isubst
  | otherwise         = throwError $ TETooLongSubstitution (length ictx) subst
  where
    weakeningLen = length ictx - length subst

    checkHelper ((_, _, ICEKind ki), SEAmbi (AmCore (ambiCore2type -> ty))) = ISEType <$> checkKind ki ty
    checkHelper ((_, _, ICEKind ki), SEAmbi (AmType ty))                    = ISEType <$> checkKind ki ty
    checkHelper ((_, _, ICEType ty), SEAmbi (AmCore (ambiCore2term -> t)))  = ISETerm <$> checkType ty t
    checkHelper ((_, _, ICEType ty), SEAmbi (AmTerm t))                     = ISETerm <$> checkType ty t
    checkHelper ((x, _, _),          se)                                    = throwError $ TESubstitutionEntryClassMismatch x se

checkContextWeakening :: (ElModeSpec m) => ElIContext m -> ElCheckM m ()
checkContextWeakening ictx0 = do
  unless (Seq.length ictx0 == Set.size (Set.fromList (fst3 <$> toList ictx0))) $ throwError $ TEDuplicatedContextEntryInWeakening ictx0
  forM_ ictx0 $ \(x, k, entry) -> do
    (k', entry') <- getFromCheckingIctx x
    testIsSameMode k k'
    unifyIContextEntry entry entry'

checkContextUsageGE :: (ElModeSpec m) => m -> ElCheckM m a -> ElCheckM m a
checkContextUsageGE k = checkContextUsageGEBy (const k)

checkContextUsageGEBy :: (ElModeSpec m) => (a -> m) -> ElCheckM m a -> ElCheckM m a
checkContextUsageGEBy f am = do
  (ause, a) <- listenUsage am
  testContextUsageGE (f a) ause
  pure a

testContextUsageGE ::  (MonadError (ElTypingError m) em, ElModeSpec m) => m -> ElContextUsage m -> em ()
testContextUsageGE k = traverse_ (testContextEntryUsageGE k . snd) . getElContextUsage

testContextEntryUsageGE :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> ElContextEntryUsage m -> em ()
testContextEntryUsageGE k (CEUKind m) = testIsGEMode m k
testContextEntryUsageGE k (CEUType m) = testIsGEMode m k

testIsGEMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> m -> em ()
testIsGEMode m k = unless (m >=!! k) $ throwError $ TEModeOrderFailure TEMOGE m k

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

------------------------------------------------------------
-- Substitution functions
------------------------------------------------------------
-- This should be a capture-avoiding substitution

applyTypeSubst :: (ElModeSpec m) => ElIType m -> ElISubst m -> ElIContext m -> ElIType m
applyTypeSubst = undefined
-- applyTypeSubst (ITyVar x) isub ictx
--   | Just (_, ISEType ity, _) <- lookupFromSubIctx isub ictx x = ity
--   | otherwise                                                 = ITyVar x
-- applyTypeSubst (ITySusp k ictxh' ity) isub ictx = undefined
-- applyTypeSubst (ITyForce k ity isub') isub ictx = undefined
-- applyTypeSubst (ITyData [ElIType m] ElId) = undefined
-- applyTypeSubst (ITyBool m) = undefined
-- applyTypeSubst (ITyInt m) = undefined
-- applyTypeSubst (ITyProd [ElIType m]) = undefined
-- applyTypeSubst (ITyUp m (ElIContext m) (ElIType m)) = undefined
-- applyTypeSubst (ITyDown m (ElIType m)) = undefined
-- applyTypeSubst (ITyArr (ElIType m) (ElIType m)) = undefined
-- applyTypeSubst (ITyForall ElId (ElIKind m) (ElIType m)) = undefined

------------------------------------------------------------
-- Type checker monad
------------------------------------------------------------

-- Constraints should be added as a state once we add them
newtype ElCheckM m a
  = ElCheckM
    { runElCheckM :: ElTypingEnvironment m -> ElIContext m -> Either (ElTypingError m) (ElContextUsage m, a)
    }
  deriving stock (Functor)

instance (ElModeSpec m) => Applicative (ElCheckM m) where
  pure = ElCheckM . const . const . pure . (UEmpty,)
  fm <*> am = ElCheckM $ \env tctx -> do
    (fuse, f) <- runElCheckM fm env tctx
    (ause, a) <- runElCheckM am env tctx
    (, f a) <$> mergeUsage fuse ause
  liftA2 f am bm = ElCheckM $ \env tctx -> do
    (ause, a) <- runElCheckM am env tctx
    (buse, b) <- runElCheckM bm env tctx
    (, f a b) <$> mergeUsage ause buse

instance (ElModeSpec m) => Monad (ElCheckM m) where
  am >>= f = ElCheckM $ \env tctx -> do
    (ause, a) <- runElCheckM am env tctx
    (buse, b) <- runElCheckM (f a) env tctx
    (, b) <$> mergeUsage ause buse

instance (ElModeSpec m) => MonadReader (ElIContext m) (ElCheckM m) where
  ask = ElCheckM $ const $ pure . (UEmpty,)
  local f am = ElCheckM $ \env -> runElCheckM am env . f

instance (ElModeSpec m) => MonadError (ElTypingError m) (ElCheckM m) where
  throwError = ElCheckM . const . const . throwError
  catchError am f = ElCheckM $ \env tctx -> catchError (runElCheckM am env tctx) (\err -> runElCheckM (f err) env tctx)

getTypeAndUse :: (ElModeSpec m) => ElId -> ElCheckM m (m, ElIKind m)
getTypeAndUse x = do
  (m, ientry) <- getFromCheckingIctx x
  case ientry of
    ICEKind iki -> do
      useTypeVariable x m
      pure (m, iki)
    ICEType _ -> throwError $ TEVariableClassMismatch x

getTermAndUse :: (ElModeSpec m) => ElId -> ElCheckM m (m, ElIType m)
getTermAndUse x = catchError inIctx $ const (getTermDecl x)
  where
    inIctx = do
      (m, ientry) <- getFromCheckingIctx x
      case ientry of
        ICEType ity -> do
          useTermVariable x m
          pure (m, ity)
        ICEKind _ -> throwError $ TEVariableClassMismatch x

getFromIctx :: (MonadError (ElTypingError m) em, ElModeSpec m) => ElIContext m -> ElId -> em (m, ElIContextEntry m)
getFromIctx ictx x =
  case Seq.findIndexR (\(x', _, _) -> x == x') ictx of
    Just i  -> let (_, m, ientry) = ictx `Seq.index` i in pure (m, ientry)
    Nothing -> throwError $ TENotInScope x

getFromCheckingIctx :: (ElModeSpec m) => ElId -> ElCheckM m (m, ElIContextEntry m)
getFromCheckingIctx x = do
  ictx <- ask
  getFromIctx ictx x

lookupFromSubIctx :: (ElModeSpec m) => ElISubst m -> ElIContext m -> ElId -> Maybe (m, ElISubstEntry m, ElIContextEntry m)
lookupFromSubIctx isub ictx x =
  case Seq.findIndexR (\(x', _, _) -> x == x') ictx of
    Just i  ->
      let
        (_, m, ientry) = ictx `Seq.index` i
      in
      case isub Seq.!? i of
        Just it  -> Just (m, it, ientry)
        Nothing -> Just (m, iSubEntryOfIContextEntry ientry, ientry)
    Nothing -> Nothing
  where
    iSubEntryOfIContextEntry (ICEKind _) = ISEType (ITyVar x)
    iSubEntryOfIContextEntry (ICEType _) = ISETerm (ITmVar x)

------------------------------------------------------------
-- Top-level based environment for the type checker
------------------------------------------------------------

data ElTypingEnvironmentEntry m
  = TEETypeDecl [(ElId, ElIKind m)]
  | TEEConDecl [ElId] [ElIType m] ElId
  | TEETermDecl (ElIType m)
  deriving stock (Eq, Ord)

data ElPostTypeEnvTop m
  = PTETopTermDef ElId (ElType m) (ElTerm m)
  | PTETopTypeDef [(ElId, ElIKind m)] ElId m [(ElId, [ElType m])]
  deriving stock (Eq, Ord, Show)

data ElPostEnvTop m
  = PETopTermDef ElId (ElIType m) (ElTerm m)
  | PETopTypeDef [(ElId, ElIKind m)] ElId m [(ElId, [ElIType m])]
  deriving stock (Eq, Ord, Show)

newtype ElTypingEnvironment m
  = ElTypingEnvironment
    { getElTypingEnvironment :: Seq (ElId, m, ElTypingEnvironmentEntry m)
    }
  deriving (Eq, Ord, Semigroup, Monoid) via (Seq (ElId, m, ElTypingEnvironmentEntry m))

askEnv :: (ElModeSpec m) => ElCheckM m (ElTypingEnvironment m)
askEnv = ElCheckM $ (pure .) . const . (UEmpty,)

underEnv :: (ElModeSpec m) => ElTypingEnvironment m -> ElCheckM m a -> ElCheckM m a
underEnv env am = ElCheckM $ const $ runElCheckM am env

------------------------------------------------------------
-- NOTE: Env does not have the concept of "use"
-- Or should it be? Polynomial time computation may need such
-- a concept

lookupEnvWithMapper :: (ElModeSpec m) => ElTypingEnvironment m -> ElId -> (ElTypingEnvironmentEntry m -> Maybe a) -> Maybe (m, a)
lookupEnvWithMapper env x f =
  case Seq.findIndexR cond $ getElTypingEnvironment env of
    Nothing -> Nothing
    Just i  ->
      let
        (_, k, eentry) = getElTypingEnvironment env `Seq.index` i
      in
      case f eentry of
        Just a -> Just (k, a)
        _      -> error $ "line " <> show (__LINE__ :: Int) <> " in " <> __FILE__
  where
    cond (x', _, eentry)
      | Just _ <- f eentry = x == x'
      | otherwise          = False

lookupTypingEnvWithMapper :: (ElModeSpec m) => ElId -> (ElTypingEnvironmentEntry m -> Maybe a) -> ElCheckM m (Maybe (m, a))
lookupTypingEnvWithMapper x f = do
  env <- askEnv
  pure $ lookupEnvWithMapper env x f

lookupTypeDecl :: (ElModeSpec m) => ElId -> ElCheckM m (Maybe (m, [(ElId, ElIKind m)]))
lookupTypeDecl x = lookupTypingEnvWithMapper x f
  where
    f (TEETypeDecl args) = Just args
    f _                  = Nothing

lookupConDecl :: (ElModeSpec m) => ElId -> ElId -> ElCheckM m (Maybe (m, ([ElId], [ElIType m])))
lookupConDecl x c = lookupTypingEnvWithMapper c f
  where
    f (TEEConDecl iys itys x')
      | x == x'              = Just (iys, itys)
    f _                      = Nothing

lookupTermDecl :: (ElModeSpec m) => ElId -> ElCheckM m (Maybe (m, ElIType m))
lookupTermDecl x = lookupTypingEnvWithMapper x f
  where
    f (TEETermDecl ity) = Just ity
    f _                 = Nothing

getFromEnvWithMapper :: (MonadError (ElTypingError m) em, ElModeSpec m) => ElTypingEnvironment m -> ElId -> (ElTypingEnvironmentEntry m -> Maybe a) -> em (m, a)
getFromEnvWithMapper env x f =
  case lookupEnvWithMapper env x f of
    Nothing  -> throwError $ TENotInScope x
    Just res -> pure res

getFromTypingEnvWithMapper :: (ElModeSpec m) => ElId -> (ElTypingEnvironmentEntry m -> Maybe a) -> ElCheckM m (m, a)
getFromTypingEnvWithMapper x f = do
  env <- askEnv
  getFromEnvWithMapper env x f

getTypeDecl :: (ElModeSpec m) => ElId -> ElCheckM m (m, [(ElId, ElIKind m)])
getTypeDecl x = getFromTypingEnvWithMapper x f
  where
    f (TEETypeDecl args) = Just args
    f _                  = Nothing

getConDecl :: (ElModeSpec m) => ElId -> ElId -> ElCheckM m (m, ([ElId], [ElIType m]))
getConDecl x c = getFromTypingEnvWithMapper c f
  where
    f (TEEConDecl iys itys x')
      | x == x'              = Just (iys, itys)
    f _                      = Nothing

getTermDecl :: (ElModeSpec m) => ElId -> ElCheckM m (m, ElIType m)
getTermDecl x = getFromTypingEnvWithMapper x f
  where
    f (TEETermDecl ity) = Just ity
    f _                 = Nothing

------------------------------------------------------------
-- Usage for the type checker
------------------------------------------------------------

data ElContextEntryUsage m
  = CEUKind m
  | CEUType m
  deriving stock (Eq, Ord)

newtype ElContextUsage m
  = ElContextUsage
    { getElContextUsage :: Seq (ElId, ElContextEntryUsage m)
    }
  deriving (Eq, Ord) via (Seq (ElId, ElContextEntryUsage m))

pattern UEmpty :: ElContextUsage m
pattern UEmpty = ElContextUsage Empty

pattern (:+*) :: ElContextUsage m -> (ElId, m) -> ElContextUsage m
pattern (:+*) xs p <- ElContextUsage ((ElContextUsage -> xs) :|> (traverse getCEUKind -> Just p)) where
  (:+*) xs p = ElContextUsage (getElContextUsage xs :|> fmap CEUKind p)

getCEUKind :: ElContextEntryUsage m -> Maybe m
getCEUKind (CEUKind m) = Just m
getCEUKind _           = Nothing

pattern (:+?) :: ElContextUsage m -> (ElId, m) -> ElContextUsage m
pattern (:+?) xs p <- ElContextUsage ((ElContextUsage -> xs) :|> (traverse getCEUType -> Just p)) where
  (:+?) xs p = ElContextUsage (getElContextUsage xs :|> fmap CEUType p)

getCEUType :: ElContextEntryUsage m -> Maybe m
getCEUType (CEUType m) = Just m
getCEUType _           = Nothing

{-# COMPLETE UEmpty, (:+*), (:+?) #-}

mergeUsage :: (ElModeSpec m) => ElContextUsage m -> ElContextUsage m -> Either (ElTypingError m) (ElContextUsage m)
mergeUsage UEmpty            use1 = pure use1
mergeUsage (use0 :+* (x, k)) use1
  | Just i <- Seq.findIndexR ((x ==) . fst) (getElContextUsage use1) = do
      let (_, entryUse) = getElContextUsage use1 `Seq.index` i
      case entryUse of
        CEUKind k' -> do
          testIsSameMode k k'
        _ -> throwError $ TEVariableClassMismatch x
      use <- mergeUsage use0 . ElContextUsage . Seq.deleteAt i $ getElContextUsage use1
      pure $ use :+* (x, k)
  | otherwise = do
      use <- mergeUsage use0 use1
      pure $ use :+* (x, k)
mergeUsage (use0 :+? (x, k)) use1
  | Just i <- Seq.findIndexR ((x ==) . fst) (getElContextUsage use1) = do
      let (_, entryUse) = getElContextUsage use1 `Seq.index` i
      case entryUse of
        CEUType k' -> do
          testIsSameMode k k'
          testIsCoMode k
        _ -> throwError $ TEVariableClassMismatch x
      use <- mergeUsage use0 . ElContextUsage . Seq.deleteAt i $ getElContextUsage use1
      pure $ use :+? (x, k)
  | otherwise = do
      use <- mergeUsage use0 use1
      pure $ use :+? (x, k)

listenUsage :: (ElModeSpec m) => ElCheckM m a -> ElCheckM m (ElContextUsage m, a)
listenUsage am = ElCheckM $ \env -> fmap duplicate . runElCheckM am env

useVariables :: ElContextUsage m -> ElCheckM m ()
useVariables use = ElCheckM . const . const $ pure (use, ())

useTypeVariable :: ElId -> m -> ElCheckM m ()
useTypeVariable x m = useVariables (UEmpty :+* (x, m))

useTermVariable :: ElId -> m -> ElCheckM m ()
useTermVariable x m = useVariables (UEmpty :+? (x, m))

------------------------------------------------------------
-- Equality checking / Unification
------------------------------------------------------------
-- As internal type/kind generators (i.e. well-formedness checkers)
-- always generate "normal" type/kinds, we can use
-- syntactic equality to check whether two types/kinds are equal.

unifyIKind :: (ElModeSpec m) => ElIKind m -> ElIKind m -> ElCheckM m ()
unifyIKind iki0 iki1 = unless (iki0 == iki1) $ throwError $ TEUnunifiableIKinds iki0 iki1

unifyIType :: (ElModeSpec m) => ElIType m -> ElIType m -> ElCheckM m ()
unifyIType ity0 ity1 = unless (ity0 == ity1) $ throwError $ TEUnunifiableITypes ity0 ity1

unifyIContextEntry :: (ElModeSpec m) => ElIContextEntry m -> ElIContextEntry m -> ElCheckM m ()
unifyIContextEntry (ICEKind iki0) (ICEKind iki1) = unifyIKind iki0 iki1
unifyIContextEntry (ICEType ity0) (ICEType ity1) = unifyIType ity0 ity1
unifyIContextEntry entry0         entry1         = throwError $ TEUnunifiableEntry entry0 entry1

------------------------------------------------------------
-- Errors for the type checker
------------------------------------------------------------

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
  = TEImplementationError String
  | TEInvalidKind (ElIKind m)
  | TENotInScope ElId
  | TEVariableClassMismatch ElId
  | TEInvalidEntryForTypeVariable ElId (ElIContextEntry m)
  | TEInvalidMultipleUsage ElId m
  | TEInvalidEmptyProd
  | TEInvalidKindForSusp (ElIKind m)
  | TEInvalidKindForForce (ElIKind m)
  | TEInvalidKindTypeForSusp
  | TEDuplicatedTypeName ElId
  | TEDuplicatedConName ElId
  | TEDuplicatedTermName ElId
  | TENoninferableType (ElType m)
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
  | TENotYetSupported String
  | TETypeArgNumberMismatch Int [ElType m]
  | TETooLongSubstitution Int (ElSubst m)
  | TESubstitutionEntryClassMismatch ElId (ElSubstEntry m)
  | TEDuplicatedContextEntryInWeakening (ElIContext m)

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
