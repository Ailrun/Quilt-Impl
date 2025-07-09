{-# LANGUAGE CPP               #-}
{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE ViewPatterns      #-}
module Quilt.TypeChecker where

import Control.Applicative        (Applicative (..))
import Control.Comonad            (Comonad (duplicate))
import Control.Monad              (forM, forM_, unless)
import Control.Monad.Except       (ExceptT, MonadError (..), liftEither,
                                   mapExceptT, runExceptT, withError)
import Control.Monad.Extra        (whenJust, whenJustM)
import Control.Monad.Reader.Class (MonadReader (..))
import Control.Monad.State.Strict (State)
import Data.Bifunctor             (Bifunctor (..))
import Data.Foldable              (Foldable (toList), foldlM, traverse_)
import Data.Sequence              (Seq (..), pattern (:|>))
import Data.Sequence              qualified as Seq
import Data.Set                   qualified as Set
import Data.Traversable.Compat    (mapAccumM)
import Data.Tuple.Extra           (fst3, thd3)
import Safe.Exact                 (zipExactMay)

import Quilt.ModeSpec
import Quilt.Substitution
import Quilt.Syntax

checkModule :: (QModeSpec m) => QModule m -> QCheckM m (QIModule m)
checkModule (QModule [] tops) = do
  (typeEnv, mayAnnTops) <- underEnv mempty $ buildTypeEnv tops
  (termEnv, annTops) <- underEnv typeEnv $ buildTermEnv mayAnnTops
  underEnv (typeEnv <> termEnv) $ QIModule [] <$> traverse checkPETop annTops
checkModule (QModule _ _)     = throwError $ TENotYetSupported "module dependence"

buildTypeEnv :: (QModeSpec m) => [QTop m] -> QCheckM m (QTypingEnvironment m, [QPostTypeEnvTop m])
buildTypeEnv = mapAccumM accumTypeEnvForTop mempty

accumTypeEnvForTop :: QModeSpec m => QTypingEnvironment m -> QTop m -> QCheckM m (QTypingEnvironment m, QPostTypeEnvTop m)
accumTypeEnvForTop env (TopTermDef x ty t)        = pure (env, PTETopTermDef x ty t)
accumTypeEnvForTop env (TopTypeDef args x k cons) = do
  whenJustM (lookupTypeDecl x) $ const $ throwError $ TEDuplicatedTypeName x
  iargs <- forM args $ \(y, yki) ->
    (y,) <$> maybe (pure $ IKiType k) (fmap fst . checkWFOfKind) yki
  let env' = env <> QTypingEnvironment [(x, k, TEETypeDecl iargs)]
  pure (env', PTETopTypeDef iargs x k cons)

buildTermEnv :: (QModeSpec m) => [QPostTypeEnvTop m] -> QCheckM m (QTypingEnvironment m, [QPostEnvTop m])
buildTermEnv = mapAccumM accumTermEnvForPTETop mempty

accumTermEnvForPTETop :: QModeSpec m => QTypingEnvironment m -> QPostTypeEnvTop m -> QCheckM m (QTypingEnvironment m, QPostEnvTop m)
accumTermEnvForPTETop env (PTETopTypeDef iargs x k cons) = do
  forM_ cons $ \(c, _) ->
    whenJustM (lookupConDecl x c) $ const $ throwError $ TEDuplicatedConName x c
  icons <- withErrorFor (TETTypeDefinition x) $ checkCons iargs cons
  let env' = env <> QTypingEnvironment (Seq.fromList (fmap (\(cn, (c, itys)) -> (c, k, TEEConDecl cn (fst <$> iargs) itys x)) (zip [0..] icons)))
  pure (env', PETopTypeDef iargs x k icons)
accumTermEnvForPTETop env (PTETopTermDef x ty t)         = do
  whenJustM (lookupTermDecl x) $ const $ throwError $ TEDuplicatedTermName x
  (ity, k) <- withErrorFor (TETTermDefinition x) . withErrorFor (TETType ty) $ checkWFOfType ty
  let env' = env <> QTypingEnvironment [(x, k, TEETermDecl ity)]
  pure (env', PETopTermDef x k ity t)

checkPETop :: (QModeSpec m) => QPostEnvTop m -> QCheckM m (QITop m)
checkPETop (PETopTypeDef iargs x k icons) = pure $ ITopTypeDef iargs x k icons
checkPETop (PETopTermDef x k ity t)       = withErrorFor (TETTermDefinition x) $ ITopTermDef x k ity <$> checkType ity t

checkCons :: (QModeSpec m) => [(QId, QIKind m)] -> [(QId, [QType m])] -> QCheckM m [(QId, [QIType m])]
checkCons iargs = traverse checkCon
  where
    checkCon (c, argTys) =
      withErrorFor (TETConstructor c)
      $ removeTypeVariables iargsrem
      $ (c,) <$> traverse (local (<> iargsctx) . checkWFOfType_) argTys

    iargsctx = Seq.fromList ((\(y, yiki) -> (y, getModeOfIKind yiki, ICEKind yiki)) <$> iargs)
    iargsrem = fmap (\(x, k, _) -> (x, k)) iargsctx

buildEnv :: (QModeSpec m) => [QITop m] -> QCheckM m (QTypingEnvironment m)
buildEnv = foldlM accumEnvForTop mempty

accumEnvForTop :: QModeSpec m => QTypingEnvironment m -> QITop m -> QCheckM m (QTypingEnvironment m)
accumEnvForTop env (ITopTermDef x k ity _) = do
  whenJustM (lookupTermDecl x) $ const $ throwError $ TEDuplicatedTermName x
  let env' = env <> QTypingEnvironment [(x, k, TEETermDecl ity)]
  pure env'
accumEnvForTop env (ITopTypeDef iargs x k icons) = do
  whenJustM (lookupTypeDecl x) $ const $ throwError $ TEDuplicatedTypeName x
  let env' = env <> QTypingEnvironment [(x, k, TEETypeDecl iargs)] <> QTypingEnvironment (Seq.fromList (fmap (\(cn, (c, itys)) -> (c, k, TEEConDecl cn (fst <$> iargs) itys x)) (zip [0..] icons)))
  pure env'

checkTopUnderModule :: (QModeSpec m) => QIModule m -> QTop m -> QCheckM m (QIModule m)
checkTopUnderModule (QIModule mids itops) top = do
  env <- buildEnv itops
  underEnv env $
    QIModule mids . (itops <>) . pure <$> checkTop top

checkTop :: (QModeSpec m) => QTop m -> QCheckM m (QITop m)
checkTop (TopTermDef x ty t) = do
  whenJustM (lookupTermDecl x) $ const $ throwError $ TEDuplicatedTermName x
  (ity, k) <- checkWFOfType ty
  env <- askEnv
  underEnv (env <> QTypingEnvironment [(x, k, TEETermDecl ity)]) $
    ITopTermDef x k ity <$> checkType ity t
checkTop (TopTypeDef args x k cons) = do
  whenJustM (lookupTypeDecl x) $ const $ throwError $ TEDuplicatedTypeName x
  iargs <- forM args $ \(y, yki) ->
    (y,) <$> maybe (pure $ IKiType k) (fmap fst . checkWFOfKind) yki
  env <- askEnv
  underEnv (env <> QTypingEnvironment [(x, k, TEETypeDecl iargs)]) $ do
    forM_ cons $ \(c, _) ->
      whenJustM (lookupConDecl x c) $ const $ throwError $ TEDuplicatedConName x c
    ITopTypeDef iargs x k <$> checkCons iargs cons

inferTypeUnderModule :: (QModeSpec m) => QIModule m -> QTerm m -> QCheckM m (QITerm m, QIType m, m)
inferTypeUnderModule (QIModule _ itops) t = do
  env <- buildEnv itops
  underEnv env $ inferType t

------------------------------------------------------------
-- "checkWFOfKind", "checkWFOfKind_",
-- "checkWFOfType", "checkWFOfType_",
-- "checkWFOfContext", ...
-- all should give a "normalized" kind/type/context/... as the result.
-- Note that "checkContext" (that checks a substitution against a context)
-- normalizes only the type part so that we can avoid unnecessary computations
-- and guarantee the termination of type checking.

checkWFOfKind :: (QModeSpec m) => QKind m -> QCheckM m (QIKind m, m)
checkWFOfKind (KiType k)          = pure (IKiType k, k)
checkWFOfKind ki@(KiUp k ctx ki') = do
  ictx <- checkWFOfContext ctx
  (iki', l) <- removeVariablesInType (putIHat ictx) $ local (<> ictx) $ checkWFOfKind ki'
  testIsLEMode l k
  withErrorFor (TETKind ki) $ checkRangeOfContext (Just l) (Just k) ictx
  pure (IKiUp k ictx iki', k)

checkWFOfKind_ :: (QModeSpec m) => QKind m -> QCheckM m (QIKind m)
checkWFOfKind_ = fmap fst . checkWFOfKind

getModeOfIKind :: (QModeSpec m) => QIKind m -> m
getModeOfIKind (IKiType k)   = k
getModeOfIKind (IKiUp k _ _) = k

testIsKindType :: (QModeSpec m) => QIKind m -> QCheckM m m
testIsKindType (IKiType k) = pure k
testIsKindType iki         = throwError (TEInvalidNonTypeKind iki)

checkWFOfType :: (QModeSpec m) => QType m -> QCheckM m (QIType m, m)
checkWFOfType (TyBool k)           = pure (ITyBool k, k)
checkWFOfType (TyInt k)            = pure (ITyInt k, k)
checkWFOfType (TyData argTys x)    = do
  (k, iargKis) <- getTypeDecl x
  case zipExactMay (snd <$> iargKis) argTys of
    Just iargKiTys -> do
      itys <- forM iargKiTys $ \(iargKi, argTy) ->
        checkContextUsageGE (getModeOfIKind iargKi) $ checkKind iargKi argTy
      pure (ITyData itys x, k)
    Nothing    -> throwError $ TETypeArgNumberMismatch x (length iargKis) argTys
checkWFOfType (TyProd [])          = throwError TEInvalidEmptyProd
checkWFOfType (TyProd (ty:tys))    = do
  (ity, k) <- checkWFOfType ty
  (itys, ks) <- unzip <$> traverse checkWFOfType tys
  traverse_ (testIsSameMode k) ks
  pure (ITyProd (ity:itys), k)
checkWFOfType (TyArray ty')        = do
  (ity, k) <- checkWFOfType ty'
  pure (ITyArray k ity, k)
checkWFOfType ty@(TyUp k ctx ty')  = do
  ictx <- checkWFOfContext ctx
  (ity, l) <- removeVariablesInType (putIHat ictx) $ local (<> ictx) $ checkWFOfType ty'
  testIsLEMode l k
  withErrorFor (TETType ty) $ checkRangeOfContext (Just l) (Just k) ictx
  pure (ITyUp k l ictx ity, k)
checkWFOfType (TyDown k ty)        = do
  (ity, m) <- checkContextUsageGEBy snd $ checkWFOfType ty
  testIsLEMode k m
  pure (ITyDown k m ity, k)
checkWFOfType (TyArr ty0 ty1)      = do
  (ity0, k0) <- checkWFOfType ty0
  (ity1, k1) <- checkWFOfType ty1
  testIsSameMode k0 k1
  pure (ITyArr ity0 ity1, k1)
checkWFOfType (TyForall x ki0 ty1) = do
  (iki0, m) <- checkContextUsageGEBy snd $ checkWFOfKind ki0
  (ity1, k) <- removeTypeVariable (x, m) $ local (:|> (x, m, ICEKind iki0)) $ checkWFOfType ty1
  testIsGEMode m k
  pure (ITyForall x iki0 ity1, k)
checkWFOfType (TySusp {})          = throwError TEInvalidKindTypeForSusp
checkWFOfType ty                   = do
  (ity, iki') <- inferKind ty
  (ity,) <$> testIsKindType iki'

checkWFOfType_ :: (QModeSpec m) => QType m -> QCheckM m (QIType m)
checkWFOfType_ = fmap fst . checkWFOfType

checkKind :: (QModeSpec m) => QIKind m -> QType m -> QCheckM m (QIType m)
checkKind iki (TySusp ctxh ty)
  | IKiUp m ictx iki' <- iki   = do
    ictxh <- checkWFOfContextHat ctxh ictx
    removeVariablesInType ictxh $ local (<> ictx) $ ITySusp m ictxh <$> checkKind iki' ty
  | otherwise                  = throwError $ TEInvalidKindForSusp iki
checkKind iki ty@(TyVar {})    = checkKindByInfer iki ty
checkKind iki ty@(TyForce {})  = checkKindByInfer iki ty
checkKind iki ty@(TyAnn {})    = checkKindByInfer iki ty
checkKind iki ty               = do
  k' <- testIsKindType iki
  (ity, k) <- checkWFOfType ty
  testIsSameMode k k'
  pure ity

checkKindByInfer :: (QModeSpec m) => QIKind m -> QType m -> QCheckM m (QIType m)
checkKindByInfer iki ty = do
  (ity, iki') <- inferKind ty
  unifyIKind iki iki'
  pure ity

inferKind :: (QModeSpec m) => QType m -> QCheckM m (QIType m, QIKind m)
inferKind (TyVar x)            = (ITyVar x,) . snd <$> getTypeAndUse x
inferKind (TyForce ty sub)     = do
  (ity, iki) <- checkContextUsageGEBy (getModeOfIKind . snd) $ inferKind ty
  case iki of
    IKiUp k ictx iki' -> do
      let idom = icontext2idomain ictx
      isub <- checkContext ictx sub
      iki'' <- substM2checkM $ applySubstKind isub idom iki'
      case ity of
        ITySusp _ _ ity' -> (, iki'') <$> substM2checkM (applySubstType isub idom ity')
        _                -> pure (ITyForce k ity isub, iki'')
    _                 -> throwError $ TEInvalidTypeBodyForForce ity iki
inferKind (TyAnn ty ki)        = do
  iki <- checkWFOfKind_ ki
  (, iki) <$> checkKind iki ty
inferKind ty@(TySusp _ _)      = throwError $ TECheckOnlyTypeInInference ty
inferKind ty                   = fmap IKiType <$> checkWFOfType ty

extractModeOfType :: (QModeSpec m) => QIType m -> QCheckM m m
extractModeOfType = fmap snd . checkWFOfType . fromInternal

checkRangeOfContext :: (QModeSpec m) => Maybe m -> Maybe m -> QIContext m -> QCheckM m ()
checkRangeOfContext mayL mayM ictx =
  withErrorFor (TETContext $ (\(x, _, entry) -> (x, fromInternal entry)) <$> ictx)
  . traverse_ checker
  $ ictx
  where
    checker =
      case (mayL, mayM) of
        (Just l, Just m) -> \(x, k, _) -> withErrorFor (TETVariable x) $ testIsLEMode l k >> testIsGTMode m k
        (_,      Just m) -> \(x, k, _) -> withErrorFor (TETVariable x) $ testIsGTMode m k
        (Just l, _)      -> \(x, k, _) -> withErrorFor (TETVariable x) $ testIsLEMode l k
        _                -> const (pure ())

checkWFOfContextEntry :: (QModeSpec m) => QContextEntry m -> QCheckM m (QIContextEntry m, m)
checkWFOfContextEntry (CEKind ki) = first ICEKind <$> checkWFOfKind ki
checkWFOfContextEntry (CEType ty) = first ICEType <$> checkWFOfType ty

-- This works only when all entries in input context have lower modes
-- than any entry in the ambient context.
checkWFOfContext :: (QModeSpec m) => QContext m -> QCheckM m (QIContext m)
checkWFOfContext = foldlM folder []
  where
    folder ictx (x, entry) =
      removeVariablesInType (putIHat ictx)
      $ (ictx :|>) . uncurry (flip (x,,))
      <$> local (<> ictx) (checkWFOfContextEntry entry)

checkWFOfContextHat :: (QModeSpec m) => QContextHat m -> QIContext m -> QCheckM m (QIContextHat m)
checkWFOfContextHat ctxh ictx = do
  unless (ctxh == icontextHat2contextHat (putIHat ictx)) $ throwError $ TEContextHatConflict ctxh ictx
  pure $ putIHat ictx

-- This function assumes that the input type is normalized
checkType :: (QModeSpec m) => QIType m -> QTerm m -> QCheckM m (QITerm m)
checkType ity (TmBuiltIn bi) = do
  k <- extractModeOfType ity
  case typeOfBuiltIn k bi of
    Just ity' -> do
      unifyIType ity ity'
      pure (ITmBuiltIn bi)
    Nothing -> throwError $ TEInvalidBuiltIn k bi
checkType ity (TmArrayTag n)
  | ITyArray _ _ <- ity = pure (ITmArrayTag n)
  | otherwise           = throwError $ TEInvalidTypeForArrayTag ity
checkType ity (TmData c args)
  | ITyData iparamTys x <- ity = do
      (_, (cn, params, iargTys)) <- getConDecl x c
      unless (length iparamTys == length params) $
        throwError $ TEInternalError $ TETypeArgNumberMismatch x (length params) (fromInternal <$> iparamTys)
      let
        sub = fmap ISEType (Seq.fromList iparamTys)
        dom = fmap (,True) (Seq.fromList params)
      iargTys' <- substM2checkM $ traverse (applySubstType sub dom) iargTys
      case zipExactMay iargTys' args of
        Just iargTys'Args -> ITmData c cn <$> traverse (uncurry checkType) iargTys'Args
        Nothing -> throwError $ TEConstructorArgNumberMismatch x c (length iargTys') args
  | otherwise = throwError $ TEInvalidTypeForData ity
checkType ity TmTrue
  | ITyBool _ <- ity = pure ITmTrue
  | otherwise        = throwError $ TEInvalidTypeForTrue ity
checkType ity TmFalse
  | ITyBool _ <- ity = pure ITmFalse
  | otherwise        = throwError $ TEInvalidTypeForFalse ity
checkType ity (TmIte t0 t1 t2) = do
  (it0, ity0, _) <- inferType t0
  case ity0 of
    ITyBool _ -> uncurry (ITmIte it0) <$> unionPair (checkType ity) (t1, t2)
    _ -> throwError $ TEInvalidConditionForIte it0 ity0
checkType ity (TmInt n)
  | ITyInt _ <- ity = pure $ ITmInt n
  | otherwise       = throwError $ TEInvalidTypeForInt ity
checkType ity (TmBinOp bop t0 t1) = do
  k <- extractModeOfType ity
  let
    (ity0, ity1, ity') = qBinOpType k bop
  unifyIType ity ity'
  it0 <- checkType ity0 t0
  it1 <- checkType ity1 t1
  pure (ITmBinOp bop it0 it1)
checkType ity (TmMatch t mayTy brs) = do
  (it, ity', k) <- checkContextUsageGEBy thd3 $ maybe (inferType t) withTypeHelper mayTy
  ITmMatch k it ity' <$> unionTraverse (checkBranch ity' k ity) brs
  where
    withTypeHelper ty' = do
      (ity', k) <- checkWFOfType ty'
      it <- checkType ity' t
      pure (it, ity', k)
checkType ity (TmTuple items)
  | ITyProd itemTys <- ity =
      case zipExactMay itemTys items of
        Just itemTysItems -> ITmTuple <$> traverse (uncurry checkType) itemTysItems
        Nothing           -> throwError $ TETupleArgNumberMismatch ity (length itemTys) items
  | otherwise              = throwError $ TEInvalidTypeForTuple ity
checkType ity (TmSusp ctxh t)
  | ITyUp m _ ictx ity' <- ity = do
    ictxh <- checkWFOfContextHat ctxh ictx
    removeVariables ictxh $ local (<> ictx) $ ITmSusp m ictxh <$> checkType ity' t
  | otherwise                = throwError $ TEInvalidTypeForSusp ity
checkType ity (TmStore t)
  | ITyDown _ h ity' <- ity = checkContextUsageGE h $ ITmStore h <$> checkType ity' t
  | otherwise               = throwError $ TEInvalidTypeForSusp ity
checkType ity (TmAmbiLam pat mayCE t)
  | ITyArr ity0 ity1 <- ity =
      case mayCE of
        Just (CEType ty0') -> do
          (ity0', k) <- checkWFOfType ty0'
          unifyIType ity0 ity0'
          handleLambda ity0 k ity1
        Just (CEKind ki0) -> throwError $ TEInvalidKindAnnForLam ki0 ity0
        Nothing -> do
          k <- extractModeOfType ity0
          handleLambda ity0 k ity1
  | ITyForall y iki0 ity1 <- ity =
      case mayCE of
        Just (CEType ty0) -> throwError $ TEInvalidTypeAnnForTypeLam ty0 iki0
        Just (CEKind ki0') -> do
          (iki0', k) <- checkContextUsageGEBy snd $ checkWFOfKind ki0'
          unifyIKind iki0 iki0'
          handleTypeLambda y iki0 k ity1
        Nothing -> handleTypeLambda y iki0 (getModeOfIKind iki0) ity1
  | otherwise               = throwError $ TEInvalidTypeForLam ity
  where
    handleLambda ity0 k ity1 = do
      (ipat, ictx) <- checkPatternType ity0 k pat
      removeVariables (putIHat ictx) $ ITmLam ipat ity0 <$> local (<> ictx) (checkType ity1 t)

    handleTypeLambda _ iki0 k ity1 =
      case pat of
        PatVar x -> do
          -- this substitution is required once we compare types more properly
          -- ity1' <- substM2checkM $ applySubstType [ISEType (ITyVar x)] [(y, True)] ity1
          removeTypeVariable (x, k) $ ITmTLam x iki0 <$> local (:|> (x, k, ICEKind iki0)) (checkType ity1 t)
        _        -> throwError $ TEInvalidPatternForTypeLam pat
checkType ity t = do
  (it, ity', _) <- inferType t
  unifyIType ity ity'
  pure it

-- This function assumes that the input types are normalized
checkBranch :: (QModeSpec m) => QIType m -> m -> QIType m -> QBranch m -> QCheckM m (QIBranch m)
checkBranch ipatTy k ibTy (pat, b) = do
  (ipat, ictx) <- checkPatternType ipatTy k pat
  removeVariables (putIHat ictx) $ (ipat,) <$> local (<> ictx) (checkType ibTy b)

-- This function always returns a normalized type
inferType :: (QModeSpec m) => QTerm m -> QCheckM m (QITerm m, QIType m, m)
inferType (TmVar x) = do
  (k, ity) <- getTermAndUse x
  pure (ITmVar x, ity, k)
inferType (TmBinOp bop t0 t1) = catchError t0First (const t1First)
  where
    t0First = do
      -- This exploits that our binary operators always have
      -- same modes for all operands. If we introduce a binary
      -- operation violates this condition, we should remove
      -- this from @inferType@.
      (it0, ity0, k) <- inferType t0
      let
        (ity0', ity1, ity) = qBinOpType k bop
      unifyIType ity0 ity0'
      it1 <- checkType ity1 t1
      pure (ITmBinOp bop it0 it1, ity, k)

    t1First = do
      (it1, ity1, k) <- inferType t1
      let
        (ity0, ity1', ity) = qBinOpType k bop
      unifyIType ity1 ity1'
      it0 <- checkType ity0 t0
      pure (ITmBinOp bop it0 it1, ity, k)
inferType (TmTuple items) = do
  (iitems, itys, ms) <- unzip3 <$> traverse inferType items
  forM_ (tail ms) $ testIsSameMode (head ms)
  pure (ITmTuple iitems, ITyProd itys, head ms)
inferType (TmForce t sub) = do
  (it, ity, k) <- checkContextUsageGEBy thd3 $ inferType t
  case ity of
    ITyUp _ l ictx ity' -> do
      isub <- checkContext ictx sub
      substM2checkM $ (ITmForce k it isub,, l) <$> applySubstType isub (icontext2idomain ictx) ity'
    _ -> throwError $ TEInvalidTermBodyForForce it ity
inferType (TmAmbiLam pat (Just (CEType ty0)) t) = do
  (ity0, k) <- checkWFOfType ty0
  (ipat, ictx) <- checkPatternType ity0 k pat
  (it, ity1, k') <- removeVariables (putIHat ictx) $ local (<> ictx) (inferType t)
  testIsSameMode k k'
  pure (ITmLam ipat ity0 it, ITyArr ity0 ity1, k)
inferType (TmAmbiLam pat (Just (CEKind ki0)) t) =
  case pat of
    PatVar x -> do
      (iki0, m) <- checkWFOfKind ki0
      (it, ity1, k) <- removeTypeVariable (x, m) $ local (:|> (x, m, ICEKind iki0)) $ inferType t
      testIsGEMode m k
      pure (ITmTLam x iki0 it, ITyForall x iki0 ity1, k)
    _        -> throwError $ TEInvalidPatternForTypeLam pat
inferType (TmAmbiApp t0 a1) = do
  (it0, ity, k) <- inferType t0
  case ity of
    ITyArr ity0 ity1 -> do
      (, ity1, k) . ITmApp it0 <$> checkTypeForAmbi ity0 a1
    ITyForall x iki0 ity1 -> do
      ity0 <- checkKindForAmbi iki0 a1
      ity1' <- substM2checkM $ applySubstType [ISEType ity0] [(x, True)] ity1
      pure (ITmTApp it0 ity0 , ity1', k)
    _ -> throwError $ TEInvalidFunctionForApp it0 ity
inferType (TmAnn t ty) = do
  (ity, k) <- checkWFOfType ty
  (, ity, k) <$> checkType ity t
inferType t = throwError $ TECheckOnlyTermInInference t

checkTypeForAmbi :: (QModeSpec m) => QIType m -> QAmbi m -> QCheckM m (QITerm m)
checkTypeForAmbi ity (AmCore ac) = checkType ity (ambiCore2term ac)
checkTypeForAmbi ity (AmTerm t)  = checkType ity t
checkTypeForAmbi _   (AmType ty) = throwError $ TEInvalidTypeArgForLam ty

checkKindForAmbi :: (QModeSpec m) => QIKind m -> QAmbi m -> QCheckM m (QIType m)
checkKindForAmbi iki (AmCore ac) = checkKind iki (ambiCore2type ac)
checkKindForAmbi iki (AmType ty) = checkKind iki ty
checkKindForAmbi _   (AmTerm tm) = throwError $ TEInvalidTermArgForTypeLam tm

checkPatternType :: (QModeSpec m) => QIType m -> m -> QPattern m -> QCheckM m (QIPattern m, QIContext m)
checkPatternType _   _ PatWild = pure (IPatWild, [])
checkPatternType ity k (PatVar x) = pure (IPatVar x, [(x, k, ICEType ity)])
checkPatternType ity _ PatTrue
  | ITyBool _ <- ity = pure (IPatTrue, [])
  | otherwise        = throwError $ TEInvalidTypeForTrue ity
checkPatternType ity _ PatFalse
  | ITyBool _ <- ity = pure (IPatFalse, [])
  | otherwise        = throwError $ TEInvalidTypeForFalse ity
checkPatternType ity _ (PatInt n)
  | ITyInt _ <- ity = pure (IPatInt n, [])
  | otherwise       = throwError $ TEInvalidTypeForInt ity
checkPatternType ity k (PatTuple pats)
  | ITyProd itemTys <- ity =
      case zipExactMay itemTys pats of
        Just itemTysPats -> bimap IPatTuple mconcat . unzip <$> traverse (uncurry (`checkPatternType` k)) itemTysPats
        Nothing           -> throwError $ TETuplePatternArgNumberMismatch ity (length itemTys) pats
  | otherwise              = throwError $ TEInvalidTypeForTuple ity
checkPatternType ity _ (PatLoad pat')
  | ITyDown _ h ity' <- ity = first IPatLoad <$> checkPatternType ity' h pat'
  | otherwise               = throwError $ TEInvalidPointerTypeForLoad ity
checkPatternType ity k (PatData c pats)
  | ITyData iparamTys x <- ity = do
      (_, (cn, params, iargTys)) <- getConDecl x c
      unless (length iparamTys == length params) $
        throwError $ TETypeArgNumberMismatch x (length params) (fromInternal <$> iparamTys)
      let
        sub = fmap ISEType (Seq.fromList iparamTys)
        dom = fmap (,True) (Seq.fromList params)
      iargTys' <- substM2checkM $ traverse (applySubstType sub dom) iargTys
      case zipExactMay iargTys' pats of
        Just iargTys'Pats -> bimap (IPatData c cn) mconcat . unzip <$> traverse (uncurry (`checkPatternType` k)) iargTys'Pats
        Nothing -> throwError $ TEConstructorPatternArgNumberMismatch x c (length iargTys') pats
  | otherwise = throwError $ TEInvalidTypeForData ity

checkContext :: (QModeSpec m) => QIContext m -> QSubst m -> QCheckM m (QISubst m)
checkContext ictx subst
  | weakeningLen >= 0 = do
      let (ictxFromWeakening, subIctx) = Seq.splitAt weakeningLen ictx
      isubst <- withErrorFor (TETSubst subst) $ traverse checkHelper $ Seq.zip subIctx subst
      checkContextWeakening ictxFromWeakening
      pure isubst
  | otherwise         = throwError $ TETooLongSubstitution (length ictx) subst
  where
    weakeningLen = length ictx - length subst

    checkHelper ((_, _, ICEKind iki), SEAmbi (AmCore (ambiCore2type -> ty))) = ISEType <$> checkKind iki ty
    checkHelper ((_, _, ICEKind iki), SEAmbi (AmType ty))                    = ISEType <$> checkKind iki ty
    checkHelper ((x, _, ICEKind iki), SEAmbi (AmTerm t))                     = throwError $ TESubstitutionEntryClassMismatchForType x t iki
    checkHelper ((_, _, ICEType ity), SEAmbi (AmCore (ambiCore2term -> t)))  = ISETerm <$> checkType ity t
    checkHelper ((_, _, ICEType ity), SEAmbi (AmTerm t))                     = ISETerm <$> checkType ity t
    checkHelper ((x, _, ICEType ity), SEAmbi (AmType ty))                    = throwError $ TESubstitutionEntryClassMismatchForTerm x ty ity

checkContextWeakening :: (QModeSpec m) => QIContext m -> QCheckM m ()
checkContextWeakening ictx0 = do
  unless (Seq.length ictx0 == Set.size (Set.fromList (fst3 <$> toList ictx0))) $ throwError $ TERepeatedContextEntryInWeakening ictx0
  forM_ ictx0 $ \(x, k, entry) -> do
    (k', entry') <- getFromCheckingIctx x
    testIsSameMode k k'
    unifyIContextEntry entry entry'

checkContextUsageGE :: (QModeSpec m) => m -> QCheckM m a -> QCheckM m a
checkContextUsageGE k = checkContextUsageGEBy (const k)

checkContextUsageGEBy :: (QModeSpec m) => (a -> m) -> QCheckM m a -> QCheckM m a
checkContextUsageGEBy f am = do
  (ause, a) <- listenUsage am
  testContextUsageGE (f a) ause
  pure a

testContextUsageGE ::  (MonadError (QTypingError m) em, QModeSpec m) => m -> QContextUsage m -> em ()
testContextUsageGE k = traverse_ (testContextEntryUsageGE k . snd) . getQContextUsage

testContextEntryUsageGE :: (MonadError (QTypingError m) em, QModeSpec m) => m -> QContextEntryUsage m -> em ()
testContextEntryUsageGE k (CEUKind m) = testIsGEMode m k
testContextEntryUsageGE k (CEUType m) = testIsGEMode m k

testContextUsageWk ::  (MonadError (QTypingError m) em, QModeSpec m) => QContextUsage m -> em ()
testContextUsageWk = traverse_ (\(x, k) -> withErrorFor (TETVariable x) $ whenJust (getCEUType k) testIsWkMode) . getQContextUsage

testIsGEMode :: (MonadError (QTypingError m) em, QModeSpec m) => m -> m -> em ()
testIsGEMode m k = unless (m >=!! k) $ throwError $ TEModeOrderFailure TEMOGE m k

testIsGTMode :: (MonadError (QTypingError m) em, QModeSpec m) => m -> m -> em ()
testIsGTMode m k = unless (m >!! k) $ throwError $ TEModeOrderFailure TEMOGT m k

testIsLEMode :: (MonadError (QTypingError m) em, QModeSpec m) => m -> m -> em ()
testIsLEMode l k = unless (l <=!! k) $ throwError $ TEModeOrderFailure TEMOLE l k

testIsSameMode :: (MonadError (QTypingError m) em, QModeSpec m) => m -> m -> em ()
testIsSameMode k0 k1 = unless (k0 == k1) $ throwError $ TEModeNotEqual k0 k1

testIsCoMode :: (MonadError (QTypingError m) em, QModeSpec m) => m -> em ()
testIsCoMode k = unless (modeSig k MdStCo) $ throwError $ TEModeStructuralRule MdStCo k

testIsWkMode :: (MonadError (QTypingError m) em, QModeSpec m) => m -> em ()
testIsWkMode k = unless (modeSig k MdStWk) $ throwError $ TEModeStructuralRule MdStWk k

------------------------------------------------------------
-- Type checker monad
------------------------------------------------------------

-- Constraints should be added as a state once we add them
newtype QCheckM m a
  = QCheckM
    { runQCheckM :: QTypingEnvironment m -> QIContext m -> ExceptT (QTypingError m) (State Integer) (QContextUsage m, a)
    }
  deriving stock (Functor)

instance (QModeSpec m) => Applicative (QCheckM m) where
  pure = QCheckM . const . const . pure . (UEmpty,)
  fm <*> am = QCheckM $ \env tctx -> do
    (fuse, f) <- runQCheckM fm env tctx
    (ause, a) <- runQCheckM am env tctx
    liftEither $ (, f a) <$> mergeUsage fuse ause
  liftA2 f am bm = QCheckM $ \env tctx -> do
    (ause, a) <- runQCheckM am env tctx
    (buse, b) <- runQCheckM bm env tctx
    liftEither $ (, f a b) <$> mergeUsage ause buse

instance (QModeSpec m) => Monad (QCheckM m) where
  am >>= f = QCheckM $ \env tctx -> do
    (ause, a) <- runQCheckM am env tctx
    (buse, b) <- runQCheckM (f a) env tctx
    liftEither $ (, b) <$> mergeUsage ause buse

instance (QModeSpec m) => MonadReader (QIContext m) (QCheckM m) where
  ask = QCheckM $ const $ pure . (UEmpty,)
  local f am = QCheckM $ \env -> runQCheckM am env . f

instance (QModeSpec m) => MonadError (QTypingError m) (QCheckM m) where
  throwError = QCheckM . const . const . throwError
  catchError am f = QCheckM $ \env tctx -> catchError (runQCheckM am env tctx) (\err -> runQCheckM (f err) env tctx)

newtype QCheckUnionM m a = QCheckUnionM { runQCheckUnionM :: QCheckM m a }
  deriving stock (Functor)

instance (QModeSpec m) => Applicative (QCheckUnionM m) where
  pure = QCheckUnionM . pure
  fm <*> am = QCheckUnionM $ QCheckM $ \env tctx -> do
    (fuse, f) <- runQCheckM (runQCheckUnionM fm) env tctx
    (ause, a) <- runQCheckM (runQCheckUnionM am) env tctx
    liftEither $ (, f a) <$> unionUsage fuse ause
  liftA2 f am bm = QCheckUnionM $ QCheckM $ \env tctx -> do
    (ause, a) <- runQCheckM (runQCheckUnionM am) env tctx
    (buse, b) <- runQCheckM (runQCheckUnionM bm) env tctx
    liftEither $ (, f a b) <$> unionUsage ause buse

instance (QModeSpec m) => Monad (QCheckUnionM m) where
  am >>= f = QCheckUnionM $ QCheckM $ \env tctx -> do
    (ause, a) <- runQCheckM (runQCheckUnionM am) env tctx
    (buse, b) <- runQCheckM (runQCheckUnionM (f a)) env tctx
    liftEither $ (, b) <$> unionUsage ause buse

unionPair :: (QModeSpec m) => (a -> QCheckM m b) -> (a, a) -> QCheckM m (b, b)
unionPair f (a1, a2) =
  runQCheckUnionM
  $ liftA2
      (,)
      (QCheckUnionM (f a1))
      (QCheckUnionM (f a2))

unionTraverse :: (QModeSpec m) => (a -> QCheckM m b) -> [a] -> QCheckM m [b]
unionTraverse _ []     = pure []
unionTraverse f [a]    = pure <$> f a
unionTraverse f (a:as) =
  runQCheckUnionM
  $ liftA2
      (:)
      (QCheckUnionM (f a))
      (QCheckUnionM (unionTraverse f as))

substM2checkM :: QSubstM m a -> QCheckM m a
substM2checkM = QCheckM . const . const . mapExceptT (fmap (first TESubstitutionError)) . fmap (UEmpty,) . runQSubstM

fullRunQCheckM :: QCheckM m a -> State Integer (Either (QTypingError m) a)
fullRunQCheckM = fmap (fmap snd) . runExceptT . ($ []) . ($ QTypingEnvironment []) . runQCheckM

-- We need this function only to check whether a type is used in
-- a valid mode or not. This does not actually "consume" the
-- assumption.
getTypeAndUse :: (QModeSpec m) => QId -> QCheckM m (m, QIKind m)
getTypeAndUse x = do
  (m, ientry) <- getFromCheckingIctx x
  case ientry of
    ICEKind iki -> do
      useTypeVariable x m
      pure (m, iki)
    ICEType _ -> throwError $ TETermVariableAsType x

getTermAndUse :: (QModeSpec m) => QId -> QCheckM m (m, QIType m)
getTermAndUse x = catchError inIctx $ const (getTermDecl x)
  where
    inIctx = do
      (m, ientry) <- getFromCheckingIctx x
      case ientry of
        ICEType ity -> do
          useTermVariable x m
          pure (m, ity)
        ICEKind _ -> throwError $ TETypeVariableAsTerm x

getFromIctx :: (MonadError (QTypingError m) em, QModeSpec m) => QIContext m -> QId -> em (m, QIContextEntry m)
getFromIctx ictx x =
  case Seq.findIndexR (\(x', _, _) -> x == x') ictx of
    Just i  -> let (_, m, ientry) = ictx `Seq.index` i in pure (m, ientry)
    Nothing -> throwError $ TENotInContext x ictx

getFromCheckingIctx :: (QModeSpec m) => QId -> QCheckM m (m, QIContextEntry m)
getFromCheckingIctx x = do
  ictx <- ask
  getFromIctx ictx x

------------------------------------------------------------
-- Top-level based environment for the type checker
------------------------------------------------------------

data QTypingEnvironmentEntry m
  = TEETypeDecl [(QId, QIKind m)]
  | TEEConDecl Int [QId] [QIType m] QId
  | TEETermDecl (QIType m)
  deriving stock (Eq, Ord, Show)

data QPostTypeEnvTop m
  = PTETopTermDef QId (QType m) (QTerm m)
  | PTETopTypeDef [(QId, QIKind m)] QId m [(QId, [QType m])]
  deriving stock (Eq, Ord, Show)

data QPostEnvTop m
  = PETopTermDef QId m (QIType m) (QTerm m)
  | PETopTypeDef [(QId, QIKind m)] QId m [(QId, [QIType m])]
  deriving stock (Eq, Ord, Show)

newtype QTypingEnvironment m
  = QTypingEnvironment
    { getQTypingEnvironment :: Seq (QId, m, QTypingEnvironmentEntry m)
    }
  deriving (Eq, Ord, Show, Semigroup, Monoid) via (Seq (QId, m, QTypingEnvironmentEntry m))

askEnv :: (QModeSpec m) => QCheckM m (QTypingEnvironment m)
askEnv = QCheckM $ (pure .) . const . (UEmpty,)

underEnv :: (QModeSpec m) => QTypingEnvironment m -> QCheckM m a -> QCheckM m a
underEnv env am = QCheckM $ const $ runQCheckM am env

------------------------------------------------------------
-- NOTE: Env does not have the concept of "use"
-- Or should it be? Polynomial time computation may need such
-- a concept

lookupEnvWithMapper :: (QModeSpec m) => QTypingEnvironment m -> QId -> (QTypingEnvironmentEntry m -> Maybe a) -> Maybe (m, a)
lookupEnvWithMapper env x f =
  case Seq.findIndexR cond $ getQTypingEnvironment env of
    Nothing -> Nothing
    Just i  ->
      let
        (_, k, eentry) = getQTypingEnvironment env `Seq.index` i
      in
      case f eentry of
        Just a -> Just (k, a)
        _      -> error $ "line " <> show (__LINE__ :: Int) <> " in " <> __FILE__
  where
    cond (x', _, eentry)
      | Just _ <- f eentry = x == x'
      | otherwise          = False

lookupTypingEnvWithMapper :: (QModeSpec m) => QId -> (QTypingEnvironmentEntry m -> Maybe a) -> QCheckM m (Maybe (m, a))
lookupTypingEnvWithMapper x f = do
  env <- askEnv
  pure $ lookupEnvWithMapper env x f

lookupTypeDecl :: (QModeSpec m) => QId -> QCheckM m (Maybe (m, [(QId, QIKind m)]))
lookupTypeDecl x = lookupTypingEnvWithMapper x f
  where
    f (TEETypeDecl args) = Just args
    f _                  = Nothing

lookupConDecl :: (QModeSpec m) => QId -> QId -> QCheckM m (Maybe (m, (Int, [QId], [QIType m])))
lookupConDecl x c = lookupTypingEnvWithMapper c f
  where
    f (TEEConDecl cn iys itys x')
      | x == x'                   = Just (cn, iys, itys)
    f _                           = Nothing

lookupTermDecl :: (QModeSpec m) => QId -> QCheckM m (Maybe (m, QIType m))
lookupTermDecl x = lookupTypingEnvWithMapper x f
  where
    f (TEETermDecl ity) = Just ity
    f _                 = Nothing

getFromEnvWithMapper :: (MonadError (QTypingError m) em, QModeSpec m) => QTypingEnvironment m -> QId -> (QTypingEnvironmentEntry m -> Maybe a) -> em (m, a)
getFromEnvWithMapper env x f =
  case lookupEnvWithMapper env x f of
    Nothing  -> throwError $ TENotInEnvironment x env
    Just res -> pure res

getFromTypingEnvWithMapper :: (QModeSpec m) => QId -> (QTypingEnvironmentEntry m -> Maybe a) -> QCheckM m (m, a)
getFromTypingEnvWithMapper x f = do
  env <- askEnv
  getFromEnvWithMapper env x f

getTypeDecl :: (QModeSpec m) => QId -> QCheckM m (m, [(QId, QIKind m)])
getTypeDecl x = getFromTypingEnvWithMapper x f
  where
    f (TEETypeDecl args) = Just args
    f _                  = Nothing

getConDecl :: (QModeSpec m) => QId -> QId -> QCheckM m (m, (Int, [QId], [QIType m]))
getConDecl x c = getFromTypingEnvWithMapper c f
  where
    f (TEEConDecl cn iys itys x')
      | x == x'                   = Just (cn, iys, itys)
    f _                           = Nothing

getTermDecl :: (QModeSpec m) => QId -> QCheckM m (m, QIType m)
getTermDecl x = getFromTypingEnvWithMapper x f
  where
    f (TEETermDecl ity) = Just ity
    f _                 = Nothing

------------------------------------------------------------
-- Usage for the type checker
------------------------------------------------------------

data QContextEntryUsage m
  = CEUKind m
  | CEUType m
  deriving stock (Eq, Ord, Show)

newtype QContextUsage m
  = QContextUsage
    { getQContextUsage :: Seq (QId, QContextEntryUsage m)
    }
  deriving (Eq, Ord, Show) via (Seq (QId, QContextEntryUsage m))

pattern UEmpty :: QContextUsage m
pattern UEmpty = QContextUsage Empty

pattern (:+*) :: QContextUsage m -> (QId, m) -> QContextUsage m
pattern (:+*) xs p <- QContextUsage ((QContextUsage -> xs) :|> (traverse getCEUKind -> Just p)) where
  (:+*) xs p = QContextUsage (getQContextUsage xs :|> fmap CEUKind p)

getCEUKind :: QContextEntryUsage m -> Maybe m
getCEUKind (CEUKind m) = Just m
getCEUKind _           = Nothing

pattern (:+?) :: QContextUsage m -> (QId, m) -> QContextUsage m
pattern (:+?) xs p <- QContextUsage ((QContextUsage -> xs) :|> (traverse getCEUType -> Just p)) where
  (:+?) xs p = QContextUsage (getQContextUsage xs :|> fmap CEUType p)

getCEUType :: QContextEntryUsage m -> Maybe m
getCEUType (CEUType m) = Just m
getCEUType _           = Nothing

{-# COMPLETE UEmpty, (:+*), (:+?) #-}

sameUsage :: (QModeSpec m) => QContextUsage m -> QContextUsage m -> Bool
sameUsage (QContextUsage use0) (QContextUsage use1) = Seq.sortOn fst use0 == Seq.sortOn fst use1

mergeUsage :: (QModeSpec m) => QContextUsage m -> QContextUsage m -> Either (QTypingError m) (QContextUsage m)
mergeUsage UEmpty            use1 = pure use1
mergeUsage (use0 :+* (x, k)) use1
  | Just i <- Seq.findIndexR ((x ==) . fst) (getQContextUsage use1) = do
      let (_, entryUse) = getQContextUsage use1 `Seq.index` i
      case entryUse of
        CEUKind k' -> do
          testIsSameMode k k'
        _ -> throwError $ TEVariableClassMismatch x
      use <- mergeUsage use0 . QContextUsage . Seq.deleteAt i $ getQContextUsage use1
      pure $ use :+* (x, k)
  | otherwise = do
      use <- mergeUsage use0 use1
      pure $ use :+* (x, k)
mergeUsage (use0 :+? (x, k)) use1
  | Just i <- Seq.findIndexR ((x ==) . fst) (getQContextUsage use1) = do
      let (_, entryUse) = getQContextUsage use1 `Seq.index` i
      case entryUse of
        CEUType k' -> do
          testIsSameMode k k'
          testIsCoMode k
        _ -> throwError $ TEVariableClassMismatch x
      use <- mergeUsage use0 . QContextUsage . Seq.deleteAt i $ getQContextUsage use1
      pure $ use :+? (x, k)
  | otherwise = do
      use <- mergeUsage use0 use1
      pure $ use :+? (x, k)

unionUsage :: (QModeSpec m) => QContextUsage m -> QContextUsage m -> Either (QTypingError m) (QContextUsage m)
unionUsage UEmpty            use1 = use1 <$ testContextUsageWk use1
unionUsage (use0 :+* (x, k)) use1
  | Just i <- Seq.findIndexR ((x ==) . fst) (getQContextUsage use1) = do
      let (_, entryUse) = getQContextUsage use1 `Seq.index` i
      case entryUse of
        CEUKind k' -> withErrorFor (TETVariable x) $ testIsSameMode k k'
        _          -> throwError $ TEVariableClassMismatch x
      use <- unionUsage use0 . QContextUsage . Seq.deleteAt i $ getQContextUsage use1
      pure $ use :+* (x, k)
  | otherwise = do
      use <- unionUsage use0 use1
      pure $ use :+* (x, k)
unionUsage (use0 :+? (x, k)) use1
  | Just i <- Seq.findIndexR ((x ==) . fst) (getQContextUsage use1) = do
      let (_, entryUse) = getQContextUsage use1 `Seq.index` i
      case entryUse of
        CEUType k' -> withErrorFor (TETVariable x) $ testIsSameMode k k'
        _          -> throwError $ TEVariableClassMismatch x
      use <- unionUsage use0 . QContextUsage . Seq.deleteAt i $ getQContextUsage use1
      pure $ use :+? (x, k)
  | otherwise = do
      withErrorFor (TETVariable x) $ testIsWkMode k
      use <- unionUsage use0 use1
      pure $ use :+? (x, k)

removeTypeV :: (QModeSpec m) => (QId, m) -> QContextUsage m -> Either (QTypingError m) (QContextUsage m)
removeTypeV _      UEmpty            = pure UEmpty
removeTypeV (x, k) (use :+* (y, k'))
  | x == y                           = use <$ testIsSameMode k k'
  | otherwise                        = (:+* (y, k')) <$> removeTypeV (x, k) use
removeTypeV (x, k) (use :+? (y, k')) = (:+? (y, k')) <$> removeTypeV (x, k) use

removeTypeVs :: (QModeSpec m) => Seq (QId, m) -> QContextUsage m -> Either (QTypingError m) (QContextUsage m)
removeTypeVs vs use = foldlM (flip removeTypeV) use vs

removeTermV :: (QModeSpec m) => (QId, m) -> QContextUsage m -> Either (QTypingError m) (QContextUsage m)
removeTermV (x, k) UEmpty            = UEmpty <$ withErrorFor (TETVariable x) (testIsWkMode k)
removeTermV (x, k) (use :+* (y, k')) = (:+* (y, k')) <$> removeTermV (x, k) use
removeTermV (x, k) (use :+? (y, k'))
  | x == y                           = use <$ testIsSameMode k k'
  | otherwise                        = (:+? (y, k')) <$> removeTermV (x, k) use

removeTermVInType :: (QModeSpec m) => (QId, m) -> QContextUsage m -> Either (QTypingError m) (QContextUsage m)
removeTermVInType (_, _) UEmpty            = pure UEmpty
removeTermVInType (x, k) (use :+* (y, k')) = (:+* (y, k')) <$> removeTermV (x, k) use
removeTermVInType (x, k) (use :+? (y, k'))
  | x == y                                 = use <$ testIsSameMode k k'
  | otherwise                              = (:+? (y, k')) <$> removeTermV (x, k) use

removeTermVs :: (QModeSpec m) => Seq (QId, m) -> QContextUsage m -> Either (QTypingError m) (QContextUsage m)
removeTermVs vs use = foldlM (flip removeTermV) use vs

removeVs :: (QModeSpec m) => QIContextHat m -> QContextUsage m -> Either (QTypingError m) (QContextUsage m)
removeVs vs use = foldlM (\use' (x, k, isKi) -> if isKi then removeTypeV (x, k) use' else removeTermV (x, k) use') use vs

removeVsInType :: (QModeSpec m) => QIContextHat m -> QContextUsage m -> Either (QTypingError m) (QContextUsage m)
removeVsInType vs use = foldlM (\use' (x, k, isKi) -> if isKi then removeTypeV (x, k) use' else removeTermVInType (x, k) use') use vs

listenUsage :: (QModeSpec m) => QCheckM m a -> QCheckM m (QContextUsage m, a)
listenUsage am = QCheckM $ \env -> fmap duplicate . runQCheckM am env

-- debugUsage :: (QModeSpec m) => QCheckM m a -> QCheckM m a
-- debugUsage am = QCheckM $ \env -> fmap (\x@(use, _) -> trace (show use) x) . runQCheckM am env

useVariables :: QContextUsage m -> QCheckM m ()
useVariables use = QCheckM . const . const $ pure (use, ())

useTypeVariable :: QId -> m -> QCheckM m ()
useTypeVariable x m = useVariables (UEmpty :+* (x, m))

useTermVariable :: QId -> m -> QCheckM m ()
useTermVariable x m = useVariables (UEmpty :+? (x, m))

removeTypeVariable :: (QModeSpec m) => (QId, m) -> QCheckM m a -> QCheckM m a
removeTypeVariable v am = QCheckM $ \env -> mapExceptT (fmap helper) . runQCheckM am env
  where
    helper (Right (use, a)) = (, a) <$> removeTypeV v use
    helper (Left err)       = Left err

removeTypeVariables :: (QModeSpec m) => Seq (QId, m) -> QCheckM m a -> QCheckM m a
removeTypeVariables vs am = QCheckM $ \env -> mapExceptT (fmap helper) . runQCheckM am env
  where
    helper (Right (use, a)) = (, a) <$> removeTypeVs vs use
    helper (Left err)       = Left err

removeTermVariable :: (QModeSpec m) => (QId, m) -> QCheckM m a -> QCheckM m a
removeTermVariable v am = QCheckM $ \env -> mapExceptT (fmap helper) . runQCheckM am env
  where
    helper (Right (use, a)) = (, a) <$> removeTermV v use
    helper (Left err)       = Left err

removeTermVariables :: (QModeSpec m) => Seq (QId, m) -> QCheckM m a -> QCheckM m a
removeTermVariables vs am = QCheckM $ \env -> mapExceptT (fmap helper) . runQCheckM am env
  where
    helper (Right (use, a)) = (, a) <$> removeTermVs vs use
    helper (Left err)       = Left err

removeVariables :: (QModeSpec m) => QIContextHat m -> QCheckM m a -> QCheckM m a
removeVariables vs am = QCheckM $ \env -> mapExceptT (fmap helper) . runQCheckM am env
  where
    helper (Right (use, a)) = (, a) <$> removeVs vs use
    helper (Left err)       = Left err

removeVariablesInType :: (QModeSpec m) => QIContextHat m -> QCheckM m a -> QCheckM m a
removeVariablesInType vs am = QCheckM $ \env -> mapExceptT (fmap helper) . runQCheckM am env
  where
    helper (Right (use, a)) = (, a) <$> removeVsInType vs use
    helper (Left err)       = Left err

------------------------------------------------------------
-- Equality checking / Unification
------------------------------------------------------------
-- As internal type/kind generators (i.e. well-formedness checkers)
-- always generate "normal" type/kinds, we can use
-- syntactic equality to check whether two types/kinds are equal.

unifyIKind :: (QModeSpec m) => QIKind m -> QIKind m -> QCheckM m ()
unifyIKind iki0 iki1 = unless (iki0 == iki1) $ throwError $ TEUnunifiableIKinds iki0 iki1

unifyIType :: (QModeSpec m) => QIType m -> QIType m -> QCheckM m ()
unifyIType ity0 ity1 = unless (ity0 == ity1) $ throwError $ TEUnunifiableITypes ity0 ity1

unifyIContextEntry :: (QModeSpec m) => QIContextEntry m -> QIContextEntry m -> QCheckM m ()
unifyIContextEntry (ICEKind iki0) (ICEKind iki1) = unifyIKind iki0 iki1
unifyIContextEntry (ICEType ity0) (ICEType ity1) = unifyIType ity0 ity1
unifyIContextEntry entry0         entry1         = throwError $ TEUnunifiableIEntry entry0 entry1

------------------------------------------------------------
-- Errors for the type checker
------------------------------------------------------------

data QTypingErrorModeOrdering
  = TEMOGT
  | TEMOGE
  | TEMOLT
  | TEMOLE
  deriving Show

data QTypingErrorTarget m
  = TETContext (QContext m)
  | TETConstructor QId
  | TETTermDefinition QId
  | TETTypeDefinition QId
  | TETVariable QId
  | TETMode m
  | TETTerm (QTerm m)
  | TETType (QType m)
  | TETKind (QKind m)
  | TETSubst (QSubst m)
  deriving Show

data QTypingError m
  = TEInvalidNonTypeKind (QIKind m)
  | TENotInEnvironment QId (QTypingEnvironment m)
  | TENotInContext QId (QIContext m)
  | TETypeVariableAsTerm QId
  | TETermVariableAsType QId
  | TEVariableClassMismatch QId
  | TEInvalidEmptyProd
  | TEInvalidKindForSusp (QIKind m)
  | TEInvalidTypeBodyForForce (QIType m) (QIKind m)
  | TEInvalidKindTypeForSusp
  | TEInvalidTypeForData (QIType m)
  | TEInvalidTypeForTrue (QIType m)
  | TEInvalidTypeForFalse (QIType m)
  | TEInvalidTypeForInt (QIType m)
  | TEInvalidTypeForTuple (QIType m)
  | TEInvalidTypeForSusp (QIType m)
  | TEInvalidTermBodyForForce (QITerm m) (QIType m)
  | TEInvalidTypeForStore (QIType m)
  | TEInvalidPointerTypeForLoad (QIType m)
  | TEInvalidTypeForLam (QIType m)
  | TEInvalidFunctionForApp (QITerm m) (QIType m)
  | TEInvalidConditionForIte (QITerm m) (QIType m)
  | TEInvalidTypeArgForLam (QType m)
  | TEInvalidTermArgForTypeLam (QTerm m)
  | TEInvalidKindAnnForLam (QKind m) (QIType m)
  | TEInvalidTypeAnnForTypeLam (QType m) (QIKind m)
  | TEInvalidPatternForTypeLam (QPattern m)
  | TEInvalidBuiltIn m QBuiltIn
  | TEInvalidTypeForArrayTag (QIType m)
  | TECheckOnlyTermInInference (QTerm m)
  | TEDuplicatedTypeName QId
  | TEDuplicatedConName QId QId
  | TEDuplicatedTermName QId
  | TECheckOnlyTypeInInference (QType m)
  | TEUnunifiableIKinds (QIKind m) (QIKind m)
  | TEUnunifiableITypes (QIType m) (QIType m)
  | TEUnunifiableIEntry (QIContextEntry m) (QIContextEntry m)
  | TEContextHatConflict (QContextHat m) (QIContext m)
  | TEModeOrderFailure QTypingErrorModeOrdering m m
  | TEModeNotEqual m m
  | TEModeStructuralRule QMdSt m
  | TENotYetSupported String
  | TETypeArgNumberMismatch QId Int [QType m]
  | TEConstructorArgNumberMismatch QId QId Int [QTerm m]
  | TEConstructorPatternArgNumberMismatch QId QId Int [QPattern m]
  | TETupleArgNumberMismatch (QIType m) Int [QTerm m]
  | TETuplePatternArgNumberMismatch (QIType m) Int [QPattern m]
  | TETooLongSubstitution Int (QSubst m)
  | TESubstitutionEntryClassMismatchForType QId (QTerm m) (QIKind m)
  | TESubstitutionEntryClassMismatchForTerm QId (QType m) (QIType m)
  | TERepeatedContextEntryInWeakening (QIContext m)
  | TESubstitutionError (QSubstError m)
  | TEFor (QTypingErrorTarget m) (QTypingError m)
  | TEInternalError (QTypingError m)
  deriving Show

withErrorFor :: (MonadError (QTypingError m) em, QModeSpec m) => QTypingErrorTarget m -> em a -> em a
withErrorFor tet = withError (TEFor tet)
