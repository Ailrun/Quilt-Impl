{-# LANGUAGE CPP             #-}
{-# LANGUAGE DerivingVia     #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns    #-}
module Elevator.TypeChecker where

import Control.Applicative        (Applicative (..))
import Control.Comonad            (Comonad (duplicate))
import Control.Monad              (forM, forM_, unless)
import Control.Monad.Except       (ExceptT, MonadError (..), withError, liftEither, mapExceptT, runExceptT)
import Control.Monad.Extra        (whenJustM, whenJust)
import Control.Monad.Reader.Class (MonadReader (..))
import Control.Monad.State.Strict (State)
import Data.Bifunctor             (Bifunctor (..))
import Data.Foldable              (Foldable (toList), traverse_, foldlM)
import Data.Sequence              (Seq (..), pattern (:|>))
import Data.Sequence              qualified as Seq
import Data.Set                   qualified as Set
import Data.Traversable.Compat    (mapAccumM)
import Data.Tuple.Extra           (fst3, thd3)
import Elevator.ModeSpec
import Elevator.Substitution
import Elevator.Syntax
import Safe.Exact                 (zipExactMay)

checkModule :: (ElModeSpec m) => ElModule m -> ElCheckM m (ElIModule m)
checkModule (ElModule [] tops) = do
  (typeEnv, mayAnnTops) <- underEnv mempty $ buildTypeEnv tops
  (termEnv, annTops) <- underEnv typeEnv $ buildTermEnv mayAnnTops
  underEnv (typeEnv <> termEnv) $ ElIModule [] <$> traverse checkPETop annTops
checkModule (ElModule _ _)     = throwError $ TENotYetSupported "module dependence"

buildTypeEnv :: (ElModeSpec m) => [ElTop m] -> ElCheckM m (ElTypingEnvironment m, [ElPostTypeEnvTop m])
buildTypeEnv = mapAccumM accumTypeEnvForTop mempty

accumTypeEnvForTop :: ElModeSpec m => ElTypingEnvironment m -> ElTop m -> ElCheckM m (ElTypingEnvironment m, ElPostTypeEnvTop m)
accumTypeEnvForTop env (TopTermDef x ty t)        = pure (env, PTETopTermDef x ty t)
accumTypeEnvForTop env (TopTypeDef args x k cons) = do
  whenJustM (lookupTypeDecl x) $ const $ throwError $ TEDuplicatedTypeName x
  iargs <- forM args $ \(y, yki) ->
    (y,) <$> maybe (pure $ IKiType k) (fmap fst . checkWFOfKind) yki
  let env' = env <> ElTypingEnvironment (Seq.singleton (x, k, TEETypeDecl iargs))
  pure (env', PTETopTypeDef iargs x k cons)

buildTermEnv :: (ElModeSpec m) => [ElPostTypeEnvTop m] -> ElCheckM m (ElTypingEnvironment m, [ElPostEnvTop m])
buildTermEnv = mapAccumM accumTermEnvForPTETop mempty

accumTermEnvForPTETop :: ElModeSpec m => ElTypingEnvironment m -> ElPostTypeEnvTop m -> ElCheckM m (ElTypingEnvironment m, ElPostEnvTop m)
accumTermEnvForPTETop env (PTETopTypeDef iargs x k cons) = do
  forM_ cons $ \(c, _) ->
    whenJustM (lookupConDecl x c) $ const $ throwError $ TEDuplicatedConName c
  icons <- withError (TEFor $ TETVariable x) $ checkCons iargs cons
  let env' = env <> ElTypingEnvironment (Seq.fromList (fmap (\(cn, (c, itys)) -> (c, k, TEEConDecl cn (fst <$> iargs) itys x)) (zip [0..] icons)))
  pure (env', PETopTypeDef iargs x k icons)
accumTermEnvForPTETop env (PTETopTermDef x ty t)         = do
  whenJustM (lookupTermDecl x) $ const $ throwError $ TEDuplicatedConName x
  (ity, k) <- withError (TEFor (TETVariable x) . TEFor (TETType ty)) $ checkWFOfType ty
  let env' = env <> ElTypingEnvironment (Seq.singleton (x, k, TEETermDecl ity))
  pure (env', PETopTermDef x k ity t)

checkPETop :: (ElModeSpec m) => ElPostEnvTop m -> ElCheckM m (ElITop m)
checkPETop (PETopTypeDef iargs x k icons) = pure $ ITopTypeDef iargs x k icons
checkPETop (PETopTermDef x k ity t)       = withError (TEFor (TETVariable x)) $ ITopTermDef x k ity <$> checkType ity t

checkCons :: (ElModeSpec m) => [(ElId, ElIKind m)] -> [(ElId, [ElType m])] -> ElCheckM m [(ElId, [ElIType m])]
checkCons iargs = traverse checkCon
  where
    checkCon (c, argTys) =
      withError (TEFor $ TETVariable c)
      $ removeTypeVariables iargsrem
      $ (c,) <$> traverse (local (<> iargsctx) . checkWFOfType_) argTys

    iargsctx = Seq.fromList ((\(y, yiki) -> (y, getModeOfIKind yiki, ICEKind yiki)) <$> iargs)
    iargsrem = fmap (\(x, k, _) -> (x, k)) iargsctx

buildEnv :: (ElModeSpec m) => [ElITop m] -> ElCheckM m (ElTypingEnvironment m)
buildEnv = foldlM accumEnvForTop mempty

accumEnvForTop :: ElModeSpec m => ElTypingEnvironment m -> ElITop m -> ElCheckM m (ElTypingEnvironment m)
accumEnvForTop env (ITopTermDef x k ity _) = do
  whenJustM (lookupTermDecl x) $ const $ throwError $ TEDuplicatedConName x
  let env' = env <> ElTypingEnvironment (Seq.singleton (x, k, TEETermDecl ity))
  pure env'
accumEnvForTop env (ITopTypeDef iargs x k icons) = do
  whenJustM (lookupTypeDecl x) $ const $ throwError $ TEDuplicatedTypeName x
  let env' = env <> ElTypingEnvironment (Seq.singleton (x, k, TEETypeDecl iargs)) <> ElTypingEnvironment (Seq.fromList (fmap (\(cn, (c, itys)) -> (c, k, TEEConDecl cn (fst <$> iargs) itys x)) (zip [0..] icons)))
  pure env'

checkTopUnderModule :: (ElModeSpec m) => ElIModule m -> ElTop m -> ElCheckM m (ElIModule m)
checkTopUnderModule (ElIModule mids itops) top = do
  env <- buildEnv itops
  underEnv env $
    ElIModule mids . (itops <>) . pure <$> checkTop top

checkTop :: (ElModeSpec m) => ElTop m -> ElCheckM m (ElITop m)
checkTop (TopTermDef x ty t) = do
  whenJustM (lookupTermDecl x) $ const $ throwError $ TEDuplicatedConName x
  (ity, k) <- checkWFOfType ty
  env <- askEnv
  underEnv (env <> ElTypingEnvironment (Seq.singleton (x, k, TEETermDecl ity))) $
    ITopTermDef x k ity <$> checkType ity t
checkTop (TopTypeDef args x k cons) = do
  whenJustM (lookupTypeDecl x) $ const $ throwError $ TEDuplicatedTypeName x
  iargs <- forM args $ \(y, yki) ->
    (y,) <$> maybe (pure $ IKiType k) (fmap fst . checkWFOfKind) yki
  env <- askEnv
  underEnv (env <> ElTypingEnvironment (Seq.singleton (x, k, TEETypeDecl iargs))) $ do
    forM_ cons $ \(c, _) ->
      whenJustM (lookupConDecl x c) $ const $ throwError $ TEDuplicatedConName c
    ITopTypeDef iargs x k <$> checkCons iargs cons

inferTypeUnderModule :: (ElModeSpec m) => ElIModule m -> ElTerm m -> ElCheckM m (ElITerm m, ElIType m, m)
inferTypeUnderModule (ElIModule _ itops) t = do
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

checkWFOfKind :: (ElModeSpec m) => ElKind m -> ElCheckM m (ElIKind m, m)
checkWFOfKind (KiType k)          = pure (IKiType k, k)
checkWFOfKind ki@(KiUp k ctx ki') = do
  ictx <- checkWFOfContext ctx
  (iki', l) <- removeVariablesInType (putIHat ictx) $ local (<> ictx) $ checkWFOfKind ki'
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
checkWFOfType (TyData argTys x)    = do
  (k, iargKis) <- getTypeDecl x
  case zipExactMay (snd <$> iargKis) argTys of
    Just iargKiTys -> do
      itys <- forM iargKiTys $ \(iargKi, argTy) ->
        checkContextUsageGE (getModeOfIKind iargKi) $ checkKind iargKi argTy
      pure (ITyData itys x, k)
    Nothing    -> throwError $ TETypeArgNumberMismatch (length iargKis) argTys
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
  withError (TEFor $ TETType ty) $ checkRangeOfContext (Just l) (Just k) ictx
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

checkWFOfType_ :: (ElModeSpec m) => ElType m -> ElCheckM m (ElIType m)
checkWFOfType_ = fmap fst . checkWFOfType

checkKind :: (ElModeSpec m) => ElIKind m -> ElType m -> ElCheckM m (ElIType m)
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
    IKiUp k ictx iki' -> do
      let idom = icontext2idomain ictx
      isub <- checkContext ictx sub
      iki'' <- substM2checkM $ applySubstKind isub idom iki'
      case ity of
        ITySusp _ _ ity' -> (, iki'') <$> substM2checkM (applySubstType isub idom ity')
        _                -> pure (ITyForce k ity isub, iki'')
    _                 -> throwError $ TEInvalidKindForForce iki
inferKind (TyAnn ty ki)        = do
  iki <- checkWFOfKind_ ki
  (, iki) <$> checkKind iki ty
inferKind ty@(TySusp _ _)      = throwError $ TENoninferableType ty
inferKind ty                   = fmap IKiType <$> checkWFOfType ty

extractModeOfType :: (ElModeSpec m) => ElIType m -> ElCheckM m m
extractModeOfType = fmap snd . checkWFOfType . fromInternal

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
checkWFOfContext = foldlM folder Seq.empty
  where
    folder ictx (x, entry) =
      removeVariablesInType (putIHat ictx)
      $ (ictx :|>) . uncurry (flip (x,,))
      <$> local (<> ictx) (checkWFOfContextEntry entry)

checkWFOfContextHat :: (ElModeSpec m) => ElContextHat m -> ElIContext m -> ElCheckM m (ElIContextHat m)
checkWFOfContextHat ctxh ictx = do
  unless (ctxh == icontextHat2contextHat (putIHat ictx)) $ throwError $ TEContextHatConflict ctxh ictx
  pure $ putIHat ictx

-- This function assumes that the input type is normalized
checkType :: (ElModeSpec m) => ElIType m -> ElTerm m -> ElCheckM m (ElITerm m)
checkType ity (TmBuiltIn bi) = do
  k <- extractModeOfType ity
  case typeOfBuiltIn k bi of
    Just ity' -> do
      unifyIType ity ity'
      pure (ITmBuiltIn bi)
    Nothing -> throwError $ TEInvalidBuiltIn bi
checkType ity (TmArrayTag n)
  | ITyArray _ _ <- ity = pure (ITmArrayTag n)
  | otherwise           = throwError $ TEInvalidTypeForArrayTag ity
checkType ity (TmData c args)
  | ITyData iparamTys x <- ity = do
      (_, (cn, params, iargTys)) <- getConDecl x c
      unless (length iparamTys == length params) $
        throwError $ TETypeArgNumberMismatch (length params) (fromInternal <$> iparamTys)
      let
        sub = fmap ISEType (Seq.fromList iparamTys)
        dom = fmap (,True) (Seq.fromList params)
      iargTys' <- substM2checkM $ traverse (applySubstType sub dom) iargTys
      case zipExactMay iargTys' args of
        Just iargTys'Args -> ITmData c cn <$> traverse (uncurry checkType) iargTys'Args
        Nothing -> throwError $ TEConstructorArgNumberMismatch (length iargTys') args
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
    ITyBool _ -> do
      liftA2
        (ITmIte it0)
        (checkType ity t1)
        (checkType ity t2)
    _ -> throwError $ TEInvalidConditionTypeForIte ity0
checkType ity (TmInt n)
  | ITyInt _ <- ity = pure $ ITmInt n
  | otherwise       = throwError $ TEInvalidTypeForInt ity
checkType ity (TmBinOp bop t0 t1) = do
  k <- extractModeOfType ity
  let
    (ity0, ity1, ity') = elBinOpType k bop
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
        Nothing           -> throwError $ TETupleArgNumberMismatch (length itemTys) items
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
  | ITyArr ity0 ity1 <- ity = do
      case mayCE of
        Just (CEType ty0') -> do
          (ity0', k) <- checkWFOfType ty0'
          unifyIType ity0 ity0'
          handleLambda ity0 k ity1
        Just (CEKind ki0) -> throwError $ TEInvalidKindAnnForLam ki0
        Nothing -> do
          k <- extractModeOfType ity0
          handleLambda ity0 k ity1
  | ITyForall _ iki0 ity1 <- ity = do
      case mayCE of
        Just (CEType ty0) -> throwError $ TEInvalidTypeAnnForTypeLam ty0
        Just (CEKind ki0') -> do
          (iki0', k) <- checkContextUsageGEBy snd $ checkWFOfKind ki0'
          unifyIKind iki0 iki0'
          handleTypeLambda iki0 k ity1
        Nothing -> handleTypeLambda iki0 (getModeOfIKind iki0) ity1
  | otherwise               = throwError $ TEInvalidTypeForLam ity
  where
    handleLambda ity0 k ity1 = do
      (ipat, ictx) <- checkPatternType ity0 k pat
      removeVariables (putIHat ictx) $ ITmLam ipat ity0 <$> local (<> ictx) (checkType ity1 t)

    handleTypeLambda iki0 k ity1 = do
      case pat of
        PatVar x -> removeTypeVariable (x, k) $ ITmTLam x iki0 <$> local (:|> (x, k, ICEKind iki0)) (checkType ity1 t)
        _        -> throwError $ TEInvalidPatternForTypeLam pat
checkType ity t = do
  (it, ity', _) <- inferType t
  unifyIType ity ity'
  pure it

-- This function assumes that the input types are normalized
checkBranch :: (ElModeSpec m) => ElIType m -> m -> ElIType m -> ElBranch m -> ElCheckM m (ElIBranch m)
checkBranch ipatTy k ibTy (pat, b) = do
  (ipat, ictx) <- checkPatternType ipatTy k pat
  removeVariables (putIHat ictx) $ (ipat,) <$> local (<> ictx) (checkType ibTy b)

-- This function always returns a normalized type
inferType :: (ElModeSpec m) => ElTerm m -> ElCheckM m (ElITerm m, ElIType m, m)
inferType (TmVar x) = do
  (k, ity) <- getTermAndUse x
  pure (ITmVar x, ity, k)
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
    _ -> throwError $ TEInvalidArgTypeForForce ity
inferType (TmAmbiApp t0 a1) = do
  (it0, ity, k) <- inferType t0
  case ity of
    ITyArr ity0 ity1 -> do
      (, ity1, k) . ITmApp it0 <$> checkTypeForAmbi ity0 a1
    ITyForall x iki0 ity1 -> do
      ity0 <- checkKindForAmbi iki0 a1
      ity1' <- substM2checkM $ applySubstType (Seq.singleton (ISEType ity0)) (Seq.singleton (x, True)) ity1
      pure (ITmTApp it0 ity0 , ity1', k)
    _ -> throwError $ TEInvalidFunctionTypeForApp ity
inferType (TmAnn t ty) = do
  (ity, k) <- checkWFOfType ty
  (, ity, k) <$> checkType ity t
inferType t = throwError $ TECheckOnlyTermInInference t

checkTypeForAmbi :: (ElModeSpec m) => ElIType m -> ElAmbi m -> ElCheckM m (ElITerm m)
checkTypeForAmbi ity (AmCore ac) = checkType ity (ambiCore2term ac)
checkTypeForAmbi ity (AmTerm t) = checkType ity t
checkTypeForAmbi _   (AmType ty) = throwError $ TEInvalidTypeArgForLam ty

checkKindForAmbi :: (ElModeSpec m) => ElIKind m -> ElAmbi m -> ElCheckM m (ElIType m)
checkKindForAmbi iki (AmCore ac) = checkKind iki (ambiCore2type ac)
checkKindForAmbi iki (AmType ty) = checkKind iki ty
checkKindForAmbi _   (AmTerm tm) = throwError $ TEInvalidTermArgForTypeLam tm

checkPatternType :: (ElModeSpec m) => ElIType m -> m -> ElPattern m -> ElCheckM m (ElIPattern m, ElIContext m)
checkPatternType _   _ PatWild = pure (IPatWild, Seq.empty)
checkPatternType ity k (PatVar x) = pure (IPatVar x, Seq.singleton (x, k, ICEType ity))
checkPatternType ity _ PatTrue
  | ITyBool _ <- ity = pure (IPatTrue, Seq.empty)
  | otherwise        = throwError $ TEInvalidTypeForTrue ity
checkPatternType ity _ PatFalse
  | ITyBool _ <- ity = pure (IPatFalse, Seq.empty)
  | otherwise        = throwError $ TEInvalidTypeForFalse ity
checkPatternType ity _ (PatInt n)
  | ITyInt _ <- ity = pure (IPatInt n, Seq.empty)
  | otherwise       = throwError $ TEInvalidTypeForInt ity
checkPatternType ity k (PatTuple pats)
  | ITyProd itemTys <- ity =
      case zipExactMay itemTys pats of
        Just itemTysPats -> bimap IPatTuple mconcat . unzip <$> traverse (uncurry (`checkPatternType` k)) itemTysPats
        Nothing           -> throwError $ TETuplePatternArgNumberMismatch (length itemTys) pats
  | otherwise              = throwError $ TEInvalidTypeForTuple ity
checkPatternType ity _ (PatLoad pat')
  | ITyDown _ h ity' <- ity = first IPatLoad <$> checkPatternType ity' h pat'
  | otherwise               = throwError $ TEInvalidTypeForLoad ity
checkPatternType ity k (PatData c pats)
  | ITyData iparamTys x <- ity = do
      (_, (cn, params, iargTys)) <- getConDecl x c
      unless (length iparamTys == length params) $
        throwError $ TETypeArgNumberMismatch (length params) (fromInternal <$> iparamTys)
      let
        sub = fmap ISEType (Seq.fromList iparamTys)
        dom = fmap (,True) (Seq.fromList params)
      iargTys' <- substM2checkM $ traverse (applySubstType sub dom) iargTys
      case zipExactMay iargTys' pats of
        Just iargTys'Pats -> bimap (IPatData c cn) mconcat . unzip <$> traverse (uncurry (`checkPatternType` k)) iargTys'Pats
        Nothing -> throwError $ TEConstructorPatternArgNumberMismatch (length iargTys') pats
  | otherwise = throwError $ TEInvalidTypeForData ity

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

testContextUsageWk ::  (MonadError (ElTypingError m) em, ElModeSpec m) => ElContextUsage m -> em ()
testContextUsageWk = traverse_ (flip whenJust testIsWkMode . getCEUType . snd) . getElContextUsage

testIsGEMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> m -> em ()
testIsGEMode m k = unless (m >=!! k) $ throwError $ TEModeOrderFailure TEMOGE m k

testIsGTMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> m -> em ()
testIsGTMode m k = unless (m >!! k) $ throwError $ TEModeOrderFailure TEMOGT m k

testIsLEMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> m -> em ()
testIsLEMode l k = unless (l <=!! k) $ throwError $ TEModeOrderFailure TEMOLE l k

testIsSameMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> m -> em ()
testIsSameMode k0 k1 = unless (k0 == k1) $ throwError $ TEModeNotEqual k0 k1

testIsCoMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> em ()
testIsCoMode k = unless (modeSig k MdStCo) $ throwError $ TEModeStructuralRule MdStCo k

testIsWkMode :: (MonadError (ElTypingError m) em, ElModeSpec m) => m -> em ()
testIsWkMode k = unless (modeSig k MdStWk) $ throwError $ TEModeStructuralRule MdStWk k

------------------------------------------------------------
-- Type checker monad
------------------------------------------------------------

-- Constraints should be added as a state once we add them
newtype ElCheckM m a
  = ElCheckM
    { runElCheckM :: ElTypingEnvironment m -> ElIContext m -> ExceptT (ElTypingError m) (State Integer) (ElContextUsage m, a)
    }
  deriving stock (Functor)

instance (ElModeSpec m) => Applicative (ElCheckM m) where
  pure = ElCheckM . const . const . pure . (UEmpty,)
  fm <*> am = ElCheckM $ \env tctx -> do
    (fuse, f) <- runElCheckM fm env tctx
    (ause, a) <- runElCheckM am env tctx
    liftEither $ (, f a) <$> mergeUsage fuse ause
  liftA2 f am bm = ElCheckM $ \env tctx -> do
    (ause, a) <- runElCheckM am env tctx
    (buse, b) <- runElCheckM bm env tctx
    liftEither $ (, f a b) <$> mergeUsage ause buse

instance (ElModeSpec m) => Monad (ElCheckM m) where
  am >>= f = ElCheckM $ \env tctx -> do
    (ause, a) <- runElCheckM am env tctx
    (buse, b) <- runElCheckM (f a) env tctx
    liftEither $ (, b) <$> mergeUsage ause buse

instance (ElModeSpec m) => MonadReader (ElIContext m) (ElCheckM m) where
  ask = ElCheckM $ const $ pure . (UEmpty,)
  local f am = ElCheckM $ \env -> runElCheckM am env . f

instance (ElModeSpec m) => MonadError (ElTypingError m) (ElCheckM m) where
  throwError = ElCheckM . const . const . throwError
  catchError am f = ElCheckM $ \env tctx -> catchError (runElCheckM am env tctx) (\err -> runElCheckM (f err) env tctx)

newtype ElCheckUnionM m a = ElCheckUnionM { runElCheckUnionM :: ElCheckM m a }
  deriving stock (Functor)

instance (ElModeSpec m) => Applicative (ElCheckUnionM m) where
  pure = ElCheckUnionM . pure
  fm <*> am = ElCheckUnionM $ ElCheckM $ \env tctx -> do
    (fuse, f) <- runElCheckM (runElCheckUnionM fm) env tctx
    (ause, a) <- runElCheckM (runElCheckUnionM am) env tctx
    liftEither $ (, f a) <$> unionUsage fuse ause
  liftA2 f am bm = ElCheckUnionM $ ElCheckM $ \env tctx -> do
    (ause, a) <- runElCheckM (runElCheckUnionM am) env tctx
    (buse, b) <- runElCheckM (runElCheckUnionM bm) env tctx
    liftEither $ (, f a b) <$> unionUsage ause buse

instance (ElModeSpec m) => Monad (ElCheckUnionM m) where
  am >>= f = ElCheckUnionM $ ElCheckM $ \env tctx -> do
    (ause, a) <- runElCheckM (runElCheckUnionM am) env tctx
    (buse, b) <- runElCheckM (runElCheckUnionM (f a)) env tctx
    liftEither $ (, b) <$> unionUsage ause buse

unionTraverse :: (ElModeSpec m) => (a -> ElCheckM m b) -> [a] -> ElCheckM m [b]
unionTraverse _ []     = pure []
unionTraverse f [a]    = pure <$> f a
unionTraverse f (a:as) =
  runElCheckUnionM
  $ liftA2
      (:)
      (ElCheckUnionM (f a))
      (ElCheckUnionM (unionTraverse f as))

substM2checkM :: ElSubstM a -> ElCheckM m a
substM2checkM = ElCheckM . const . const . mapExceptT (fmap (first TESubstitutionError)) . fmap (UEmpty,) . runElSubstM

fullRunElCheckM :: ElCheckM m a -> State Integer (Either (ElTypingError m) a)
fullRunElCheckM = fmap (fmap snd) . runExceptT . ($ Seq.empty) . ($ ElTypingEnvironment Seq.empty) . runElCheckM

-- We need this function only to check whether a type is used in
-- a valid mode or not. This does not actually "consume" the
-- assumption.
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
    Nothing -> throwError $ TENotInScope x (Left ictx)

getFromCheckingIctx :: (ElModeSpec m) => ElId -> ElCheckM m (m, ElIContextEntry m)
getFromCheckingIctx x = do
  ictx <- ask
  getFromIctx ictx x

------------------------------------------------------------
-- Top-level based environment for the type checker
------------------------------------------------------------

data ElTypingEnvironmentEntry m
  = TEETypeDecl [(ElId, ElIKind m)]
  | TEEConDecl Int [ElId] [ElIType m] ElId
  | TEETermDecl (ElIType m)
  deriving stock (Eq, Ord, Show)

data ElPostTypeEnvTop m
  = PTETopTermDef ElId (ElType m) (ElTerm m)
  | PTETopTypeDef [(ElId, ElIKind m)] ElId m [(ElId, [ElType m])]
  deriving stock (Eq, Ord, Show)

data ElPostEnvTop m
  = PETopTermDef ElId m (ElIType m) (ElTerm m)
  | PETopTypeDef [(ElId, ElIKind m)] ElId m [(ElId, [ElIType m])]
  deriving stock (Eq, Ord, Show)

newtype ElTypingEnvironment m
  = ElTypingEnvironment
    { getElTypingEnvironment :: Seq (ElId, m, ElTypingEnvironmentEntry m)
    }
  deriving (Eq, Ord, Show, Semigroup, Monoid) via (Seq (ElId, m, ElTypingEnvironmentEntry m))

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

lookupConDecl :: (ElModeSpec m) => ElId -> ElId -> ElCheckM m (Maybe (m, (Int, [ElId], [ElIType m])))
lookupConDecl x c = lookupTypingEnvWithMapper c f
  where
    f (TEEConDecl cn iys itys x')
      | x == x'                   = Just (cn, iys, itys)
    f _                           = Nothing

lookupTermDecl :: (ElModeSpec m) => ElId -> ElCheckM m (Maybe (m, ElIType m))
lookupTermDecl x = lookupTypingEnvWithMapper x f
  where
    f (TEETermDecl ity) = Just ity
    f _                 = Nothing

getFromEnvWithMapper :: (MonadError (ElTypingError m) em, ElModeSpec m) => ElTypingEnvironment m -> ElId -> (ElTypingEnvironmentEntry m -> Maybe a) -> em (m, a)
getFromEnvWithMapper env x f =
  case lookupEnvWithMapper env x f of
    Nothing  -> throwError $ TENotInScope x (Right env)
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

getConDecl :: (ElModeSpec m) => ElId -> ElId -> ElCheckM m (m, (Int, [ElId], [ElIType m]))
getConDecl x c = getFromTypingEnvWithMapper c f
  where
    f (TEEConDecl cn iys itys x')
      | x == x'                   = Just (cn, iys, itys)
    f _                           = Nothing

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
  deriving stock (Eq, Ord, Show)

newtype ElContextUsage m
  = ElContextUsage
    { getElContextUsage :: Seq (ElId, ElContextEntryUsage m)
    }
  deriving (Eq, Ord, Show) via (Seq (ElId, ElContextEntryUsage m))

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

unionUsage :: (ElModeSpec m) => ElContextUsage m -> ElContextUsage m -> Either (ElTypingError m) (ElContextUsage m)
unionUsage UEmpty            use1 = use1 <$ testContextUsageWk use1
unionUsage (use0 :+* (x, k)) use1
  | Just i <- Seq.findIndexR ((x ==) . fst) (getElContextUsage use1) = do
      let (_, entryUse) = getElContextUsage use1 `Seq.index` i
      case entryUse of
        CEUKind k' -> withError (TEFor $ TETVariable x) $ testIsSameMode k k'
        _ -> throwError $ TEVariableClassMismatch x
      use <- unionUsage use0 . ElContextUsage . Seq.deleteAt i $ getElContextUsage use1
      pure $ use :+* (x, k)
  | otherwise = do
      use <- unionUsage use0 use1
      pure $ use :+* (x, k)
unionUsage (use0 :+? (x, k)) use1
  | Just i <- Seq.findIndexR ((x ==) . fst) (getElContextUsage use1) = do
      let (_, entryUse) = getElContextUsage use1 `Seq.index` i
      case entryUse of
        CEUType k' -> withError (TEFor $ TETVariable x) $ testIsSameMode k k'
        _ -> throwError $ TEVariableClassMismatch x
      use <- unionUsage use0 . ElContextUsage . Seq.deleteAt i $ getElContextUsage use1
      pure $ use :+? (x, k)
  | otherwise = do
      withError (TEFor $ TETVariable x) $ testIsWkMode k
      use <- unionUsage use0 use1
      pure $ use :+? (x, k)

removeTypeV :: (ElModeSpec m) => (ElId, m) -> ElContextUsage m -> Either (ElTypingError m) (ElContextUsage m)
removeTypeV _      UEmpty            = pure UEmpty
removeTypeV (x, k) (use :+* (y, k'))
  | x == y                           = use <$ testIsSameMode k k'
  | otherwise                        = (:+* (y, k')) <$> removeTypeV (x, k) use
removeTypeV (x, k) (use :+? (y, k')) = (:+? (y, k')) <$> removeTypeV (x, k) use

removeTypeVs :: (ElModeSpec m) => Seq (ElId, m) -> ElContextUsage m -> Either (ElTypingError m) (ElContextUsage m)
removeTypeVs vs use = foldlM (flip removeTypeV) use vs

removeTermV :: (ElModeSpec m) => (ElId, m) -> ElContextUsage m -> Either (ElTypingError m) (ElContextUsage m)
removeTermV (_, k) UEmpty            = UEmpty <$ testIsWkMode k
removeTermV (x, k) (use :+* (y, k')) = (:+* (y, k')) <$> removeTermV (x, k) use
removeTermV (x, k) (use :+? (y, k'))
  | x == y                           = use <$ testIsSameMode k k'
  | otherwise                        = (:+? (y, k')) <$> removeTermV (x, k) use

removeTermVInType :: (ElModeSpec m) => (ElId, m) -> ElContextUsage m -> Either (ElTypingError m) (ElContextUsage m)
removeTermVInType (_, _) UEmpty            = pure UEmpty
removeTermVInType (x, k) (use :+* (y, k')) = (:+* (y, k')) <$> removeTermV (x, k) use
removeTermVInType (x, k) (use :+? (y, k'))
  | x == y                                 = use <$ testIsSameMode k k'
  | otherwise                              = (:+? (y, k')) <$> removeTermV (x, k) use

removeTermVs :: (ElModeSpec m) => Seq (ElId, m) -> ElContextUsage m -> Either (ElTypingError m) (ElContextUsage m)
removeTermVs vs use = foldlM (flip removeTermV) use vs

removeVs :: (ElModeSpec m) => ElIContextHat m -> ElContextUsage m -> Either (ElTypingError m) (ElContextUsage m)
removeVs vs use = foldlM (\use' (x, k, isKi) -> if isKi then removeTypeV (x, k) use' else removeTermV (x, k) use') use vs

removeVsInType :: (ElModeSpec m) => ElIContextHat m -> ElContextUsage m -> Either (ElTypingError m) (ElContextUsage m)
removeVsInType vs use = foldlM (\use' (x, k, isKi) -> if isKi then removeTypeV (x, k) use' else removeTermVInType (x, k) use') use vs

listenUsage :: (ElModeSpec m) => ElCheckM m a -> ElCheckM m (ElContextUsage m, a)
listenUsage am = ElCheckM $ \env -> fmap duplicate . runElCheckM am env

-- debugUsage :: (ElModeSpec m) => ElCheckM m a -> ElCheckM m a
-- debugUsage am = ElCheckM $ \env -> fmap (\x@(use, _) -> trace (show use) x) . runElCheckM am env

useVariables :: ElContextUsage m -> ElCheckM m ()
useVariables use = ElCheckM . const . const $ pure (use, ())

useTypeVariable :: ElId -> m -> ElCheckM m ()
useTypeVariable x m = useVariables (UEmpty :+* (x, m))

useTermVariable :: ElId -> m -> ElCheckM m ()
useTermVariable x m = useVariables (UEmpty :+? (x, m))

removeTypeVariable :: (ElModeSpec m) => (ElId, m) -> ElCheckM m a -> ElCheckM m a
removeTypeVariable v am = ElCheckM $ \env -> mapExceptT (fmap helper) . runElCheckM am env
  where
    helper (Right (use, a)) = (, a) <$> removeTypeV v use
    helper (Left err)       = Left err

removeTypeVariables :: (ElModeSpec m) => Seq (ElId, m) -> ElCheckM m a -> ElCheckM m a
removeTypeVariables vs am = ElCheckM $ \env -> mapExceptT (fmap helper) . runElCheckM am env
  where
    helper (Right (use, a)) = (, a) <$> removeTypeVs vs use
    helper (Left err)       = Left err

removeTermVariable :: (ElModeSpec m) => (ElId, m) -> ElCheckM m a -> ElCheckM m a
removeTermVariable v am = ElCheckM $ \env -> mapExceptT (fmap helper) . runElCheckM am env
  where
    helper (Right (use, a)) = (, a) <$> removeTermV v use
    helper (Left err)       = Left err

removeTermVariables :: (ElModeSpec m) => Seq (ElId, m) -> ElCheckM m a -> ElCheckM m a
removeTermVariables vs am = ElCheckM $ \env -> mapExceptT (fmap helper) . runElCheckM am env
  where
    helper (Right (use, a)) = (, a) <$> removeTermVs vs use
    helper (Left err)       = Left err

removeVariables :: (ElModeSpec m) => ElIContextHat m -> ElCheckM m a -> ElCheckM m a
removeVariables vs am = ElCheckM $ \env -> mapExceptT (fmap helper) . runElCheckM am env
  where
    helper (Right (use, a)) = (, a) <$> removeVs vs use
    helper (Left err)       = Left err

removeVariablesInType :: (ElModeSpec m) => ElIContextHat m -> ElCheckM m a -> ElCheckM m a
removeVariablesInType vs am = ElCheckM $ \env -> mapExceptT (fmap helper) . runElCheckM am env
  where
    helper (Right (use, a)) = (, a) <$> removeVsInType vs use
    helper (Left err)       = Left err

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
  deriving Show

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
  deriving Show

data ElTypingError m
  = TEImplementationError String
  | TEInvalidKind (ElIKind m)
  | TENotInScope ElId (Either (ElIContext m) (ElTypingEnvironment m))
  | TEVariableClassMismatch ElId
  | TEInvalidEntryForTypeVariable ElId (ElIContextEntry m)
  | TEInvalidMultipleUsage ElId m
  | TEInvalidEmptyProd
  | TEInvalidKindForSusp (ElIKind m)
  | TEInvalidKindForForce (ElIKind m)
  | TEInvalidKindTypeForSusp
  | TEInvalidTypeForData (ElIType m)
  | TEInvalidTypeForTrue (ElIType m)
  | TEInvalidTypeForFalse (ElIType m)
  | TEInvalidTypeForInt (ElIType m)
  | TEInvalidTypeForTuple (ElIType m)
  | TEInvalidTypeForSusp (ElIType m)
  | TEInvalidArgTypeForForce (ElIType m)
  | TEInvalidTypeForStore (ElIType m)
  | TEInvalidTypeForLoad (ElIType m)
  | TEInvalidTypeForLam (ElIType m)
  | TEInvalidFunctionTypeForApp (ElIType m)
  | TEInvalidConditionTypeForIte (ElIType m)
  | TEInvalidTypeArgForLam (ElType m)
  | TEInvalidTermArgForTypeLam (ElTerm m)
  | TEInvalidKindAnnForLam (ElKind m)
  | TEInvalidTypeAnnForTypeLam (ElType m)
  | TEInvalidPatternForTypeLam (ElPattern m)
  | TEInvalidBuiltIn ElBuiltIn
  | TEInvalidTypeForArrayTag (ElIType m)
  | TECheckOnlyTermInInference (ElTerm m)
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
  | TEConstructorArgNumberMismatch Int [ElTerm m]
  | TEConstructorPatternArgNumberMismatch Int [ElPattern m]
  | TETupleArgNumberMismatch Int [ElTerm m]
  | TETuplePatternArgNumberMismatch Int [ElPattern m]
  | TETooLongSubstitution Int (ElSubst m)
  | TESubstitutionEntryClassMismatch ElId (ElSubstEntry m)
  | TEDuplicatedContextEntryInWeakening (ElIContext m)
  | TESubstitutionError String
  deriving Show
