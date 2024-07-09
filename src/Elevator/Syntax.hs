{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}
module Elevator.Syntax
  ( ElId
  , elId
  , decorateElId
  , isDecoratedElId
  , dropDecorationFromElId

  , ElModuleId(..)

  , ElModule(..)
  , ElIModule(..)

  , ElCommand(..)

  , ElTop(..)
  , ElITop(..)

  , ElKind(..)
  , ElIKind(..)
  , ElType(..)
  , ElIType(..)

  , ElContextEntry(..)
  , ElIContextEntry(..)
  , ElContext
  , ElIContext
  , ElIDomain
  , ElContextHat
  , ElIContextHat

  , putHat
  , putIHat
  , isCEKind
  , icontext2idomain
  , icontextHat2idomain

  , ElBuiltIn(..)
  , ElTerm(..)
  , ElITerm(..)

  , ElBranch
  , ElIBranch
  , ElPattern(..)
  , ElIPattern(..)

  , ElBinOp(..)
  , elBinOpType

  , ElSubst
  , ElISubst
  , ElSubstEntry(..)
  , ElISubstEntry(..)

  , ElAmbi(..)
  , ElAmbiCore(..)
  , ambiCore2term
  , ambiCore2type

  , FromInternal(..)
  , icontext2context
  , icontextHat2contextHat
  , isubst2subst

  , toBuiltIn
  , fromBuiltIn
  , typeOfBuiltIn
  ) where

import Data.Bifunctor    (Bifunctor (bimap))
import Data.Hashable     (Hashable)
import Data.Sequence     (Seq)
import Data.Sequence     qualified as Seq
import Data.String       (IsString (fromString))
import Data.Text         (Text)
import Data.Text         qualified as Text
import Data.Tuple.Extra  (fst3)
import Elevator.ModeSpec (ElModeSpec (modeEff))
import Prettyprinter     (Pretty)

newtype ElId = ElId Text
  deriving (Hashable, Eq, Ord, Show, Semigroup, IsString, Pretty) via Text

elId :: Text -> ElId
elId = ElId

decorateElId :: ElId -> String -> ElId
decorateElId (ElId x) s = ElId $ x <> "~" <> fromString s

isDecoratedElId :: ElId -> Bool
isDecoratedElId (ElId x) = "~" `Text.isInfixOf` x

dropDecorationFromElId :: ElId -> ElId
dropDecorationFromElId (ElId x) = ElId . Text.dropEnd 1 $ Text.dropWhileEnd (/= '~') x

newtype ElModuleId = ElModuleId [ElId]
  deriving (Eq, Ord, Show) via [ElId]

data ElModule m = ElModule [ElModuleId] [ElTop m]
  deriving stock (Eq, Ord, Show)

data ElIModule m = ElIModule [ElModuleId] [ElITop m]
  deriving stock (Eq, Ord, Show)

data ElCommand m
  = ComTop (ElTop m)
  | ComTerm (ElTerm m)
  deriving stock (Eq, Ord, Show)

data ElTop m
  = TopTermDef ElId (ElType m) (ElTerm m)
  | TopTypeDef [(ElId, Maybe (ElKind m))] ElId m [(ElId, [ElType m])]
  deriving stock (Eq, Ord, Show)

data ElITop m
  = ITopTermDef ElId m (ElIType m) (ElITerm m)
  | ITopTypeDef [(ElId, ElIKind m)] ElId m [(ElId, [ElIType m])]
  deriving stock (Eq, Ord, Show)

data ElKind m
  = KiType m
  -- | "m" is the mode of the entire kind
  | KiUp m (ElContext m) (ElKind m)
  deriving stock (Eq, Ord, Show)

data ElIKind m
  = IKiType m
  -- | "m" is the mode of the entire kind
  | IKiUp m (ElIContext m) (ElIKind m)
  deriving stock (Eq, Ord, Show)

data ElType m
  = TyVar ElId
  | TySusp (ElContextHat m) (ElType m)
  | TyForce (ElType m) (ElSubst m)
  | TyData [ElType m] ElId
  | TyBool m
  | TyInt m
  | TyProd [ElType m]
  | TyArray (ElType m)
  -- | "m" is the mode of the entire type
  | TyUp m (ElContext m) (ElType m)
  -- | "m" is the mode of the entire type
  | TyDown m (ElType m)
  | TyArr (ElType m) (ElType m)
  | TyForall ElId (ElKind m) (ElType m)
  | TyAnn (ElType m) (ElKind m)
  deriving stock (Eq, Ord, Show)

data ElIType m
  = ITyVar ElId
  -- | "m" is the mode of the entire type
  | ITySusp m (ElIContextHat m) (ElIType m)
  -- | "m" is the mode of the inner type
  | ITyForce m (ElIType m) (ElISubst m)
  | ITyData [ElIType m] ElId
  | ITyBool m
  | ITyInt m
  | ITyProd [ElIType m]
  | ITyArray m (ElIType m)
  -- | The first "m" is the mode of the entire type
  -- and the second "m" is the mode of the inner type
  | ITyUp m m (ElIContext m) (ElIType m)
  -- | The first "m" is the mode of the entire type
  -- and the second "m" is the mode of the inner type
  | ITyDown m m (ElIType m)
  | ITyArr (ElIType m) (ElIType m)
  | ITyForall ElId (ElIKind m) (ElIType m)
  deriving stock (Eq, Ord, Show)

data ElContextEntry m
  = CEKind (ElKind m)
  | CEType (ElType m)
  deriving stock (Eq, Ord, Show)

data ElIContextEntry m
  = ICEKind (ElIKind m)
  | ICEType (ElIType m)
  deriving stock (Eq, Ord, Show)

type ElContext m = Seq (ElId, ElContextEntry m)
type ElIContext m = Seq (ElId, m, ElIContextEntry m)
type ElIDomain m = Seq (ElId, Bool)

type ElContextHat m = Seq ElId
type ElIContextHat m = Seq (ElId, m, Bool)

putHat :: ElContext m -> ElContextHat m
putHat = fmap fst

putIHat :: ElIContext m -> ElIContextHat m
putIHat = fmap (\(x, m, ce) -> (x, m, isCEKind ce))

isCEKind :: ElIContextEntry m -> Bool
isCEKind (ICEKind _) = True
isCEKind (ICEType _) = False

icontext2idomain :: ElIContext m -> ElIDomain m
icontext2idomain = fmap (\(x, _, ce) -> (x, isCEKind ce))

icontextHat2idomain :: ElIContextHat m -> ElIDomain m
icontextHat2idomain = fmap (\(x, _, isKi) -> (x, isKi))

data ElBuiltIn
  = BIWithAlloc
  | BIWrite
  | BIRead
  deriving stock (Eq, Ord, Show)

data ElTerm m
  = TmVar ElId
  | TmArrayTag Integer
  | TmBuiltIn ElBuiltIn
  | TmData ElId [ElTerm m]
  | TmTrue
  | TmFalse
  -- | If-then-else
  | TmIte (ElTerm m) (ElTerm m) (ElTerm m)
  | TmInt Integer
  | TmBinOp ElBinOp (ElTerm m) (ElTerm m)
  | TmTuple [ElTerm m]
  | TmMatch (ElTerm m) (Maybe (ElType m)) [ElBranch m]
  | TmSusp (ElContextHat m) (ElTerm m)
  | TmForce (ElTerm m) (ElSubst m)
  | TmStore (ElTerm m)
  | TmAmbiLam (ElPattern m) (Maybe (ElContextEntry m)) (ElTerm m)
  | TmAmbiApp (ElTerm m) (ElAmbi m)
  | TmAnn (ElTerm m) (ElType m)
  deriving stock (Eq, Ord, Show)

data ElITerm m
  = ITmVar ElId
  | ITmArrayTag Integer
  | ITmBuiltIn ElBuiltIn
  | ITmData ElId Int [ElITerm m]
  | ITmTrue
  | ITmFalse
  -- | If-then-else
  | ITmIte (ElITerm m) (ElITerm m) (ElITerm m)
  | ITmInt Integer
  | ITmBinOp ElBinOp (ElITerm m) (ElITerm m)
  | ITmTuple [ElITerm m]
  -- | "m" is the mode of the scrutinee
  | ITmMatch m (ElITerm m) (ElIType m) [ElIBranch m]
  -- | "m" is the mode of the entire exp
  | ITmSusp m (ElIContextHat m) (ElITerm m)
  -- | "m" is the mode of the inner exp
  | ITmForce m (ElITerm m) (ElISubst m)
  -- | "m" is the mode of the inner exp
  | ITmStore m (ElITerm m)
  | ITmLam (ElIPattern m) (ElIType m) (ElITerm m)
  | ITmTLam ElId (ElIKind m) (ElITerm m)
  | ITmApp (ElITerm m) (ElITerm m)
  | ITmTApp (ElITerm m) (ElIType m)
  deriving stock (Eq, Ord, Show)

type ElBranch m = (ElPattern m, ElTerm m)
type ElIBranch m = (ElIPattern m, ElITerm m)

data ElPattern m
  = PatWild
  | PatVar ElId
  | PatTrue
  | PatFalse
  | PatInt Integer
  | PatTuple [ElPattern m]
  | PatLoad (ElPattern m)
  | PatData ElId [ElPattern m]
  deriving stock (Eq, Ord, Show)

data ElIPattern m
  = IPatWild
  | IPatVar ElId
  | IPatTrue
  | IPatFalse
  | IPatInt Integer
  | IPatTuple [ElIPattern m]
  | IPatLoad (ElIPattern m)
  | IPatData ElId Int [ElIPattern m]
  deriving stock (Eq, Ord, Show)

newtype ElSubstEntry m
  = SEAmbi (ElAmbi m)
  deriving stock (Eq, Ord, Show)

data ElISubstEntry m
  = ISEType (ElIType m)
  | ISETerm (ElITerm m)
  deriving stock (Eq, Ord, Show)

type ElSubst m = Seq (ElSubstEntry m)
type ElISubst m = Seq (ElISubstEntry m)

data ElBinOp
  = OpAdd
  | OpSub
  | OpMul
  | OpDiv
  | OpMod
  | OpEq
  | OpNe
  | OpLe
  | OpLt
  | OpGe
  | OpGt
  deriving stock (Eq, Ord, Show)

elBinOpType :: m -> ElBinOp -> (ElIType m, ElIType m, ElIType m)
elBinOpType k OpAdd = (ITyInt k, ITyInt k, ITyInt k)
elBinOpType k OpSub = (ITyInt k, ITyInt k, ITyInt k)
elBinOpType k OpMul = (ITyInt k, ITyInt k, ITyInt k)
elBinOpType k OpDiv = (ITyInt k, ITyInt k, ITyInt k)
elBinOpType k OpMod = (ITyInt k, ITyInt k, ITyInt k)
elBinOpType k OpEq  = (ITyInt k, ITyInt k, ITyBool k)
elBinOpType k OpNe  = (ITyInt k, ITyInt k, ITyBool k)
elBinOpType k OpLe  = (ITyInt k, ITyInt k, ITyBool k)
elBinOpType k OpLt  = (ITyInt k, ITyInt k, ITyBool k)
elBinOpType k OpGe  = (ITyInt k, ITyInt k, ITyBool k)
elBinOpType k OpGt  = (ITyInt k, ITyInt k, ITyBool k)

data ElAmbi m
  = AmCore (ElAmbiCore m)
  | AmTerm (ElTerm m)
  | AmType (ElType m)
  deriving stock (Eq, Ord, Show)

data ElAmbiCore m
  = AmVar ElId
  | AmSusp (ElContextHat m) (ElAmbiCore m)
  | AmForce (ElAmbiCore m) (ElSubst m)
  deriving stock (Eq, Ord, Show)

ambiCore2term :: ElAmbiCore m -> ElTerm m
ambiCore2term (AmVar x)       = TmVar x
ambiCore2term (AmSusp ctxh a) = TmSusp ctxh (ambiCore2term a)
ambiCore2term (AmForce a sub) = TmForce (ambiCore2term a) sub

ambiCore2type :: ElAmbiCore m -> ElType m
ambiCore2type (AmVar x)       = TyVar x
ambiCore2type (AmSusp ctxh a) = TySusp ctxh (ambiCore2type a)
ambiCore2type (AmForce a sub) = TyForce (ambiCore2type a) sub

class FromInternal a where
  type Internal a
  fromInternal :: Internal a -> a

instance FromInternal (ElModule m) where
  type Internal (ElModule m) = ElIModule m
  fromInternal (ElIModule imports tops) = ElModule imports (fromInternal <$> tops)

instance FromInternal (ElTop m) where
  type Internal (ElTop m) = ElITop m
  fromInternal (ITopTermDef x _ ty t) = TopTermDef x (fromInternal ty) (fromInternal t)
  fromInternal (ITopTypeDef ys x k cons) = TopTypeDef (fmap (Just . fromInternal) <$> ys) x k (fmap (fmap (fmap fromInternal)) cons)

icontext2context :: ElIContext m -> ElContext m
icontext2context = fmap (\(x, _, entry) -> (x, fromInternal entry))

icontextHat2contextHat :: ElIContextHat m -> ElContextHat m
icontextHat2contextHat = fmap fst3

instance FromInternal (ElKind m) where
  type Internal (ElKind m) = ElIKind m
  fromInternal (IKiType k) = KiType k
  fromInternal (IKiUp k ictx iki) = KiUp k (icontext2context ictx) (fromInternal iki)

instance FromInternal (ElSubstEntry m) where
  type Internal (ElSubstEntry m) = ElISubstEntry m
  fromInternal (ISEType ity) = SEAmbi (AmType (fromInternal ity))
  fromInternal (ISETerm itm) = SEAmbi (AmTerm (fromInternal itm))

isubst2subst :: ElISubst m -> ElSubst m
isubst2subst = fmap fromInternal

instance FromInternal (ElType m) where
  type Internal (ElType m) = ElIType m
  fromInternal (ITyVar x) = TyVar x
  fromInternal (ITySusp _ ihctx ity) = TySusp (icontextHat2contextHat ihctx) (fromInternal ity)
  fromInternal (ITyForce _ ity isub) = TyForce (fromInternal ity) (isubst2subst isub)
  fromInternal (ITyData itys x) = TyData (fromInternal <$> itys) x
  fromInternal (ITyBool k) = TyBool k
  fromInternal (ITyInt k) = TyInt k
  fromInternal (ITyProd itys) = TyProd (fromInternal <$> itys)
  fromInternal (ITyArray _ ity) = TyArray (fromInternal ity)
  fromInternal (ITyUp k _ ictx ity) = TyUp k (icontext2context ictx) (fromInternal ity)
  fromInternal (ITyDown k _ ity) = TyDown k (fromInternal ity)
  fromInternal (ITyArr ity0 ity1) = TyArr (fromInternal ity0) (fromInternal ity1)
  fromInternal (ITyForall x iki ity) = TyForall x (fromInternal iki) (fromInternal ity)

instance FromInternal (ElContextEntry m) where
  type Internal (ElContextEntry m) = ElIContextEntry m
  fromInternal (ICEKind iki) = CEKind (fromInternal iki)
  fromInternal (ICEType ity) = CEType (fromInternal ity)

instance FromInternal (ElTerm m) where
  type Internal (ElTerm m) = ElITerm m
  fromInternal (ITmVar x) = TmVar x
  fromInternal (ITmArrayTag n) = TmArrayTag n
  fromInternal (ITmBuiltIn x) = TmBuiltIn x
  fromInternal (ITmData x _ its) = TmData x (fromInternal <$> its)
  fromInternal ITmTrue = TmTrue
  fromInternal ITmFalse = TmFalse
  fromInternal (ITmIte it it0 it1) = TmIte (fromInternal it) (fromInternal it0) (fromInternal it1)
  fromInternal (ITmInt n) = TmInt n
  fromInternal (ITmBinOp bop it0 it1) = TmBinOp bop (fromInternal it0) (fromInternal it1)
  fromInternal (ITmTuple its) = TmTuple (fromInternal <$> its)
  fromInternal (ITmMatch _ it ity ibrs) = TmMatch (fromInternal it) (Just (fromInternal ity)) (bimap fromInternal fromInternal <$> ibrs)
  fromInternal (ITmSusp _ ihctx it) = TmSusp (icontextHat2contextHat ihctx) (fromInternal it)
  fromInternal (ITmForce _ it isub) = TmForce (fromInternal it) (isubst2subst isub)
  fromInternal (ITmStore _ it) = TmStore (fromInternal it)
  fromInternal (ITmLam pat ty it) = TmAmbiLam (fromInternal pat) (Just (CEType (fromInternal ty))) (fromInternal it)
  fromInternal (ITmTLam x ki it) = TmAmbiLam (PatVar x) (Just (CEKind (fromInternal ki))) (fromInternal it)
  fromInternal (ITmApp it0 it1) = TmAmbiApp (fromInternal it0) (AmTerm (fromInternal it1))
  fromInternal (ITmTApp it0 ity1) = TmAmbiApp (fromInternal it0) (AmType (fromInternal ity1))

instance FromInternal (ElPattern m) where
  type Internal (ElPattern m) = ElIPattern m
  fromInternal IPatWild            = PatWild
  fromInternal (IPatVar x)         = PatVar x
  fromInternal IPatTrue            = PatTrue
  fromInternal IPatFalse           = PatFalse
  fromInternal (IPatInt n)         = PatInt n
  fromInternal (IPatTuple pats)    = PatTuple (fromInternal <$> pats)
  fromInternal (IPatLoad pat)      = PatLoad (fromInternal pat)
  fromInternal (IPatData c _ pats) = PatData c (fromInternal <$> pats)

toBuiltIn :: ElId -> Maybe ElBuiltIn
toBuiltIn "withAlloc" = Just BIWithAlloc
toBuiltIn "write"     = Just BIWrite
toBuiltIn "read"      = Just BIRead
toBuiltIn _           = Nothing

fromBuiltIn :: ElBuiltIn -> ElId
fromBuiltIn BIWithAlloc = "withAlloc"
fromBuiltIn BIWrite     = "write"
fromBuiltIn BIRead      = "read"

typeOfBuiltIn :: (ElModeSpec m) => m -> ElBuiltIn -> Maybe (ElIType m)
typeOfBuiltIn k BIWithAlloc = do
  h <- modeEff k
  pure
    $ ITyForall "a" (IKiUp h Seq.empty (IKiType k))
    $ ITyForall "b" (IKiUp h Seq.empty (IKiType k))
    $ ITyArr (ITyInt k)
    $ ITyArr (bangA h)
    $ ITyArr (ITyArr (array h) (ITyProd [array h, bangB h]))
    $ bangB h
  where
    bang h ty = ITyDown k h (ITyUp h k Seq.empty ty)
    bangA h = bang h (ITyForce h (ITyVar "a") Seq.empty)
    bangB h = bang h (ITyForce h (ITyVar "b") Seq.empty)
    array h = ITyArray k (ITyForce h (ITyVar "a") Seq.empty)
typeOfBuiltIn k BIWrite = do
  h <- modeEff k
  pure
    $ ITyForall "a" (IKiUp h Seq.empty (IKiType k))
    $ ITyArr (ITyInt k)
    $ ITyArr (bangA h)
    $ ITyArr (array h)
    $ array h
  where
    bang h ty = ITyDown k h (ITyUp h k Seq.empty ty)
    bangA h = bang h (ITyForce h (ITyVar "a") Seq.empty)
    array h = ITyArray k (ITyForce h (ITyVar "a") Seq.empty)
typeOfBuiltIn k BIRead = do
  h <- modeEff k
  pure
    $ ITyForall "a" (IKiUp h Seq.empty (IKiType k))
    $ ITyArr (ITyInt k)
    $ ITyArr (array h)
    $ ITyProd [bangA h, array h]
  where
    bang h ty = ITyDown k h (ITyUp h k Seq.empty ty)
    bangA h = bang h (ITyForce h (ITyVar "a") Seq.empty)
    array h = ITyArray k (ITyForce h (ITyVar "a") Seq.empty)
