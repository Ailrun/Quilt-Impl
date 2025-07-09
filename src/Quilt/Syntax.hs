{-# LANGUAGE DerivingVia       #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies      #-}
module Quilt.Syntax
  ( QId
  , qId
  , decorateQId
  , isDecoratedQId
  , dropDecorationFromQId

  , QModuleId(..)

  , QModule(..)
  , QIModule(..)

  , QCommand(..)

  , QTop(..)
  , QITop(..)

  , QKind(..)
  , QIKind(..)
  , QType(..)
  , QIType(..)

  , QContextEntry(..)
  , QIContextEntry(..)
  , QContext
  , QIContext
  , QIDomain
  , QContextHat
  , QIContextHat

  , putHat
  , putIHat
  , isCEKind
  , icontext2idomain
  , icontextHat2idomain

  , QBuiltIn(..)
  , QTerm(..)
  , QITerm(..)

  , QBranch
  , QIBranch
  , QPattern(..)
  , QIPattern(..)

  , QBinOp(..)
  , qBinOpType

  , QSubst
  , QISubst
  , QSubstEntry(..)
  , QISubstEntry(..)

  , QAmbi(..)
  , QAmbiCore(..)
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

import Data.Bifunctor   (Bifunctor (bimap))
import Data.Hashable    (Hashable)
import Data.Sequence    (Seq)
import Data.Sequence    qualified as Seq
import Data.String      (IsString (fromString))
import Data.Text        (Text)
import Data.Text        qualified as Text
import Data.Tuple.Extra (fst3)
import Prettyprinter    (Pretty)

import Quilt.ModeSpec   (QModeSpec (modeEff))

newtype QId = QId Text
  deriving (Hashable, Eq, Ord, Show, Semigroup, IsString, Pretty) via Text

qId :: Text -> QId
qId = QId

decorateQId :: QId -> String -> QId
decorateQId (QId x) s = QId $ x <> "~" <> fromString s

isDecoratedQId :: QId -> Bool
isDecoratedQId (QId x) = "~" `Text.isInfixOf` x

dropDecorationFromQId :: QId -> QId
dropDecorationFromQId (QId x) = QId . Text.dropEnd 1 $ Text.dropWhileEnd (/= '~') x

newtype QModuleId = QModuleId [QId]
  deriving (Eq, Ord, Show) via [QId]

data QModule m = QModule [QModuleId] [QTop m]
  deriving stock (Eq, Ord, Show)

data QIModule m = QIModule [QModuleId] [QITop m]
  deriving stock (Eq, Ord, Show)

data QCommand m
  = ComTop (QTop m)
  | ComTerm (QTerm m)
  deriving stock (Eq, Ord, Show)

data QTop m
  = TopTermDef QId (QType m) (QTerm m)
  | TopTypeDef [(QId, Maybe (QKind m))] QId m [(QId, [QType m])]
  deriving stock (Eq, Ord, Show)

data QITop m
  = ITopTermDef QId m (QIType m) (QITerm m)
  | ITopTypeDef [(QId, QIKind m)] QId m [(QId, [QIType m])]
  deriving stock (Eq, Ord, Show)

data QKind m
  = KiType m
  -- | "m" is the mode of the entire kind
  | KiUp m (QContext m) (QKind m)
  deriving stock (Eq, Ord, Show)

data QIKind m
  = IKiType m
  -- | "m" is the mode of the entire kind
  | IKiUp m (QIContext m) (QIKind m)
  deriving stock (Eq, Ord, Show)

data QType m
  = TyVar QId
  | TySusp (QContextHat m) (QType m)
  | TyForce (QType m) (QSubst m)
  | TyData [QType m] QId
  | TyBool m
  | TyInt m
  | TyProd [QType m]
  | TyArray (QType m)
  -- | "m" is the mode of the entire type
  | TyUp m (QContext m) (QType m)
  -- | "m" is the mode of the entire type
  | TyDown m (QType m)
  | TyArr (QType m) (QType m)
  | TyForall QId (QKind m) (QType m)
  | TyAnn (QType m) (QKind m)
  deriving stock (Eq, Ord, Show)

data QIType m
  = ITyVar QId
  -- | "m" is the mode of the entire type
  | ITySusp m (QIContextHat m) (QIType m)
  -- | "m" is the mode of the inner type
  | ITyForce m (QIType m) (QISubst m)
  | ITyData [QIType m] QId
  | ITyBool m
  | ITyInt m
  | ITyProd [QIType m]
  | ITyArray m (QIType m)
  -- | The first "m" is the mode of the entire type
  -- and the second "m" is the mode of the inner type
  | ITyUp m m (QIContext m) (QIType m)
  -- | The first "m" is the mode of the entire type
  -- and the second "m" is the mode of the inner type
  | ITyDown m m (QIType m)
  | ITyArr (QIType m) (QIType m)
  | ITyForall QId (QIKind m) (QIType m)
  deriving stock (Eq, Ord, Show)

data QContextEntry m
  = CEKind (QKind m)
  | CEType (QType m)
  deriving stock (Eq, Ord, Show)

data QIContextEntry m
  = ICEKind (QIKind m)
  | ICEType (QIType m)
  deriving stock (Eq, Ord, Show)

type QContext m = Seq (QId, QContextEntry m)
type QIContext m = Seq (QId, m, QIContextEntry m)
type QIDomain m = Seq (QId, Bool)

type QContextHat m = Seq QId
type QIContextHat m = Seq (QId, m, Bool)

putHat :: QContext m -> QContextHat m
putHat = fmap fst

putIHat :: QIContext m -> QIContextHat m
putIHat = fmap (\(x, m, ce) -> (x, m, isCEKind ce))

isCEKind :: QIContextEntry m -> Bool
isCEKind (ICEKind _) = True
isCEKind (ICEType _) = False

icontext2idomain :: QIContext m -> QIDomain m
icontext2idomain = fmap (\(x, _, ce) -> (x, isCEKind ce))

icontextHat2idomain :: QIContextHat m -> QIDomain m
icontextHat2idomain = fmap (\(x, _, isKi) -> (x, isKi))

data QBuiltIn
  = BIWithAlloc
  | BIWrite
  | BIRead
  deriving stock (Eq, Ord, Show)

data QTerm m
  = TmVar QId
  | TmArrayTag Integer
  | TmBuiltIn QBuiltIn
  | TmData QId [QTerm m]
  | TmTrue
  | TmFalse
  -- | If-then-else
  | TmIte (QTerm m) (QTerm m) (QTerm m)
  | TmInt Integer
  | TmBinOp QBinOp (QTerm m) (QTerm m)
  | TmTuple [QTerm m]
  | TmMatch (QTerm m) (Maybe (QType m)) [QBranch m]
  | TmSusp (QContextHat m) (QTerm m)
  | TmForce (QTerm m) (QSubst m)
  | TmStore (QTerm m)
  | TmAmbiLam (QPattern m) (Maybe (QContextEntry m)) (QTerm m)
  | TmAmbiApp (QTerm m) (QAmbi m)
  | TmAnn (QTerm m) (QType m)
  deriving stock (Eq, Ord, Show)

data QITerm m
  = ITmVar QId
  | ITmArrayTag Integer
  | ITmBuiltIn QBuiltIn
  | ITmData QId Int [QITerm m]
  | ITmTrue
  | ITmFalse
  -- | If-then-else
  | ITmIte (QITerm m) (QITerm m) (QITerm m)
  | ITmInt Integer
  | ITmBinOp QBinOp (QITerm m) (QITerm m)
  | ITmTuple [QITerm m]
  -- | "m" is the mode of the scrutinee
  | ITmMatch m (QITerm m) (QIType m) [QIBranch m]
  -- | "m" is the mode of the entire exp
  | ITmSusp m (QIContextHat m) (QITerm m)
  -- | "m" is the mode of the inner exp
  | ITmForce m (QITerm m) (QISubst m)
  -- | "m" is the mode of the inner exp
  | ITmStore m (QITerm m)
  | ITmLam (QIPattern m) (QIType m) (QITerm m)
  | ITmTLam QId (QIKind m) (QITerm m)
  | ITmApp (QITerm m) (QITerm m)
  | ITmTApp (QITerm m) (QIType m)
  deriving stock (Eq, Ord, Show)

type QBranch m = (QPattern m, QTerm m)
type QIBranch m = (QIPattern m, QITerm m)

data QPattern m
  = PatWild
  | PatVar QId
  | PatTrue
  | PatFalse
  | PatInt Integer
  | PatTuple [QPattern m]
  | PatLoad (QPattern m)
  | PatData QId [QPattern m]
  deriving stock (Eq, Ord, Show)

data QIPattern m
  = IPatWild
  | IPatVar QId
  | IPatTrue
  | IPatFalse
  | IPatInt Integer
  | IPatTuple [QIPattern m]
  | IPatLoad (QIPattern m)
  | IPatData QId Int [QIPattern m]
  deriving stock (Eq, Ord, Show)

newtype QSubstEntry m
  = SEAmbi (QAmbi m)
  deriving stock (Eq, Ord, Show)

data QISubstEntry m
  = ISEType (QIType m)
  | ISETerm (QITerm m)
  deriving stock (Eq, Ord, Show)

type QSubst m = Seq (QSubstEntry m)
type QISubst m = Seq (QISubstEntry m)

data QBinOp
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

qBinOpType :: m -> QBinOp -> (QIType m, QIType m, QIType m)
qBinOpType k OpAdd = (ITyInt k, ITyInt k, ITyInt k)
qBinOpType k OpSub = (ITyInt k, ITyInt k, ITyInt k)
qBinOpType k OpMul = (ITyInt k, ITyInt k, ITyInt k)
qBinOpType k OpDiv = (ITyInt k, ITyInt k, ITyInt k)
qBinOpType k OpMod = (ITyInt k, ITyInt k, ITyInt k)
qBinOpType k OpEq  = (ITyInt k, ITyInt k, ITyBool k)
qBinOpType k OpNe  = (ITyInt k, ITyInt k, ITyBool k)
qBinOpType k OpLe  = (ITyInt k, ITyInt k, ITyBool k)
qBinOpType k OpLt  = (ITyInt k, ITyInt k, ITyBool k)
qBinOpType k OpGe  = (ITyInt k, ITyInt k, ITyBool k)
qBinOpType k OpGt  = (ITyInt k, ITyInt k, ITyBool k)

data QAmbi m
  = AmCore (QAmbiCore m)
  | AmTerm (QTerm m)
  | AmType (QType m)
  deriving stock (Eq, Ord, Show)

data QAmbiCore m
  = AmVar QId
  | AmSusp (QContextHat m) (QAmbiCore m)
  | AmForce (QAmbiCore m) (QSubst m)
  deriving stock (Eq, Ord, Show)

ambiCore2term :: QAmbiCore m -> QTerm m
ambiCore2term (AmVar x)       = TmVar x
ambiCore2term (AmSusp ctxh a) = TmSusp ctxh (ambiCore2term a)
ambiCore2term (AmForce a sub) = TmForce (ambiCore2term a) sub

ambiCore2type :: QAmbiCore m -> QType m
ambiCore2type (AmVar x)       = TyVar x
ambiCore2type (AmSusp ctxh a) = TySusp ctxh (ambiCore2type a)
ambiCore2type (AmForce a sub) = TyForce (ambiCore2type a) sub

class FromInternal a where
  type Internal a
  fromInternal :: Internal a -> a

instance FromInternal (QModule m) where
  type Internal (QModule m) = QIModule m
  fromInternal (QIModule imports tops) = QModule imports (fromInternal <$> tops)

instance FromInternal (QTop m) where
  type Internal (QTop m) = QITop m
  fromInternal (ITopTermDef x _ ty t) = TopTermDef x (fromInternal ty) (fromInternal t)
  fromInternal (ITopTypeDef ys x k cons) = TopTypeDef (fmap (Just . fromInternal) <$> ys) x k (fmap (fmap (fmap fromInternal)) cons)

icontext2context :: QIContext m -> QContext m
icontext2context = fmap (\(x, _, entry) -> (x, fromInternal entry))

icontextHat2contextHat :: QIContextHat m -> QContextHat m
icontextHat2contextHat = fmap fst3

instance FromInternal (QKind m) where
  type Internal (QKind m) = QIKind m
  fromInternal (IKiType k) = KiType k
  fromInternal (IKiUp k ictx iki) = KiUp k (icontext2context ictx) (fromInternal iki)

instance FromInternal (QSubstEntry m) where
  type Internal (QSubstEntry m) = QISubstEntry m
  fromInternal (ISEType ity) = SEAmbi (AmType (fromInternal ity))
  fromInternal (ISETerm itm) = SEAmbi (AmTerm (fromInternal itm))

isubst2subst :: QISubst m -> QSubst m
isubst2subst = fmap fromInternal

instance FromInternal (QType m) where
  type Internal (QType m) = QIType m
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

instance FromInternal (QContextEntry m) where
  type Internal (QContextEntry m) = QIContextEntry m
  fromInternal (ICEKind iki) = CEKind (fromInternal iki)
  fromInternal (ICEType ity) = CEType (fromInternal ity)

instance FromInternal (QTerm m) where
  type Internal (QTerm m) = QITerm m
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

instance FromInternal (QPattern m) where
  type Internal (QPattern m) = QIPattern m
  fromInternal IPatWild            = PatWild
  fromInternal (IPatVar x)         = PatVar x
  fromInternal IPatTrue            = PatTrue
  fromInternal IPatFalse           = PatFalse
  fromInternal (IPatInt n)         = PatInt n
  fromInternal (IPatTuple pats)    = PatTuple (fromInternal <$> pats)
  fromInternal (IPatLoad pat)      = PatLoad (fromInternal pat)
  fromInternal (IPatData c _ pats) = PatData c (fromInternal <$> pats)

toBuiltIn :: QId -> Maybe QBuiltIn
toBuiltIn "withAlloc" = Just BIWithAlloc
toBuiltIn "write"     = Just BIWrite
toBuiltIn "read"      = Just BIRead
toBuiltIn _           = Nothing

fromBuiltIn :: QBuiltIn -> QId
fromBuiltIn BIWithAlloc = "withAlloc"
fromBuiltIn BIWrite     = "write"
fromBuiltIn BIRead      = "read"

typeOfBuiltIn :: (QModeSpec m) => m -> QBuiltIn -> Maybe (QIType m)
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
