{-# LANGUAGE DerivingVia  #-}
{-# LANGUAGE TypeFamilies #-}
module Elevator.Syntax
  ( ElId
  , elId

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
  , ElContextHat
  , ElIContextHat

  , putHat
  , putIHat

  , ElTerm(..)
  , ElITerm(..)

  , ElBranch
  , ElIBranch
  , ElPattern(..)

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
  ) where

import Data.Hashable (Hashable)
import Data.Sequence (Seq)
import Data.String   (IsString)
import Data.Text     (Text)
import Prettyprinter (Pretty)

newtype ElId = ElId Text
  deriving (Hashable, Eq, Ord, Show, IsString, Pretty) via Text

elId :: Text -> ElId
elId = ElId

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
  = ITopTermDef ElId (ElIType m) (ElITerm m)
  | ITopTypeDef [(ElId, ElIKind m)] ElId m [(ElId, [ElIType m])]
  deriving stock (Eq, Ord, Show)

data ElKind m
  = KiType m
  -- | "m" is the mode of the scrutinee
  | KiUp m (ElContext m) (ElKind m)
  deriving stock (Eq, Ord, Show)

data ElIKind m
  = IKiType m
  -- | "m" is the destination mode
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
  -- | "m" is the destination mode
  | TyUp m (ElContext m) (ElType m)
  -- | "m" is the destination mode
  | TyDown m (ElType m)
  | TyArr (ElType m) (ElType m)
  | TyForall ElId (ElKind m) (ElType m)
  | TyAnn (ElType m) (ElKind m)
  deriving stock (Eq, Ord, Show)

data ElIType m
  = ITyVar ElId
  -- | "m" is the destination mode
  | ITySusp m (ElIContextHat m) (ElIType m)
  -- | "m" is the destination mode
  | ITyForce m (ElIType m) (ElISubst m)
  | ITyData [ElIType m] ElId
  | ITyBool m
  | ITyInt m
  | ITyProd [ElIType m]
  -- | "m" is the destination mode
  | ITyUp m (ElIContext m) (ElIType m)
  -- | "m" is the destination mode
  | ITyDown m (ElIType m)
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

type ElContextHat m = Seq ElId
type ElIContextHat m = Seq (ElId, m)

putHat :: ElContext m -> ElContextHat m
putHat = fmap fst

putIHat :: ElIContext m -> ElIContextHat m
putIHat = fmap (\(x, m, _) -> (x, m))

data ElTerm m
  = TmVar ElId
  | TmData ElId [ElTerm m]
  | TmTrue
  | TmFalse
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
  | ITmData ElId [ElITerm m]
  | ITmTrue
  | ITmFalse
  | ITmIte (ElITerm m) (ElITerm m) (ElITerm m)
  | ITmInt Integer
  | ITmBinOp ElBinOp (ElITerm m) (ElITerm m)
  | ITmTuple [ElITerm m]
  -- | "m" is the mode of the scrutinee
  | ITmMatch m (ElITerm m) (ElIType m) [ElIBranch m]
  -- | "m" is the destination mode
  | ITmSusp m (ElIContextHat m) (ElITerm m)
  -- | "m" is the destination mode
  | ITmForce m (ElITerm m) (ElISubst m)
  -- | "m" is the destination mode
  | ITmStore m (ElITerm m)
  | ITmLam (ElPattern m) (ElIType m) (ElITerm m)
  | ITmTLam ElId (ElIKind m) (ElITerm m)
  | ITmApp (ElITerm m) (ElITerm m)
  | ITmTApp (ElITerm m) (ElIType m)
  deriving stock (Eq, Ord, Show)

type ElBranch m = (ElPattern m, ElTerm m)
type ElIBranch m = (ElPattern m, ElITerm m)

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

newtype ElSubstEntry m
  = SEAmbi (ElAmbi m)
  deriving stock (Eq, Ord, Show)

data ElISubstEntry m
  = ISEType (ElIType m)
  | ISETerm (ElITerm m)
  deriving stock (Eq, Ord, Show)

type ElSubst m = Seq (ElSubstEntry m)
type ElISubst m = Seq (ElId, ElISubstEntry m)

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

elBinOpType :: m -> ElBinOp -> (ElType m, ElType m, ElType m)
elBinOpType m OpAdd = (TyInt m, TyInt m, TyInt m)
elBinOpType m OpSub = (TyInt m, TyInt m, TyInt m)
elBinOpType m OpMul = (TyInt m, TyInt m, TyInt m)
elBinOpType m OpDiv = (TyInt m, TyInt m, TyInt m)
elBinOpType m OpMod = (TyInt m, TyInt m, TyInt m)
elBinOpType m OpEq  = (TyInt m, TyInt m, TyBool m)
elBinOpType m OpNe  = (TyInt m, TyInt m, TyBool m)
elBinOpType m OpLe  = (TyInt m, TyInt m, TyBool m)
elBinOpType m OpLt  = (TyInt m, TyInt m, TyBool m)
elBinOpType m OpGe  = (TyInt m, TyInt m, TyBool m)
elBinOpType m OpGt  = (TyInt m, TyInt m, TyBool m)

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
  fromInternal (ITopTermDef x ty t) = TopTermDef x (fromInternal ty) (fromInternal t)
  fromInternal (ITopTypeDef ys x k cons) = TopTypeDef (fmap (Just . fromInternal) <$> ys) x k (fmap (fmap (fmap fromInternal)) cons)

icontext2context :: ElIContext m -> ElContext m
icontext2context = fmap (\(x, _, entry) -> (x, fromInternal entry))

instance FromInternal (ElKind m) where
  type Internal (ElKind m) = ElIKind m
  fromInternal (IKiType k) = KiType k
  fromInternal (IKiUp k ictx iki) = KiUp k (icontext2context ictx) (fromInternal iki)

instance FromInternal (ElSubstEntry m) where
  type Internal (ElSubstEntry m) = ElISubstEntry m
  fromInternal (ISEType ity) = SEAmbi (AmType (fromInternal ity))
  fromInternal (ISETerm itm) = SEAmbi (AmTerm (fromInternal itm))

isubst2subst :: ElISubst m -> ElSubst m
isubst2subst = fmap (fromInternal . snd)

instance FromInternal (ElType m) where
  type Internal (ElType m) = ElIType m
  fromInternal (ITyVar x) = TyVar x
  fromInternal (ITySusp _ ihctx ity) = TySusp (fst <$> ihctx) (fromInternal ity)
  fromInternal (ITyForce _ ity isub) = TyForce (fromInternal ity) (isubst2subst isub)
  fromInternal (ITyData itys x) = TyData (fromInternal <$> itys) x
  fromInternal (ITyBool k) = TyBool k
  fromInternal (ITyInt k) = TyInt k
  fromInternal (ITyProd itys) = TyProd (fromInternal <$> itys)
  fromInternal (ITyUp k ictx ity) = TyUp k (icontext2context ictx) (fromInternal ity)
  fromInternal (ITyDown k ity) = TyDown k (fromInternal ity)
  fromInternal (ITyArr ity0 ity1) = TyArr (fromInternal ity0) (fromInternal ity1)
  fromInternal (ITyForall x iki ity) = TyForall x (fromInternal iki) (fromInternal ity)

instance FromInternal (ElContextEntry m) where
  type Internal (ElContextEntry m) = ElIContextEntry m
  fromInternal (ICEKind iki) = CEKind (fromInternal iki)
  fromInternal (ICEType ity) = CEType (fromInternal ity)

instance FromInternal (ElTerm m) where
  type Internal (ElTerm m) = ElITerm m
  fromInternal (ITmVar x) = TmVar x
  fromInternal (ITmData x its) = TmData x (fromInternal <$> its)
  fromInternal ITmTrue = TmTrue
  fromInternal ITmFalse = TmFalse
  fromInternal (ITmIte it it0 it1) = TmIte (fromInternal it) (fromInternal it0) (fromInternal it1)
  fromInternal (ITmInt n) = TmInt n
  fromInternal (ITmBinOp bop it0 it1) = TmBinOp bop (fromInternal it0) (fromInternal it1)
  fromInternal (ITmTuple its) = TmTuple (fromInternal <$> its)
  fromInternal (ITmMatch _ it ity ibrs) = TmMatch (fromInternal it) (Just (fromInternal ity)) (fmap fromInternal <$> ibrs)
  fromInternal (ITmSusp _ ihctx it) = TmSusp (fst <$> ihctx) (fromInternal it)
  fromInternal (ITmForce _ it isub) = TmForce (fromInternal it) (isubst2subst isub)
  fromInternal (ITmStore _ it) = TmStore (fromInternal it)
  fromInternal (ITmLam x ty it) = TmAmbiLam x (Just (CEType (fromInternal ty))) (fromInternal it)
  fromInternal (ITmTLam x ki it) = TmAmbiLam (PatVar x) (Just (CEKind (fromInternal ki))) (fromInternal it)
  fromInternal (ITmApp it0 it1) = TmAmbiApp (fromInternal it0) (AmTerm (fromInternal it1))
  fromInternal (ITmTApp it0 ity1) = TmAmbiApp (fromInternal it0) (AmType (fromInternal ity1))
