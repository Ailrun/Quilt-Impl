{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeFamilies #-}
module Elevator.Syntax
  ( ElId
  , elId

  , ElKind(..)
  , ElIKind(..)
  , ElType(..)
  , ElIType(..)
  , ElContextEntry
  , ElIContextEntry
  , ElContext
  , ElIContext
  , ElContextHat
  , ElIContextHat

  , ElProgram(..)
  , ElIProgram(..)

  , ElTop(..)
  , ElITop(..)

  , ElTerm(..)
  , ElITerm(..)

  , ElBinOp(..)
  , elBinOpType

  , ElSubst
  , ElISubst

  , FromInternal(..)
  ) where

import Data.Hashable (Hashable)
import Data.String   (IsString)
import Data.Text     (Text)
import Prettyprinter (Pretty)

newtype ElId = ElId Text
  deriving (Hashable, Eq, Ord, Show, IsString, Pretty) via Text

elId :: Text -> ElId
elId = ElId

newtype ElProgram m = ElProgram [ElTop m]
  deriving stock (Eq, Show)

newtype ElIProgram m = ElIProgram [ElITop m]
  deriving stock (Eq, Show)

data ElTop m
  = ElTmDef ElId m (ElType m) (ElTerm m)
  | ElTyDef [ElId] ElId m [(ElId, [ElType m])]
  deriving stock (Eq, Show)

data ElITop m
  = ElITmDef ElId m (ElIType m) (ElITerm m)
  | ElITyDef [ElId] ElId m [(ElId, [ElIType m])]
  deriving stock (Eq, Show)

data ElKind m
  = KiType m
  | KiUp m (ElContext m) (ElKind m)
  deriving stock (Eq, Show)

data ElIKind m
  = IKiType m
  | IKiUp m (ElIContext m) (ElIKind m)
  deriving stock (Eq, Show)

data ElType m
  = TyVar ElId
  | TyThunk (ElContextHat m) (ElType m)
  | TyForce (ElType m) (ElSubst m)
  | TyData [ElType m] ElId
  | TyBool m
  | TyInt m
  | TyUp m (ElContext m) (ElType m)
  | TyDown m (ElType m)
  | TyArr (ElType m) (ElType m)
  | TyForall ElId (ElKind m) (ElType m)
  deriving stock (Eq, Show)

data ElIType m
  = ITyVar ElId
  | ITyThunk (ElIContextHat m) (ElIType m)
  | ITyForce (ElIType m) (ElISubst m)
  | ITyData [ElIType m] ElId
  | ITyBool m
  | ITyInt m
  | ITyUp m (ElIContext m) (ElIType m)
  | ITyDown m (ElIType m)
  | ITyArr (ElIType m) (ElIType m)
  | ITyForall ElId (ElIKind m) (ElIType m)
  deriving stock (Eq, Show)

data ElContextEntry m
  = EntryOfKi (ElKind m)
  | EntryOfTy (ElType m)
  deriving stock (Eq, Show)

data ElIContextEntry m
  = IEntryOfKi (ElIKind m)
  | IEntryOfTy (ElIType m)
  deriving stock (Eq, Show)

type ElContext m = [(ElId, ElContextEntry m)]
type ElIContext m = [(ElId, ElIContextEntry m)]

type ElContextHat m = [ElId]
type ElIContextHat m = ElContextHat m

data ElTerm m
  = TmVar ElId
  | TmData ElId [ElTerm m]
  | TmTrue
  | TmFalse
  | TmIte (ElTerm m) (ElTerm m) (ElTerm m)
  | TmInt Integer
  | TmBinOp ElBinOp (ElTerm m) (ElTerm m)
  | TmMatch (ElTerm m) (ElBranch m)
  | TmThunk (ElContextHat m) (ElTerm m)
  | TmForce (ElTerm m) (ElSubst m)
  | TmStore (ElTerm m)
  | TmLoad ElId (ElTerm m) (ElTerm m)
  | TmLam ElId (Maybe (Either (ElType m) (ElKind m))) (ElTerm m)
  | TmApp (ElTerm m) (ElAmbi m)
  | TmAnn (ElTerm m) (ElType m)
  deriving stock (Eq, Show)

data ElAmbi m
  = AmVar ElId
  | AmData ElId [ElAmbi m]
  | AmThunk (ElContextHat m) (ElAmbi m)
  | AmForce (ElAmbi m) (ElSubst m)
  | AmTerm (ElTerm m)
  | AmType (ElType m)
  deriving stock (Eq, Show)

data ElITerm m
  = ITmVar ElId
  | ITmData ElId [ElITerm m]
  | ITmTrue
  | ITmFalse
  | ITmIte (ElITerm m) (ElITerm m) (ElITerm m)
  | ITmInt Integer
  | ITmBinOp ElBinOp (ElITerm m) (ElITerm m)
  | ITmMatch (ElITerm m) (ElIBranch m)
  | ITmThunk m (ElIContextHat m) (ElITerm m)
  | ITmForce m (ElITerm m) (ElISubst m)
  | ITmStore m (ElITerm m)
  | ITmLoad m m ElId (ElITerm m) (ElITerm m)
  | ITmLam ElId (ElType m) (ElITerm m)
  | ITmTLam ElId (ElKind m) (ElITerm m)
  | ITmApp (ElITerm m) (ElITerm m)
  | ITmTApp (ElITerm m) (ElIType m)
  deriving stock (Eq, Show)

type ElBranch m = [(ElPattern m, ElTerm m)]
type ElIBranch m = [(ElPattern m, ElITerm m)]

data ElPattern m
  = PatWild
  | PatVar ElId
  | PatTrue
  | PatFalse
  | PatInt Integer
  | PatConst ElId [ElPattern m]
  deriving stock (Eq, Show)

type ElSubst m = [ElTerm m]
type ElISubst m = [ElITerm m]

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

class FromInternal a where
  type Internal a
  fromInternal :: Internal a -> a

instance FromInternal (ElProgram m) where
  type Internal (ElProgram m) = ElIProgram m
  fromInternal (ElIProgram tops) = ElProgram (fromInternal <$> tops)

instance FromInternal (ElTop m) where
  type Internal (ElTop m) = ElITop m
  fromInternal (ElITmDef x k ty t) = ElTmDef x k (fromInternal ty) (fromInternal t)
  fromInternal (ElITyDef ys x k cons) = ElTyDef ys x k (fmap (fmap (fmap fromInternal)) cons)

instance FromInternal (ElKind m) where
  type Internal (ElKind m) = ElIKind m
  fromInternal (IKiType k) = KiType k
  fromInternal (IKiUp l ictx iki) = KiUp l (fmap fromInternal <$> ictx) (fromInternal iki)

instance FromInternal (ElType m) where
  type Internal (ElType m) = ElIType m
  fromInternal (ITyVar x) = TyVar x
  fromInternal (ITyThunk ihctx ity) = TyThunk ihctx (fromInternal ity)
  fromInternal (ITyForce ity isub) = TyForce (fromInternal ity) (fromInternal <$> isub)
  fromInternal (ITyData itys x) = TyData (fromInternal <$> itys) x
  fromInternal (ITyBool k) = TyBool k
  fromInternal (ITyInt k) = TyInt k
  fromInternal (ITyUp l ictx ity) = TyUp l (fmap fromInternal <$> ictx) (fromInternal ity)
  fromInternal (ITyDown m ity) = TyDown m (fromInternal ity)
  fromInternal (ITyArr ity0 ity1) = TyArr (fromInternal ity0) (fromInternal ity1)
  fromInternal (ITyForall x iki ity) = TyForall x (fromInternal iki) (fromInternal ity)

instance FromInternal (ElContextEntry m) where
  type Internal (ElContextEntry m) = ElIContextEntry m
  fromInternal (IEntryOfKi iki) = EntryOfKi (fromInternal iki)
  fromInternal (IEntryOfTy ity) = EntryOfTy (fromInternal ity)

instance FromInternal (ElTerm m) where
  type Internal (ElTerm m) = ElITerm m
  fromInternal (ITmVar x) = TmVar x
  fromInternal (ITmData x its) = TmData x (fromInternal <$> its)
  fromInternal ITmTrue = TmTrue
  fromInternal ITmFalse = TmFalse
  fromInternal (ITmIte it it0 it1) = TmIte (fromInternal it) (fromInternal it0) (fromInternal it1)
  fromInternal (ITmInt n) = TmInt n
  fromInternal (ITmBinOp bop it0 it1) = TmBinOp bop (fromInternal it0) (fromInternal it1)
  fromInternal (ITmMatch it ibrs) = TmMatch (fromInternal it) (fmap fromInternal <$> ibrs)
  fromInternal (ITmThunk _ ihctx it) = TmThunk ihctx (fromInternal it)
  fromInternal (ITmForce _ it isub) = TmForce (fromInternal it) (fromInternal <$> isub)
  fromInternal (ITmStore _ it) = TmStore (fromInternal it)
  fromInternal (ITmLoad _ _ x it it0) = TmLoad x (fromInternal it) (fromInternal it0)
  fromInternal (ITmLam x ty it) = TmLam x (Just (Left ty)) (fromInternal it)
  fromInternal (ITmTLam x ki it) = TmLam x (Just (Right ki)) (fromInternal it)
  fromInternal (ITmApp it0 it1) = TmApp (fromInternal it0) (AmTerm (fromInternal it1))
  fromInternal (ITmTApp it0 ity1) = TmApp (fromInternal it0) (AmType (fromInternal ity1))
