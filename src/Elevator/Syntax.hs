{-# LANGUAGE DerivingVia #-}
module Elevator.Syntax
  ( ElId
  , elId

  , ElProgram(..)

  , ElTop(..)

  , ElType(..)

  , ElTerm(..)
  , ElBinOp(..)
  , elBinOpType
  , elBinOpTypeWithMode
  ) where

import Data.Hashable (Hashable)
import Data.Text     (Text)
import GHC.Natural   (Natural)
import Prettyprinter (Pretty)

newtype ElId = ElId Text
  deriving (Hashable, Eq, Ord, Show, Pretty) via Text

elId :: Text -> ElId
elId = ElId

newtype ElProgram m = ElProgram [ElTop m]
  deriving stock (Eq, Show)

data ElTop m
  = ElDef ElId m (ElType m) (ElTerm m)
  deriving stock (Eq, Show)

data ElType m
  = TyNat
  | TyBool
  | TyUp m m (ElType m)
  | TyDown m m (ElType m)
  | TyArr (ElType m) (ElType m)
  deriving stock (Eq, Show)

data ElTerm m
  = TmVar ElId
  | TmTrue
  | TmFalse
  | TmIte (ElTerm m) (ElTerm m) (ElTerm m)
  | TmNat Natural
  | TmSucc (ElTerm m)
  | TmNatCase (ElTerm m) (ElTerm m) ElId (ElTerm m)
  | TmBinOp ElBinOp (ElTerm m) (ElTerm m)
  | TmLift m (ElTerm m)
  | TmUnlift m (ElTerm m)
  | TmRet m (ElTerm m)
  | TmLetRet m ElId (ElTerm m) (ElTerm m)
  | TmLam ElId (Maybe (ElType m)) (ElTerm m)
  | TmApp (ElTerm m) (ElTerm m)
  deriving stock (Eq, Show)

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

elBinOpType :: ElBinOp -> (ElType m, ElType m, ElType m)
elBinOpType OpAdd = (TyNat, TyNat, TyNat)
elBinOpType OpSub = (TyNat, TyNat, TyNat)
elBinOpType OpMul = (TyNat, TyNat, TyNat)
elBinOpType OpDiv = (TyNat, TyNat, TyNat)
elBinOpType OpMod = (TyNat, TyNat, TyNat)
elBinOpType OpEq  = (TyNat, TyNat, TyBool)
elBinOpType OpNe  = (TyNat, TyNat, TyBool)
elBinOpType OpLe  = (TyNat, TyNat, TyBool)
elBinOpType OpLt  = (TyNat, TyNat, TyBool)
elBinOpType OpGe  = (TyNat, TyNat, TyBool)
elBinOpType OpGt  = (TyNat, TyNat, TyBool)

elBinOpTypeWithMode :: m -> ElBinOp -> (ElType m, ElType m, ElType m)
elBinOpTypeWithMode _ = elBinOpType
