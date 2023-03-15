{-# LANGUAGE DerivingVia #-}
module Elevator.Syntax
  ( ElId
  , elId

  , ElType(..)

  , ElTerm(..)
  , ElBinOp(..)
  , elBinOpType
  ) where

import Data.Text   (Text)
import GHC.Natural (Natural)

newtype ElId = ElId Text
  deriving (Eq, Ord, Show) via Text

elId :: Text -> ElId
elId = ElId

-- TODO - Add top-level decls

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
  | TmBinOp ElBinOp (ElTerm m) (ElTerm m)
  | TmLift m m (ElTerm m)
  | TmUnlift m m (ElTerm m)
  | TmRet m m (ElTerm m)
  | TmLetRet m m ElId (ElTerm m) (ElTerm m)
  | TmLam ElId m (ElType m) (ElTerm m)
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
