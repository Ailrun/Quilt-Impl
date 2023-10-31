{-# LANGUAGE DerivingVia #-}
module ElevatorExt.Linear.Syntax where

import           Elevator.Syntax
import           GHC.Natural     (Natural)

data ElxType
  = TyxNat
  | TyxBool
  | TyxBox ElxType
  | TyxArr ElxType ElxType
  deriving stock (Eq, Show)

newtype ElxProgram = ElxProgram [ElxTop]
  deriving stock (Eq, Show)

data ElxTop
  = ElxDef ElId ElxType ElxTerm
  deriving stock (Eq, Show)

data ElxTerm
  = TmxVar ElId
  | TmxTrue
  | TmxFalse
  | TmxIte ElxTerm ElxTerm ElxTerm
  | TmxNat Natural
  | TmxSucc ElxTerm
  | TmxNatCase ElxTerm ElxTerm ElId ElxTerm
  | TmxBinOp ElBinOp ElxTerm ElxTerm
  | TmxBox ElxTerm
  | TmxLetBox ElId ElxTerm ElxTerm
  | TmxLam ElId (Maybe ElxType) ElxTerm
  | TmxApp ElxTerm ElxTerm
  | TmxAnn ElxTerm ElxType
  deriving stock (Eq, Show)

