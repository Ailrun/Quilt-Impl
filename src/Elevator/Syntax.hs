{-# LANGUAGE DerivingVia #-}
module Elevator.Syntax
  ( ElId
  , ElType(..)
  , ElTerm(..)
  ) where

import GHC.Natural (Natural)

newtype ElId = ElId String
  deriving (Eq, Ord, Show) via String

data ElType m
  = TyNat
  | TyUp m m (ElType m)
  | TyDown m m (ElType m)
  | TyArr (ElType m) (ElType m)
  deriving stock (Eq, Show)

data ElTerm m
  = TmVar ElId
  | TmNat Natural
  | TmLift m m (ElTerm m)
  | TmUnlift m m (ElTerm m)
  | TmRet m m (ElTerm m)
  | TmLetRet m m ElId (ElTerm m) (ElTerm m)
  | TmLam m ElId (ElType m) (ElTerm m)
  | TmApp (ElTerm m) (ElTerm m)
  deriving stock (Eq, Show)
