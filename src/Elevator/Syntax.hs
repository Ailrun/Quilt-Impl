{-# LANGUAGE DerivingVia #-}
module Elevator.Syntax
  ( ElId
  , elId
  , ElType(..)
  , ElTerm(..)
  ) where

import Data.Text   (Text)
import GHC.Natural (Natural)

newtype ElId = ElId Text
  deriving (Eq, Ord, Show) via Text

elId :: Text -> ElId
elId = ElId

-- TODO - add top-level decls

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
  | TmLam ElId m (ElType m) (ElTerm m)
  | TmApp (ElTerm m) (ElTerm m)
  -- TODO - add unary/binary operations, recursion
  deriving stock (Eq, Show)
