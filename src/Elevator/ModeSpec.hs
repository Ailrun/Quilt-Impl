{-# LANGUAGE DerivingVia #-}
module Elevator.ModeSpec
  ( ElModeKey
  , elKeyToMode

  , ElSt(..)
  , elStWithWk
  , elStWithCo

  , ElOp(..)

  , ElModeSpec(..)
  , mskey
  , (<!!)
  , (>=!!)
  , (>!!)
  ) where

import Data.Set (Set)

newtype ElModeKey m = ElModeKey (String, m)

instance Eq (ElModeKey m) where
  (ElModeKey (s0, _)) == (ElModeKey (s1, _)) = s0 == s1

instance Ord (ElModeKey m) where
  compare (ElModeKey (s0, _)) (ElModeKey (s1, _)) = compare s0 s1

instance Show (ElModeKey m) where
  show (ElModeKey (s, _)) = "<ElMode " <> s <> ">"

elKeyToMode :: ElModeKey m -> m
elKeyToMode (ElModeKey (_, m)) = m

data ElSt
  = StAll
  | StWk
  | StCo
  | StNone
  deriving (Eq, Show)

elStWithWk :: ElSt -> Bool
elStWithWk StAll = True
elStWithWk StWk  = True
elStWithWk _     = False

elStWithCo :: ElSt -> Bool
elStWithCo StAll = True
elStWithCo StCo  = True
elStWithCo _     = False

data ElOp
  = OpNat
  | OpArr
  | OpUp
  | OpDown
  deriving (Eq, Show)

class (Eq m) => ElModeSpec m where
  msinit :: m
  msshow :: m -> String
  (<=!!) :: m -> m -> Bool
  msst :: m -> ElSt
  msop :: m -> Set ElOp

mskey :: (ElModeSpec m) => m -> ElModeKey m
mskey m = ElModeKey (msshow m, m)

(<!!) :: (ElModeSpec m) => m -> m -> Bool
x <!! y = x /= y && x <=!! y
{-# INLINE (<!!) #-}

(>=!!) :: (ElModeSpec m) => m -> m -> Bool
x >=!! y = y <=!! x
{-# INLINE (>=!!) #-}

(>!!) :: (ElModeSpec m) => m -> m -> Bool
x >!! y = y <!! x
{-# INLINE (>!!) #-}
