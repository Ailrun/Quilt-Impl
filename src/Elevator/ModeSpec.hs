{-# LANGUAGE DerivingVia #-}
module Elevator.ModeSpec
  ( ElModeKey
  , elKeyToMode

  , ElMdSt(..)
  , elMdStWithWk
  , elMdStWithCo

  , ElMdOp(..)

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
  show (ElModeKey (s, _)) = "<" <> s <> ">"

elKeyToMode :: ElModeKey m -> m
elKeyToMode (ElModeKey (_, m)) = m

data ElMdSt
  = MdStAll
  | MdStWk
  | MdStCo
  | MdStNone
  deriving (Eq, Show)

elMdStWithWk :: ElMdSt -> Bool
elMdStWithWk MdStAll = True
elMdStWithWk MdStWk  = True
elMdStWithWk _       = False

elMdStWithCo :: ElMdSt -> Bool
elMdStWithCo MdStAll = True
elMdStWithCo MdStCo  = True
elMdStWithCo _       = False

data ElMdOp
  = MdOpNat
  | MdOpBool
  | MdOpArr
  | MdOpUp
  | MdOpDown
  deriving (Eq, Ord, Show)

class (Eq m, Show m) => ElModeSpec m where
  msshow :: m -> String
  msreadMay :: String -> Maybe m
  (<=!!) :: m -> m -> Bool
  msst :: m -> ElMdSt
  msop :: m -> Set ElMdOp

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
