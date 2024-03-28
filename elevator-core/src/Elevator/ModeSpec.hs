{-# LANGUAGE DerivingVia #-}
module Elevator.ModeSpec
  ( ElMdSt(..)

  , ElModeSpec(..)
  , (<!!)
  , (>=!!)
  , (>!!)
  ) where

import Data.Hashable (Hashable)

data ElMdSt
  = MdStWk
  | MdStCo
  deriving (Eq, Show)

class (Show m, Hashable m) => ElModeSpec m where
  showMode :: m -> String
  readModeEither :: String -> Either String m
  (<=!!) :: m -> m -> Bool
  modeSt :: m -> ElMdSt -> Bool

(<!!) :: (ElModeSpec m) => m -> m -> Bool
x <!! y = not (y <=!! x) && x <=!! y
{-# INLINE (<!!) #-}

(>=!!) :: (ElModeSpec m) => m -> m -> Bool
x >=!! y = y <=!! x
{-# INLINE (>=!!) #-}

(>!!) :: (ElModeSpec m) => m -> m -> Bool
x >!! y = y <!! x
{-# INLINE (>!!) #-}
