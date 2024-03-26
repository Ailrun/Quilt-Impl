{-# LANGUAGE DerivingVia #-}
module Elevator.ModeSpec
  ( ElMdSt(..)
  , ElMdOp(..)

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

data ElMdOp
  = MdOpInt
  | MdOpBool
  | MdOpArr
  | MdOpUp
  | MdOpDown
  deriving (Eq, Ord, Show)

class (Show m, Hashable m) => ElModeSpec m where
  showMode :: m -> String
  readModeEither :: String -> Either String m
  (<=!!) :: m -> m -> Bool
  modeSt :: m -> ElMdSt -> Bool
  modeOp :: m -> ElMdOp -> Bool

(<!!) :: (ElModeSpec m) => m -> m -> Bool
x <!! y = x /= y && x <=!! y
{-# INLINE (<!!) #-}

(>=!!) :: (ElModeSpec m) => m -> m -> Bool
x >=!! y = y <=!! x
{-# INLINE (>=!!) #-}

(>!!) :: (ElModeSpec m) => m -> m -> Bool
x >!! y = y <!! x
{-# INLINE (>!!) #-}
