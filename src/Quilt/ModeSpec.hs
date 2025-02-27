{-# LANGUAGE DerivingVia #-}
module Quilt.ModeSpec
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
  -- Helper for error message
  showMode :: m -> String
  -- Helper for parser
  readModeEither :: String -> Either String m
  -- Main specification
  (<=!!) :: m -> m -> Bool
  modeSig :: m -> ElMdSt -> Bool
  modeEff :: m -> Maybe m

(<!!) :: (ElModeSpec m) => m -> m -> Bool
x <!! y = not (y <=!! x) && x <=!! y
{-# INLINE (<!!) #-}

(>=!!) :: (ElModeSpec m) => m -> m -> Bool
x >=!! y = y <=!! x
{-# INLINE (>=!!) #-}

(>!!) :: (ElModeSpec m) => m -> m -> Bool
x >!! y = y <!! x
{-# INLINE (>!!) #-}
