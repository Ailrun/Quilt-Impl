{-# LANGUAGE DerivingVia #-}
module Quilt.ModeSpec
  ( QMdSt(..)

  , QModeSpec(..)
  , (<!!)
  , (>!!)
  ) where

import Data.Hashable (Hashable)

data QMdSt
  = MdStWk
  | MdStCo
  deriving (Eq, Show)

class (Show m, Hashable m) => QModeSpec m where
  -- Helper for error message
  showMode :: m -> String
  -- Helper for parser
  readModeEither :: String -> Either String m

  -- Accessibility relation
  -- You can define either of them.
  (<=!!) :: m -> m -> Bool
  (<=!!) = flip (>=!!)
  {-# INLINE (<=!!) #-}

  (>=!!) :: m -> m -> Bool
  (>=!!) = flip (<=!!)
  {-# INLINE (>=!!) #-}

  modeSig :: m -> QMdSt -> Bool

  -- Mutability in the input mode
  -- is possible only if there is
  -- an unrestricted output mode.
  modeEff :: m -> Maybe m
  modeEff _ = Nothing

  {-# MINIMAL showMode,readModeEither,((<=!!) | (>=!!)),modeSig #-}

(<!!) :: (QModeSpec m) => m -> m -> Bool
x <!! y = not (y <=!! x) && x <=!! y
{-# INLINE (<!!) #-}

(>!!) :: (QModeSpec m) => m -> m -> Bool
x >!! y = y <!! x
{-# INLINE (>!!) #-}
