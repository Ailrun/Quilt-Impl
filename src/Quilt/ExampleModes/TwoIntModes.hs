{-# LANGUAGE DeriveAnyClass #-}
module Quilt.ExampleModes.TwoIntModes where

import Data.Hashable
import Data.Proxy     (Proxy (Proxy))
import GHC.Generics

import Quilt.ModeSpec

data TwoIntModes = MA | MB
  deriving (Eq, Show, Generic, Hashable)

twoIntModesProxy :: Proxy TwoIntModes
twoIntModesProxy = Proxy

instance QModeSpec TwoIntModes where
  showMode MA = "A"
  showMode MB = "B"

  readModeEither "A" = Right MA
  readModeEither "B" = Right MB
  readModeEither _   = Left "Should be either <A> or <B>"

  MA >=!! MB = True
  m  >=!! n  = m == n

  modeSig _ _ = True
