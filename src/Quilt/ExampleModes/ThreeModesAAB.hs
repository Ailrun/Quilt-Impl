{-# LANGUAGE DeriveAnyClass #-}
module Quilt.ExampleModes.ThreeModesAAB where

import Data.Hashable
import Data.Proxy     (Proxy (Proxy))
import GHC.Generics

import Quilt.ModeSpec

data ThreeModesAAB = MA | MA' | MB
  deriving (Eq, Show, Generic, Hashable)

threeModesAABProxy :: Proxy ThreeModesAAB
threeModesAABProxy = Proxy

instance QModeSpec ThreeModesAAB where
  showMode MA  = "A"
  showMode MA' = "A'"
  showMode MB  = "B"

  readModeEither "A"  = Right MA
  readModeEither "A'" = Right MA'
  readModeEither "B"  = Right MB
  readModeEither _    = Left "Should be either <A>, <A'>, or <B>"

  MA  >=!! MB = True
  MA' >=!! MB = True
  m   >=!! n  = m == n

  modeSig _ _ = True
