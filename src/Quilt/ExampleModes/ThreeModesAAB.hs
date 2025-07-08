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

instance ElModeSpec ThreeModesAAB where
  showMode MA  = "A"
  showMode MA' = "A'"
  showMode MB  = "B"

  readModeEither "A"  = Right MA
  readModeEither "A'" = Right MA'
  readModeEither "B"  = Right MB
  readModeEither _    = Left "Should be either <A>, <A'>, or <B>"

  MB <=!! MA  = True
  MB <=!! MA' = True
  m  <=!! n   = m == n

  modeSig _ _ = True

  modeEff _  = Nothing
