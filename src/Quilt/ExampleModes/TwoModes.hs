{-# LANGUAGE DeriveAnyClass #-}
module Quilt.ExampleModes.TwoModes where

import Data.Hashable
import Data.Proxy     (Proxy (Proxy))
import GHC.Generics

import Quilt.ModeSpec

data TwoModes = MA | MB
  deriving (Eq, Show, Generic, Hashable)

twoModesProxy :: Proxy TwoModes
twoModesProxy = Proxy

instance ElModeSpec TwoModes where
  showMode MA = "A"
  showMode MB = "B"

  readModeEither "A" = Right MA
  readModeEither "B" = Right MB
  readModeEither _   = Left "Should be either <A> or <B>"

  MB <=!! MA = True
  m  <=!! n  = m == n

  modeSig _ _ = True

  modeEff _ = Nothing
