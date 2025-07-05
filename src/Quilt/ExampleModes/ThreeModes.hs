{-# LANGUAGE DeriveAnyClass #-}
module Quilt.ExampleModes.ThreeModes where

import Data.Hashable
import Data.Proxy     (Proxy (Proxy))
import GHC.Generics

import Quilt.ModeSpec

data ThreeModes = MA | MB | MC
  deriving (Eq, Show, Generic, Hashable)

threeModesProxy :: Proxy ThreeModes
threeModesProxy = Proxy

instance ElModeSpec ThreeModes where
  showMode MA = "A"
  showMode MB = "B"
  showMode MC = "C"

  readModeEither "A" = Right MA
  readModeEither "B" = Right MB
  readModeEither "C" = Right MC
  readModeEither _   = Left "Should be either <A>, <B>, or <C>"

  MC <=!! MA = True
  MB <=!! MA = True
  MC <=!! MB = True
  MB <=!! MC = True
  m  <=!! n  = m == n

  modeSig MA _ = True
  modeSig MB _ = False
  modeSig MC _ = False

  modeEff MB = Just MA
  modeEff MC = Just MA
  modeEff _  = Nothing
