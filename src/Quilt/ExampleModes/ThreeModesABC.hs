{-# LANGUAGE DeriveAnyClass #-}
module Quilt.ExampleModes.ThreeModesABC where

import Data.Hashable
import Data.Proxy     (Proxy (Proxy))
import GHC.Generics

import Quilt.ModeSpec

data ThreeModesABC = MA | MB | MC
  deriving (Eq, Show, Generic, Hashable)

threeModesABCProxy :: Proxy ThreeModesABC
threeModesABCProxy = Proxy

instance ElModeSpec ThreeModesABC where
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
