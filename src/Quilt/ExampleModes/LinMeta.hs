{-# LANGUAGE DeriveAnyClass #-}
module Quilt.ExampleModes.LinMeta where

import Data.Hashable
import GHC.Generics

import Quilt.ModeSpec

data LinMeta = MCode | MGC | MGF
  deriving (Eq, Show, Generic, Hashable)

instance ElModeSpec LinMeta where
  showMode MCode = "C"
  showMode MGC   = "GC"
  showMode MGF   = "GF"

  readModeEither "C"  = Right MCode
  readModeEither "GC" = Right MGC
  readModeEither "GF" = Right MGF
  readModeEither _    = Left "Should be either <C>, <GC>, or <GF>"

  MGC <=!! MCode = True
  MGF <=!! MCode = True
  MGF <=!! MGC   = True
  m   <=!! n     = m == n

  modeSig MGF _ = False
  modeSig _   _ = True

  modeEff MGF = Just MGC
  modeEff _   = Nothing
