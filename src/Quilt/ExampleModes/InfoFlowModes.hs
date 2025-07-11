{-# LANGUAGE DeriveAnyClass #-}
module Quilt.ExampleModes.InfoFlowModes where

import Data.Hashable
import Data.Proxy     (Proxy (Proxy))
import GHC.Generics

import Quilt.ModeSpec

data InfoFlowModes = MCode | MProg | MSecure
  deriving (Eq, Show, Generic, Hashable)

infoFlowModesProxy :: Proxy InfoFlowModes
infoFlowModesProxy = Proxy

instance QModeSpec InfoFlowModes where
  showMode MCode   = "C"
  showMode MProg   = "P"
  showMode MSecure = "S"

  readModeEither "C" = Right MCode
  readModeEither "P" = Right MProg
  readModeEither "S" = Right MSecure
  readModeEither _   = Left "Should be either <C>, <P>, or <S>"

  MCode >=!! MProg   = True
  MCode >=!! MSecure = True
  MProg >=!! MSecure = True
  m     >=!! n       = m == n

  modeSig _ _ = True
