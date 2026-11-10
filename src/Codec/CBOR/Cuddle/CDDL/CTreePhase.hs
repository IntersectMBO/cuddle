{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}

module Codec.CBOR.Cuddle.CDDL.CTreePhase (
  CTreePhase,
  XTerm (..),
  XCddl (..),
  XRule (..),
  XXTopLevel,
) where

import Codec.CBOR.Cuddle.CDDL (XCddl, XRule, XTerm, XXTopLevel, XXType2)
import Codec.CBOR.Cuddle.CDDL.Custom.Core (RuleTerm)
import Codec.CBOR.Cuddle.CDDL.Custom.Generator (TermGenerator)
import Codec.CBOR.Cuddle.CDDL.Custom.Validator (TermValidator)
import Data.Default.Class (Default)
import Data.Hashable (Hashable)
import GHC.Generics (Generic)

type data CTreePhase

data instance XTerm CTreePhase = CTreeXTerm
  deriving (Generic, Show, Eq, Ord)
  deriving anyclass (Hashable, Default)

data instance XXTopLevel CTreePhase
  deriving (Generic, Show, Eq, Ord)

data instance XCddl CTreePhase = CTreeXCddl
  deriving (Generic, Show, Eq, Ord)

data instance XRule CTreePhase
  = CTreeXRule (Maybe (TermGenerator RuleTerm)) (Maybe TermValidator)
  deriving (Generic)

data instance XXType2 CTreePhase
  deriving (Generic, Show, Eq, Ord)
  deriving anyclass (Hashable)
