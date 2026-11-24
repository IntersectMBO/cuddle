{-# LANGUAGE TypeData #-}

module Codec.CBOR.Cuddle.CDDL.Phase (
  CTreePhase,
  MonoReferenced,
  MonoSimplePhase,
  HuddleStage,
  showSimple,
) where

import Codec.CBOR.Cuddle.IndexMappable (IndexMappable (..))

type data CTreePhase

type data MonoReferenced

type data MonoSimplePhase

type data HuddleStage

-- | Project any phase that maps to 'MonoSimplePhase' down to a `Show`able
-- representation. Used for debug output by `Gen`, `Validator`, etc.
showSimple ::
  forall a phase.
  ( IndexMappable a phase MonoSimplePhase
  , Show (a MonoSimplePhase)
  ) =>
  a phase -> String
showSimple = show . mapIndex @_ @_ @MonoSimplePhase
