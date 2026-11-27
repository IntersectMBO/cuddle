{-# LANGUAGE DefaultSignatures #-}

module Codec.CBOR.Cuddle.IndexMappable (
  IndexMappable (..),
) where

import Data.Coerce (Coercible, coerce)

class IndexMappable f i j where
  mapIndex :: f i -> f j
  default mapIndex :: Coercible (f i) (f j) => f i -> f j
  mapIndex = coerce
