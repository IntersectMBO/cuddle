module Codec.CBOR.Cuddle.CDDL.Options (
  CuddleOptions (..),
  AllowedLengthEncodings (..),
) where

import Data.Default.Class (Default (..))

data AllowedLengthEncodings
  = DefiniteAndIndefinite
  | DefiniteOnly
  | IndefiniteOnly
  deriving (Eq, Ord, Enum, Bounded, Show)

data CuddleOptions = CuddleOptions
  { optAllowedLengthEncodings :: AllowedLengthEncodings
  , optMapFailOnDuplicateKey :: Bool
  }

instance Default CuddleOptions where
  def =
    CuddleOptions
      { optAllowedLengthEncodings = DefiniteAndIndefinite
      , optMapFailOnDuplicateKey = False
      }
