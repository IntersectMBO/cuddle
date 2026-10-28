{-# LANGUAGE LambdaCase #-}

module Codec.CBOR.Cuddle.CBOR.Canonical (
  CanonicalTerm (..),
  NInt,
  toCanonical,
  toNInt,
  fromNInt,
  uintMax,
  nintMin,
  canonicalEq,
) where

import Codec.CBOR.Term (Term (..))
import Data.Bifunctor (bimap)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSL
import Data.Function (on)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text.Lazy qualified as TL
import Data.Word (Word64, Word8)
import GHC.Generics (Generic)
import Numeric.Half (Half, toHalf)
import Test.QuickCheck (Arbitrary (..))

-- | A negative integer in the range @[-2^64, -1]@: exactly the values
-- representable by CBOR major type 1 (RFC 8949 §3.1). The range is wider
-- than 'Int64' on the negative side, so it can't be stored as a plain
-- signed integer.
newtype NInt = NInt Word64
  deriving (Eq, Ord, Bounded)

instance Show NInt where
  showsPrec p x =
    showParen (p > 10) $ showString "toNInt " . showsPrec 11 (fromNInt x)

instance Arbitrary NInt where
  arbitrary = NInt <$> arbitrary

toNInt :: Integer -> Maybe NInt
toNInt x
  | x >= nintMin && x < 0 = Just . NInt . fromInteger $ x - nintMin
  | otherwise = Nothing

fromNInt :: NInt -> Integer
fromNInt (NInt n) = nintMin + toInteger n

-- | Convert a `cborg` @Term@ to a @CanonicalTerm@.
--
-- A CBOR map with duplicate keys is well-formed but invalid (RFC 8949 §5.6).
-- Canonicalizing such a map is not currently supported and raises an 'error'.
-- This only arises in the niche case of a duplicate-keyed map nested in a
-- position the validator does not otherwise reject (e.g. a map used as a map
-- key). If you hit this, please open an issue.
toCanonical :: Term -> CanonicalTerm
toCanonical = \case
  TInt i -> integerToCanonical $ toInteger i
  TInteger n -> integerToCanonical n
  TBytes bs -> CTBytes bs
  TBytesI bs -> CTBytes $ BSL.toStrict bs
  TString s -> CTString s
  TStringI s -> CTString $ TL.toStrict s
  TList ts -> mkList ts
  TListI ts -> mkList ts
  TMap kvs -> mkMap kvs
  TMapI kvs -> mkMap kvs
  TTagged 2 inner
    | Just bs <- tagBytes inner -> integerToCanonical $ bytesToUnsigned bs
  TTagged 3 inner
    | Just bs <- tagBytes inner -> integerToCanonical $ -1 - bytesToUnsigned bs
  TTagged w t -> CTTagged w $ toCanonical t
  TBool False -> CTSimple 20
  TBool True -> CTSimple 21
  TNull -> CTSimple 22
  TSimple w -> CTSimple w
  THalf f -> CTHalf $ toHalf f
  TFloat f -> CTFloat f
  TDouble d -> CTDouble d
  where
    mkMap kvs =
      let pairs = bimap toCanonical toCanonical <$> kvs
          m = Map.fromList pairs
       in if Map.size m == length pairs
            then CTMap m
            else
              error
                "toCanonical: encountered a map with duplicate keys, which is \
                \not currently supported. Please open an issue at \
                \https://github.com/input-output-hk/cuddle/issues"
    mkList ts = CTList $ toCanonical <$> ts
    tagBytes (TBytes bs) = Just bs
    tagBytes (TBytesI bs) = Just $ BSL.toStrict bs
    tagBytes _ = Nothing

integerToCanonical :: Integer -> CanonicalTerm
integerToCanonical n
  | n >= 0, n <= uintMax = CTInt $ fromInteger n
  | n < 0, n >= nintMin = CTNInt . NInt . fromInteger $ n - nintMin
  | n > uintMax = CTTagged 2 . CTBytes $ unsignedToBytes n
  | otherwise = CTTagged 3 . CTBytes . unsignedToBytes $ -1 - n

bytesToUnsigned :: ByteString -> Integer
bytesToUnsigned = BS.foldl' (\acc b -> acc * 256 + toInteger b) 0

unsignedToBytes :: Integer -> ByteString
unsignedToBytes = BS.pack . reverse . go
  where
    go 0 = []
    go n = let (d, r) = divMod n 256 in fromInteger r : go d

-- | A canonical representation of CBOR data items. Two 'CanonicalTerm's
-- compare equal exactly when the underlying CBOR items are equivalent
-- under the /extended generic data model/ of RFC 8949 §3.4.3 — the same
-- notion of equality that determines whether two map keys are duplicates
-- (RFC 8949 §3.1, §5.6).
--
-- Differences from 'Codec.CBOR.Term.Term':
--
-- * Major types 0 and 1 are split into 'CTInt' and 'CTNInt' (matching
--   the on-wire structure) instead of overlapping in 'TInt'/'TInteger'.
-- * Bignums (tags 2 and 3) whose value fits in @[-2^64, 2^64 - 1]@
--   are normalized into 'CTInt' / 'CTNInt' (RFC 8949 §3.4.3).
-- * Definite- and indefinite-length variants are merged: there is no
--   separate constructor for what 'Codec.CBOR.Term.TBytesI',
--   'Codec.CBOR.Term.TStringI', 'Codec.CBOR.Term.TListI',
--   'Codec.CBOR.Term.TMapI' represent.
-- * Maps use 'Data.Map.Strict.Map' rather than a list of pairs, so
--   key order is irrelevant.
-- * 'TBool' and 'TNull' are folded into 'CTSimple' (values 20, 21, 22
--   per RFC 8949 §3.3).
-- * 'THalf', 'TFloat', 'TDouble' remain distinct constructors: the
--   generic data model treats different float widths as distinct items
--   (RFC 8949 §2).
data CanonicalTerm
  = CTInt !Word64
  | CTNInt !NInt
  | CTBytes !ByteString
  | CTString !Text
  | CTList ![CanonicalTerm]
  | CTMap !(Map CanonicalTerm CanonicalTerm)
  | CTTagged !Word64 !CanonicalTerm
  | CTSimple !Word8
  | CTHalf !Half
  | CTFloat !Float
  | CTDouble !Double
  deriving (Generic, Eq, Ord, Show)

-- Bounds

uintMax :: Integer
uintMax = 2 ^ (64 :: Int) - 1

nintMin :: Integer
nintMin = -(2 ^ (64 :: Int))

canonicalEq :: Term -> Term -> Bool
canonicalEq = (==) `on` toCanonical
