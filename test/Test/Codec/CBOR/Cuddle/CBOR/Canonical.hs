{-# LANGUAGE OverloadedStrings #-}

module Test.Codec.CBOR.Cuddle.CBOR.Canonical (spec) where

import Codec.CBOR.Cuddle.CBOR.Canonical (
  CanonicalTerm (..),
  fromNInt,
  nintMin,
  toCanonical,
  toNInt,
  uintMax,
 )
import Codec.CBOR.Term (Term (..))
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSL
import Data.Set qualified as Set
import Data.Text.Lazy qualified as TL
import Data.Word (Word64)
import Test.Hspec
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck

spec :: Spec
spec = do
  describe "NInt" $ do
    it "toNInt accepts exactly [-2^64, -1]" $ do
      toNInt 0 `shouldBe` Nothing
      toNInt 1 `shouldBe` Nothing
      toNInt (nintMin - 1) `shouldBe` Nothing
      toNInt nintMin `shouldNotBe` Nothing
      toNInt (-1) `shouldNotBe` Nothing

    prop "toNInt . fromNInt = Just" $ \n ->
      toNInt (fromNInt n) === Just n

    it "boundary values roundtrip" $ do
      fmap fromNInt (toNInt (-1)) `shouldBe` Just (-1)
      fmap fromNInt (toNInt nintMin) `shouldBe` Just nintMin

    prop "Ord on NInt agrees with Ord on the represented Integer" $ \a b ->
      compare a b === compare (fromNInt a) (fromNInt b)

  describe "toCanonical" $ do
    describe "integer normalization" $ do
      prop "TInt and TInteger of the same value are equal" $ \i ->
        toCanonical (TInt i) === toCanonical (TInteger (toInteger i))

      prop "in-range positive bignum collapses to CTInt" $ \(w :: Word64) ->
        let n = toInteger w
         in toCanonical (TTagged 2 (TBytes (unsignedBE n)))
              === toCanonical (TInteger n)

      prop "in-range negative bignum collapses to CTNInt" $ \nint ->
        let n = fromNInt nint
         in toCanonical (TTagged 3 (TBytes (unsignedBE (-1 - n))))
              === toCanonical (TInteger n)

      it "bignum with leading zeros canonicalizes" $
        toCanonical (TTagged 2 (TBytes (BS.pack [0, 0, 5])))
          `shouldBe` CTInt 5

      prop "bignum from TBytesI matches TBytes" $ \(w :: Word64) ->
        let bs = unsignedBE (toInteger w)
         in toCanonical (TTagged 2 (TBytesI (BSL.fromStrict bs)))
              === toCanonical (TTagged 2 (TBytes bs))

      it "true bignum (above uintMax) stays tagged" $
        let n = uintMax + 1
         in toCanonical (TInteger n)
              `shouldBe` CTTagged 2 (CTBytes (unsignedBE n))

      it "true bignum (below nintMin) stays tagged" $
        let n = nintMin - 1
         in toCanonical (TInteger n)
              `shouldBe` CTTagged 3 (CTBytes (unsignedBE (-1 - n)))

    describe "definite/indefinite variants merge" $ do
      it "TBytes ≡ TBytesI" $
        toCanonical (TBytes "abc")
          `shouldBe` toCanonical (TBytesI (BSL.fromStrict "abc"))

      it "TString ≡ TStringI" $
        toCanonical (TString "abc")
          `shouldBe` toCanonical (TStringI (TL.fromStrict "abc"))

      it "TList ≡ TListI" $
        toCanonical (TList [TInt 1, TInt 2])
          `shouldBe` toCanonical (TListI [TInt 1, TInt 2])

      it "TMap ≡ TMapI" $
        toCanonical (TMap [(TInt 1, TInt 2)])
          `shouldBe` toCanonical (TMapI [(TInt 1, TInt 2)])

    describe "bool/null go through CTSimple" $ do
      it "TBool False ≡ TSimple 20" $
        toCanonical (TBool False) `shouldBe` toCanonical (TSimple 20)
      it "TBool True ≡ TSimple 21" $
        toCanonical (TBool True) `shouldBe` toCanonical (TSimple 21)
      it "TNull ≡ TSimple 22" $
        toCanonical TNull `shouldBe` toCanonical (TSimple 22)

    describe "maps" $ do
      it "key order is irrelevant" $
        toCanonical (TMap [(TInt 1, TInt 10), (TInt 2, TInt 20)])
          `shouldBe` toCanonical (TMap [(TInt 2, TInt 20), (TInt 1, TInt 10)])

      -- `TInt 1` and `TInteger 1` are distinct raw keys that canonicalize to
      -- the same key, so these exercise duplicate-key handling after
      -- canonicalization.
      describe "pairs sharing a canonical key" $ do
        let dupKeyMap =
              TMap [(TInt 1, TInt 10), (TInteger 1, TInt 20)]

        it "retains pairs with different values without throwing" $
          case toCanonical dupKeyMap of
            CTMap pairs ->
              pairs
                `shouldBe` Set.fromList
                  [ (CTInt 1, CTInt 10)
                  , (CTInt 1, CTInt 20)
                  ]
            other -> expectationFailure $ "expected CTMap, got " <> show other

        it "compare equal after reordering" $
          toCanonical dupKeyMap
            `shouldBe` toCanonical (TMap [(TInteger 1, TInt 20), (TInt 1, TInt 10)])

        it "compare unequal when a distinct pair is removed" $ do
          toCanonical dupKeyMap
            `shouldNotBe` toCanonical (TMap [(TInt 1, TInt 10)])
          toCanonical dupKeyMap
            `shouldNotBe` toCanonical (TMap [(TInteger 1, TInt 20)])

        it "collapse identical canonical pairs" $ do
          let collapsed = toCanonical (TMap [(TInt 1, TInt 10), (TInteger 1, TInt 10)])
          collapsed `shouldBe` CTMap (Set.singleton (CTInt 1, CTInt 10))
          collapsed `shouldBe` toCanonical (TMap [(TInt 1, TInt 10)])

    describe "floats stay distinct by width" $ do
      it "THalf 1.0 ≠ TFloat 1.0" $
        toCanonical (THalf 1.0) `shouldNotBe` toCanonical (TFloat 1.0)
      it "TFloat 1.0 ≠ TDouble 1.0" $
        toCanonical (TFloat 1.0) `shouldNotBe` toCanonical (TDouble 1.0)

-- | Encode a non-negative Integer as a big-endian byte string with no leading zeros.
unsignedBE :: Integer -> BS.ByteString
unsignedBE = BS.pack . reverse . go
  where
    go 0 = []
    go n = fromInteger (n `mod` 256) : go (n `div` 256)
