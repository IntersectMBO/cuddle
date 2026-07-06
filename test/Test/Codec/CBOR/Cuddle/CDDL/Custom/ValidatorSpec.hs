{-# LANGUAGE OverloadedStrings #-}

module Test.Codec.CBOR.Cuddle.CDDL.Custom.ValidatorSpec (
  spec,
  succeedsWith,
) where

import Codec.CBOR.Cuddle.CDDL.CTree (CTreeRoot (..))
import Codec.CBOR.Cuddle.CDDL.Custom.Core (RuleTerm (..))
import Codec.CBOR.Cuddle.CDDL.Custom.Validator (
  CustomValidatorResult (..),
  Validator,
  ValidatorPhase,
  runValidator,
  unwrapSingle,
  validateArrayTerm,
  validateBytesTerm,
  validateInt,
  validateMapTerm,
  validateNInt,
  validateNonEmpty,
  validateStringTerm,
  validateUInt,
  validateUniqueList,
 )
import Codec.CBOR.Term (Term (..))
import Control.Monad (unless, void)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as LBS
import Data.List (nub)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Data.Text.Lazy qualified as LT
import Data.Word (Word8)
import Test.Codec.CBOR.Cuddle.CDDL.Validator ()
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (
  Property,
  counterexample,
  forAll,
  property,
  shuffle,
  (.&&.),
  (===),
 )

emptyRoot :: CTreeRoot ValidatorPhase
emptyRoot = CTreeRoot Map.empty

-- | The validator succeeds and returns the expected value.
succeedsWith :: (Eq a, Show a) => Validator a -> a -> Property
succeedsWith v expected = runValidator checked emptyRoot === CustomValidatorSuccess
  where
    checked = do
      x <- v
      unless (x == expected) . fail $ "Unexpected result: " <> show x

succeeds :: Validator a -> Bool
succeeds v = runValidator (void v) emptyRoot == CustomValidatorSuccess

fails :: Validator a -> Property
fails v =
  counterexample "Expected the validator to fail" . property . not $ succeeds v

spec :: Spec
spec = do
  describe "validateInt" $ do
    prop "accepts any TInt and returns its value" $ \i ->
      validateInt (TInt i) `succeedsWith` toInteger i
    prop "rejects non-int terms" $
      fails (validateInt (TString "hi")) .&&. fails (validateInt (TList []))

  describe "validateUInt" $ do
    prop "accepts a TInt iff it is non-negative" $ \i ->
      if i >= 0
        then validateUInt (TInt i) `succeedsWith` toInteger i
        else fails (validateUInt (TInt i))
    prop "rejects non-int terms" $
      fails (validateUInt TNull)

  describe "validateNInt" $ do
    prop "accepts a TInt iff it is negative" $ \i ->
      if i < 0
        then validateNInt (TInt i) `succeedsWith` toInteger i
        else fails (validateNInt (TInt i))
    prop "rejects non-int terms" $
      fails (validateNInt (TBytes ""))

  describe "validateArrayTerm" $ do
    prop "accepts definite and indefinite lists" $ \is ->
      let ts = map TInt is
       in validateArrayTerm (TList ts) `succeedsWith` ts
            .&&. validateArrayTerm (TListI ts) `succeedsWith` ts
    prop "rejects non-list terms" $ \i ->
      fails (validateArrayTerm (TInt i))

  describe "validateBytesTerm" $ do
    prop "accepts definite and indefinite bytes" $ \ws ->
      let bs = BS.pack ws
       in validateBytesTerm (TBytes bs) `succeedsWith` bs
            .&&. validateBytesTerm (TBytesI $ LBS.fromStrict bs) `succeedsWith` bs
    prop "converts chunked indefinite bytes to strict" $ \(chunks :: [[Word8]]) ->
      validateBytesTerm (TBytesI . LBS.fromChunks $ map BS.pack chunks)
        `succeedsWith` BS.pack (concat chunks)
    prop "rejects non-bytes terms" $
      fails (validateBytesTerm (TString "hi"))

  describe "validateStringTerm" $ do
    prop "accepts definite and indefinite strings" $ \s ->
      let t = T.pack s
       in validateStringTerm (TString t) `succeedsWith` t
            .&&. validateStringTerm (TStringI $ LT.fromStrict t) `succeedsWith` t
    prop "converts chunked indefinite strings to strict" $ \(chunks :: [String]) ->
      validateStringTerm (TStringI . LT.fromChunks $ map T.pack chunks)
        `succeedsWith` T.pack (concat chunks)
    prop "rejects non-string terms" $
      fails (validateStringTerm (TBytes "hi"))

  describe "validateMapTerm" $ do
    prop "accepts definite and indefinite maps" $ \(kvs :: [(Int, Int)]) ->
      let ts = [(TInt k, TInt v) | (k, v) <- kvs]
       in validateMapTerm (TMap ts) `succeedsWith` ts
            .&&. validateMapTerm (TMapI ts) `succeedsWith` ts
    prop "rejects non-map terms" $
      fails (validateMapTerm (TList []))

  describe "validateNonEmpty" $ do
    prop "succeeds on a non-empty list and preserves the elements" $ \x (xs :: [Int]) ->
      fmap NE.toList (validateNonEmpty (x : xs)) `succeedsWith` (x : xs)
    prop "fails on an empty list" $
      fails (validateNonEmpty ([] :: [Int]))

  describe "validateUnique" $ do
    prop "agrees with a nub oracle" $ \(xs :: [Term]) ->
      succeeds (validateUniqueList xs) === (nub xs == xs)
    prop "fails whenever a duplicate is present" $ \x (xs :: [Term]) ->
      forAll (shuffle (x : x : xs)) $ \ys ->
        fails (validateUniqueList ys)

  describe "unwrapSingle" $ do
    prop "returns the term inside a SingleTerm" $ \i ->
      unwrapSingle (SingleTerm (TInt i)) `succeedsWith` TInt i
    prop "rejects pair and group terms" $ \i ->
      fails (unwrapSingle (PairTerm (TInt i) (TInt i)))
        .&&. fails (unwrapSingle (GroupTerm []))
