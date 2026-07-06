module Test.Codec.CBOR.Cuddle.CDDL.Custom.GeneratorSpec (spec) where

import Codec.CBOR.Cuddle.CDDL.CTree (CTreeRoot (..))
import Codec.CBOR.Cuddle.CDDL.Custom.Generator (
  CBORGen,
  GenConfig (..),
  genArrayTerm,
  genBytesTerm,
  genMapTerm,
  genStringTerm,
  ifTwiddle,
  runCBORGen,
 )
import Codec.CBOR.Cuddle.CDDL.Custom.Generator qualified as Gen
import Codec.CBOR.Cuddle.CDDL.Custom.Validator (
  validateArrayTerm,
  validateBytesTerm,
  validateMapTerm,
  validateStringTerm,
 )
import Codec.CBOR.Term (Term (..))
import Data.ByteString qualified as BS
import Data.List (sort)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Test.AntiGen (runAntiGen)
import Test.Codec.CBOR.Cuddle.CDDL.Custom.ValidatorSpec (succeedsWith)
import Test.Hspec (Spec, describe)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (
  Gen,
  chooseInt,
  classify,
  total,
  (===),
 )
import Test.QuickCheck.GenT qualified as GenT

runCustomGen :: Bool -> CBORGen a -> Gen a
runCustomGen twiddle =
  runAntiGen . runCBORGen GenConfig {gcRoot = CTreeRoot Map.empty, gcTwiddle = twiddle}

isIndefinite :: Term -> Bool
isIndefinite TListI {} = True
isIndefinite TBytesI {} = True
isIndefinite TStringI {} = True
isIndefinite TMapI {} = True
isIndefinite _ = False

spec :: Spec
spec = do
  describe "term generators with twiddling disabled" $ do
    prop "genArrayTerm yields a definite list" $ \is -> do
      let ts = map TInt is
      res <- runCustomGen False $ genArrayTerm ts
      pure $ res === TList ts
    prop "genBytesTerm yields definite bytes" $ \ws -> do
      let bs = BS.pack ws
      res <- runCustomGen False $ genBytesTerm bs
      pure $ res === TBytes bs
    prop "genStringTerm yields a definite string" $ \s -> do
      let t = T.pack s
      res <- runCustomGen False $ genStringTerm t
      pure $ res === TString t
    prop "genMapTerm yields a definite map" $ \(kvs :: [(Int, Int)]) -> do
      let ts = [(TInt k, TInt v) | (k, v) <- kvs]
      res <- runCustomGen False $ genMapTerm ts
      pure $ res === TMap ts
    prop "ifTwiddle takes the second branch" $ do
      res <- runCustomGen False $ ifTwiddle (pure True) (pure False)
      pure $ res === False

  describe "term generators with twiddling enabled" $ do
    prop "genArrayTerm roundtrips through validateArrayTerm" $ \is -> do
      let ts = map TInt is
      res <- runCustomGen True $ genArrayTerm ts
      pure
        . classify (isIndefinite res) "indefinite"
        $ validateArrayTerm res `succeedsWith` ts
    prop "genBytesTerm roundtrips through validateBytesTerm" $ \ws -> do
      let bs = BS.pack ws
      res <- runCustomGen True $ genBytesTerm bs
      pure
        . classify (isIndefinite res) "indefinite"
        $ validateBytesTerm res `succeedsWith` bs
    prop "genStringTerm roundtrips through validateStringTerm" $ \s -> do
      let t = T.pack s
      res <- runCustomGen True $ genStringTerm t
      pure
        . classify (isIndefinite res) "indefinite"
        $ validateStringTerm res `succeedsWith` t
    prop "genMapTerm roundtrips through validateMapTerm" $ \(kvs :: [(Int, Int)]) -> do
      let ts = [(TInt k, TInt v) | (k, v) <- kvs]
      res <- runCustomGen True $ genMapTerm ts
      pure
        . classify (isIndefinite res) "indefinite"
        $ validateMapTerm res `succeedsWith` ts
    prop "ifTwiddle takes the first branch" $ do
      res <- runCustomGen True $ ifTwiddle (pure True) (pure False)
      pure $ res === True

  describe "lifted QuickCheck functions" $ do
    prop "shuffle returns a permutation" $ \(xs :: [Int]) -> do
      ys <- runCustomGen True $ Gen.shuffle xs
      pure $ sort ys === sort xs
    prop "scale sets the size seen by the generator" $ do
      k <- chooseInt (0, 99)
      sz <- runCustomGen True $ Gen.scale (const k) (GenT.sized pure)
      pure $ sz === k
    prop "arbitrary lifts into CBORGen" $ do
      n <- runCustomGen True (Gen.arbitrary :: CBORGen Int)
      pure . classify (n /= 0) "non-zero" $ total n
