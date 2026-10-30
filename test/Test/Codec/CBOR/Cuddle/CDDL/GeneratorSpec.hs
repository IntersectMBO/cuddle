{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Test.Codec.CBOR.Cuddle.CDDL.GeneratorSpec (spec) where

import Codec.CBOR.Cuddle.CBOR.Gen (GenPhase, generateFromName)
import Codec.CBOR.Cuddle.CDDL (Name)
import Codec.CBOR.Cuddle.CDDL.CTree (CTreeRoot (..))
import Codec.CBOR.Cuddle.CDDL.Custom.Generator (GenConfig (..), runCBORGen, twiddleAll)
import Codec.CBOR.Cuddle.CDDL.Resolve (MonoReferenced, MonoSimplePhase, fullResolveCDDL)
import Codec.CBOR.Cuddle.Huddle (Huddle, toCDDL)
import Codec.CBOR.Cuddle.IndexMappable (IndexMappable (..), mapCDDLDropExt)
import Codec.CBOR.Pretty (prettyHexEnc)
import Codec.CBOR.Read (deserialiseFromBytes)
import Codec.CBOR.Term (Term (..), decodeTerm, encodeTerm)
import Codec.CBOR.Write (toStrictByteString)
import Data.ByteString.Lazy qualified as LBS
import Data.Text qualified as T
import Data.Text.Lazy qualified as TL
import Test.AntiGen (ZapResult (..), prettyZapResult, runAntiGen, zapAntiGenResult)
import Test.Codec.CBOR.Cuddle.CDDL.Examples.Huddle (
  bytesExample,
  customGenExample,
  opCertExample,
  optionalMapExample,
  rangeListExample,
  rangeMapExample,
  refTermExample,
  sizeBytesExample,
  sizeTextExample,
  tagRangeExample,
  taggedUintExample,
 )
import Test.Codec.CBOR.Cuddle.CDDL.Validator (expectInvalid, genAndValidateRule, validateCBOR_)
import Test.Hspec (HasCallStack, Spec, describe, runIO, shouldSatisfy, xdescribe)
import Test.Hspec.Core.Spec (SpecM)
import Test.Hspec.QuickCheck (prop)
import Test.QuickCheck (Gen, Property, Testable (..), classify, counterexample)
import Text.Pretty.Simple (pShow)

generateCDDL :: CTreeRoot GenPhase -> Gen Term
generateCDDL cddl = runAntiGen . runCBORGen cfg $ generateFromName "root"
  where
    cfg =
      GenConfig
        { gcRoot = cddl
        , gcTwiddle = twiddleAll
        }

tryResolveHuddle :: HasCallStack => Huddle -> SpecM () (CTreeRoot MonoReferenced)
tryResolveHuddle huddle = do
  case fullResolveCDDL . mapCDDLDropExt $ toCDDL huddle of
    Right x -> pure x
    Left err -> runIO . fail $ "Failed to resolve CDDL:\n" <> show err

expectZapInvalidates :: CTreeRoot MonoReferenced -> Name -> Property
expectZapInvalidates cddl name = property $ do
  let
    cfg =
      GenConfig
        { gcRoot = mapIndex cddl
        , gcTwiddle = twiddleAll
        }
  res@ZapResult {zrValue} <- zapAntiGenResult 1 . runCBORGen cfg $ generateFromName name
  let
    bs = toStrictByteString $ encodeTerm zrValue
    validationRes = validateCBOR_ bs name $ mapIndex cddl
    failMsg =
      unlines
        [ case deserialiseFromBytes decodeTerm (LBS.fromStrict bs) of
            Right (_, t) -> prettyHexEnc (encodeTerm t)
            Left _ -> mempty
        , mempty
        , T.unpack $ prettyZapResult res
        ]
  pure . counterexample failMsg $ expectInvalid validationRes

zapInvalidatesHuddle :: String -> Huddle -> Spec
zapInvalidatesHuddle n huddle = do
  cddl <- tryResolveHuddle huddle
  prop n . counterexample (TL.unpack . pShow $ mapIndex @_ @_ @MonoSimplePhase cddl) $
    expectZapInvalidates cddl "root"

-- | Test that generated values are valid for a Huddle schema
genAndValidateHuddle :: String -> Huddle -> Spec
genAndValidateHuddle n huddle = do
  cddl <- tryResolveHuddle huddle
  genAndValidateRule n "root" cddl

spec :: Spec
spec = do
  describe "Positive generator" $ do
    describe "Generated value validates" $ do
      -- Note: simpleTermExample and refTermExample use custom generators
      -- that intentionally produce type-mismatched values, so they're excluded
      genAndValidateHuddle "opCert" opCertExample
      genAndValidateHuddle "sizeText" sizeTextExample
      genAndValidateHuddle "sizeBytes" sizeBytesExample
      genAndValidateHuddle "rangeList" rangeListExample
      genAndValidateHuddle "rangeMap" rangeMapExample
      genAndValidateHuddle "tagRange" tagRangeExample
      xdescribe "Generator cannot reliably produce unique keys for maps" $ do
        genAndValidateHuddle "optionalMapExample" optionalMapExample

  describe "Negative generator" $ do
    describe "Zapped value fails to validate" $ do
      zapInvalidatesHuddle "customGen" customGenExample
      zapInvalidatesHuddle "refTerm" refTermExample
      zapInvalidatesHuddle "opCert" opCertExample
      zapInvalidatesHuddle "sizeText" sizeTextExample
      zapInvalidatesHuddle "sizeBytes" sizeBytesExample
      zapInvalidatesHuddle "rangeList" rangeListExample
      zapInvalidatesHuddle "rangeMap" rangeMapExample
      xdescribe "Generator cannot reliably produce unique keys for maps" $ do
        zapInvalidatesHuddle "optionalMapExample" optionalMapExample

  describe "Custom generators" $ do
    describe "Huddle" $ do
      customGenExampleCddl <- tryResolveHuddle customGenExample
      prop "If a term has a custom generator then it is used" $ do
        res <- generateCDDL $ mapIndex customGenExampleCddl
        pure $
          res `shouldSatisfy` \case
            TInt i -> i > 3 && i < 7
            _ -> False
      refTermExampleCddl <- tryResolveHuddle refTermExample
      prop "Custom generator works when called via reference" $ do
        res <- generateCDDL $ mapIndex refTermExampleCddl
        pure $
          res `shouldSatisfy` \case
            TList [TInt 0, TInt i] -> i > 3 && i < 7
            TListI [TInt 0, TInt i] -> i > 3 && i < 7
            _ -> False
      bytesExampleCddl <- tryResolveHuddle bytesExample
      prop "Bytes are generated correctly" $ do
        res <- generateCDDL $ mapIndex bytesExampleCddl
        pure $
          res `shouldSatisfy` \case
            TBytes "\x01\x02\x03\xff" -> True
            TBytesI "\x01\x02\x03\xff" -> True
            _ -> False
      tagRangeExampleCddl <- tryResolveHuddle tagRangeExample
      prop "tagRange generator covers edges and middle" $ do
        res <- generateCDDL $ mapIndex tagRangeExampleCddl
        let tags = case res of
              TList xs -> [t | TTagged t _ <- xs]
              TListI xs -> [t | TTagged t _ <- xs]
              _ -> []
            classifyTag t p =
              classify (t == 1280 || t == 1400) "edge tag (1280 or 1400)" $
                classify (t > 1280 && t < 1400) "middle tag (1281..1399)" p
            base =
              counterexample ("tags: " <> show tags) $
                all (\t -> t >= 1280 && t <= 1400) tags
        pure $ foldr classifyTag (property base) tags

  describe "Tagged bytes zapping" $ do
    taggedBytesCddl <- tryResolveHuddle taggedUintExample
    let cfg =
          GenConfig
            { gcRoot = mapIndex taggedBytesCddl
            , gcTwiddle = twiddleAll
            }
    prop "labels zapped result" $ do
      ZapResult {zrValue} <-
        zapAntiGenResult 1 . runCBORGen cfg $ generateFromName "root"
      let
        isBytes TBytes {} = True
        isBytes TBytesI {} = True
        isBytes _ = False
        tagOmitted = case zrValue of
          TTagged {} -> False
          _ -> True
        tagChanged = case zrValue of
          TTagged t _ -> t /= 42
          _ -> False
        innerValueZapped = case zrValue of
          TTagged 42 inner -> not (isBytes inner)
          _ -> False
      pure
        . classify tagOmitted "tag omitted"
        . classify tagChanged "tag changed"
        . classify innerValueZapped "inner value zapped"
        $ expectInvalid
          (validateCBOR_ (toStrictByteString $ encodeTerm zrValue) "root" $ mapIndex taggedBytesCddl)
