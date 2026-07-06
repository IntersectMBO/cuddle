{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Test.Codec.CBOR.Cuddle.CDDL.Validator (
  spec,
  expectValid,
  expectInvalid,
  genAndValidateCddl,
  genAndValidateRule,
  validateCBOR_,
) where

import Codec.CBOR.Cuddle.CBOR.Canonical (toCanonical)
import Codec.CBOR.Cuddle.CBOR.Gen (generateFromName)
import Codec.CBOR.Cuddle.CBOR.Validator (
  ValidatorPhase,
  validateCBOR,
 )
import Codec.CBOR.Cuddle.CBOR.Validator.Trace (
  Evidenced (..),
  SValidity (..),
  ValidationTrace,
  defaultTraceOptions,
  prettyValidationTrace,
 )
import Codec.CBOR.Cuddle.CDDL (Name (..))
import Codec.CBOR.Cuddle.CDDL.CTree (CTreeRoot (..))
import Codec.CBOR.Cuddle.CDDL.CTree qualified as CTree
import Codec.CBOR.Cuddle.CDDL.Custom.Core (RuleTerm (..))
import Codec.CBOR.Cuddle.CDDL.Custom.Generator (GenConfig (..), runCBORGen)
import Codec.CBOR.Cuddle.CDDL.Custom.Validator (TermValidator)
import Codec.CBOR.Cuddle.CDDL.Postlude (appendPostlude)
import Codec.CBOR.Cuddle.CDDL.Resolve (MonoReferenced, fullResolveCDDL)
import Codec.CBOR.Cuddle.Huddle (
  CanQuantify (..),
  GroupDef,
  Huddle,
  HuddleItem (..),
  Value (..),
  a,
  arr,
  collectFrom,
  int,
  opt,
  toCDDL,
  withValidator,
  (=:=),
  (=:~),
 )
import Codec.CBOR.Cuddle.Huddle qualified as H
import Codec.CBOR.Cuddle.IndexMappable (mapCDDLDropExt, mapIndex)
import Codec.CBOR.Cuddle.Parser (pCDDL)
import Codec.CBOR.Pretty (prettyHexEnc)
import Codec.CBOR.Term (Term (..), encodeTerm)
import Codec.CBOR.Write (toStrictByteString)
import Control.Monad (forM_)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as LBS
import Data.Containers.ListUtils (nubOrdOn)
import Data.Either (fromRight)
import Data.Map qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Data.Text.Lazy qualified as LT
import Paths_cuddle (getDataFileName)
import Prettyprinter (defaultLayoutOptions, layoutPretty)
import Prettyprinter.Render.Terminal (renderStrict)
import Test.AntiGen (runAntiGen)
import Test.Codec.CBOR.Cuddle.CDDL.Examples.Huddle (
  huddleArray,
  huddleMap,
  huddleRangeArray,
  huddleRangeMap,
 )
import Test.Hspec (
  Expectation,
  HasCallStack,
  Spec,
  describe,
  expectationFailure,
  it,
  runIO,
 )
import Test.Hspec.QuickCheck
import Test.QuickCheck (
  Arbitrary (..),
  Gen,
  NonNegative (..),
  choose,
  counterexample,
  elements,
  forAll,
  infiniteListOf,
  listOf,
  listOf1,
  oneof,
  scale,
  shuffle,
  vectorOf,
 )
import Text.Megaparsec (runParser)

validateCBOR_ ::
  HasCallStack =>
  BS.ByteString ->
  Name ->
  CTreeRoot ValidatorPhase ->
  Evidenced ValidationTrace
validateCBOR_ bs n cddl = either (\e -> error $ "validateCBOR failed:\n" <> show e) id $ validateCBOR bs n cddl

-- | Test that a specific rule in a resolved CDDL generates valid values
genAndValidateRule :: String -> Name -> CTreeRoot MonoReferenced -> Spec
genAndValidateRule description name resolvedCddl =
  prop description $ do
    let
      genCfg =
        GenConfig
          { gcRoot = mapIndex resolvedCddl
          , gcTwiddle = True
          }
    cborTerm <- runAntiGen . runCBORGen genCfg $ generateFromName name
    let
      generatedCbor = toStrictByteString $ encodeTerm cborTerm
      res = validateCBOR_ generatedCbor name (mapIndex resolvedCddl)
      extraInfo =
        unlines
          [ "CBOR term:"
          , prettyHexEnc $ encodeTerm cborTerm
          ]
    pure . counterexample extraInfo $ expectValid res

-- | Test that all rules in a resolved CDDL generate valid values
genAndValidateCddl :: String -> CTreeRoot MonoReferenced -> Spec
genAndValidateCddl description resolvedCddl@(CTreeRoot m) = do
  let
    isRule CTree.Group {} = False
    isRule _ = True
  describe description $ do
    forM_ (Map.keys $ Map.filter isRule m) $ \name@(Name n) ->
      genAndValidateRule (T.unpack n) name resolvedCddl

genAndValidateFromFile :: FilePath -> Spec
genAndValidateFromFile path = do
  contents <- runIO $ T.readFile =<< getDataFileName path
  let
    cddl = fromRight (error "Failed to parse CDDL") $ runParser pCDDL path contents
    resolverError x =
      error $ "Failed to resolve the CDDL from file " <> show path <> ":\n" <> show x
    resolvedCddl =
      either resolverError id . fullResolveCDDL . appendPostlude $
        mapCDDLDropExt cddl
  genAndValidateCddl path resolvedCddl

genInfiniteUniqueListOn :: Ord b => (a -> b) -> Gen a -> Gen [a]
genInfiniteUniqueListOn f = fmap (nubOrdOn f) . infiniteListOf

genHuddleRangeMap :: (Int, Int) -> Gen Term
genHuddleRangeMap rng@(lo, hi) = do
  n <- choose rng
  let genKV = (,) <$> fmap TInt arbitrary <*> fmap TBool arbitrary
  genMapTerm . take n
    =<< scale (const $ max lo hi) (genInfiniteUniqueListOn (toCanonical . fst) genKV)

genHuddleArrayRequiredTerms :: Gen [Term]
genHuddleArrayRequiredTerms = do
  ints <- listOf1 $ TInt <$> arbitrary
  text <-
    oneof
      [ (: []) <$> (genStringTerm . T.pack =<< arbitrary)
      , pure []
      ]
  lastInt <- TInt . getNonNegative <$> arbitrary
  pure $ ints <> text <> [lastInt]

genHuddleArrayTerms :: Gen [Term]
genHuddleArrayTerms = do
  bools <- listOf $ TBool <$> arbitrary
  required <- genHuddleArrayRequiredTerms
  pure $ bools <> required

genHuddleArray :: Gen Term
genHuddleArray = genHuddleArrayTerms >>= genArrayTerm

genBadArrayReversed :: Gen Term
genBadArrayReversed = genHuddleArrayTerms >>= genArrayTerm . reverse . (TBool True :)

genBadArrayMissingLastInt :: Gen Term
genBadArrayMissingLastInt =
  genHuddleArrayTerms >>= genArrayTerm . reverse . dropWhile isNonNegativeInt . reverse
  where
    isNonNegativeInt (TInt x) | x >= 0 = True
    isNonNegativeInt _ = False

genHuddleRangeArray :: Gen Term
genHuddleRangeArray = do
  numInts <- choose (3, 4)
  ints <- vectorOf numInts $ TInt <$> arbitrary
  numBools <- choose (0, 3)
  bools <- vectorOf numBools $ TBool <$> arbitrary
  numTexts <- choose (3, 10)
  texts <- vectorOf numTexts $ genStringTerm . T.pack =<< arbitrary
  genArrayTerm $ ints <> bools <> texts

genArrayTerm :: [Term] -> Gen Term
genArrayTerm xs = elements [TList xs, TListI xs]

genMapTerm :: [(Term, Term)] -> Gen Term
genMapTerm x = elements [TMap x, TMapI x]

genStringTerm :: Text -> Gen Term
genStringTerm x = elements [TString x, TStringI (LT.fromStrict x)]

genBytesTerm :: ByteString -> Gen Term
genBytesTerm x = elements [TBytes x, TBytesI $ LBS.fromStrict x]

arbitraryByteString :: Gen ByteString
arbitraryByteString = BS.pack <$> arbitrary

instance Arbitrary Term where
  arbitrary =
    oneof
      [ TInt <$> arbitrary
      , TInteger <$> arbitrary
      , TBytes . BS.pack <$> arbitrary
      , TBytesI . LBS.pack <$> arbitrary
      , TString . T.pack <$> arbitrary
      , TStringI . LT.pack <$> arbitrary
      , TList <$> listOf (scale (`div` 2) arbitrary)
      , TListI <$> listOf (scale (`div` 2) arbitrary)
      , TMap <$> listOf (scale (`div` 2) $ (,) <$> arbitrary <*> arbitrary)
      , TMapI <$> listOf (scale (`div` 2) $ (,) <$> arbitrary <*> arbitrary)
      , -- TODO properly implement tagged generation
        -- , TTagged <$> arbitrary <*> arbitrary
        TBool <$> arbitrary
      , pure TNull
      , pure $ TSimple 23 -- TODO add other values once they are supported by cuddle
      , THalf <$> arbitrary
      , TFloat <$> arbitrary
      , TDouble <$> arbitrary
      ]

genFullMap :: Gen Term
genFullMap = do
  field1 <- do
    es <- listOf $ TInt . getNonNegative <$> arbitrary
    pure (TInt 1, TList es)
  lField2 <-
    oneof
      [ do
          b <- arbitrary
          pure [(TInt 2, TBool b)]
      , pure []
      ]
  strFields <-
    nubOrdOn (toCanonical . fst)
      <$> listOf ((,) <$> (genStringTerm . T.pack =<< arbitrary) <*> (TInt <$> arbitrary))
  bytesFields <-
    nubOrdOn (toCanonical . fst)
      <$> listOf1 ((,) <$> (genBytesTerm =<< arbitraryByteString) <*> arbitrary)
  allFields <- shuffle $ field1 : lField2 <> strFields <> bytesFields
  genMapTerm allFields

genBadMapInvalidIndex :: Gen Term
genBadMapInvalidIndex =
  pure $
    TMap
      [ (TInt 1, TList [])
      , (TInt 99, TList [])
      , (TBytes "foo", TBytes "bar")
      ]

validateHuddle ::
  HasCallStack =>
  Huddle ->
  Name ->
  Term ->
  Evidenced ValidationTrace
validateHuddle huddle name term = do
  let
    resolvedCddl = case fullResolveCDDL . mapCDDLDropExt $ toCDDL huddle of
      Right root -> root
      Left err -> error $ show err
    bs = toStrictByteString $ encodeTerm term
  validateCBOR_ bs name (mapIndex resolvedCddl)

expectValid :: Evidenced ValidationTrace -> Expectation
expectValid (Evidenced SValid _) = pure ()
expectValid (Evidenced SInvalid t) =
  expectationFailure . T.unpack $
    "Expected a success, got failure:\n"
      <> renderStrict (layoutPretty defaultLayoutOptions $ prettyValidationTrace defaultTraceOptions t)

expectInvalid :: Evidenced ValidationTrace -> Expectation
expectInvalid (Evidenced SValid t) =
  expectationFailure . T.unpack $
    "Expected a failure, but got success:\n"
      <> renderStrict (layoutPretty defaultLayoutOptions $ prettyValidationTrace defaultTraceOptions t)
expectInvalid _ = pure ()

stringValidator :: TermValidator
stringValidator (SingleTerm (TString _)) = pure ()
stringValidator (SingleTerm (TStringI _)) = pure ()
stringValidator t = fail $ "Expected a string, got\n" <> show t

bytesValidator :: TermValidator
bytesValidator (SingleTerm (TBytes _)) = pure ()
bytesValidator (SingleTerm (TBytesI _)) = pure ()
bytesValidator t = fail $ "Expected bytes, got\n" <> show t

spec :: Spec
spec = describe "Validator" $ do
  describe "Generate and validate from file" $ do
    genAndValidateFromFile "cddl/basic_assign.cddl"
    genAndValidateFromFile "cddl/conway.cddl"
    genAndValidateFromFile "cddl/costmdls_min.cddl"
    genAndValidateFromFile "cddl/issue80-min.cddl"
    genAndValidateFromFile "cddl/pretty.cddl"
    genAndValidateFromFile "cddl/shelley.cddl"
    genAndValidateFromFile "cddl/validator.cddl"
  describe "Term tests" $ do
    describe "Maps and arrays" $ do
      describe "Positive" $ do
        prop "Validates a full map" . forAll genFullMap $
          expectValid . validateHuddle huddleMap "a"
        prop "Validates array" . forAll genHuddleArray $
          expectValid . validateHuddle huddleArray "a"
        prop "Validates map with correct number of range elements"
          . forAll (genHuddleRangeMap (5, 10))
          $ expectValid . validateHuddle huddleRangeMap "a"
        prop "Validates array with ranges" . forAll genHuddleRangeArray $
          expectValid . validateHuddle huddleRangeArray "a"
      describe "Negative" $ do
        prop "Fails to validate a map with an unexpected index"
          . forAll genBadMapInvalidIndex
          $ expectInvalid . validateHuddle huddleMap "a"
        prop "Fails to validate reversed array" . forAll genBadArrayReversed $
          expectInvalid . validateHuddle huddleArray "a"
        prop "Fails to validate array with missing non-negative int at the end"
          . forAll genBadArrayMissingLastInt
          $ expectInvalid . validateHuddle huddleArray "a"
        prop "Fails to validate map with too few range elements"
          . forAll (genHuddleRangeMap (0, 4))
          $ expectInvalid . validateHuddle huddleRangeMap "a"
        prop "Fails to validate map with too many range elements"
          . forAll (genHuddleRangeMap (11, 20))
          $ expectInvalid . validateHuddle huddleRangeMap "a"

    -- Regression tests showing that optional ('?') validation is broken when
    -- the optional element is inside a group (`grp` / `=:~`) that is itself
    -- referenced inside an array. When the optional element is absent,
    -- `consumeGroup` receives a corrupted leftover-term list (due to `(<>)`
    -- on the result tuple accumulating terms from the failed consume path),
    -- causing the continuation to see phantom extra terms and report them as
    -- `ListValidationLeftoverTerms` instead of succeeding.
    describe "Group" $ do
      describe "Optional inside a group referenced from an array" $ do
        let
          -- @
          --   root = [innerGrp, int]
          --   innerGrp = (int, ? bool)
          -- @
          -- => [int, ? bool, int]
          optionalInGroupHuddle :: Huddle
          optionalInGroupHuddle =
            let
              innerGrp :: GroupDef
              innerGrp = "innerGrp" =:~ [a VInt, opt $ a VBool]
             in
              collectFrom
                [ HIRule $ "root" =:= arr [a innerGrp, a VInt]
                ]
        it "Validates when optional entry is present" $
          expectValid $
            validateHuddle optionalInGroupHuddle "root" (TList [TInt 1, TBool True, TInt 2])
        it "Validates when optional entry is absent" $
          expectValid $
            validateHuddle optionalInGroupHuddle "root" (TList [TInt 1, TInt 2])
      describe "ZeroOrMore (*) inside a group referenced from an array" $ do
        let
          -- @
          --   root = [zeroOrMoreGrp, text]
          --   zeroOrMoreGrp = (* bool, int)
          -- @
          -- => [* bool, int, text]
          zeroOrMoreInGroupHuddle :: Huddle
          zeroOrMoreInGroupHuddle =
            let
              zeroOrMoreGrp :: GroupDef
              zeroOrMoreGrp = "zeroOrMoreGrp" =:~ [0 <+ a VBool, a VInt]
             in
              collectFrom
                [ HIRule $ "root" =:= arr [a zeroOrMoreGrp, a VText]
                ]

        it "Validates when zero-or-more entry has elements" $
          expectValid $
            validateHuddle
              zeroOrMoreInGroupHuddle
              "root"
              (TList [TBool True, TBool False, TInt 42, TString "hi"])
        it "Validates when zero-or-more entry has zero elements" $
          expectValid $
            validateHuddle zeroOrMoreInGroupHuddle "root" (TList [TInt 42, TString "hi"])
      describe "Bounded (n..m) inside a group referenced from an array" $ do
        -- @
        --   root = [boundedGrp, text]
        --   boundedGrp = (0..2 bool, int)
        -- @
        -- => [0..2 bool, int, text]
        let boundedInGroupHuddle :: Huddle
            boundedInGroupHuddle =
              let boundedGrp :: GroupDef
                  boundedGrp = "boundedGrp" =:~ [0 <+ a VBool +> 2, a VInt]
               in collectFrom
                    [ HIRule $ "root" =:= arr [a boundedGrp, a VText]
                    ]
        it "Validates when bounded entry has elements (within bounds)" $
          expectValid $
            validateHuddle
              boundedInGroupHuddle
              "root"
              (TList [TBool True, TInt 42, TString "hi"])
        it "Validates when bounded entry has zero elements (lower bound is 0)" $
          expectValid $
            validateHuddle boundedInGroupHuddle "root" (TList [TInt 42, TString "hi"])

    describe "Bignums" $ do
      let
        bignum = 2 ^ (64 :: Int) :: Integer
        bignumCBOR = toStrictByteString . encodeTerm $ TInteger bignum
        resolveCDDL cddlText =
          let cddl = fromRight (error "Failed to parse CDDL") $ runParser pCDDL "" cddlText
           in either (error . show) id . fullResolveCDDL . appendPostlude $ mapCDDLDropExt cddl
      it "Validates a bignum >= 2^64 against biguint" $
        expectValid $
          validateCBOR_ bignumCBOR "a" (mapIndex $ resolveCDDL "a = biguint")
      it "Validates a bignum >= 2^64 against bigint" $
        expectValid $
          validateCBOR_ bignumCBOR "a" (mapIndex $ resolveCDDL "a = bigint")
      it "Validates a bignum >= 2^64 against integer" $
        expectValid $
          validateCBOR_ bignumCBOR "a" (mapIndex $ resolveCDDL "a = integer")
      it "Rejects a bignum >= 2^64 against int" $
        expectInvalid $
          validateCBOR_ bignumCBOR "a" (mapIndex $ resolveCDDL "a = int")
      it "Rejects a bignum >= 2^64 against uint" $
        expectInvalid $
          validateCBOR_ bignumCBOR "a" (mapIndex $ resolveCDDL "a = uint")

  describe "Custom validator" $ do
    describe "Positive" $ do
      prop "Validates with custom validator" $ do
        term <- genStringTerm . T.pack =<< arbitrary
        num <- arbitrary
        let
          huddle =
            collectFrom
              [ HIRule . withValidator stringValidator $ "a" =:= int num
              ]
        pure . expectValid $ validateHuddle huddle "a" term
      prop "Validates with custom validator behind a reference" $ do
        stringTerm <- genStringTerm . T.pack =<< arbitrary
        arrTerm <- genArrayTerm [stringTerm]
        num <- arbitrary
        let
          ruleA = withValidator stringValidator $ "a" =:= int num
          huddle =
            collectFrom
              [ HIRule ruleA
              , HIRule $ "b" =:= arr [a ruleA]
              ]
        pure . expectValid $ validateHuddle huddle "b" arrTerm
      prop "Validates with custom validator in a choice within a group" $ do
        bs <- BS.pack <$> listOf1 arbitrary
        let
          ruleA = withValidator bytesValidator $ "a" =:= VText
          huddle =
            collectFrom
              [ HIRule ruleA
              , HIRule $ "b" =:= arr [0, a (ruleA H./ VNil)]
              ]
        arrTerm <- genArrayTerm [TInt 0, TBytes bs]
        pure . expectValid $ validateHuddle huddle "b" arrTerm
    describe "Negative" $ do
      prop "Fails if term is valid against the Huddle, but not the custom validator" $ do
        stringTerm <- genStringTerm . T.pack =<< arbitrary
        let
          huddle =
            collectFrom
              [ HIRule . withValidator bytesValidator $ "a" =:= VText
              ]
        pure . expectInvalid $ validateHuddle huddle "a" stringTerm
      prop "Fails if term is valid against the Huddle, but not the custom validator, behind a reference" $ do
        stringTerm <- genStringTerm . T.pack =<< arbitrary
        let
          ruleA = withValidator bytesValidator $ "a" =:= VText
          ruleB = "b" =:= arr [a ruleA]
          huddle =
            collectFrom
              [ HIRule ruleA
              , HIRule ruleB
              ]
        pure . expectInvalid $ validateHuddle huddle "a" stringTerm
