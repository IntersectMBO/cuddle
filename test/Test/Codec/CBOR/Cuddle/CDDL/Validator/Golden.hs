{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Test.Codec.CBOR.Cuddle.CDDL.Validator.Golden (spec) where

import Codec.CBOR.Cuddle.CDDL (Name, mapCDDLDropExt)
import Codec.CBOR.Cuddle.CDDL.Custom.Validator (
  defaultTraceOptions,
  foldEvidenced,
  prettyStepTrace,
 )
import Codec.CBOR.Cuddle.CDDL.Resolve (fullResolveCDDL)
import Codec.CBOR.Cuddle.Huddle (Huddle, toCDDL)
import Codec.CBOR.Cuddle.IndexMappable (mapIndex)
import Codec.CBOR.Term (Term (..), encodeTerm)
import Codec.CBOR.Write (toStrictByteString)
import Codec.CBOR.Write qualified as CBOR
import Control.Monad ((<=<))
import Data.Either (fromRight)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Paths_cuddle (getDataFileName)
import Prettyprinter (defaultLayoutOptions, layoutPretty)
import Prettyprinter.Render.Terminal qualified as Ansi
import System.FilePath ((</>))
import Test.Codec.CBOR.Cuddle.CDDL.Examples.Huddle (
  cborControlExample,
  choicesExample,
  deeplyNestedRefExample,
  huddleRangeArray,
  listSkippedRuleExample,
  listSkippedRuleNestedExample,
  listTooShortExample,
  listZeroOrMoreExample,
  mapLeftoverKVExample,
  mapNestedValueExample,
  mapNoMatchingKeyExample,
  refTermExample,
 )
import Test.Codec.CBOR.Cuddle.CDDL.Validator (validateCBOR_)
import Test.Hspec (Spec, describe, it)
import Test.Hspec.Golden (Golden (..))

listTooShortTerm :: Term
listTooShortTerm = TList [TInt 42]

huddleRangeArrayTermTwoStrings :: Term
huddleRangeArrayTermTwoStrings =
  TList
    [ TInt 0
    , TInt 1
    , TString "one"
    , TString "two"
    ]

refTermTooLong :: Term
refTermTooLong =
  TList
    [ TInt 0
    , TList
        [ TInt 1
        , TInt 2
        , TInt 3
        , TInt 4
        ]
    ]

choiceAlmostSecond :: Term
choiceAlmostSecond =
  TList
    [ TInt 1
    , TBool True
    , TInt 1
    ]

listSkippedRuleTerm :: Term
listSkippedRuleTerm = TList [TInt 1, TInt 2]

listSkippedRuleNestedTerm :: Term
listSkippedRuleNestedTerm = TList [TInt 1, TList [TInt 2, TInt 3]]

mapLeftoverKVTerm :: Term
mapLeftoverKVTerm = TMap [(TInt 2, TString "hello")]

mapNoMatchingKeyTerm :: Term
mapNoMatchingKeyTerm = TMap [(TInt 99, TString "hello")]

listZeroOrMoreTerm :: Term
listZeroOrMoreTerm = TList [TInt 1, TInt 2, TString "hello", TBool True]

mapNestedValueTerm :: Term
mapNestedValueTerm = TMap [(TInt 1, TList [TInt 2, TInt 3])]

cborControlBad :: Term
cborControlBad = TBytes . toStrictByteString $ encodeTerm (TList [TInt 1, TInt 2, TInt 4])

validatorPrettyGolden :: String -> Huddle -> Name -> Term -> Spec
validatorPrettyGolden testName huddle n term =
  it testName $
    Golden
      { goldenFile = "golden" </> testName <> ".txt"
      , readFromFile = T.readFile <=< getDataFileName
      , writeToFile = \fp txt -> getDataFileName fp >>= (`T.writeFile` txt)
      , actualFile = Nothing
      , output = str
      , encodePretty = T.unpack
      , failFirstTime = False
      }
  where
    bs = CBOR.toStrictByteString $ encodeTerm term
    treeRoot =
      fromRight (error "Failed to resolve CDDL") . fullResolveCDDL . mapCDDLDropExt $
        toCDDL huddle
    str =
      Ansi.renderStrict
        . layoutPretty defaultLayoutOptions
        . foldEvidenced (prettyStepTrace defaultTraceOptions)
        . validateCBOR_ bs n
        $ mapIndex treeRoot

spec :: Spec
spec = describe "golden" $ do
  describe "error messages" $ do
    validatorPrettyGolden
      "huddleRangeArrayTwoStrings"
      huddleRangeArray
      "a"
      huddleRangeArrayTermTwoStrings
    validatorPrettyGolden
      "refTermTooLong"
      refTermExample
      "root"
      refTermTooLong
    validatorPrettyGolden
      "choiceAlmostSecond"
      choicesExample
      "root"
      choiceAlmostSecond
    validatorPrettyGolden
      "cborControlBad"
      cborControlExample
      "root"
      cborControlBad
    validatorPrettyGolden
      "listTooShort"
      listTooShortExample
      "root"
      listTooShortTerm
    validatorPrettyGolden
      "listSkippedRule"
      listSkippedRuleExample
      "root"
      listSkippedRuleTerm
    validatorPrettyGolden
      "listSkippedRuleNested"
      listSkippedRuleNestedExample
      "root"
      listSkippedRuleNestedTerm
    validatorPrettyGolden
      "mapLeftoverKV"
      mapLeftoverKVExample
      "root"
      mapLeftoverKVTerm
    validatorPrettyGolden
      "mapNoMatchingKey"
      mapNoMatchingKeyExample
      "root"
      mapNoMatchingKeyTerm
    validatorPrettyGolden
      "listZeroOrMore"
      listZeroOrMoreExample
      "root"
      listZeroOrMoreTerm
    validatorPrettyGolden
      "mapNestedValue"
      mapNestedValueExample
      "root"
      mapNestedValueTerm
    -- Deeply nested refs competing against a rule that makes actual term
    -- progress. The stacked refs should NOT win over real term progress.
    validatorPrettyGolden
      "deeplyNestedRefVsRealProgress"
      deeplyNestedRefExample
      "root"
      (TList [TInt 1, TList [TInt 1, TString "hello"]])
