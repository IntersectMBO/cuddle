{-# LANGUAGE OverloadedStrings #-}

module Test.Codec.CBOR.Cuddle.CDDL.Examples (spec) where

import Codec.CBOR.Cuddle.CDDL (Value (..), ValueVariant (..), mapCDDLDropExt)
import Codec.CBOR.Cuddle.CDDL.CTree (CTree (..), CTreeRoot, PTerm (..))
import Codec.CBOR.Cuddle.CDDL.Postlude (appendPostlude)
import Codec.CBOR.Cuddle.CDDL.Resolve (
  MonoReferenced,
  NameResolutionFailure (..),
  fullResolveCDDL,
 )
import Codec.CBOR.Cuddle.Parser (pCDDL)
import Data.Text.IO qualified as T
import Paths_cuddle (getDataFileName)
import Test.HUnit (assertFailure)
import Test.Hspec
import Text.Megaparsec (parse)
import Text.Megaparsec.Error (errorBundlePretty)

tryValidateFile :: FilePath -> IO (Either NameResolutionFailure (CTreeRoot MonoReferenced))
tryValidateFile filePath = do
  absoluteFilePath <- getDataFileName filePath
  contents <- T.readFile absoluteFilePath
  cddl <- case parse pCDDL "" contents of
    Right x -> pure $ appendPostlude x
    Left x -> fail $ "Failed to parse the file:\n" <> errorBundlePretty x
  pure . fullResolveCDDL $ mapCDDLDropExt cddl

validateExpectSuccess :: FilePath -> Spec
validateExpectSuccess filePath = it ("Successfully validates " <> filePath) $ do
  res <- tryValidateFile filePath
  case res of
    Right _ -> pure ()
    Left err -> assertFailure $ "Failed to validate:\n" <> show err

validateExpectFailure :: FilePath -> NameResolutionFailure -> Spec
validateExpectFailure filePath expectedFailure = it ("Fails to validate " <> filePath) $ do
  res <- tryValidateFile filePath
  case res of
    Right _ -> assertFailure "Expected a failure, but succeeded instead"
    Left e -> e `shouldBe` expectedFailure

spec :: Spec
spec = do
  describe "Validator" $ do
    describe "Positive" $ do
      validateExpectSuccess "cddl/byron.cddl"
      validateExpectSuccess "cddl/conway.cddl"
      validateExpectSuccess "cddl/shelley.cddl"
      validateExpectSuccess "cddl/basic_assign.cddl"
      validateExpectSuccess "cddl/issue80-min.cddl"
      validateExpectSuccess "cddl/pretty.cddl"
    describe "Negative" $ do
      validateExpectFailure "cddl/validator/negative/unknown-name.cddl" $
        UnboundReference "a"
      validateExpectFailure "cddl/validator/negative/too-few-args.cddl" $
        MismatchingArgs "foo" ["a", "b"]
      validateExpectFailure "cddl/validator/negative/too-many-args.cddl" $
        MismatchingArgs "foo" ["a"]
      validateExpectFailure "cddl/validator/negative/args-to-postlude.cddl" $
        ArgsToPostlude PTUInt [Literal (Value (VUInt 3) mempty)]
