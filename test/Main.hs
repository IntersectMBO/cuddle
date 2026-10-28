module Main (main) where

import System.IO (BufferMode (..), hSetBuffering, hSetEncoding, stdout, utf8)
import Test.Codec.CBOR.Cuddle.CBOR.Canonical qualified as Canonical
import Test.Codec.CBOR.Cuddle.CDDL.Custom.GeneratorSpec qualified as CustomGenerator
import Test.Codec.CBOR.Cuddle.CDDL.Custom.ValidatorSpec qualified as CustomValidator
import Test.Codec.CBOR.Cuddle.CDDL.Examples qualified as Examples
import Test.Codec.CBOR.Cuddle.CDDL.GeneratorSpec qualified as Generator
import Test.Codec.CBOR.Cuddle.CDDL.Parser (parserSpec)
import Test.Codec.CBOR.Cuddle.CDDL.Pretty (roundtripSpec)
import Test.Codec.CBOR.Cuddle.CDDL.Pretty.Golden qualified as PrettyGolden
import Test.Codec.CBOR.Cuddle.CDDL.Validator qualified as Validator
import Test.Codec.CBOR.Cuddle.CDDL.Validator.Golden qualified as ValidatorGolden
import Test.Codec.CBOR.Cuddle.Huddle (huddleSpec)
import Test.Hspec
import Test.Hspec.Runner

hspecConfig :: Config
hspecConfig =
  defaultConfig
    { configColorMode = ColorAlways
    }

main :: IO ()
main = do
  hSetBuffering stdout LineBuffering
  hSetEncoding stdout utf8
  hspecWith hspecConfig $ do
    describe "Canonical" Canonical.spec
    describe "Parser" parserSpec
    describe "Huddle" huddleSpec
    describe "Examples" Examples.spec
    describe "Generator" Generator.spec
    describe "Custom" $ do
      describe "Generator" CustomGenerator.spec
      describe "Validator" CustomValidator.spec
    describe "Pretty" $ do
      describe "Golden" PrettyGolden.spec
      describe "Roundtrip" roundtripSpec
    describe "Validator" $ do
      describe "Properties" Validator.spec
      describe "Golden" ValidatorGolden.spec
