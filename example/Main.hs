{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Codec.CBOR.Cuddle.CBOR.Gen (generateFromName)
import Codec.CBOR.Cuddle.CDDL (Name (..))
import Codec.CBOR.Cuddle.CDDL.Custom.Generator (GenConfig (..), runCBORGen, twiddleAll)
import Codec.CBOR.Cuddle.CDDL.Resolve (MonoSimplePhase, fullResolveCDDL)
import Codec.CBOR.Cuddle.Huddle (toCDDL)
import Codec.CBOR.Cuddle.IndexMappable (IndexMappable (..), mapCDDLDropExt)
import Codec.CBOR.Cuddle.Parser (pCDDL)
import Codec.CBOR.Cuddle.Pretty (PrettyStage)
import Conway (conway)
import Data.Text qualified as T
import Data.Text.IO qualified as T
import Prettyprinter (Pretty (pretty))
import Prettyprinter.Util (putDocW)
import System.Environment (getArgs)
import Test.AntiGen (runAntiGen)
import Test.QuickCheck (generate)
import Text.Megaparsec (ParseErrorBundle, Parsec, errorBundlePretty, runParser)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [fn] -> do
      parseFromFile pCDDL fn >>= \case
        Left err -> putStrLn $ errorBundlePretty err
        Right res -> do
          putDocW 80 $ pretty (mapIndex @_ @_ @PrettyStage res)
          putStrLn "\n"
          putStrLn "--------------------------------------------------------------------------------"
          putStrLn " Resolving"
          putStrLn "--------------------------------------------------------------------------------"
          case fullResolveCDDL (mapCDDLDropExt res) of
            Left nre -> putStrLn $ "Resolution error: " <> show nre
            Right resolved -> print (mapIndex @_ @_ @MonoSimplePhase resolved)
    [fn, name] -> do
      putStrLn "--------------------------------------------------------------------------------"
      putStrLn " Generating a term"
      putStrLn "--------------------------------------------------------------------------------"
      parseFromFile pCDDL fn >>= \case
        Left err -> putStrLn $ errorBundlePretty err
        Right res -> do
          case fullResolveCDDL (mapCDDLDropExt res) of
            Left nre -> error $ show nre
            Right resolved -> do
              let cfg = GenConfig {gcRoot = mapIndex resolved, gcTwiddle = twiddleAll}
              term <- generate . runAntiGen . runCBORGen cfg $ generateFromName (Name (T.pack name))
              print term
    [] -> do
      let cw = toCDDL conway
      putDocW 80 $ pretty (mapIndex @_ @_ @PrettyStage cw)
    _ -> putStrLn "Expected filename"

parseFromFile ::
  Parsec e T.Text a ->
  String ->
  IO (Either (ParseErrorBundle T.Text e) a)
parseFromFile p file = runParser p file <$> T.readFile file
