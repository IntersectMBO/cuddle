{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

module Main (main) where

import Codec.CBOR.Cuddle.CBOR.Gen (generateFromName)
import Codec.CBOR.Cuddle.CBOR.Validator
import Codec.CBOR.Cuddle.CBOR.Validator.Trace (
  Evidenced (..),
  SValidity (..),
  TraceOptions (..),
  prettyValidationTrace,
 )
import Codec.CBOR.Cuddle.CDDL (CDDL, Name (..), fromRules, sortCDDL)
import Codec.CBOR.Cuddle.CDDL.CTree (CTreeRoot)
import Codec.CBOR.Cuddle.CDDL.Custom.Generator (
  GenConfig (..),
  runCBORGen,
  twiddleAll,
  twiddleNothing,
 )
import Codec.CBOR.Cuddle.CDDL.Postlude (appendPostlude)
import Codec.CBOR.Cuddle.CDDL.Resolve (
  fullResolveCDDL,
 )
import Codec.CBOR.Cuddle.IndexMappable (IndexMappable (..), mapCDDLDropExt)
import Codec.CBOR.Cuddle.Parser (ParserStage, pCDDL)
import Codec.CBOR.Cuddle.Pretty (PrettyStage, renderCDDL)
import Codec.CBOR.FlatTerm (toFlatTerm)
import Codec.CBOR.Pretty (prettyHexEnc)
import Codec.CBOR.Read (deserialiseFromBytes)
import Codec.CBOR.Term (Term, decodeTerm, encodeTerm)
import Codec.CBOR.Write (toStrictByteString)
import Control.Monad (unless)
import Data.ByteString (ByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Base16 qualified as Base16
import Data.ByteString.Char8 qualified as BSC
import Data.ByteString.Lazy qualified as LBS
import Data.Char (isSpace)
import Data.IORef (newIORef)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)
import Data.Text.IO qualified as T
import Data.Version (showVersion)
import Options.Applicative
import Paths_cuddle (version)
import Prettyprinter (
  LayoutOptions (..),
  PageWidth (..),
  defaultLayoutOptions,
  layoutPretty,
  vsep,
 )
import Prettyprinter.Render.Terminal qualified as Ansi
import System.Exit (exitFailure, exitSuccess)
import System.IO (hPutStrLn, stderr)
import System.Random (newStdGen)
import System.Random.Stateful (IOGenM (..), Uniform (..))
import Test.AntiGen (zapAntiGen)
import Test.QuickCheck (Gen)
import Test.QuickCheck.Gen (Gen (..))
import Test.QuickCheck.Random (mkQCGen)
import Text.Megaparsec (ParseErrorBundle, Parsec, errorBundlePretty, runParser)

data Command
  = Format FormatOpts FilePath
  | Validate ValidateOpts FilePath
  | GenerateCBOR GenOpts FilePath
  | ValidateCBOR ValidateCBOROpts FilePath
  | FormatCBOR FormatCBOROpts FilePath

newtype ValidateOpts = ValidateOpts {vNoPrelude :: Bool}

pValidateOpts :: Parser ValidateOpts
pValidateOpts =
  ValidateOpts
    <$> switch
      ( long "no-prelude"
          <> help "Do not include the CDDL prelude."
      )

-- | Various formats for outputtting CBOR
data CBOROutputFormat
  = AsBinary
  | AsHex
  | AsDiagnostic
  | AsTerm
  | AsFlatTerm

outputFormatOptions :: Map String CBOROutputFormat
outputFormatOptions =
  Map.fromList
    [ ("binary", AsBinary)
    , ("hex", AsHex)
    , ("pretty", AsDiagnostic)
    , ("diagnostic", AsDiagnostic)
    , ("term", AsTerm)
    , ("flat", AsFlatTerm)
    ]

pCBOROutputFormat :: ReadM CBOROutputFormat
pCBOROutputFormat = eitherReader $ \k ->
  case Map.lookup k outputFormatOptions of
    Just x -> Right x
    Nothing ->
      Left $
        unlines
          [ "invalid value: " <> k
          , "expecting one of: " <> unwords (Map.keys outputFormatOptions)
          ]

data GenOpts = GenOpts
  { outputFormat :: CBOROutputFormat
  , outputTo :: Maybe String
  , gNoPrelude :: Bool
  , goSeed :: Maybe Int
  , goSize :: Int
  , goNegative :: Bool
  , goTwiddle :: Bool
  , itemName :: T.Text
  }

pGenOpts :: Parser GenOpts
pGenOpts =
  GenOpts
    <$> option
      pCBOROutputFormat
      ( long "format"
          <> short 'f'
          <> help "Output format"
          <> value AsHex
          <> completeWith (Map.keys outputFormatOptions)
      )
    <*> optional
      ( strOption
          ( long "out-file"
              <> short 'o'
              <> help "Write to"
              <> action "file"
          )
      )
    <*> switch
      ( long "no-prelude"
          <> help "Do not include the CDDL prelude."
      )
    <*> optional
      ( option auto $
          long "seed"
            <> short 's'
            <> help "Generator seed"
      )
    <*> option
      auto
      ( long "size"
          <> help "Generator size"
          <> value 30
      )
    <*> switch
      ( long "negative"
          <> short 'n'
          <> help "Generate a negative (zapped) example"
      )
    <*> ( not
            <$> switch
              ( long "no-twiddle"
                  <> help "Do not generate indefinite encodings"
              )
        )
    <*> argument
      str
      (metavar "RULE" <> help "Name of the CDDL rule to generate a CBOR term for")

newtype FormatOpts = FormatOpts
  {sort :: Bool}

pFormatOpts :: Parser FormatOpts
pFormatOpts =
  FormatOpts
    <$> switch
      ( long "sort-rules"
          <> help "Sort the CDDL rule definitions before printing."
      )

data ValidateCBOROpts = ValidateCBOROpts
  { vcNoPrelude :: Bool
  , vcInputFormat :: CBORInputFormat
  , vcTraceOpts :: TraceOptions
  , vcItemName :: T.Text
  , vcInput :: FilePath
  }

pTraceOpts :: Parser TraceOptions
pTraceOpts =
  TraceOptions
    <$> flag
      True
      False
      ( long "no-fold-valid"
          <> help "Do not squash valid elements in lists/maps when printing validation trace"
      )

pValidateCBOROpts :: Parser ValidateCBOROpts
pValidateCBOROpts =
  ValidateCBOROpts
    <$> switch
      ( long "no-prelude"
          <> help "Do not include the CDDL prelude."
      )
    <*> option
      pCBORInputFormat
      ( long "format"
          <> short 'f'
          <> help "Output format"
          <> completeWith (Map.keys inputFormatOptions)
      )
    <*> pTraceOpts
    <*> argument
      str
      ( metavar "RULE"
          <> help "Name of the CDDL rule to validate this file with"
      )
    <*> argument str (metavar "CBOR_FILE" <> action "file")

data CBORInputFormat
  = FromHex
  | FromBinary

inputFormatOptions :: Map String CBORInputFormat
inputFormatOptions =
  Map.fromList
    [ ("hex", FromHex)
    , ("binary", FromBinary)
    ]

data FormatCBOROpts = FormatCBOROpts
  { dcInputFormat :: CBORInputFormat
  , dcOutputFormat :: CBOROutputFormat
  , dcOutputFile :: Maybe FilePath
  }

pCBORInputFormat :: ReadM CBORInputFormat
pCBORInputFormat = eitherReader $ \k -> case Map.lookup k inputFormatOptions of
  Just x -> Right x
  Nothing ->
    Left $
      unlines
        [ "invalid value: " <> k
        , "expecting one of: " <> unwords (Map.keys inputFormatOptions)
        ]

pFormatCBOROpts :: Parser FormatCBOROpts
pFormatCBOROpts =
  FormatCBOROpts
    <$> option
      pCBORInputFormat
      ( long "fin"
          <> help "Input format"
          <> value FromBinary
          <> completeWith (Map.keys inputFormatOptions)
      )
    <*> option
      pCBOROutputFormat
      ( long "fout"
          <> help "Output format"
          <> value AsDiagnostic
          <> completeWith (Map.keys outputFormatOptions)
      )
    <*> optional
      ( strOption
          ( long "out-file"
              <> short 'o'
              <> help "Write to"
              <> action "file"
          )
      )

pCommand :: Parser Command
pCommand =
  subparser
    ( command
        "format"
        ( info
            (Format <$> pFormatOpts <*> argument str (metavar "CDDL_FILE" <> action "file") <**> helper)
            (progDesc "Format the provided CDDL file")
        )
        <> command
          "validate"
          ( info
              (Validate <$> pValidateOpts <*> argument str (metavar "CDDL_FILE" <> action "file") <**> helper)
              (progDesc "Validate the provided CDDL file")
          )
        <> command
          "gen"
          ( info
              (GenerateCBOR <$> pGenOpts <*> argument str (metavar "CDDL_FILE" <> action "file") <**> helper)
              (progDesc "Generate a CBOR term matching the schema")
          )
        <> command
          "validate-cbor"
          ( info
              ( ValidateCBOR
                  <$> pValidateCBOROpts
                  <*> argument str (metavar "CDDL_FILE" <> action "file") <**> helper
              )
              (progDesc "Validate a CBOR file against a schema")
          )
        <> command
          "format-cbor"
          ( info
              (FormatCBOR <$> pFormatCBOROpts <*> argument str (metavar "CBOR_FILE" <> action "file") <**> helper)
              (progDesc "Output a CBOR binary in diagnostic formatting")
          )
    )

main :: IO ()
main = do
  options <-
    execParser $
      info
        (pCommand <**> helper <**> simpleVersioner (showVersion version))
        ( fullDesc
            <> progDesc "Manipulate CDDL files"
            <> header "cuddle - a CDDL tool for validating, formatting, and generating CBOR"
            <> footerDoc
              ( Just $
                  vsep
                    [ "To enable shell completions, add the appropriate line to your shell config:"
                    , "  Bash: source <(cuddle --bash-completion-script cuddle)"
                    , "  Zsh:  source <(cuddle --zsh-completion-script cuddle)"
                    , "  Fish: cuddle --fish-completion-script cuddle | source"
                    ]
              )
        )
  run options

tryParseFromFile :: FilePath -> IO (CDDL ParserStage)
tryParseFromFile cddlFile =
  parseFromFile pCDDL cddlFile >>= \case
    Left err -> do
      putStrLnErr $ errorBundlePretty err
      exitFailure
    Right res -> pure res

formatTerm :: Term -> CBOROutputFormat -> ByteString
formatTerm term = \case
  AsTerm -> encodeUtf8 . T.pack $ show term
  AsFlatTerm -> encodeUtf8 . T.pack . show . toFlatTerm $ encodeTerm term
  AsBinary -> toStrictByteString $ encodeTerm term
  AsHex -> Base16.encode . toStrictByteString $ encodeTerm term
  AsDiagnostic -> encodeUtf8 . T.pack . prettyHexEnc $ encodeTerm term

runGen :: Int -> Int -> Gen a -> a
runGen seed size gen = unGen gen (mkQCGen seed) size

tryReadCBOR :: CBORInputFormat -> FilePath -> IO ByteString
tryReadCBOR format path = do
  contentsRaw <- BS.readFile path
  case format of
    FromBinary -> pure contentsRaw
    FromHex -> case Base16.decode . BSC.filter (not . isSpace) $ contentsRaw of
      Right x -> pure x
      Left err -> putStrLnErr (show err <> " when decoding hex input") >> exitFailure

run :: Command -> IO ()
run = \case
  Format fOpts cddlFile -> do
    res <- tryParseFromFile cddlFile
    let
      defs
        | sort fOpts = fromRules $ sortCDDL res
        | otherwise = res
      layoutOptions = defaultLayoutOptions {layoutPageWidth = AvailablePerLine 80 1}
      formattedText = renderCDDL layoutOptions $ mapIndex @_ @_ @PrettyStage defs
    T.putStr formattedText
  Validate vOpts cddlFile -> do
    res <- tryParseFromFile cddlFile
    let
      cddl
        | vNoPrelude vOpts = res
        | otherwise = appendPostlude res
    case fullResolveCDDL $ mapCDDLDropExt cddl of
      Left err -> putStrLnErr (show err) >> exitFailure
      Right _ -> exitSuccess
  GenerateCBOR GenOpts {..} cddlFile -> do
    res <- tryParseFromFile cddlFile
    let
      cddl
        | gNoPrelude = res
        | otherwise = appendPostlude res
    case fullResolveCDDL $ mapCDDLDropExt cddl of
      Left err -> putStrLnErr (show err) >> exitFailure
      Right mt -> do
        seed <- case goSeed of
          Just s -> pure s
          Nothing -> uniformM . IOGenM =<< newIORef =<< newStdGen
        let
          zapN
            | goNegative = 1
            | otherwise = 0
          cfg =
            GenConfig
              { gcRoot = mapIndex mt
              , gcTwiddle = if goTwiddle then twiddleAll else twiddleNothing
              }
          term = runGen seed goSize . zapAntiGen zapN . runCBORGen cfg $ generateFromName (Name itemName)
          formatted = formatTerm term outputFormat
        case outputTo of
          Just outputPath -> BS.writeFile outputPath formatted
          Nothing -> BSC.putStrLn formatted
        putStrLnErr $ "seed: " <> show seed
  ValidateCBOR ValidateCBOROpts {..} cddlFile -> do
    res <- tryParseFromFile cddlFile
    let
      cddl
        | vcNoPrelude = res
        | otherwise = appendPostlude res
    case fullResolveCDDL $ mapCDDLDropExt cddl of
      Left err -> putStrLnErr (show err) >> exitFailure
      Right mt -> do
        cbor <- BS.readFile vcInput
        runValidateCBOR cbor (Name vcItemName) (mapIndex mt) vcTraceOpts
  FormatCBOR FormatCBOROpts {..} cborFile -> do
    contents <- tryReadCBOR dcInputFormat cborFile
    term <- case deserialiseFromBytes decodeTerm (LBS.fromStrict contents) of
      Right (leftover, term) -> do
        unless (LBS.null leftover) . putStrLnErr $
          "Warning: " <> show (LBS.length leftover) <> " leftover bytes after decoding"
        pure term
      Left err -> putStrLnErr (show err) >> exitFailure
    let
      formatted = formatTerm term dcOutputFormat
    case dcOutputFile of
      Just outputPath -> BS.writeFile outputPath formatted
      Nothing -> BSC.putStrLn formatted

putStrLnErr :: String -> IO ()
putStrLnErr = hPutStrLn stderr

parseFromFile ::
  Parsec e T.Text a ->
  String ->
  IO (Either (ParseErrorBundle T.Text e) a)
parseFromFile p file = runParser p file <$> T.readFile file

runValidateCBOR :: BS.ByteString -> Name -> CTreeRoot ValidatorPhase -> TraceOptions -> IO ()
runValidateCBOR bs rule cddl traceOpts =
  case validateCBOR bs rule cddl of
    Left err -> do
      putStrLnErr $ "CBOR validation failed:\n" <> show err
      exitFailure
    Right (Evidenced validity trc) -> do
      T.putStrLn . Ansi.renderStrict . layoutPretty defaultLayoutOptions $
        prettyValidationTrace traceOpts trc
      putStrLn mempty
      case validity of
        SValid -> do
          putStrLn "Validation successful"
          exitSuccess
        SInvalid -> do
          putStrLn "Validation failed"
          exitFailure
