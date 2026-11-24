{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}

module Codec.CBOR.Cuddle.Parser where

import Codec.CBOR.Cuddle.CDDL
import Codec.CBOR.Cuddle.CDDL.CtlOp (CtlOp)
import Codec.CBOR.Cuddle.CDDL.CtlOp qualified as COp
import Codec.CBOR.Cuddle.Comments (
  Comment,
  HasComment (..),
  WithComment (..),
  appendComment,
  withComment,
  (!*>),
  (<*!),
 )
import Codec.CBOR.Cuddle.IndexMappable (IndexMappable)
import Codec.CBOR.Cuddle.Parser.Lexer (
  Parser,
  charInRange,
  pCommentBlock,
  space,
  trailingSpace,
 )
import Control.Applicative.Combinators.NonEmpty qualified as NE
import Data.ByteString.Base16 qualified as Base16
import Data.Foldable (Foldable (..))
import Data.Functor (void, ($>))
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Maybe (isJust)
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Encoding (encodeUtf8)
import Data.Void (Void)
import GHC.Generics (Generic)
import GHC.Word (Word64, Word8)
import Optics.Core ((&), (.~))
import Text.Megaparsec
import Text.Megaparsec.Char hiding (space)
import Text.Megaparsec.Char qualified as C
import Text.Megaparsec.Char.Lexer qualified as L

type data ParserStage

newtype instance XXTopLevel ParserStage = ParserXXTopLevel Comment
  deriving (Generic, Show, Eq)

newtype instance XXType2 ParserStage = ParserXXType2 Void
  deriving (Generic, Show, Eq)

newtype instance XTerm ParserStage = ParserXTerm {unParserXTerm :: Comment}
  deriving (Generic, Semigroup, Monoid, Show, Eq)

newtype instance XRule ParserStage = ParserXRule {unParserXRule :: Comment}
  deriving (Generic, Semigroup, Monoid, Show, Eq)

newtype instance XCddl ParserStage = ParserXCddl [Comment]
  deriving (Generic, Semigroup, Monoid, Show, Eq)

instance HasComment (XTerm ParserStage) where
  commentL = #unParserXTerm

instance HasComment (XRule ParserStage) where
  commentL = #unParserXRule

pCDDL :: Parser (CDDL ParserStage)
pCDDL = do
  initialComments <- many (try $ C.space *> pCommentBlock <* notFollowedBy pRule)
  initialRuleComment <- C.space *> optional pCommentBlock
  initialRule <- pRule
  cddlTail <- many $ pTopLevel <* C.space
  eof
    $> CDDL
      (appendComment initialRule (fold initialRuleComment))
      cddlTail
      (ParserXXTopLevel <$> initialComments)

pTopLevel :: Parser (TopLevel ParserStage)
pTopLevel = try tlRule <|> tlComment
  where
    tlRule = do
      mCmt <- optional pCommentBlock
      rule <- pRule
      pure . TopLevelRule $ appendComment rule (fold mCmt)
    tlComment = XXTopLevel . ParserXXTopLevel <$> pCommentBlock

pRule :: Parser (Rule ParserStage)
pRule = do
  name <- pName
  genericParam <- optcomp pGenericParameters
  cmt <- space
  (assign, typeOrGrp) <-
    choice
      [ try $
          (,)
            <$> pAssignT
            <* space
            <*> (TOGType <$> pType0 <* notFollowedBy (space >> (":" <|> "=>")))
      , (,) <$> pAssignG <* space <*> (TOGGroup <$> pGrpEntry)
      ]
  pure $ Rule name genericParam assign typeOrGrp (ParserXRule cmt)

pName :: Parser Name
pName = label "name" $ do
  fc <- firstChar
  rest <- many midChar
  pure $ Name . T.pack $ (fc : rest)
  where
    firstChar = letterChar <|> char '@' <|> char '_' <|> char '$'
    midChar =
      alphaNumChar
        <|> char '@'
        <|> char '_'
        <|> char '$'
        <|> ((char '.' <|> char '-') <* notFollowedBy (space1 <|> eof <|> void eol))

pAssignT :: Parser Assign
pAssignT =
  choice
    [ AssignEq <$ "="
    , AssignExt <$ "/="
    ]

pAssignG :: Parser Assign
pAssignG =
  choice
    [ AssignEq <$ "="
    , AssignExt <$ "//="
    ]

pGenericParameter :: Parser (GenericParameter ParserStage)
pGenericParameter = GenericParameter <$> pName <*> pure mempty

pGenericParameters :: Parser (GenericParameters ParserStage)
pGenericParameters =
  GenericParameters
    <$> between "<" ">" (NE.sepBy1 (space !*> pGenericParameter <*! space) ",")

pGenericArg :: Parser (GenericArg ParserStage)
pGenericArg =
  GenericArg
    <$> between "<" ">" (NE.sepBy1 (space !*> pType1 <*! space) ",")

pType0 :: Parser (Type0 ParserStage)
pType0 = Type0 <$> sepBy1' (space !*> pType1 <*! trailingSpace) (try "/")

pType1 :: Parser (Type1 ParserStage)
pType1 = do
  v <- pType2
  rest <- optional $ do
    (cmtFst, tyOp) <- try $ do
      cmt <- space
      tyOp <- pTyOp
      pure (cmt, tyOp)
    cmtSnd <- space
    w <- pType2
    pure (cmtFst, tyOp, cmtSnd, w)
  case rest of
    Just (cmtFst, tyOp, cmtSnd, w) ->
      pure $ Type1 v (Just (tyOp, w)) . ParserXTerm $ cmtFst <> cmtSnd
    Nothing -> pure $ Type1 v Nothing mempty

pType2 :: Parser (Type2 ParserStage)
pType2 =
  choice
    [ T2Value <$> pValue
    , T2Name <$> pName <*> optional pGenericArg
    , T2Group <$> label "group" ("(" *> pType0Cmt <* ")")
    , T2Map <$> label "map" ("{" *> pGroup <* "}")
    , T2Array <$> label "array" ("[" *> space !*> pGroup <*! space <* "]")
    , T2Unwrapped <$> ("~" *> space *> pName) <*> optional pGenericArg
    , do
        _ <- "&"
        cmt <- space
        choice
          [ T2Enum <$> ("(" *> space !*> pGroup <*! pure cmt <*! space <* ")")
          , T2EnumRef <$> pName <*> optional pGenericArg
          ]
    , "#" *> do
        mmajor :: Maybe Word8 <- optional L.decimal
        case mmajor of
          Just major -> do
            mminor <- optional ("." *> L.decimal)
            let
              pTag
                | major == 6 = T2Tag mminor <$> ("(" *> pType0Cmt <* ")")
                | otherwise = empty
            pTag <|> pure (T2DataItem major mminor)
          Nothing -> pure T2Any
    ]
  where
    pType0Cmt = do
      pre <- space
      Type0 (t :| ts) <- pType0
      post <- space
      pure . Type0 $ (t & commentL .~ (pre <> post)) :| ts

pHeadNumber :: Parser Word64
pHeadNumber = L.decimal

pRangeOp :: Parser RangeBound
pRangeOp = label "range operator" $ try ("..." $> ClOpen) <|> (".." $> Closed)

pCtlOp :: Parser CtlOp
pCtlOp =
  label "control operator" $
    "."
      *> choice
        ( try
            <$> [ "cborseq" $> COp.Cborseq
                , "cbor" $> COp.Cbor
                , "size" $> COp.Size
                , "bits" $> COp.Bits
                , "within" $> COp.Within
                , "and" $> COp.And
                , "lt" $> COp.Lt
                , "le" $> COp.Le
                , "gt" $> COp.Gt
                , "ge" $> COp.Ge
                , "eq" $> COp.Eq
                , "ne" $> COp.Ne
                , "default" $> COp.Default
                , "regexp" $> COp.Regexp
                ]
        )

pGroup :: Parser (Group ParserStage)
pGroup = Group <$> NE.sepBy1 (space !*> pGrpChoice) "//"

pGrpChoice :: Parser (GrpChoice ParserStage)
pGrpChoice = GrpChoice <$> many (space !*> pGrpEntry <*! pOptCom) <*> mempty

pGrpEntry :: Parser (GroupEntry ParserStage)
pGrpEntry = do
  occur <- optcomp pOccur
  cmt <- space
  WithComment cmt' variant <-
    choice
      [ try $ do
          mKey <- optcomp $ pMemberKey <*! space
          t0 <- pType0
          pure $ GEType <$> sequence mKey <*> pure t0
      , try $ withComment <$> (GERef <$> pName <*> optional pGenericArg)
      , withComment . GEGroup <$> ("(" *> space !*> pGroup <*! space <* ")")
      ]
  pure $ GroupEntry occur variant (ParserXTerm $ cmt <> cmt')

pMemberKey :: Parser (WithComment (MemberKey ParserStage))
pMemberKey =
  choice
    [ try $ do
        t1 <- pType1
        cmt0 <- space
        cmt1 <- fold <$> optcomp ("^" *> space) <* "=>"
        pure $ WithComment (cmt0 <> cmt1) (MKType t1)
    , try $ do
        name <- pName
        cmt <- space
        _ <- ":"
        pure . WithComment cmt $ MKBareword name
    , do
        val <- pValue
        cmt <- space
        _ <- ":"
        pure . WithComment cmt $ MKValue val
    ]

pOptCom :: Parser Comment
pOptCom = space <*! (fold <$> optional ("," >> space))

pOccur :: Parser OccurrenceIndicator
pOccur =
  label "occurrence indicator" $
    choice
      [ char '+' $> OIOneOrMore
      , char '?' $> OIOptional
      , pBounded
      ]

pValue :: Parser Value
pValue =
  label "value" $
    (`Value` mempty)
      <$> choice
        [ try pFloat
        , try pInt
        , try pBytes
        , pText
        , try pBool
        ]
  where
    pSignedNum :: Num a => Parser a -> Parser (Bool, a)
    pSignedNum valParser = do
      sign <- optional "-"
      val <- valParser <* notFollowedBy "*"
      pure (isJust sign, val)
    -- Need to ensure that number values are not actually bounds on a later
    -- value.
    pInt =
      pSignedNum L.decimal >>= \case
        (False, val)
          | val <= fromIntegral (maxBound @Word64) -> pure . VUInt $ fromIntegral val
          | otherwise -> pure $ VBignum val
        (True, val)
          | val <= fromIntegral (maxBound @Word64) -> pure . VNInt $ fromIntegral val
          | otherwise -> pure . VBignum $ -val
    pFloat =
      pSignedNum L.float >>= \case
        (False, val) -> pure $ VFloat64 val
        (True, val) -> pure . VFloat64 $ negate val
    -- Currently this doesn't allow string escaping
    pSChar :: Parser Text
    pSChar = takeWhileP (Just "character") $ \x ->
      or $
        [ charInRange '\x20' '\x21'
        , charInRange '\x23' '\x5b'
        , charInRange '\x5d' '\x7e'
        , charInRange '\x80' '\x10fffd'
        ]
          <*> pure x
    pText = VText <$> ("\"" *> pSChar <* "\"")
    pSByte = takeWhileP (Just "byte character") $ \x ->
      or $
        [ charInRange '\x20' '\x26'
        , charInRange '\x28' '\x5b'
        , charInRange '\x5d' '\x10fffd'
        ]
          <*> pure x
    pBytes = do
      _qualifier <- optional ("h" <|> "b64")
      bytes <- between "'" "'" pSByte
      case Base16.decode $ encodeUtf8 bytes of
        Right x -> pure $ VBytes x
        Left err -> fail err
    pBool = label "boolean" $ do
      b <-
        (True <$ string "true")
          <|> (False <$ string "false")
      pure $ VBool b

pTyOp :: Parser TyOp
pTyOp =
  choice
    [ try $ RangeOp <$> pRangeOp
    , CtrlOp <$> pCtlOp
    ]

pBounded :: Parser OccurrenceIndicator
pBounded = do
  lo <- optional L.decimal
  _ <- char '*'
  hi <- optional L.decimal
  pure $ case (lo, hi) of
    (Nothing, Nothing) -> OIZeroOrMore
    (x, y) -> OIBounded x y

-- | A variant of 'optional' for composite parsers, which will consume no input
-- if it fails.
optcomp :: MonadParsec e s f => f a -> f (Maybe a)
optcomp = optional . try

{-
cddl = S *(rule S)
rule = typename [genericparm] S assignt S type
     / groupname [genericparm] S assigng S grpent

typename = id
groupname = id

assignt = "=" / "/="
assigng = "=" / "//="

genericparm = "<" S id S *("," S id S ) ">"
genericarg = "<" S type1 S *("," S type1 S ) ">"

type = type1 *(S "/" S type1)

type1 = type2 [S (rangeop / ctlop) S type2]
; space may be needed before the operator if type2 ends in a name

type2 = value
      / typename [genericarg]
      / "(" S type S ")"
      / "{" S group S "}"
      / "[" S group S "]"
      / "~" S typename [genericarg]
      / "&" S "(" S group S ")"
      / "&" S groupname [genericarg]
      / "#" "6" ["." head-number] "(" S type S ")"
      / "#" "7" ["." head-number]
      / "#" DIGIT ["." uint]                ; major/ai
      / "#"                                 ; any
head-number = uint / ("<" type ">")

rangeop = "..." / ".."

ctlop = "." id

group = grpchoice *(S "//" S grpchoice)

grpchoice = *(grpent optcom)

grpent = [occur S] [memberkey S] type
       / [occur S] groupname [genericarg]  ; preempted by above
       / [occur S] "(" S group S ")"

memberkey = type1 S ["^" S] "=>"
          / bareword S ":"
          / value S ":"

bareword = id

optcom = S ["," S]

occur = [uint] "*" [uint]
      / "+"
      / "?"

uint = DIGIT1 *DIGIT
     / "0x" 1*HEXDIG
     / "0b" 1*BINDIG
     / "0"

value = number
      / text
      / bytes

int = ["-"] uint

; This is a float if it has fraction or exponent; int otherwise
number = hexfloat / (int ["." fraction] ["e" exponent ])
hexfloat = ["-"] "0x" 1*HEXDIG ["." 1*HEXDIG] "p" exponent
fraction = 1*DIGIT
exponent = ["+"/"-"] 1*DIGIT

text = %x22 *SCHAR %x22
SCHAR = %x20-21 / %x23-5B / %x5D-7E / NONASCII / SESC

SESC = "\" ( %x22 / "/" / "\" /                 ; \" \/ \\
             %x62 / %x66 / %x6E / %x72 / %x74 / ; \b \f \n \r \t
             (%x75 hexchar) )                   ; \uXXXX

hexchar = "{" (1*"0" [ hexscalar ] / hexscalar) "}" /
          non-surrogate / (high-surrogate "\" %x75 low-surrogate)
non-surrogate = ((DIGIT / "A"/"B"/"C" / "E"/"F") 3HEXDIG) /
                ("D" %x30-37 2HEXDIG )
high-surrogate = "D" ("8"/"9"/"A"/"B") 2HEXDIG
low-surrogate = "D" ("C"/"D"/"E"/"F") 2HEXDIG
hexscalar = "10" 4HEXDIG / HEXDIG1 4HEXDIG
          / non-surrogate / 1*3HEXDIG

bytes = [bsqual] %x27 *BCHAR %x27
BCHAR = %x20-26 / %x28-5B / %x5D-7E / NONASCII / SESC / "\'" / CRLF
bsqual = "h" / "b64"

id = EALPHA *(*("-" / ".") (EALPHA / DIGIT))
ALPHA = %x41-5A / %x61-7A
EALPHA = ALPHA / "@" / "_" / "$"
DIGIT = %x30-39
DIGIT1 = %x31-39
HEXDIG = DIGIT / "A" / "B" / "C" / "D" / "E" / "F"
HEXDIG1 = DIGIT1 / "A" / "B" / "C" / "D" / "E" / "F"
BINDIG = %x30-31

S = *WS
WS = SP / NL
SP = %x20
NL = COMMENT / CRLF
COMMENT = ";" *PCHAR CRLF
PCHAR = %x20-7E / NONASCII
NONASCII = %xA0-D7FF / %xE000-10FFFD
CRLF = %x0A / %x0D.0A
-}

-- | Variant on 'NE.sepEndBy1' which doesn't consume the separator
sepBy1' :: MonadParsec e s m => m a -> m sep -> m (NonEmpty a)
sepBy1' p sep = NE.fromList <$> go
  where
    go = liftA2 (:) p (many (try $ sep *> p))

-- * IndexMappable

-- ParserStage ~ ParserStage

instance IndexMappable XCddl ParserStage ParserStage

instance IndexMappable XXTopLevel ParserStage ParserStage

instance IndexMappable XXType2 ParserStage ParserStage

instance IndexMappable XTerm ParserStage ParserStage

instance IndexMappable XRule ParserStage ParserStage
