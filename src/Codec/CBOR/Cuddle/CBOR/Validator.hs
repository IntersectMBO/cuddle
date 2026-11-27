{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Codec.CBOR.Cuddle.CBOR.Validator (
  validateCBOR,
  validateFromName,
  validateFromGRef,
  validateTerm,
  ValidatorPhase,
  ValidateCBORError (..),
) where

import Codec.CBOR.Cuddle.CBOR.Canonical (toCanonical)
import Codec.CBOR.Cuddle.CDDL hiding (CDDL, Group, Rule)
import Codec.CBOR.Cuddle.CDDL.CTree
import Codec.CBOR.Cuddle.CDDL.CtlOp
import Codec.CBOR.Cuddle.CDDL.Custom.Core (
  MonadCddl (..),
  evalBool,
  evalBytes,
  evalDouble,
  evalInteger,
  evalInterval,
  evalText,
 )
import Codec.CBOR.Cuddle.CDDL.Custom.Validator
import Codec.CBOR.Cuddle.CDDL.Phase (MonoSimplePhase, showSimple)
import Codec.CBOR.Cuddle.IndexMappable (IndexMappable (..))
import Codec.CBOR.Cuddle.Interval ((...))
import Codec.CBOR.Cuddle.Interval qualified as Interval
import Codec.CBOR.Read
import Codec.CBOR.Term
import Control.Applicative (Alternative (..), optional)
import Control.Monad (filterM, void)
import Data.Bits hiding (And)
import Data.ByteString qualified as BS
import Data.ByteString.Lazy qualified as BSL
import Data.Foldable (Foldable (..), asum)
import Data.Function (on)
import Data.IntSet qualified as IS
import Data.List (maximumBy)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Maybe
import Data.Set qualified as Set
import Data.Text qualified as T
import Data.Text.Foreign (lengthWord8)
import Data.Text.Lazy qualified as TL
import Data.Word
import GHC.Float
import GHC.Stack (HasCallStack)
import Text.Regex.TDFA ((=~))

data ValidateCBORError
  = DecodingFailed DeserialiseFailure
  | LeftoverBytes BSL.ByteString
  | RuleDoesNotExist Name
  deriving (Show, Eq)

--------------------------------------------------------------------------------
-- Main entry point
validateCBOR ::
  HasCallStack =>
  BS.ByteString ->
  Name ->
  CTreeRoot ValidatorPhase ->
  Either ValidateCBORError (Evidenced (StepTrace TermBlock))
validateCBOR bs ruleName cddl@(CTreeRoot tree) =
  case deserialiseFromBytes decodeTerm (BSL.fromStrict bs) of
    Left e -> Left $ DecodingFailed e
    Right (rest, term)
      | BSL.null rest -> case tree Map.!? ruleName of
          Just rule -> Right $ runValidator (validateTerm term rule) $ ValidateEnv cddl mempty
          Nothing -> Left $ RuleDoesNotExist ruleName
      | otherwise -> Left $ LeftoverBytes rest

-- | Validate a CBOR 'Term' against a top-level rule from inside a custom
-- validator.
validateFromName ::
  HasCallStack => Name -> Term -> Validator ()
validateFromName n term = do
  mRule <- lookupCddl n
  case mRule of
    Nothing -> fail $ "Unbound name: " <> show n
    Just rule -> validateTerm term rule

-- | Validate a CBOR 'Term' against the type bound to the given generic
-- parameter at the enclosing rule. Use this from inside a custom validator
-- attached to a generic rule.
validateFromGRef ::
  HasCallStack => GRef -> Term -> Validator ()
validateFromGRef ref term = do
  mRule <- lookupGRef ref
  case mRule of
    Nothing -> fail $ "Unbound generic reference: " <> show ref
    Just rule -> validateTerm term rule

applyCustomValidator ::
  (TermValidator -> TermValidator) ->
  CTree ValidatorPhase ->
  Term ->
  Validator ()
applyCustomValidator f x = f (`validateTerm` x)

--------------------------------------------------------------------------------
-- Terms

-- | Core function that validates a CBOR term to a particular rule of the CDDL
-- spec
validateTerm ::
  Term ->
  CTree ValidatorPhase ->
  Validator ()
validateTerm term rule
  | CTreeE (VRuleRef n) <- rule = dereference n $ validateTerm term
  | CTreeE (VValidator f x) <- rule = applyCustomValidator f x term
  | otherwise =
      case term of
        TInt i -> validateInteger (fromIntegral i) rule
        TInteger i -> validateInteger i rule
        TBytes b -> validateBytes b rule
        TBytesI b -> validateBytes (BSL.toStrict b) rule
        TString s -> validateText s rule
        TStringI s -> validateText (TL.toStrict s) rule
        TList ts -> validateList ts rule
        TListI ts -> validateList ts rule
        TMap ts -> validateMap ts rule
        TMapI ts -> validateMap ts rule
        TTagged w t -> validateTagged w t rule
        TBool b -> validateBool b rule
        TNull -> validateNull rule
        TSimple s -> validateSimple s rule
        THalf h -> validateHalf h rule
        TFloat h -> validateFloat h rule
        TDouble d -> validateDouble d rule

validateRange ::
  (HasCallStack, Ord a) =>
  a ->
  CTree ValidatorPhase ->
  (CTree ValidatorPhase -> Validator (Maybe a)) ->
  Validator ()
validateRange v rule evalElem = do
  interval <- expectWellFormed <$> evalInterval evalElem rule
  ruleVerdict rule $ Interval.contains interval v

--------------------------------------------------------------------------------
-- Ints and integers

-- | Validation of an Int or Integer. CBOR categorizes every integral in `TInt`
-- or `TInteger` but it can be the case that we are decoding something that is
-- expected to be a `Word64` even if we get a `TInt`.
--
-- > ghci> encodeWord64 15
-- > [TkInt 15]
-- > ghci> encodeWord64 maxBound
-- > [TkInteger 18446744073709551615]
--
-- For this reason, we cannot assume that bounds or literals are going to be
-- Ints, so we convert everything to Integer.
validateInteger ::
  HasCallStack =>
  Integer ->
  CTree ValidatorPhase ->
  Validator ()
validateInteger i rule =
  case rule of
    CTreeE (VRuleRef n) -> dereference n $ validateInteger i
    CTreeE (VValidator f x) -> f (`validateTerm` x) $ TInteger i
    -- echo "C24101" | xxd -r -p - example.cbor
    -- echo "foo = int" > a.cddl
    -- cddl a.cddl validate example.cbor
    --
    -- but
    --
    -- echo "C249010000000000000000"| xxd -r -p - example.cbor
    -- echo "foo = int" > a.cddl
    -- cddl a.cddl validate example.cbor
    --
    -- and they are both bigints?

    -- a = any
    Postlude PTAny -> accept rule
    -- a = int
    Postlude PTInt
      | i >= nintMin && i <= uintMax -> accept rule
    -- a = uint
    Postlude PTUInt
      | i >= 0 && i <= uintMax -> accept rule
    -- a = nint
    Postlude PTNInt
      | i >= nintMin && i <= -1 -> accept rule
    -- a = x
    Literal _ -> do
      x <- evalInteger rule
      ruleVerdict rule $ x == Just i
    -- a = foo .ctrl bar
    Control op tgt ctrl -> validateInteger i tgt >> controlInteger i op ctrl
    -- a = foo / bar
    Choice opts -> validateChoice (validateInteger i) opts
    -- a = x..y
    Range {} -> validateRange i rule evalInteger
    -- a = &(x, y, z)
    Enum g ->
      case g of
        CTreeE (VRuleRef n) -> dereference n $ validateInteger i
        Group g' -> validateInteger i (Choice (NE.fromList g'))
        _ -> error "Not yet implemented"
    -- a = x: y
    -- Note KV cannot appear on its own, but we will use this when validating
    -- lists.
    KV _ v _ -> validateInteger i v
    Tag 2 x -> validateBigInt x
    Tag 3 x -> validateBigInt x
    _ -> reject rule
  where
    validateBigInt x = case x of
      CTreeE (VRuleRef n) -> dereference n validateBigInt
      Postlude PTBytes -> accept rule
      Control op tgt@(Postlude PTBytes) ctrl ->
        validateBytes bs tgt >> controlBytes bs op ctrl
        where
          -- TODO figure out a way to turn Integer into bytes or figure out why
          -- tagged bigints are decoded as integers in the first place
          bs = mempty
      _ -> reject rule

-- | Controls for an Integer
controlInteger ::
  HasCallStack =>
  Integer ->
  CtlOp ->
  CTree ValidatorPhase ->
  Validator ()
controlInteger i op (CTreeE (VRuleRef n)) = dereferenceNoTrace n $ controlInteger i op
controlInteger i op ctrl = case op of
  Size -> do
    sz <- expectWellFormed <$> evalInteger ctrl
    verdict $ Interval.contains (0 ... 256 ^ sz) i
  Bits -> do
    indices <- case ctrl of
      Literal (Value (VUInt i') _) -> pure [i']
      Choice nodes -> getIndicesOfChoice nodes
      Range ff tt incl -> getIndicesOfRange ff tt incl
      Enum g -> getIndicesOfEnum g
      _ -> error "Not yet implemented"
    verdict $ go (IS.fromList (map fromIntegral indices)) i 0
    where
      go _ 0 _ = True
      go indices n idx =
        let bitSet = testBit n 0
            allowed = not bitSet || IS.member idx indices
         in allowed && go indices (shiftR n 1) (idx + 1)
  Lt -> verdictOnControl (i <)
  Gt -> verdictOnControl (i >)
  Le -> verdictOnControl (i <=)
  Ge -> verdictOnControl (i >=)
  Eq -> verdictOnControl (i ==)
  Ne -> verdictOnControl (i /=)
  _ -> error $ "unexpected control: " <> showSimple ctrl
  where
    verdict = controlVerdict op ctrl
    verdictOnControl f = do
      x <- expectWellFormed <$> evalInteger ctrl
      verdict $ f x

--------------------------------------------------------------------------------
-- Floating point (Float16, Float32, Float64)
--
-- As opposed to Integral types, there seems to be no ambiguity when encoding
-- and decoding floating-point numbers.

-- | Validating a `Float16`
validateHalf ::
  HasCallStack =>
  Float ->
  CTree ValidatorPhase ->
  Validator ()
validateHalf f (CTreeE (VRuleRef n)) = dereference n $ validateHalf f
validateHalf f (CTreeE (VValidator v x)) = applyCustomValidator v x $ THalf f
validateHalf f rule =
  case rule of
    -- a = any
    Postlude PTAny -> accept rule
    -- a = float16
    Postlude PTHalf -> accept rule
    -- a = 0.5
    Literal _ -> do
      x <- evalDouble rule
      ruleVerdict rule $ x == Just (float2Double f)
    -- a = foo / bar
    Choice opts -> validateChoice (validateHalf f) opts
    -- a = foo .ctrl bar
    Control op tgt ctrl -> validateHalf f tgt >> controlHalf f op ctrl
    -- a = x..y
    Range {} -> do
      interval <- expectWellFormed <$> evalInterval evalDouble rule
      ruleVerdict rule $ Interval.contains interval $ float2Double f
    _ -> reject rule

-- | Controls for `Float16`
controlHalf ::
  HasCallStack =>
  Float ->
  CtlOp ->
  CTree ValidatorPhase ->
  Validator ()
controlHalf f op (CTreeE (VRuleRef n)) = dereferenceNoTrace n $ controlHalf f op
controlHalf (float2Double -> v) op ctrl = case op of
  Lt -> verdictOnControl (v <)
  Gt -> verdictOnControl (v >)
  Le -> verdictOnControl (v <=)
  Ge -> verdictOnControl (v >=)
  Eq -> verdictOnControl (v ==)
  Ne -> verdictOnControl (v /=)
  _ -> error $ "Not yet implemented for half: " <> show op
  where
    verdict = controlVerdict op ctrl
    verdictOnControl f = do
      x <- expectWellFormed <$> evalDouble ctrl
      verdict $ f x

-- | Validating a `Float32`
validateFloat ::
  HasCallStack =>
  Float ->
  CTree ValidatorPhase ->
  Validator ()
validateFloat f (CTreeE (VRuleRef n)) = dereference n $ validateFloat f
validateFloat f (CTreeE (VValidator v x)) = applyCustomValidator v x $ TFloat f
validateFloat f rule =
  case rule of
    -- a = any
    Postlude PTAny -> accept rule
    -- a = float32
    Postlude PTFloat -> accept rule
    -- a = 0.000000005
    Literal _ -> do
      x <- evalDouble rule
      ruleVerdict rule $ x == Just (float2Double f)
    -- a = foo / bar
    Choice opts -> validateChoice (validateFloat f) opts
    -- a = foo .ctrl bar
    Control op tgt ctrl -> validateFloat f tgt >> controlFloat f op ctrl
    -- a = x..y
    Range {} -> do
      interval <- expectWellFormed <$> evalInterval evalDouble rule
      ruleVerdict rule $ Interval.contains interval $ float2Double f
    _ -> reject rule

-- | Controls for `Float32`
controlFloat ::
  HasCallStack =>
  Float ->
  CtlOp ->
  CTree ValidatorPhase ->
  Validator ()
controlFloat f op (CTreeE (VRuleRef n)) = dereferenceNoTrace n $ controlFloat f op
controlFloat (float2Double -> v) op ctrl = case op of
  Lt -> verdictOnControl (v <)
  Gt -> verdictOnControl (v >)
  Le -> verdictOnControl (v <=)
  Ge -> verdictOnControl (v >=)
  Eq -> verdictOnControl (v ==)
  Ne -> verdictOnControl (v /=)
  _ -> error $ "Not yet implemented for half: " <> show op
  where
    verdict = controlVerdict op ctrl
    verdictOnControl f = do
      x <- expectWellFormed <$> evalDouble ctrl
      verdict $ f x

-- | Validating a `Float64`
validateDouble ::
  HasCallStack =>
  Double ->
  CTree ValidatorPhase ->
  Validator ()
validateDouble f (CTreeE (VRuleRef n)) = dereference n $ validateDouble f
validateDouble f (CTreeE (VValidator v x)) = applyCustomValidator v x $ TDouble f
validateDouble f rule =
  case rule of
    -- a = any
    Postlude PTAny -> accept rule
    -- a = float64
    Postlude PTDouble -> accept rule
    -- a = 0.0000000000000000000000000000000000000000000005
    -- TODO: it is unclear if smaller floats should also validate
    Literal (Value (VFloat64 f') _) | f == f' -> accept rule
    -- a = foo / bar
    Choice opts -> validateChoice (validateDouble f) opts
    -- a = foo .ctrl bar
    Control op tgt ctrl -> validateDouble f tgt >> controlDouble f op ctrl
    -- a = x..y
    -- TODO it is unclear if this should mix floating point types too
    Range {} -> validateRange f rule evalDouble
    _ -> reject rule

-- | Controls for `Float64`
controlDouble ::
  HasCallStack =>
  Double ->
  CtlOp ->
  CTree ValidatorPhase ->
  Validator ()
controlDouble v op (CTreeE (VRuleRef n)) = dereferenceNoTrace n $ controlDouble v op
controlDouble v op ctrl = case op of
  Eq -> verdictOnControl (v ==)
  Ne -> verdictOnControl (v /=)
  _ -> error $ "Not yet implmented for double: " <> show op
  where
    verdict = controlVerdict op ctrl
    verdictOnControl f = do
      x <- expectWellFormed <$> evalDouble ctrl
      verdict $ f x

--------------------------------------------------------------------------------
-- Bool

-- | Validating a boolean
validateBool ::
  HasCallStack =>
  Bool ->
  CTree ValidatorPhase ->
  Validator ()
validateBool b (CTreeE (VRuleRef n)) = dereference n $ validateBool b
validateBool b (CTreeE (VValidator v x)) = applyCustomValidator v x $ TBool b
validateBool b rule =
  case rule of
    -- a = any
    Postlude PTAny -> accept rule
    -- a = bool
    Postlude PTBool -> accept rule
    -- a = true
    Literal _ -> do
      x <- evalBool rule
      ruleVerdict rule $ x == Just b
    -- a = foo .ctrl bar
    Control op tgt ctrl -> validateBool b tgt >> controlBool b op ctrl
    -- a = foo / bar
    Choice opts -> validateChoice (validateBool b) opts
    _ -> reject rule

-- | Controls for `Bool`
controlBool ::
  HasCallStack =>
  Bool ->
  CtlOp ->
  CTree ValidatorPhase ->
  Validator ()
controlBool b op (CTreeE (VRuleRef n)) = dereferenceNoTrace n $ controlBool b op
controlBool b op ctrl = case op of
  Eq -> verdictOnControl (b ==)
  Ne -> verdictOnControl (b /=)
  _ -> error $ "Not yet implemented for bool: " <> show op
  where
    verdict = controlVerdict op ctrl
    verdictOnControl f = do
      x <- expectWellFormed <$> evalBool ctrl
      verdict $ f x

--------------------------------------------------------------------------------
-- Simple

-- | Validating a `TSimple`. It is unclear if this is used for anything else than `undefined`.
validateSimple ::
  Word8 ->
  CTree ValidatorPhase ->
  Validator ()
validateSimple i (CTreeE (VRuleRef n)) = dereference n $ validateSimple i
validateSimple i (CTreeE (VValidator v x)) = applyCustomValidator v x $ TSimple i
validateSimple 23 rule =
  case rule of
    -- a = any
    Postlude PTAny -> accept rule
    -- a = undefined
    Postlude PTUndefined -> accept rule
    -- a = foo / bar
    Choice opts -> validateChoice (validateSimple 23) opts
    _ -> reject rule
validateSimple n _ = error $ "Found simple different to 23! please report this somewhere! Found: " <> show n

--------------------------------------------------------------------------------
-- Null/nil

-- | Validating nil
validateNull ::
  CTree ValidatorPhase -> Validator ()
validateNull (CTreeE (VRuleRef n)) = dereference n validateNull
validateNull (CTreeE (VValidator v x)) = applyCustomValidator v x TNull
validateNull rule =
  case rule of
    -- a = any
    Postlude PTAny -> accept rule
    -- a = nil
    Postlude PTNil -> accept rule
    Choice opts -> validateChoice validateNull opts
    _ -> reject rule

--------------------------------------------------------------------------------
-- Bytes

-- | Validating a byte sequence
validateBytes ::
  HasCallStack =>
  BS.ByteString ->
  CTree ValidatorPhase ->
  Validator ()
validateBytes bs (CTreeE (VRuleRef n)) = dereference n $ validateBytes bs
validateBytes bs (CTreeE (VValidator v x)) = applyCustomValidator v x $ TBytes bs
validateBytes bs rule =
  case rule of
    -- a = any
    Postlude PTAny -> accept rule
    -- a = bytes
    Postlude PTBytes -> accept rule
    -- a = h'123456'
    Literal _ -> do
      x <- evalBytes rule
      ruleVerdict rule $ x == Just bs
    -- a = foo .ctrl bar
    Control op tgt ctrl -> validateBytes bs tgt >> controlBytes bs op ctrl
    -- a = foo / bar
    Choice opts -> validateChoice (validateBytes bs) opts
    _ -> reject rule

-- | Controls for byte strings
controlBytes ::
  HasCallStack =>
  BS.ByteString ->
  CtlOp ->
  CTree ValidatorPhase ->
  Validator ()
controlBytes bs op (CTreeE (VRuleRef n)) = dereferenceNoTrace n $ controlBytes bs op
controlBytes bs op ctrl = case op of
  Size -> validateRange (toInteger $ BS.length bs) ctrl evalInteger
  Bits -> do
    indices <-
      case ctrl of
        Literal (Value (VUInt i') _) -> pure [i']
        Choice nodes -> getIndicesOfChoice nodes
        Range ff tt incl -> getIndicesOfRange ff tt incl
        Enum g -> getIndicesOfEnum g
        _ -> error "Not yet implemented"
    bitsControlCheck (map fromIntegral indices)
    where
      bitsControlCheck :: [Int] -> Validator ()
      bitsControlCheck allowedBits = verdict $ all isAllowedBit [0 .. totalBits - 1]
        where
          allowedSet = IS.fromList allowedBits
          totalBits = BS.length bs * 8
          isAllowedBit n =
            let byteIndex = n `shiftR` 3
                bitIndex = n .&. 7
             in case BS.indexMaybe bs byteIndex of
                  Just byte -> not (testBit byte bitIndex) || IS.member n allowedSet
                  Nothing -> True
  Cbor -> case deserialiseFromBytes decodeTerm (BSL.fromStrict bs) of
    Right (BSL.null -> True, term) -> withCborControl ctrl $ validateTerm term ctrl
    _ -> verdict False
  Cborseq -> case deserialiseFromBytes decodeTerm (BSL.fromStrict (BS.snoc (BS.cons 0x9f bs) 0xff)) of
    Right (BSL.null -> True, TListI terms) -> withCborseqControl ctrl $ validateListBlock terms [Occur ctrl OIZeroOrMore]
    _ -> verdict False
  _ -> error $ "Not yet implmented for bytes: " <> show op
  where
    verdict = controlVerdict op ctrl

--------------------------------------------------------------------------------
-- Text

-- | Validating text strings
validateText ::
  HasCallStack =>
  T.Text ->
  CTree ValidatorPhase ->
  Validator ()
validateText txt (CTreeE (VRuleRef n)) = dereference n $ validateText txt
validateText txt (CTreeE (VValidator v x)) = applyCustomValidator v x $ TString txt
validateText txt rule =
  case rule of
    -- a = any
    Postlude PTAny -> accept rule
    -- a = text
    Postlude PTText -> accept rule
    -- a = "foo"
    Literal {} -> do
      x <- evalText rule
      ruleVerdict rule $ x == Just txt
    -- a = foo .ctrl bar
    Control op tgt ctrl -> validateText txt tgt >> controlText txt op ctrl
    -- a = foo / bar
    Choice opts -> validateChoice (validateText txt) opts
    _ -> reject rule

-- | Controls for text strings
controlText ::
  HasCallStack =>
  T.Text ->
  CtlOp ->
  CTree ValidatorPhase ->
  Validator ()
controlText bs op (CTreeE (VRuleRef n)) = dereferenceNoTrace n $ controlText bs op
controlText bs op ctrl = case op of
  Size -> validateRange (toInteger $ lengthWord8 bs) ctrl evalInteger
  Regexp -> case ctrl of
    Literal (Value (VText rxp) _) -> case bs =~ rxp :: (T.Text, T.Text, T.Text) of
      ("", bs', "") -> verdict $ bs == bs'
      _ -> verdict False
    _ -> error "Invalid control value in .regexp"
  _ -> error $ "Not yet implemented for text: " <> show op
  where
    verdict = controlVerdict op ctrl

--------------------------------------------------------------------------------
-- Tagged values

-- | Validating a `TTagged`
validateTagged ::
  Word64 ->
  Term ->
  CTree ValidatorPhase ->
  Validator ()
validateTagged tag term (CTreeE (VRuleRef n)) = dereference n $ validateTagged tag term
validateTagged tag term (CTreeE (VValidator v x)) = applyCustomValidator v x $ TTagged tag term
validateTagged tag term rule =
  case rule of
    Postlude PTAny -> accept rule
    Tag tag' rule' ->
      -- If the tag does not match, this is a direct fail
      if tag == tag'
        then withTag tag $ validateTerm term rule'
        else failWith $ InvalidTag tag' tag
    Choice opts -> validateChoice (validateTagged tag term) opts
    _ -> reject rule

-- --------------------------------------------------------------------------------
-- -- Lists

clampedPred :: (Eq a, Num a, Enum a) => a -> a
clampedPred 0 = 0
clampedPred x = pred x

closestMatch ::
  (CTree ValidatorPhase -> ValidatorT b' ()) ->
  [CTree ValidatorPhase] ->
  ValidatorT b (Maybe (CTree MonoSimplePhase, StepTrace b' IsInvalid))
closestMatch tryRule candidates = do
  results <- traverse (\r -> (mapIndex r,) <$> runBlock (tryRule $ unwrapOccur r)) candidates
  pure . fmap (maximumBy (compare `on` (measureProgress . snd))) . NE.nonEmpty $
    [(r, trc) | (r, Left trc) <- results, measureProgress trc > mempty]
  where
    unwrapOccur (Occur ct _) = ct
    unwrapOccur ct = ct

validateListBlock ::
  [Term] ->
  [CTree ValidatorPhase] ->
  ValidatorT ListBlock ()
validateListBlock terms rules = do
  res <- matchSeq rules terms
  case res of
    [] -> pure ()
    t : ts -> do
      closest <- closestMatch (validateTerm t) . reverse $ [r | r@Occur {} <- rules]
      failWith $ ArrayLeftoverTerms (t NE.:| ts) closest
  where
    matchSingle :: CTree ValidatorPhase -> [Term] -> ValidatorT ListBlock [Term]
    matchSingle r [] = failWith $ ArrayLeftoverRule $ mapIndex r
    matchSingle r (t : ts) = case r of
      CTreeE (VRuleRef n) -> dereference n $ \ref -> matchSingle ref (t : ts)
      CTreeE (VValidator v x) -> do
        element $ applyCustomValidator v x t
        pure ts
      KV _ v _ -> matchSingle v (t : ts)
      Group rs -> matchSeq rs (t : ts)
      _ -> do
        element $ validateTerm t r
        pure ts

    -- low inclusive, high exclusive
    matchBounded ::
      Word64 -> Maybe Word64 -> CTree ValidatorPhase -> [Term] -> ValidatorT ListBlock [Term]
    matchBounded lo mHi r ts
      | withinBounds && canConsumeMore = do
          res <- optional $ matchSingle r ts
          case res of
            Just remainingTerms -> matchBounded newLo newHi r remainingTerms
            Nothing -> pure ts
      | withinBounds = pure ts
      | otherwise = do
          remainingTerms <- matchSingle r ts
          matchBounded newLo newHi r remainingTerms
      where
        withinBounds = lo == 0
        canConsumeMore = maybe True (> 0) mHi

        newLo = clampedPred lo
        newHi = clampedPred <$> mHi

    matchSeq :: [CTree ValidatorPhase] -> [Term] -> ValidatorT ListBlock [Term]
    matchSeq [] ts = pure ts
    matchSeq (r : rs) ts = case r of
      Occur ct oi -> do
        remainingTerms <- case oi of
          OIOptional -> matchBounded 0 (Just 1) ct ts
          OIBounded lb ub -> matchBounded (fromMaybe 0 lb) ub ct ts
          OIZeroOrMore -> matchBounded 0 Nothing ct ts
          OIOneOrMore -> matchBounded 1 Nothing ct ts
        matchSeq rs remainingTerms
      _ -> do
        remainingTerms <- matchSingle r ts
        matchSeq rs remainingTerms

validateList ::
  [Term] ->
  CTree ValidatorPhase ->
  Validator ()
validateList terms (CTreeE (VRuleRef n)) = dereference n $ validateList terms
validateList terms (CTreeE (VValidator v x)) = applyCustomValidator v x $ TList terms
validateList terms rule =
  case rule of
    Postlude PTAny -> accept rule
    Array rules -> withArray $ validateListBlock terms rules
    Choice opts -> validateChoice (validateList terms) opts
    _ -> reject rule

--------------------------------------------------------------------------------
-- Maps

validateMapBlock ::
  [(Term, Term)] ->
  [CTree ValidatorPhase] ->
  ValidatorT MapBlock ()
validateMapBlock terms rules = do
  checkDuplicates $ toCanonical . fst <$> terms
  _ <- matchSeq [] rules terms
  pure ()
  where
    checkDuplicates = go mempty
      where
        go _ [] = pure ()
        go seen (k : ts)
          | k `Set.member` seen = failWith $ MapDuplicateKeys k
          | otherwise = go (Set.insert k seen) ts

    matchSingle ::
      CTree ValidatorPhase ->
      [(Term, Term)] ->
      ValidatorT MapBlock [(Term, Term)]
    matchSingle r [] = failWith $ MapUnappliedRules $ mapIndex r NE.:| []
    matchSingle r ts@((k, v) : tt) = case r of
      CTreeE (VRuleRef n) -> do
        dereference n $ \r' -> matchSingle r' ts
      CTreeE (VValidator _ _) ->
        error
          "Custom validators not supported for individual map entries. Write a custom validator for the map instead"
      KV kr vr _ -> do
        entry (validateTerm k kr) (validateTerm v vr)
        pure tt
      Group rs -> matchSeq [] rs ts
      _ -> error "Unsupported rule in map"

    consumeOne ::
      CTree ValidatorPhase ->
      [(Term, Term)] ->
      ValidatorT MapBlock ([(Term, Term)], Maybe (CTree ValidatorPhase))
    consumeOne r ts = case r of
      Occur _ (OIBounded _ (Just 0)) -> empty -- no capacity left
      Occur ct oi -> (,next ct oi) <$> matchSingle ct ts
      _ -> (,Nothing) <$> matchSingle r ts
      where
        next ct = \case
          OIOptional -> Nothing
          OIOneOrMore -> Just $ Occur ct OIZeroOrMore
          OIZeroOrMore -> Just $ Occur ct OIZeroOrMore
          OIBounded mlb mub -> Just $ Occur ct $ OIBounded (clampedPred <$> mlb) (clampedPred <$> mub)

    matchSeq ::
      [CTree ValidatorPhase] ->
      [CTree ValidatorPhase] ->
      [(Term, Term)] ->
      ValidatorT MapBlock [(Term, Term)]
    matchSeq tried rs [] = do
      let
        checkUnsatisfied = \case
          CTreeE (VRuleRef n) -> dereference n checkUnsatisfied
          Occur _ oi -> pure $ case oi of
            OIOptional -> False
            OIZeroOrMore -> False
            OIBounded mlb _ -> maybe False (> 0) mlb
            OIOneOrMore -> True
          _ -> pure True
      unappliedRules <- filterM checkUnsatisfied (reverse tried <> rs)
      case unappliedRules of
        [] -> pure []
        x : xs -> failWith $ MapUnappliedRules $ mapIndex <$> x NE.:| xs
    matchSeq tried [] (t : ts) =
      failWith . MapLeftoverEntries (t NE.:| ts)
        =<< closestMatch (\r -> void $ matchSingle r [t]) (reverse tried)
    matchSeq tried (r : rs) ts =
      ( do
          (rest, r') <- consumeOne r ts
          matchSeq [] (reverse tried <> maybeToList r' <> rs) rest
      )
        <|> matchSeq (r : tried) rs ts

validateMap ::
  HasCallStack =>
  [(Term, Term)] ->
  CTree ValidatorPhase ->
  Validator ()
validateMap terms (CTreeE (VRuleRef n)) = dereference n $ validateMap terms
validateMap terms (CTreeE (VValidator v x)) = applyCustomValidator v x $ TMap terms
validateMap terms rule =
  case rule of
    Postlude PTAny -> accept rule
    Map rules -> withMap $ validateMapBlock terms rules
    Choice opts -> validateChoice (validateMap terms) opts
    _ -> reject rule

--------------------------------------------------------------------------------
-- Choices

validateChoice ::
  (CTree ValidatorPhase -> Validator ()) ->
  NE.NonEmpty (CTree ValidatorPhase) ->
  Validator ()
validateChoice f rs = asum $ zipWith g [0 ..] (toList rs)
  where
    g i = withChoice i . f

--------------------------------------------------------------------------------
-- Bits control

getIndicesOfChoice :: NE.NonEmpty (CTree ValidatorPhase) -> Validator [Word64]
getIndicesOfChoice x = mconcat <$> traverse go (toList x)
  where
    go = \case
      Literal (Value (VUInt v) _) -> pure [fromIntegral v]
      KV _ v _ ->
        case v of
          CTreeE (VRuleRef n) -> dereferenceNoTrace n go
          Literal (Value (VUInt v') _) -> pure [fromIntegral v']
          somethingElse ->
            error $
              "Malformed value in KV in choice in .bits: "
                <> showSimple somethingElse
      Range ff tt incl -> getIndicesOfRange ff tt incl
      Enum g -> getIndicesOfEnum g
      somethingElse ->
        error $
          "Malformed alternative in choice in .bits: "
            <> showSimple somethingElse

getIndicesOfRange ::
  CTree ValidatorPhase -> CTree ValidatorPhase -> RangeBound -> Validator [Word64]
getIndicesOfRange (CTreeE (VRuleRef n)) tt incl =
  dereferenceNoTrace n $ \ff -> getIndicesOfRange ff tt incl
getIndicesOfRange ff (CTreeE (VRuleRef n)) incl =
  dereferenceNoTrace n $ \tt -> getIndicesOfRange ff tt incl
getIndicesOfRange ff tt incl =
  case (ff, tt) of
    (Literal (Value (VUInt ff') _), Literal (Value (VUInt tt') _)) ->
      pure $ case incl of
        ClOpen -> init rng
        Closed -> rng
      where
        rng = [ff' .. tt']
    (lo, hi) -> error $ "Malformed range in .bits: (" <> showSimple lo <> ", " <> showSimple hi <> ")"

getIndicesOfEnum :: CTree ValidatorPhase -> Validator [Word64]
getIndicesOfEnum (CTreeE (VRuleRef n)) = dereferenceNoTrace n getIndicesOfEnum
getIndicesOfEnum g =
  case g of
    Group g' -> getIndicesOfChoice (fromJust $ NE.nonEmpty g')
    somethingElse -> error $ "Malformed enum in .bits: " <> showSimple somethingElse

dereferenceNoTrace :: Name -> (CTree ValidatorPhase -> ValidatorT b a) -> ValidatorT b a
dereferenceNoTrace n act = do
  mRes <- lookupCddl n
  case mRes of
    Just x -> act x
    Nothing -> fail "Rule does not exist"

dereference :: Name -> (CTree ValidatorPhase -> ValidatorT b a) -> ValidatorT b a
dereference n = withRef n . dereferenceNoTrace n

--------------------------------------------------------------------------------
-- Utils

expectWellFormed :: HasCallStack => Maybe a -> a
expectWellFormed (Just x) = x
expectWellFormed Nothing = error "Rules are not well-formed"

ruleVerdict :: CTree ValidatorPhase -> Bool -> Validator ()
ruleVerdict rule True = accept rule
ruleVerdict rule False = reject rule
