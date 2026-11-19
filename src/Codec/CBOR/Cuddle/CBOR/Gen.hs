{-# LANGUAGE CPP #-}
#if MIN_VERSION_random(1,3,0)
{-# OPTIONS_GHC -Wno-deprecations #-} -- Due to usage of `split`
#endif
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | Generate example CBOR given a CDDL specification
module Codec.CBOR.Cuddle.CBOR.Gen (
  generateFromName,
  generateFromGRef,
  GenPhase,
  XXCTree (..),
  twiddleArray,
  twiddleMap,
  twiddleText,
  twiddleBytes,
  evalDouble,
  evalInteger,
  evalArray,

  -- * Generator helpers
  genNBytes,
  genNBytesText,
  genBytes,
  genText,
  genInteger,
  genTerm,
) where

#if MIN_VERSION_random(1,3,0)
#endif
import Codec.CBOR.Cuddle.CBOR.Canonical (
  nintMin,
  toCanonical,
  uintMax,
 )
import Codec.CBOR.Cuddle.CBOR.Validator (validateAgainst)
import Codec.CBOR.Cuddle.CDDL (
  GRef (..),
  Name (..),
  OccurrenceIndicator (..),
  RangeBound (..),
  Value (..),
  ValueVariant (..),
 )
import Codec.CBOR.Cuddle.CDDL.CTree (
  CTree (..),
  CTreeRoot (..),
  PTerm (..),
  foldCTree,
 )
import Codec.CBOR.Cuddle.CDDL.CTree qualified as CTree
import Codec.CBOR.Cuddle.CDDL.CtlOp qualified as CtlOp
import Codec.CBOR.Cuddle.CDDL.Custom.Core (MonadCddl (..), RuleTerm (..))
import Codec.CBOR.Cuddle.CDDL.Custom.Generator (
  CBORGen,
  GenConfig (..),
  GenEnv (..),
  GenPhase,
  TermGenerator (..),
  bindGen,
  constrain,
  deferGen,
  genFromInterval,
  rangeInInterval,
  simpleGen,
 )
import Codec.CBOR.Cuddle.CDDL.Custom.Generator qualified as Gen
import Codec.CBOR.Cuddle.CDDL.Custom.Validator (
  CustomValidatorResult (..),
  ValidatorPhase,
  runValidator,
 )
import Codec.CBOR.Cuddle.CDDL.Resolve (XXCTree (..), showSimple)
import Codec.CBOR.Cuddle.IndexMappable (IndexMappable (..))
import Codec.CBOR.Cuddle.Interval (
  Interval (..),
  IntervalBound (..),
  greaterThanOrEqual,
  intersect,
  lessThanOrEqual,
  universe,
  (..=),
 )
import Codec.CBOR.Cuddle.Interval qualified as Interval
import Codec.CBOR.Term (Term (..))
import Codec.CBOR.Term qualified as CBOR
import Codec.CBOR.Write qualified as CBOR
import Control.Monad (forM, zipWithM)
import Control.Monad.Reader (asks)
import Data.ByteString (ByteString)
import Data.ByteString.Lazy qualified as LBS
import Data.Char (chr)
import Data.Functor ((<&>))
import Data.List (sortOn)
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromMaybe)
import Data.Ord (Down (..))
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Internal.Encoding.Utf8 (utf8Length)
import Data.Text.Lazy qualified as LT
import Data.Text.Lazy qualified as TL
import Data.Text.Lazy.Builder (toLazyText)
import Data.Text.Lazy.Builder qualified as LB
import Data.Word (Word64, Word8)
import GHC.Float (double2Float, float2Double)
import GHC.Stack (HasCallStack)
import Numeric.Half (fromHalf, toHalf)
import System.Random.Stateful (Random, StatefulGen (..), runStateGen_, uniformByteStringM)
import Test.AntiGen (
  MonadAntiGen (..),
  annotate,
  antiChoose,
  faultyBool,
  faultyNum,
  reweigh,
  runAntiGen,
  (#!),
  (|!),
  (||!),
 )
import Test.QuickCheck (
  Arbitrary,
  NonNegative (..),
  shuffle,
 )
import Test.QuickCheck qualified as QC
import Test.QuickCheck.Gen (Gen (..), getSize)
import Test.QuickCheck.GenT (MonadGen (..), elements, frequency, listOf, oneof, vectorOf)

-- TODO remove this once QuickCheck gets QC
data QC = QC

instance StatefulGen QC Gen where
  uniformWord32 QC = MkGen (\r _n -> runStateGen_ r uniformWord32)
  uniformWord64 QC = MkGen (\r _n -> runStateGen_ r uniformWord64)
#if MIN_VERSION_random(1,3,0)
  uniformByteArrayM pinned sz QC = 
    MkGen (\r _n -> runStateGen_ r (uniformByteArrayM pinned sz))
#else
  uniformShortByteString k QC =
    MkGen (\r _n -> runStateGen_ r (uniformShortByteString k))
#endif

--------------------------------------------------------------------------------
-- Lifted MonadGen utils
--------------------------------------------------------------------------------

arbitrary :: (Arbitrary a, MonadGen m) => m a
arbitrary = liftGen QC.arbitrary

scale :: MonadGen m => (Int -> Int) -> m a -> m a
scale f m = sized $ \n -> resize (f n) m

suchThat :: Monad m => m a -> (a -> Bool) -> m a
suchThat gen p = go 100
  where
    go (n :: Int)
      | n > 0 = do
          v <- gen
          if p v then pure v else go $ pred n
      | otherwise = error "Failed to generate a fitting value after 100 tries"

--------------------------------------------------------------------------------
-- Generator infrastructure
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Postlude
--------------------------------------------------------------------------------

-- | Simple values that are either unassigned or don't have a specialized type already
simple :: [Word8]
simple =
  -- TODO add the other values once they are supported
  -- [0 .. 19] ++ [23] ++ [32 ..]
  [23]

genHalf :: TermGenerator Float
genHalf = go universe mempty
  where
    go rng exclude =
      TermGenerator
        { tgGenerator =
            let gen = do
                  half <- toHalf <$> rangeInInterval (-65504, 65504) rng `suchThat` (`Set.notMember` exclude)
                  if isDenormalized half
                    then gen
                    else pure $ fromHalf half
             in gen
        , tgConstrain = \case
            Gen.Range cRng -> Just $ deferGen $ do
              -- TODO think about the edges
              rng' <- forM cRng $ fmap double2Float . evalDouble
              pure $ go (rng `intersect` rng') exclude
            Gen.Eq term -> Just $ deferGen $ do
              x <- evalDouble term
              pure $ go (rng `intersect` Interval.singleton (double2Float x)) exclude
            Gen.Neq term -> Just $ deferGen $ do
              x <- evalDouble term
              pure $ go rng $ Set.insert (double2Float x) exclude
            _ -> Nothing
        }

genTwiddled ::
  (a -> Term) ->
  (a -> Term) ->
  a ->
  CBORGen Term
genTwiddled definite indefinite term = do
  elements [definite term, indefinite term]

twiddleArray :: [Term] -> CBORGen Term
twiddleArray = genTwiddled TList TListI

twiddleMap :: [(Term, Term)] -> CBORGen Term
twiddleMap = genTwiddled TMap TMapI

twiddleText :: Text -> CBORGen Term
twiddleText = genTwiddled TString (TStringI . TL.fromStrict)

twiddleBytes :: ByteString -> CBORGen Term
twiddleBytes = genTwiddled TBytes (TBytesI . LBS.fromStrict)

genTerm :: CBORGen Term
genTerm =
  oneof
    [ TInt <$> choose (minBound, maxBound)
    , TInteger
        <$> oneof
          [ choose (toInteger (maxBound :: Int) + 1, toInteger (maxBound :: Word64))
          , choose (negate (toInteger (maxBound :: Word64)), toInteger (minBound :: Int) - 1)
          ]
    , twiddleBytes =<< genNBytes . getNonNegative =<< arbitrary
    , twiddleText . T.pack =<< arbitrary
    , twiddleArray =<< listOf smallerTerm
    , twiddleMap =<< listOf ((,) <$> smallerTerm <*> smallerTerm)
    , TTagged <$> choose (6, maxBound :: Word64) <*> smallerTerm
    , TBool <$> arbitrary
    , pure TNull
    , TSimple <$> elements simple
    , THalf <$> tgGenerator genHalf
    , TFloat <$> arbitrary
    , TDouble <$> arbitrary
    ]
  where
    smallerTerm :: CBORGen Term
    smallerTerm = scale (`div` 5) genTerm

genNBytes :: MonadGen m => Int -> m ByteString
genNBytes n = liftGen (uniformByteStringM n QC)

-- | Caps a length range at the QuickCheck size, unless that would leave it
-- empty, in which case the range is returned unchanged.
capAtSize :: Int -> Interval Int -> Interval Int
capAtSize sz int
  | Interval.isEmpty capped = int
  | otherwise = capped
  where
    capped = int `intersect` lessThanOrEqual sz

genBytes :: TermGenerator ByteString
genBytes = go Nothing $ greaterThanOrEqual 0
  where
    go mCbor szRange =
      TermGenerator
        { tgGenerator =
            case mCbor of
              Nothing -> sized $ \sz -> do
                numElems <- genFromInterval $ capAtSize sz szRange
                genNBytes numElems
              Just cbor -> do
                term <- tgGenerator $ genForCTree cbor
                case term of
                  SingleTerm t -> pure $ CBOR.toStrictByteString $ CBOR.encodeTerm t
                  _ -> error "Expected a single term"
        , tgConstrain = \case
            Gen.Size rngRule -> Just $ deferGen $ do
              newRange <- evalInterval evalInteger rngRule
              pure $ go mCbor $ szRange `intersect` fmap fromIntegral newRange
            Gen.Cbor cbor
              -- Only allow constraining with .cbor once
              | Nothing <- mCbor -> Just $ go (Just cbor) szRange
            _ -> Nothing
        }

genCharAtMostBytes :: MonadGen m => Int -> m Char
genCharAtMostBytes 1 = chr <$> choose (0x00, 0x7F)
genCharAtMostBytes 2 = chr <$> choose (0x00, 0x7FF)
genCharAtMostBytes 3 = chr <$> oneof [choose (0x00, 0xD7FF), choose (0xE000, 0xFFFF)]
genCharAtMostBytes n
  | n <= 0 = error "expected positive number"
  | otherwise = chr <$> oneof [choose (0x00, 0xD7FF), choose (0xE000, 0x10FFFF)]

genNBytesText :: MonadGen m => Int -> m Text
genNBytesText n = do
  let
    go m !acc
      | m <= 0 = pure acc
      | otherwise = do
          c <- genCharAtMostBytes m
          go (m - utf8Length c) (acc <> LB.singleton c)
  builder <- go n mempty
  pure . LT.toStrict $ toLazyText builder

genText :: TermGenerator Text
genText = go $ greaterThanOrEqual 0
  where
    go sizeRange =
      TermGenerator
        { tgGenerator = sized $ \sz -> do
            n <- genFromInterval $ capAtSize sz sizeRange
            genNBytesText n
        , tgConstrain = \case
            Gen.Size rngRule -> Just $ deferGen $ do
              newRange <- evalInterval evalInteger rngRule
              pure . go $ sizeRange `intersect` fmap fromIntegral newRange
            _ -> Nothing
        }

-- | Primitive types defined by the CDDL specification, with their generators
genPostlude :: PTerm -> TermGenerator Term
genPostlude pt = go $ genPTerm pt
  where
    -- Constraints only reach the generator for @pt@: a term of a different
    -- type is invalid whatever the control operator says.
    go tg =
      TermGenerator
        { tgGenerator = do
            p <- faultyPTerm pt
            tgGenerator $ if p == pt then tg else genPTerm p
        , tgConstrain = fmap go . tgConstrain tg
        }
    genExcluding ls =
      elements (filter (`notElem` ls) [minBound .. maxBound])
    nonPInteger p =
      pure p |! genExcluding [PTUInt, PTNInt, PTInt, PTAny]
    -- Introduces a decision point that can change the type of the CBOR term that is generated
    faultyPTerm t = reweigh 0.1 $
      case t of
        PTAny -> pure PTAny
        p@PTUInt -> nonPInteger p
        p@PTNInt -> nonPInteger p
        p@PTInt -> nonPInteger p
        p -> pure p |! genExcluding [PTAny, p]

genInteger :: Interval Integer -> (Integer, Integer) -> TermGenerator Integer
genInteger validRng invalidRng = go validRng mempty
  where
    go validInterval excluded =
      TermGenerator
        { tgGenerator =
            rangeInInterval invalidRng validInterval `suchThat` (`Set.notMember` excluded)
        , tgConstrain = \case
            Gen.Size szRule -> Just $ deferGen $ do
              sz <- evalInteger szRule
              pure $ go (validInterval `intersect` lessThanOrEqual (2 ^ sz)) excluded
            Gen.Range intRule -> Just $ deferGen $ do
              int <- traverse evalInteger intRule
              pure $ go (validInterval `intersect` int) excluded
            Gen.Eq r -> Just $ deferGen $ do
              x <- evalInteger r
              pure $ go (validInterval `intersect` Interval.singleton x) excluded
            Gen.Neq r -> Just $ deferGen $ do
              x <- evalInteger r
              pure $ go validInterval $ Set.insert x excluded
            _ -> Nothing
        }

genFloat :: TermGenerator Float
genFloat = simpleGen arbitrary

genDouble :: TermGenerator Double
genDouble = simpleGen arbitrary

-- | Given a CDDL postlude type, generates a value of that type
genPTerm :: PTerm -> TermGenerator Term
genPTerm = \case
  PTBool -> simpleGen $ TBool <$> arbitrary
  -- For integers, introduce decision points that sometimes generate
  -- out-of-bounds values
  PTUInt -> TInteger <$> genInteger (0 ..= uintMax) outOfBounds
  PTNInt -> TInteger <$> genInteger (nintMin ..= (-1)) outOfBounds
  PTInt -> TInteger <$> genInteger (nintMin ..= uintMax) outOfBounds
  PTHalf -> THalf <$> genHalf
  PTFloat -> TFloat <$> genFloat
  PTDouble -> TDouble <$> genDouble
  PTBytes -> bindGen twiddleBytes genBytes
  PTText -> bindGen twiddleText genText
  PTAny -> simpleGen genTerm
  PTNil -> simpleGen $ pure TNull
  PTUndefined -> simpleGen $ pure $ TSimple 23
  where
    outOfBounds = (2 * nintMin, 2 * uintMax)

--------------------------------------------------------------------------------
-- Kinds of terms
--------------------------------------------------------------------------------

-- | Recursively flatten wrapped list. That is, expand any groups out to their
-- individual entries.
flattenWrappedList :: [RuleTerm] -> [RuleTerm]
flattenWrappedList [] = []
flattenWrappedList (GroupTerm xxs : xs) =
  flattenWrappedList xxs <> flattenWrappedList xs
flattenWrappedList (y : xs) = y : flattenWrappedList xs

-- | Convert a list of wrapped terms to a list of terms. If any 'PairTerm's are
-- present, we just take their "value" part.
singleTermList :: [RuleTerm] -> Maybe [Term]
singleTermList [] = Just []
singleTermList (SingleTerm x : xs) = (x :) <$> singleTermList xs
singleTermList (PairTerm _ y : xs) = (y :) <$> singleTermList xs
singleTermList _ = Nothing

-- | Remove all negative generators from the `AntiGen`.
dropNegativeGen :: MonadAntiGen m => m a -> m a
dropNegativeGen = mapAntiGen $ liftGen . runAntiGen

--------------------------------------------------------------------------------
-- Generator functions
--------------------------------------------------------------------------------

range :: Enum a => RangeBound -> a -> a -> (a, a)
range ClOpen x y = (x, pred y)
range Closed x y = (x, y)

genBetween ::
  ( Integral a
  , Random a
  , MonadAntiGen m
  , MonadGen m
  ) =>
  (a, a) -> m a
genBetween rng = do
  size <- liftGen getSize
  let
    sizeBounds :: Integral a => (a, a)
    sizeBounds = (0, fromIntegral size)
  antiChoose rng sizeBounds

genForCTree :: HasCallStack => CTree GenPhase -> TermGenerator RuleTerm
genForCTree node = case node of
  CTree.Literal v -> SingleTerm <$> valueToTerm v
  CTree.Postlude pt -> SingleTerm <$> genPostlude pt
  CTree.Map nodes -> genMap nodes
  CTree.Array nodes -> genArray nodes
  CTree.Choice (NE.toList -> nodes) -> simpleGen $ do
    ix <- choose (0, length nodes - 1)
    tgGenerator . genForCTree $ nodes !! ix
  CTree.Group nodes -> simpleGen $ GroupTerm <$> traverse (tgGenerator . genForCTree) nodes
  CTree.KV key value _cut -> genKV key value
  CTree.Occur item occurs ->
    applyOccurenceIndicator occurs (genForCTree item)
  CTree.Range from to bounds -> simpleGen $ genRange from to bounds
  CTree.Control op target controller -> genControl op target controller
  CTree.Enum tree -> genEnum tree
  CTree.Unwrap n -> genForCTree n
  CTree.Tag t n -> genTag t n
  CTree.CTreeE (GenRef n) -> genForNode n
  CTree.CTreeE (GenGenerator gen _) -> gen
  CTree.CTreeE (GenValidator _ x) -> genForCTree x

isInvalidAgainstNode :: CTreeRoot GenPhase -> Term -> CTree GenPhase -> Bool
isInvalidAgainstNode cTreeRoot term node =
  case runValidator (validateAgainst term $ mapIndex node) (mapIndex cTreeRoot) of
    CustomValidatorSuccess -> False
    CustomValidatorFailure {} -> True

-- | Generate a map from a list of nodes
genMap ::
  HasCallStack => [CTree GenPhase] -> TermGenerator RuleTerm
genMap nodes = simpleGen $ do
  let
    elemsNeeded KV {} = 1
    elemsNeeded (Occur _ OIOneOrMore) = 1
    elemsNeeded (Occur _ (OIBounded (Just lo) _)) = lo
    elemsNeeded _ = 0

    tryGenKV ::
      Int -> [(Term, Term)] -> CTree GenPhase -> CTree GenPhase -> CBORGen (Maybe (Term, Term))
    tryGenKV nTries m kNode vNode
      | null m = go nTries
      | otherwise =
          go nTries
            ||! oneof
              [ reuseKey #! "duplicateKey"
              , reuseKeyValue #! "duplicateKV"
              ]
      where
        canonicalKeys = toCanonical . fst <$> m
        unS (SingleTerm x) = x
        unS x = error $ "Expected single, got " <> show x
        genFromNode n = unS <$> scale (`div` 2) (tgGenerator $ genForCTree n)
        go !n
          | n > 0 = do
              k <- genFromNode kNode #! "key"
              if toCanonical k `notElem` canonicalKeys
                then do
                  v <- genFromNode vNode #! "value"
                  pure $ Just (k, v)
                else go (n - 1)
          | otherwise = pure Nothing
        reuseKey = do
          k <- elements $ fst <$> m
          v <- genFromNode vNode #! "value"
          pure $ Just (k, v)
        reuseKeyValue = Just <$> elements m

    genNodes :: Int -> [(Term, Term)] -> [CTree GenPhase] -> CBORGen (Maybe [(Term, Term)])
    genNodes _ m [] = pure $ Just m
    genNodes !i !m (n : ns) =
      let
        ann :: CBORGen a -> CBORGen a
        ann = annotate (T.pack $ show i)
        -- A term was produced, advance the index
        next x y = scale (\s -> max 0 (s - 1)) $ genNodes (i + 1) x y
        -- No term was produced, keep the index
        same x y = scale (\s -> max 0 (s - 1)) $ genNodes i x y
        optGenKV kNode vNode = sized $ \sz ->
          frequency [(1, pure Nothing), (max 0 sz, ann $ tryGenKV 10 m kNode vNode)]
       in
        case n of
          KV kNode vNode _ -> do
            mKV <- ann $ tryGenKV 100 m kNode vNode
            case mKV of
              Just (k, v) -> next ((k, v) : m) ns ||! same m ns
              Nothing -> pure Nothing
          Occur kv@(KV kNode vNode _) oi -> case oi of
            OIOptional -> do
              mt <- optGenKV kNode vNode
              case mt of
                Just (k, v) -> next ((k, v) : m) ns
                Nothing -> same m ns
            OIZeroOrMore -> do
              mt <- optGenKV kNode vNode
              case mt of
                Just (k, v) -> next ((k, v) : m) (n : ns)
                Nothing -> same m ns
            OIOneOrMore ->
              ( do
                  mKV <- ann $ tryGenKV 100 m kNode vNode
                  case mKV of
                    Just (k, v) -> next ((k, v) : m) (Occur kv OIZeroOrMore : ns)
                    Nothing -> pure Nothing
              )
                ||! same m ns
            OIBounded mlb mub -> do
              sz <- fromIntegral <$> liftGen getSize
              let
                lowerBound = fromMaybe 0 mlb
                upperBound = fromMaybe (max lowerBound sz) mub
                outerBound = maybe upperBound (max sz . succ) mub
                genElems i' m' nElems
                  | nElems <= 0 =
                      scale (\s -> max 0 (s - 1)) $ genNodes (i' + 1) m' ns
                  | otherwise = do
                      mKV <- annotate (T.pack $ show i') $ tryGenKV 100 m' kNode vNode
                      case mKV of
                        Just (k, v) -> genElems (i' + 1) ((k, v) : m') $ nElems - 1
                        Nothing -> pure Nothing
              nElems <- antiChoose (lowerBound, upperBound) (0, outerBound)
              genElems i m nElems
          node -> error $ "Unexpected node: " <> showSimple node
  mItems <- genNodes 0 [] $ sortOn (Down . elemsNeeded) nodes
  case mItems of
    Just items -> do
      cTreeRoot <- asks $ gcRoot . geConfig
      items' <-
        pure items ||! do
          let
            keyIsInvalidAgainstNode term = \case
              KV kNode _ _ -> isInvalidAgainstNode cTreeRoot term kNode
              Occur x _ -> keyIsInvalidAgainstNode term x
              node -> error $ "Unexpected node: " <> showSimple node
          junkKV <-
            (,) <$> (genTerm `suchThat` \t -> all (keyIsInvalidAgainstNode t) nodes) <*> genTerm
          pure $ junkKV : items
      shuffledItems <- liftGen $ shuffle items'
      SingleTerm <$> twiddleMap shuffledItems
    Nothing -> error "Failed to generate unique keys for map after max retries"

-- | Generate an array from a list of nodes
genArray :: HasCallStack => [CTree GenPhase] -> TermGenerator RuleTerm
genArray nodes = simpleGen generator
  where
    generator :: CBORGen RuleTerm
    generator = do
      items <-
        singleTermList . flattenWrappedList
          <$> zipWithM
            (\i node -> annotate (T.pack $ show i) . tgGenerator $ genForCTree node)
            [0 :: Int ..]
            nodes
      case items of
        Just ts -> do
          cTreeRoot <- asks $ gcRoot . geConfig
          SingleTerm
            <$> twiddleArray ts ||! do
              let
                genCorruptedList = do
                  idx <- choose (0, length ts)
                  junkElem <- genTerm
                  let
                    (lInit, lTail) = splitAt idx ts
                  twiddleArray $ lInit <> [junkElem] <> lTail
              genCorruptedList `suchThat` \l -> isInvalidAgainstNode cTreeRoot l (Array nodes)
        Nothing -> error "Something weird happened which shouldn't be possible"

-- | Generate a key-value pair
genKV :: HasCallStack => CTree GenPhase -> CTree GenPhase -> TermGenerator RuleTerm
genKV key value = simpleGen $ do
  kg <- annotate "key" . tgGenerator $ genForCTree key
  vg <- annotate "value" . tgGenerator $ genForCTree value
  case (kg, vg) of
    (SingleTerm k, SingleTerm v) -> pure $ PairTerm k v
    _ ->
      error $
        "Non single-term generated outside of group context: "
          <> showSimple key
          <> " => "
          <> showSimple value

-- | Generate a value from a range
genRange ::
  HasCallStack =>
  CTree GenPhase ->
  CTree GenPhase ->
  RangeBound ->
  CBORGen RuleTerm
genRange from to bounds = do
  term1 <- dropNegativeGen . tgGenerator $ genForCTree from
  term2 <- dropNegativeGen . tgGenerator $ genForCTree to
  case (term1, term2) of
    (SingleTerm (TInt a), SingleTerm (TInt b))
      | a <= b -> genBetween (range bounds a b) <&> SingleTerm . TInt
    (SingleTerm (TInt a), SingleTerm (TInteger b))
      | fromIntegral a <= b ->
          genBetween (range bounds (fromIntegral a) b) <&> SingleTerm . TInteger
    (SingleTerm (TInteger a), SingleTerm (TInteger b))
      | a <= b -> genBetween (range bounds a b) <&> SingleTerm . TInteger
    (SingleTerm (THalf a), SingleTerm (THalf b))
      | a <= b -> choose (range bounds a b) <&> SingleTerm . THalf
    (SingleTerm (TFloat a), SingleTerm (TFloat b))
      | a <= b -> choose (range bounds a b) <&> SingleTerm . TFloat
    (SingleTerm (TDouble a), SingleTerm (TDouble b))
      | a <= b -> choose (range bounds a b) <&> SingleTerm . TDouble
    (a, b) -> error $ "invalid range (a = " <> show a <> ", b = " <> show b <> ")"

evalDouble :: CTree GenPhase -> CBORGen Double
evalDouble = \case
  Literal (Value var _)
    | VFloat16 x <- var -> pure $ float2Double x
    | VFloat32 x <- var -> pure $ float2Double x
    | VFloat64 x <- var -> pure x
  CTreeE (GenGenerator _ t) -> evalDouble t
  CTreeE (GenValidator _ t) -> evalDouble t
  CTreeE (GenRef n) -> evalDouble =<< resolveRef n
  _ -> error "Expected double"

evalInteger :: CTree GenPhase -> CBORGen Integer
evalInteger = \case
  Literal (Value var _)
    | VUInt x <- var -> pure $ toInteger x
    | VNInt x <- var -> pure . negate $ toInteger x
    | VBignum x <- var -> pure x
  CTreeE (GenGenerator _ t) -> evalInteger t
  CTreeE (GenValidator _ t) -> evalInteger t
  CTreeE (GenRef n) -> evalInteger =<< resolveRef n
  _ -> error "Expected integer"

evalArray :: (CTree GenPhase -> CBORGen a) -> CTree GenPhase -> CBORGen [a]
evalArray f = \case
  Array es -> traverse f es
  CTreeE (GenGenerator _ t) -> evalArray f t
  CTreeE (GenValidator _ t) -> evalArray f t
  CTreeE (GenRef n) -> evalArray f =<< resolveRef n
  _ -> error "Expected array"

evalInterval :: (CTree GenPhase -> CBORGen a) -> CTree GenPhase -> CBORGen (Interval a)
evalInterval f = \case
  Range loRule hiRule bound -> do
    lo <- f loRule
    hi <- f hiRule
    pure $ Interval (ClosedBound lo) $ case bound of
      ClOpen -> OpenBound hi
      Closed -> ClosedBound hi
  CTreeE (GenGenerator _ t) -> evalInterval f t
  CTreeE (GenValidator _ t) -> evalInterval f t
  CTreeE (GenRef n) -> evalInterval f =<< resolveRef n
  x -> Interval.singleton <$> f x

-- | Generate a value with a control operator applied
genControl ::
  HasCallStack =>
  CtlOp.CtlOp ->
  CTree GenPhase ->
  CTree GenPhase ->
  TermGenerator RuleTerm
genControl op target controller = deferGen $ do
  pure $ constrain (constraint controller) (genForCTree target)
  where
    constraint ctl = case op of
      CtlOp.Size -> Gen.Size ctl
      CtlOp.Bits -> error "Not yet implemented"
      CtlOp.Regexp -> error "Not yet implemented"
      -- Generated from rather than evaluated, so it keeps its references
      CtlOp.Cbor -> Gen.Cbor controller
      CtlOp.Cborseq -> error "Not yet implemented"
      CtlOp.Within -> error "Not yet implemented"
      CtlOp.And -> error "Not yet implemented"
      CtlOp.Lt -> Gen.Range $ Interval.lessThan ctl
      CtlOp.Le -> Gen.Range $ Interval.lessThanOrEqual ctl
      CtlOp.Gt -> Gen.Range $ Interval.greaterThan ctl
      CtlOp.Ge -> Gen.Range $ Interval.greaterThanOrEqual ctl
      CtlOp.Eq -> Gen.Eq ctl
      CtlOp.Ne -> Gen.Neq ctl
      CtlOp.Default -> Gen.Default ctl

-- | Generate a value from an enum
genEnum :: HasCallStack => CTree GenPhase -> TermGenerator RuleTerm
genEnum tree = simpleGen $ case tree of
  CTree.Group trees -> do
    ix <- choose (0, length trees - 1)
    tgGenerator $ genForCTree $ trees !! ix
  _ -> error "Attempt to form an enum from something other than a group"

-- | Generate a tagged value
genTag :: HasCallStack => Word64 -> CTree GenPhase -> TermGenerator RuleTerm
genTag t node = simpleGen $ do
  omitTag <- faultyBool False
  if omitTag
    then tgGenerator $ genForCTree node
    else do
      tag <- faultyNum t
      innerTerm <- case tag of
        -- TODO remove this case once we switch away from cborg's Term
        n
          | n == 2 || n == 3 -> do
              res <- tgGenerator $ genForCTree node
              pure $ case res of
                SingleTerm (TBytesI bs) -> SingleTerm $ TBytes $ LBS.toStrict bs
                _ -> res
        _ -> tgGenerator $ genForCTree node
      case innerTerm of
        SingleTerm term -> pure . SingleTerm $ TTagged tag term
        _ -> error "Expected a single term"

genForNode :: HasCallStack => Name -> TermGenerator RuleTerm
genForNode name = deferGen $ genForCTree <$> resolveRef name

-- | Take a reference and resolve it to the relevant Tree, following multiple
-- links if necessary.
resolveRef :: Name -> CBORGen (CTree GenPhase)
resolveRef n = do
  mRule <- lookupCddl n
  -- Since we follow a reference, we decrease the 'size' of the Gen monad.
  scale (\x -> max 0 $ x - 1) $
    case mRule of
      Nothing -> error $ "Unbound reference: " <> show n
      Just val -> pure val

-- | Generate a CBOR Term corresponding to a top-level name.
--
-- Since we apply this to a monomorphised CTree, the names must be monomorphic
-- terms in the original CDDL.
--
-- This will throw an error if the generated item does not correspond to a
-- single CBOR term (e.g. if the name resolves to a group, which cannot be
-- generated outside a context).
generateFromName :: HasCallStack => Name -> CBORGen Term
generateFromName n = do
  mRule <- lookupCddl n
  case mRule of
    Nothing -> error $ "Unbound reference: " <> show n
    Just val ->
      tgGenerator (genForCTree val) >>= \case
        SingleTerm x -> pure x
        _ ->
          error $
            "Tried to generate a top-level term for "
              <> show n
              <> ", but it does not correspond to a single term."

-- | Generate a 'RuleTerm' for the type bound to the given generic
-- parameter at the enclosing rule. Use this from inside a custom generator
-- attached to a generic rule.
generateFromGRef :: HasCallStack => GRef -> CBORGen RuleTerm
generateFromGRef ref = do
  mRule <- lookupGRef ref
  case mRule of
    Nothing -> error $ "Unbound generic reference: " <> show ref
    Just val -> tgGenerator $ genForCTree val

sizeBiasedBool :: MonadGen m => m Bool
sizeBiasedBool = sized $ \sz -> (> 1) <$> choose (0, sz)

listOfScaled :: MonadGen m => m a -> m [a]
listOfScaled g = sized $ \sz -> do
  i <- choose (0, sz)
  vectorOf i $ scale (`div` (i + 1)) g

listOfScaled1 :: (MonadGen m, MonadAntiGen m) => m a -> m [a]
listOfScaled1 g = sized $ \sz -> do
  i <- choose (1, max sz 1) |! pure 0
  vectorOf i $ scale (`div` (i + 1)) g

-- | Apply an occurence indicator to a group entry
applyOccurenceIndicator ::
  OccurrenceIndicator ->
  TermGenerator RuleTerm ->
  TermGenerator RuleTerm
applyOccurenceIndicator oi oldGen = simpleGen $ case oi of
  OIOptional ->
    sizeBiasedBool >>= \case
      False -> pure $ GroupTerm mempty
      True -> tgGenerator oldGen
  OIZeroOrMore -> GroupTerm <$> listOfScaled (tgGenerator oldGen)
  OIOneOrMore -> GroupTerm <$> listOfScaled1 (tgGenerator oldGen)
  OIBounded mlb mub ->
    sized $ \sz -> do
      let
        lb = fromMaybe 0 mlb
        ub = fromMaybe (lb + fromIntegral sz) mub
      i <- fromIntegral <$> genBetween (lb, ub)
      GroupTerm <$> vectorOf i (scale (`div` (i + 1)) (tgGenerator oldGen))

valueToTerm :: Value -> TermGenerator Term
valueToTerm (Value x _) = simpleGen $ valueVariantToTerm x

valueVariantToTerm :: ValueVariant -> CBORGen Term
valueVariantToTerm (VUInt i)
  | toInteger i <= toInteger (maxBound :: Int) = pure $ TInt (fromIntegral i)
  | otherwise = pure $ TInteger (fromIntegral i)
valueVariantToTerm (VNInt i)
  | -toInteger i >= toInteger (minBound :: Int) = pure $ TInt (-fromIntegral i)
  | otherwise = pure $ TInteger (-fromIntegral i)
valueVariantToTerm (VBignum i) = pure $ TInteger i
valueVariantToTerm (VFloat16 i) = pure $ THalf i
valueVariantToTerm (VFloat32 i) = pure $ TFloat i
valueVariantToTerm (VFloat64 i) = pure $ TDouble i
valueVariantToTerm (VText t) = twiddleText t
valueVariantToTerm (VBytes b) = twiddleBytes b
valueVariantToTerm (VBool b) = pure $ TBool b

instance IndexMappable CTree GenPhase ValidatorPhase where
  mapIndex = foldCTree mapExt mapIndex
    where
      mapExt = \case
        GenRef n -> CTreeE $ VRuleRef n
        GenGenerator _ x -> mapIndex x
        GenValidator v x -> CTreeE . VValidator v $ mapIndex x

instance IndexMappable CTreeRoot GenPhase ValidatorPhase where
  mapIndex (CTreeRoot m) = CTreeRoot $ mapIndex <$> m
