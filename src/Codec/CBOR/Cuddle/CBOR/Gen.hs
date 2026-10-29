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

-- | Generate example CBOR given a CDDL specification
module Codec.CBOR.Cuddle.CBOR.Gen (
  generateFromName,
  generateFromGRef,
  GenPhase,
  XXCTree (..),
) where

#if MIN_VERSION_random(1,3,0)
#endif
import Codec.CBOR.Cuddle.CBOR.Canonical (nintMin, toCanonical, uintMax)
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
  PTerm (..),
 )
import Codec.CBOR.Cuddle.CDDL.CTree qualified as CTree
import Codec.CBOR.Cuddle.CDDL.CtlOp qualified as CtlOp
import Codec.CBOR.Cuddle.CDDL.Custom.Core (MonadCddl (..), RuleTerm (..))
import Codec.CBOR.Cuddle.CDDL.Custom.Generator (
  CBORGen,
  GenConfig (..),
  GenEnv (..),
  GenPhase,
  disableTwiddle,
 )
import Codec.CBOR.Cuddle.CDDL.Resolve (XXCTree (..), showSimple)
import Codec.CBOR.Term (Term (..))
import Codec.CBOR.Term qualified as CBOR
import Codec.CBOR.Write qualified as CBOR
import Control.Monad (zipWithM, (<=<))
import Control.Monad.Reader (asks)
import Data.ByteString (ByteString)
import Data.ByteString.Lazy qualified as LBS
import Data.Char (chr)
import Data.Functor ((<&>))
import Data.List (sortOn)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Ord (Down (..))
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Internal.Encoding.Utf8 (utf8Length)
import Data.Text.Lazy qualified as LT
import Data.Text.Lazy qualified as TL
import Data.Text.Lazy.Builder (toLazyText)
import Data.Text.Lazy.Builder qualified as LB
import Data.Word (Word64, Word8)
import GHC.Stack (HasCallStack)
import Numeric.Half (Half (..), fromHalf)
import Prettyprinter (Pretty (..), layoutCompact)
import Prettyprinter.Render.Text (renderStrict)
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
import Test.QuickCheck.GenT (MonadGen (..), elements, frequency, listOf, oneof, suchThat, vectorOf)

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

genHalf :: MonadGen m => m Float
genHalf = do
  half <- Half <$> arbitrary
  if isDenormalized half
    then genHalf
    else pure $ fromHalf half

twiddleString :: Text -> CBORGen Term
twiddleString t = do
  twiddle <- asks (gcTwiddle . geConfig)
  if twiddle
    then ($ t) <$> elements [TString, TStringI . TL.fromStrict]
    else pure $ TString t

twiddleList :: [Term] -> CBORGen Term
twiddleList t = do
  twiddle <- asks (gcTwiddle . geConfig)
  if twiddle
    then ($ t) <$> elements [TList, TListI]
    else pure $ TList t

twiddleBytes :: ByteString -> CBORGen Term
twiddleBytes t = do
  twiddle <- asks (gcTwiddle . geConfig)
  if twiddle
    then ($ t) <$> elements [TBytes, TBytesI . LBS.fromStrict]
    else pure $ TBytes t

twiddleMap :: [(Term, Term)] -> CBORGen Term
twiddleMap t = do
  twiddle <- asks (gcTwiddle . geConfig)
  if twiddle
    then ($ t) <$> elements [TMap, TMapI]
    else pure $ TMap t

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
    , twiddleString . T.pack =<< arbitrary
    , twiddleList =<< listOf smallerTerm
    , twiddleMap =<< listOf ((,) <$> smallerTerm <*> smallerTerm)
    , TTagged <$> choose (6, maxBound :: Word64) <*> smallerTerm
    , TBool <$> arbitrary
    , pure TNull
    , TSimple <$> elements simple
    , THalf <$> genHalf
    , TFloat <$> arbitrary
    , TDouble <$> arbitrary
    ]
  where
    smallerTerm :: CBORGen Term
    smallerTerm = scale (`div` 5) genTerm

genNBytes :: MonadGen m => Int -> m ByteString
genNBytes n = liftGen (uniformByteStringM n QC)

genBytes :: MonadGen m => m ByteString
genBytes = sized $ \sz -> do
  numElems <- choose (0, sz)
  genNBytes numElems

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

genText :: MonadGen m => m Text
genText = sized $ \sz -> genNBytesText =<< choose (0, sz)

-- | Primitive types defined by the CDDL specification, with their generators
genPostlude :: PTerm -> CBORGen Term
genPostlude pt = genPTerm =<< faultyPTerm pt
  where
    genExcluding ls =
      elements (filter (`notElem` ls) [minBound .. maxBound])
    nonPInteger p =
      pure p |! genExcluding [PTUInt, PTNInt, PTInt, PTAny]
    -- \| Introduces a decision point that can change the type of the CBOR term that is generated
    faultyPTerm t = reweigh 0.1 $
      case t of
        PTAny -> pure PTAny
        p@PTUInt -> nonPInteger p
        p@PTNInt -> nonPInteger p
        p@PTInt -> nonPInteger p
        p -> pure p |! genExcluding [PTAny, p]
    genUInt = choose (0, uintMax)
    genNInt = choose (nintMin, -1)
    genAboveUInt = choose (uintMax + 1, 2 * uintMax)
    genBelowNInt = choose (2 * nintMin, nintMin - 1)
    -- \| Given a CDDL postlude type, generates a value of that type
    genPTerm = \case
      PTBool -> TBool <$> arbitrary
      -- For integers, introduce decision points that sometimes generate
      -- out-of-bounds values
      PTUInt -> TInteger <$> genUInt |! oneof [genNInt, genBelowNInt, genAboveUInt]
      PTNInt -> TInteger <$> genNInt |! oneof [genUInt, genBelowNInt, genAboveUInt]
      PTInt -> TInteger <$> choose (nintMin, uintMax)
      PTHalf -> THalf <$> genHalf
      PTFloat -> TFloat <$> arbitrary
      PTDouble -> TDouble <$> arbitrary
      PTBytes -> twiddleBytes =<< genBytes
      PTText -> twiddleString =<< genText
      PTAny -> genTerm
      PTNil -> pure TNull
      PTUndefined -> pure $ TSimple 23

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

genSized :: HasCallStack => Word64 -> CTree GenPhase -> CBORGen RuleTerm
genSized s target = annotateTerm target $ case target of
  CTree.Postlude PTText -> fmap SingleTerm . twiddleString =<< genNBytesText (fromIntegral s)
  CTree.Postlude PTBytes -> fmap SingleTerm . twiddleBytes =<< genNBytes (fromIntegral s)
  CTree.Postlude PTUInt -> SingleTerm . TInteger <$> choose (0, 256 ^ s - 1)
  _ -> error "Cannot apply size operator to target "

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

-- | Annotate a generator with the label derived from a CTree node.
-- Control nodes are transparent — the annotation comes from the target inside.
annotateTerm :: CTree GenPhase -> CBORGen a -> CBORGen a
annotateTerm = \case
  CTree.Literal _ -> annotate "literal"
  CTree.Postlude pt -> annotate $ renderStrict . layoutCompact $ pretty pt
  CTree.Map _ -> annotate "map"
  CTree.Array _ -> annotate "array"
  CTree.Choice _ -> id
  CTree.Group _ -> annotate "group"
  CTree.KV {} -> annotate "kv"
  CTree.Occur {} -> id
  CTree.Range {} -> annotate "range"
  CTree.Control {} -> id
  CTree.Enum _ -> annotate "enum"
  CTree.Unwrap _ -> annotate "unwrap"
  CTree.Tag {} -> annotate "tag"
  CTree.CTreeE (GenRef n) -> annotate (unName n)
  CTree.CTreeE (GenGenerator _ _) -> annotate "custom_generator"

genForCTree :: HasCallStack => CTree GenPhase -> CBORGen RuleTerm
genForCTree node = annotateTerm node $ case node of
  CTree.Literal v -> SingleTerm <$> valueToTerm v
  CTree.Postlude pt -> SingleTerm <$> genPostlude pt
  CTree.Map nodes -> genMap nodes
  CTree.Array nodes -> genArray nodes
  CTree.Choice (NE.toList -> nodes) -> do
    ix <- choose (0, length nodes - 1)
    genForCTree $ nodes !! ix
  CTree.Group nodes -> GroupTerm <$> traverse genForCTree nodes
  CTree.KV key value _cut -> genKV key value
  CTree.Occur item occurs ->
    applyOccurenceIndicator occurs (genForCTree item)
  CTree.Range from to bounds -> genRange from to bounds
  CTree.Control op target controller -> genControl op target controller
  CTree.Enum tree -> genEnum tree
  CTree.Unwrap n -> genForCTree n
  CTree.Tag t n -> genTag t n
  CTree.CTreeE (GenRef n) -> genForNode n
  CTree.CTreeE (GenGenerator gen _) -> gen

-- | Generate a map from a list of nodes
genMap ::
  HasCallStack => [CTree GenPhase] -> CBORGen RuleTerm
genMap nodes = do
  let
    elemsNeeded KV {} = 1
    elemsNeeded (Occur _ OIOneOrMore) = 1
    elemsNeeded (Occur _ (OIBounded (Just lo) _)) = lo
    elemsNeeded _ = 0

    tryGenKV ::
      Int -> Map.Map Term Term -> CTree GenPhase -> CTree GenPhase -> CBORGen (Maybe (Term, Term))
    tryGenKV nTries m kNode vNode
      | Map.null m = go nTries
      | otherwise =
          go nTries
            ||! oneof
              [ reuseKey #! "duplicateKey"
              , reuseKeyValue #! "duplicateKV"
              ]
      where
        canonicalKeys = toCanonical <$> Map.keys m
        unS (SingleTerm x) = x
        unS x = error $ "Expected single, got " <> show x
        genFromNode n = unS <$> scale (`div` 2) (genForCTree n)
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
          k <- elements $ Map.keys m
          v <- genFromNode vNode #! "value"
          pure $ Just (k, v)
        reuseKeyValue = Just <$> elements (Map.toList m)

    genNodes :: Int -> Map.Map Term Term -> [CTree GenPhase] -> CBORGen (Maybe (Map.Map Term Term))
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
              Just (k, v) -> next (Map.insert k v m) ns ||! same m ns
              Nothing -> pure Nothing
          Occur kv@(KV kNode vNode _) oi -> case oi of
            OIOptional -> do
              mt <- optGenKV kNode vNode
              case mt of
                Just (k, v) -> next (Map.insert k v m) ns
                Nothing -> same m ns
            OIZeroOrMore -> do
              mt <- optGenKV kNode vNode
              case mt of
                Just (k, v) -> next (Map.insert k v m) (n : ns)
                Nothing -> same m ns
            OIOneOrMore -> genNodes i m (kv : Occur kv OIZeroOrMore : ns) ||! same m ns
            OIBounded mlb mub -> do
              sz <- fromIntegral <$> liftGen getSize
              let lowerBound = fromMaybe 0 mlb
              let mGenOutOfBounds =
                    oneof
                      <$> fmap (\lb -> [genBetween (0, lb - 1) | lb > 0]) mlb
                        <> fmap (\ub -> [genBetween (ub + 1, max sz $ ub + 2)]) mub
                  genInBounds = genBetween (lowerBound, fromMaybe (max lowerBound sz) mub)
              let
                genElems i' m' nElems
                  | nElems <= 0 =
                      scale (\s -> max 0 (s - 1)) $ genNodes (i' + 1) m' ns
                  | otherwise = do
                      mKV <- annotate (T.pack $ show i') $ tryGenKV 100 m kNode vNode
                      case mKV of
                        Just (k, v) -> genElems (i' + 1) (Map.insert k v m') $ nElems - 1
                        Nothing -> pure Nothing
              nElems <- case mGenOutOfBounds of
                Just genOutOfBounds -> genInBounds ||! genOutOfBounds
                Nothing -> genInBounds
              genElems i m nElems
          node -> error $ "Unexpected node: " <> showSimple node
  mItems <- genNodes 0 Map.empty $ sortOn (Down . elemsNeeded) nodes
  case mItems of
    Just items -> do
      shuffledItems <- liftGen . shuffle $ Map.toList items
      SingleTerm <$> twiddleMap shuffledItems
    Nothing -> error "Failed to generate unique keys for map after max retries"

-- | Generate an array from a list of nodes
genArray :: HasCallStack => [CTree GenPhase] -> CBORGen RuleTerm
genArray nodes = do
  items <-
    singleTermList . flattenWrappedList
      <$> zipWithM
        (\i node -> annotate (T.pack $ show i) $ genForCTree node)
        [0 :: Int ..]
        nodes
  case items of
    Just ts -> SingleTerm <$> twiddleList ts
    Nothing -> error "Something weird happened which shouldn't be possible"

-- | Generate a key-value pair
genKV :: HasCallStack => CTree GenPhase -> CTree GenPhase -> CBORGen RuleTerm
genKV key value = do
  kg <- annotate "key" $ genForCTree key
  vg <- annotate "value" $ genForCTree value
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
  term1 <- dropNegativeGen $ genForCTree from
  term2 <- dropNegativeGen $ genForCTree to
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

-- | Generate a value with a control operator applied
genControl ::
  HasCallStack =>
  CtlOp.CtlOp ->
  CTree GenPhase ->
  CTree GenPhase ->
  CBORGen RuleTerm
genControl op target controller = annotateTerm target $ do
  resolvedController <- case controller of
    CTreeE (GenRef n) -> dropNegativeGen $ resolveRef n
    x -> pure x
  case (op, resolvedController) of
    (CtlOp.Le, CTree.Literal (Value (VUInt n) _)) -> case target of
      CTree.Postlude PTUInt -> SingleTerm . TInteger <$> choose (0, fromIntegral n)
      _ -> error "Cannot apply le operator to target"
    (CtlOp.Le, _) -> error $ "Invalid controller for .le operator: " <> showSimple controller
    (CtlOp.Lt, CTree.Literal (Value (VUInt n) _)) -> case target of
      CTree.Postlude PTUInt -> SingleTerm . TInteger <$> choose (0, fromIntegral n - 1)
      _ -> error "Cannot apply lt operator to target"
    (CtlOp.Lt, _) -> error $ "Invalid controller for .lt operator: " <> showSimple controller
    (CtlOp.Size, CTree.Literal (Value (VUInt s) _)) -> do
      s' <- pure s |! sized (\sz -> choose (0, fromIntegral sz) `suchThat` (/= s))
      genSized s' target
    (CtlOp.Size, CTree.Range {CTree.from, CTree.to}) ->
      case (from, to) of
        (CTree.Literal (Value (VUInt f) _), CTree.Literal (Value (VUInt t) _)) -> do
          s <- sized $ \sz ->
            antiChoose
              (fromIntegral f, fromIntegral t)
              (0, max (succ t) $ fromIntegral sz)
          genSized s target
        _ ->
          error $
            "Invalid controller for .size operator: "
              <> showSimple controller
    (CtlOp.Size, _) ->
      error $
        "Invalid controller for .size operator: "
          <> showSimple controller
    (CtlOp.Cbor, _) -> do
      enc <- genForCTree controller
      case enc of
        SingleTerm x -> fmap SingleTerm . twiddleBytes $ CBOR.toStrictByteString (CBOR.encodeTerm x)
        _ -> error "Controller does not correspond to a single term"
    (c, _) -> error $ "Controller not yet implemented: " <> show c

-- | Generate a value from an enum
genEnum :: HasCallStack => CTree GenPhase -> CBORGen RuleTerm
genEnum tree = case tree of
  CTree.Group trees -> do
    ix <- choose (0, length trees - 1)
    genForCTree $ trees !! ix
  _ -> error "Attempt to form an enum from something other than a group"

-- | Generate a tagged value
genTag :: HasCallStack => Word64 -> CTree GenPhase -> CBORGen RuleTerm
genTag t node = do
  omitTag <- faultyBool False
  if omitTag
    then genForCTree node
    else do
      tag <- faultyNum t
      enc <- case tag of
        n
          | n == 2 || n == 3 ->
              -- TODO remove this once `cborg` can decode indefinite bytes in bignums
              disableTwiddle $ genForCTree node
        _ -> genForCTree node
      case enc of
        SingleTerm x -> pure $ SingleTerm $ TTagged tag x
        _ -> error "Tag controller does not correspond to a single term"

genForNode :: HasCallStack => Name -> CBORGen RuleTerm
genForNode = genForCTree <=< resolveRef

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
      genForCTree val >>= \case
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
    Just val -> genForCTree val

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
  CBORGen RuleTerm ->
  CBORGen RuleTerm
applyOccurenceIndicator OIOptional oldGen =
  sizeBiasedBool >>= \case
    False -> pure $ GroupTerm mempty
    True -> oldGen
applyOccurenceIndicator OIZeroOrMore oldGen =
  GroupTerm <$> listOfScaled oldGen
applyOccurenceIndicator OIOneOrMore oldGen =
  GroupTerm <$> listOfScaled1 oldGen
applyOccurenceIndicator (OIBounded mlb mub) oldGen =
  sized $ \sz -> do
    let
      lb = fromMaybe 0 mlb
      ub = fromMaybe (lb + fromIntegral sz) mub
    i <- fromIntegral <$> genBetween (lb, ub)
    GroupTerm <$> vectorOf i (scale (`div` (i + 1)) oldGen)

valueToTerm :: Value -> CBORGen Term
valueToTerm (Value x _) = valueVariantToTerm x

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
valueVariantToTerm (VText t) = twiddleString t
valueVariantToTerm (VBytes b) = twiddleBytes b
valueVariantToTerm (VBool b) = pure $ TBool b
