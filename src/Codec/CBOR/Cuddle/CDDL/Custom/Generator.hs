{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}

module Codec.CBOR.Cuddle.CDDL.Custom.Generator (
  GenPhase,
  CBORGen,
  XXCTree (..),
  HasGenerator (..),
  GenConfig (..),
  GenEnv (..),
  runCBORGen,
  withAntiGen,
  withLocalGenBindings,

  -- * Term generator
  TermGenerator (..),
  simpleGen,
  constrain,

  -- * Twiddling
  TwiddleConfig (..),
  TwiddlePolicy (..),
  isIndefiniteAllowed,
  isDefiniteAllowed,
  twiddleUniform,
  twiddleAll,
  twiddleNothing,
  withTwiddle,
  disableTwiddle,

  -- * Contstraints
  GenConstraint (..),

  -- * Interval
  Interval (..),
  IntervalBound (..),
  isEmpty,
  intersect,
  singleton,
  contains,
  genFromInterval,
) where

import Codec.CBOR.Cuddle.CBOR.Canonical (CanonicalTerm)
import Codec.CBOR.Cuddle.CDDL (GRef (..), Name (..))
import Codec.CBOR.Cuddle.CDDL.CTree (CTree, CTreeRoot (..), XXCTree)
import Codec.CBOR.Cuddle.CDDL.Custom.Core (MonadCddl (..), RuleTerm)
import Codec.CBOR.Cuddle.CDDL.Custom.Validator (TermValidator)
import Codec.CBOR.Term (Term)
import Control.Monad.Reader (MonadReader (..), MonadTrans (..), ReaderT (..), asks, mapReaderT)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Text (Text)
import Data.Word (Word64, Word8)
import GHC.Generics (Generic)
import Optics.Lens (Lens')
import System.Random (Random)
import Test.AntiGen (AntiGen, MonadAntiGen (..))
import Test.QuickCheck.GenT (MonadGen (..), suchThat)
import Text.Regex.TDFA (Regex)

type data GenPhase

data TwiddlePolicy
  = DefiniteOnly
  | IndefiniteOnly
  | DefiniteAndIndefinite
  deriving (Generic, Show, Eq, Ord, Enum)

isDefiniteAllowed :: TwiddlePolicy -> Bool
isDefiniteAllowed IndefiniteOnly = False
isDefiniteAllowed _ = True

isIndefiniteAllowed :: TwiddlePolicy -> Bool
isIndefiniteAllowed DefiniteOnly = False
isIndefiniteAllowed _ = True

data TwiddleConfig = TwiddleConfig
  { tcBytes :: !TwiddlePolicy
  , tcArrays :: !TwiddlePolicy
  , tcText :: !TwiddlePolicy
  , tcMaps :: !TwiddlePolicy
  }
  deriving (Generic, Show, Eq, Ord)

twiddleUniform :: TwiddlePolicy -> TwiddleConfig
twiddleUniform policy =
  TwiddleConfig
    { tcBytes = policy
    , tcArrays = policy
    , tcText = policy
    , tcMaps = policy
    }

twiddleAll :: TwiddleConfig
twiddleAll = twiddleUniform DefiniteAndIndefinite

twiddleNothing :: TwiddleConfig
twiddleNothing = twiddleUniform DefiniteOnly

-- | User-supplied configuration for the generator monad.
data GenConfig = GenConfig
  { gcRoot :: CTreeRoot GenPhase
  , gcTwiddle :: !TwiddleConfig
  }
  deriving (Generic)

-- | Runtime environment for the generator monad: the user-supplied
-- 'GenConfig' plus the bindings active at the current point.
data GenEnv = GenEnv
  { geConfig :: GenConfig
  , geLocal :: Map Name (CTree GenPhase)
  }
  deriving (Generic)

newtype CBORGen a = CBORGen (ReaderT GenEnv AntiGen a)
  deriving (Functor, Applicative, Monad, MonadReader GenEnv)

instance MonadGen CBORGen where
  liftGen g = CBORGen $ ReaderT $ \_ -> liftGen g
  variant n (CBORGen m) = CBORGen $ mapReaderT (variant n) m
  sized f = CBORGen . ReaderT $ \env -> sized $ \n ->
    let CBORGen m = f n in runReaderT m env
  resize n (CBORGen m) = CBORGen $ mapReaderT (resize n) m
  choose rng = CBORGen . ReaderT $ \_ -> choose rng

instance MonadAntiGen CBORGen where
  liftAntiGen = CBORGen . lift
  mapAntiGen f (CBORGen m) = CBORGen $ mapReaderT f m

runCBORGen :: GenConfig -> CBORGen a -> AntiGen a
runCBORGen cfg (CBORGen m) =
  runReaderT m GenEnv {geConfig = cfg, geLocal = Map.empty}

instance MonadCddl CBORGen where
  type Phase CBORGen = GenPhase

  lookupCddl n = do
    CTreeRoot root <- asks (gcRoot . geConfig)
    pure $ Map.lookup n root

  lookupGRef (GRef t) = do
    binds <- asks geLocal
    pure $ Map.lookup (Name t) binds

withAntiGen :: (AntiGen a -> AntiGen b) -> CBORGen a -> CBORGen b
withAntiGen f (CBORGen m) = CBORGen $ mapReaderT f m

withTwiddle :: (TwiddleConfig -> TwiddleConfig) -> CBORGen a -> CBORGen a
withTwiddle f =
  local
    ( \env ->
        env
          { geConfig =
              (geConfig env)
                { gcTwiddle = f (gcTwiddle $ geConfig env)
                }
          }
    )

disableTwiddle :: CBORGen a -> CBORGen a
disableTwiddle = withTwiddle $ const twiddleNothing

-- | Run an action with the given local generic bindings installed.
-- Used to wrap custom generators attached to generic rules so that
-- 'lookupGRef' resolves to the type bound at the enclosing rule.
withLocalGenBindings ::
  Map Name (CTree GenPhase) -> CBORGen a -> CBORGen a
withLocalGenBindings binds =
  local (\env -> env {geLocal = binds `Map.union` geLocal env})

data instance XXCTree GenPhase
  = GenRef Name
  | GenGenerator (TermGenerator RuleTerm) (CTree GenPhase)
  | GenValidator TermValidator (CTree GenPhase)

class HasGenerator a where
  generatorL :: Lens' a (Maybe (TermGenerator RuleTerm))

data IntervalBound a
  = OpenBound a
  | ClosedBound a
  | Unbounded
  deriving (Eq, Show)

boundary :: IntervalBound a -> Maybe a
boundary = \case
  Unbounded -> Nothing
  OpenBound x -> Just x
  ClosedBound x -> Just x

data Interval a = Interval (IntervalBound a) (IntervalBound a)
  deriving (Eq, Show)

-- | This function checks whether the interval contains any elements. It does
-- not take the bounds of the type into account, it only checks whether the
-- lower bound is smaller than the upper bound
isEmpty :: Ord a => Interval a -> Bool
isEmpty = \case
  Interval (ClosedBound lo) (ClosedBound hi) -> lo > hi
  Interval lo hi
    | Just l <- boundary lo
    , Just h <- boundary hi ->
        l >= h
  _ -> False

-- | Computes the intersection of two intervals. The result may be empty (see
-- 'isEmpty').
intersect :: Ord a => Interval a -> Interval a -> Interval a
intersect (Interval lo1 hi1) (Interval lo2 hi2) =
  Interval (tighter (>) lo1 lo2) (tighter (<) hi1 hi2)
  where
    -- Picks the more restrictive of two bounds. @better x y@ holds when @x@
    -- is strictly more restrictive than @y@. On equal boundaries an open bound
    -- is more restrictive than a closed one.
    tighter _ Unbounded b = b
    tighter _ a Unbounded = a
    tighter better a b
      | Just x <- boundary a
      , Just y <- boundary b =
          if
            | better x y -> a
            | better y x -> b
            | OpenBound _ <- a -> a
            | otherwise -> b
    tighter _ a _ = a

singleton :: a -> Interval a
singleton x = Interval (ClosedBound x) (ClosedBound x)

contains :: Ord a => Interval a -> a -> Bool
contains (Interval lo hi) x = satisifesUpper && satisfiesLower
  where
    satisifesUpper = case hi of
      Unbounded -> True
      OpenBound y -> x < y
      ClosedBound y -> x <= y
    satisfiesLower = case lo of
      Unbounded -> True
      OpenBound y -> y < x
      ClosedBound y -> y <= x

instance Ord a => Semigroup (Interval a) where
  (<>) = intersect

instance Ord a => Monoid (Interval a) where
  mempty = Interval Unbounded Unbounded

genFromInterval ::
  ( MonadGen m
  , Bounded a
  , Random a
  , Ord a
  ) =>
  Interval a ->
  m a
genFromInterval int@(Interval lo hi) = choose (boundLo, boundHi) `suchThat` contains int
  where
    boundLo = fromMaybe minBound $ boundary lo
    boundHi = fromMaybe maxBound $ boundary hi

data GenConstraint
  = -- | Constrains the size of a string or bytestring in bytes
    Size (Interval CanonicalTerm)
  | -- | Constrains the range of allowed values to the interval. This also covers
    -- the .gt and .lt operators.
    Range (Interval CanonicalTerm)
  | Eq CanonicalTerm
  | Neq CanonicalTerm
  | -- | Specifies the indices at which a bit is allowed to be set
    Bits (Set Word8)
  | -- | Constrains the string to ones that match the regex
    Regexp Regex
  | -- | The bytestring must match the CDDL rule
    Cbor (CTree GenPhase)
  | -- | Catch-all for nonstandard control operators
    CustomControl Text Term
  deriving (Generic)

data TermGenerator a = TermGenerator
  { tgGenerator :: CBORGen a
  , tgConstrain :: GenConstraint -> Maybe (TermGenerator a)
  }

-- | Constructs a @TermGenerator@ that fails whenever a control operator is
-- applied to it.
simpleGen :: CBORGen a -> TermGenerator a
simpleGen gen =
  TermGenerator
    { tgGenerator = gen
    , tgConstrain = const Nothing
    }

constrain :: GenConstraint -> TermGenerator a -> TermGenerator a
constrain c (TermGenerator _ f) = case f c of
  Just g -> g
  Nothing -> error "Failed to apply constraint"
