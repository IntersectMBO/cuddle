{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

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
  deferGen,
  bindGen,
  genFromInterval,
  rangeInInterval,

  -- * Contstraints
  GenConstraint (..),
  showConstraint,
) where

import Codec.CBOR.Cuddle.CDDL (GRef (..), Name (..))
import Codec.CBOR.Cuddle.CDDL.CTree (CTree, CTreeRoot (..), XXCTree)
import Codec.CBOR.Cuddle.CDDL.Custom.Core (MonadCddl (..), RuleTerm)
import Codec.CBOR.Cuddle.CDDL.Custom.Validator (TermValidator)
import Codec.CBOR.Cuddle.Interval (Interval (..), boundary, contains, isEmpty)
import Control.Monad.Reader (MonadReader (..), MonadTrans (..), ReaderT (..), asks, mapReaderT)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Generics (Generic)
import GHC.Stack (HasCallStack)
import Optics.Lens (Lens')
import System.Random (Random)
import Test.AntiGen (AntiGen, MonadAntiGen (..))
import Test.QuickCheck.GenT (MonadGen (..), suchThat)
import Text.Regex.TDFA (Regex)

type data GenPhase

-- | User-supplied configuration for the generator monad.
newtype GenConfig = GenConfig
  { gcRoot :: CTreeRoot GenPhase
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

-- | Run an action with the given local generic bindings installed.
-- Used to wrap custom generators attached to generic rules so that
-- 'lookupGRef' resolves to the type bound at the enclosing rule.
withLocalGenBindings ::
  Map Name (CTree GenPhase) -> CBORGen a -> CBORGen a
withLocalGenBindings binds =
  local (\env -> env {geLocal = binds `Map.union` geLocal env})

data instance XXCTree GenPhase
  = GenRef Name
  | GenGenerator (TermGenerator RuleTerm -> TermGenerator RuleTerm) (CTree GenPhase)
  | GenValidator (TermValidator -> TermValidator) (CTree GenPhase)

class HasGenerator a where
  generatorL :: Lens' a (TermGenerator RuleTerm -> TermGenerator RuleTerm)

genFromInterval ::
  ( HasCallStack
  , MonadGen m
  , Bounded a
  , Random a
  , Ord a
  , Show a
  ) =>
  Interval a ->
  m a
genFromInterval = rangeInInterval (minBound, maxBound)

-- | Generates a value in the interval, using the given bounds in place of
-- missing boundaries. Fails if the interval is empty (see 'isEmpty').
rangeInInterval ::
  ( HasCallStack
  , MonadGen m
  , Random a
  , Ord a
  , Show a
  ) =>
  (a, a) ->
  Interval a ->
  m a
rangeInInterval (lb, ub) int@(Interval lo hi)
  | isEmpty int = error $ "rangeInInterval: empty interval " <> show int
  | otherwise = choose (boundLo, boundHi) `suchThat` contains int
  where
    boundLo = fromMaybe lb $ boundary lo
    boundHi = fromMaybe ub $ boundary hi

data GenConstraint
  = -- | Constrains the size of a string or bytestring in bytes
    Size (CTree GenPhase)
  | -- | Constrains the range of allowed values to the interval. This also covers
    -- the .gt and .lt operators.
    Range (Interval (CTree GenPhase))
  | Eq (CTree GenPhase)
  | Neq (CTree GenPhase)
  | Default (CTree GenPhase)
  | -- | Specifies the indices at which a bit is allowed to be set
    Bits (Set Integer)
  | -- | Constrains the string to ones that match the regex
    Regexp Regex
  | -- | The bytestring must match the CDDL rule
    Cbor (CTree GenPhase)
  | Cborseq (CTree GenPhase)
  | -- | Catch-all for nonstandard control operators
    CustomControl Text (CTree GenPhase)
  | And (CTree GenPhase)
  | Within (CTree GenPhase)
  deriving (Generic)

data TermGenerator a = TermGenerator
  { tgGenerator :: CBORGen a
  , tgConstrain :: GenConstraint -> Maybe (TermGenerator a)
  }
  deriving (Functor)

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
  Nothing -> error $ "Failed to apply constraint:\n" <> T.unpack (showConstraint c)

-- | A 'TermGenerator' that can only be built while generating, for example
-- because building it needs to look up a rule. Constraints applied to it are
-- kept and applied in order once it has been built.
deferGen :: CBORGen (TermGenerator a) -> TermGenerator a
deferGen mkGen = go []
  where
    go cs =
      TermGenerator
        { tgGenerator = do
            g <- mkGen
            tgGenerator $ foldr constrain g cs
        , tgConstrain = \c -> Just . go $ c : cs
        }

-- | Runs a generator action on each value the generator produces.
-- Constraints still apply to the original generator.
bindGen :: (a -> CBORGen b) -> TermGenerator a -> TermGenerator b
bindGen f tg =
  TermGenerator
    { tgGenerator = f =<< tgGenerator tg
    , tgConstrain = fmap (bindGen f) . tgConstrain tg
    }

showConstraint :: GenConstraint -> Text
showConstraint = \case
  Size _ -> ".size"
  Range _ -> ".range"
  Eq _ -> ".eq"
  Neq _ -> ".neq"
  Default _ -> ".default"
  Bits _ -> ".bits"
  Regexp _ -> ".regexp"
  Cbor _ -> ".cbor"
  Cborseq _ -> ".cborseq"
  CustomControl c _ -> "." <> c
  And _ -> ".and"
  Within _ -> ".within"

-- * IndexMappable
