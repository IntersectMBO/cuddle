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
) where

import Codec.CBOR.Cuddle.CDDL (GRef (..), Name (..))
import Codec.CBOR.Cuddle.CDDL.CTree (CTree, CTreeRoot (..), XXCTree)
import Codec.CBOR.Cuddle.CDDL.Custom.Core (MonadCddl (..), RuleTerm)
import Codec.CBOR.Cuddle.CDDL.Custom.Validator (TermValidator)
import Codec.CBOR.Term (Term)
import Control.Monad.Reader (MonadReader (..), MonadTrans (..), ReaderT (..), asks, mapReaderT)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Text (Text)
import Data.Word (Word64, Word8)
import GHC.Generics (Generic)
import Optics.Lens (Lens')
import Test.AntiGen (AntiGen, MonadAntiGen (..))
import Test.QuickCheck.GenT (MonadGen (..))
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
  | GenGenerator TermGenerator (CTree GenPhase)
  | GenValidator TermValidator (CTree GenPhase)

class HasGenerator a where
  generatorL :: Lens' a (Maybe TermGenerator)

data IntervalBound a
  = OpenBound a
  | ClosedBound a
  | Unbounded
  deriving (Eq, Show)

data Interval a = Interval (IntervalBound a) (IntervalBound a)
  deriving (Eq, Show)

data GenConstraint
  = -- | Constrains the size of a string or bytestring in bytes
    Size (Interval Word64)
  | -- | Constrains the range of allowed values to the interval. This also covers
    -- the .gt and .lt operators.
    Range (Interval Word64)
  | Eq Term
  | Neq Term
  | -- | Specifies the indices at which a bit is allowed to be set
    Bits (Set Word8)
  | -- | Constrains the string to ones that match the regex
    Regexp Regex
  | -- | The bytestring must match the CDDL rule
    Cbor (CTree GenPhase)
  | -- | Catch-all for nonstandard control operators
    CustomControl Text Term
  deriving (Generic)

data TermGenerator = TermGenerator
  { tgGenerator :: CBORGen RuleTerm
  , tgConstrain :: GenConstraint -> Maybe TermGenerator
  }

-- | Constructs a @TermGenerator@ that fails whenever a control operator is
-- applied to it.
simpleGen :: CBORGen RuleTerm -> TermGenerator
simpleGen gen =
  TermGenerator
    { tgGenerator = gen
    , tgConstrain = const Nothing
    }

constrain :: GenConstraint -> TermGenerator -> TermGenerator
constrain c (TermGenerator _ f) = case f c of
  Just g -> g
  Nothing -> error "Failed to apply constraint"
