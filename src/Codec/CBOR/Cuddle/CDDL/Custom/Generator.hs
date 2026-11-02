{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}

module Codec.CBOR.Cuddle.CDDL.Custom.Generator (
  GenPhase,
  CBORGen,
  XXCTree (..),
  HasGenerator (..),
  GenConfig (..),
  GenEnv (..),
  liftAntiGen,
  runCBORGen,
  withAntiGen,
  withLocalGenBindings,

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
) where

import Codec.CBOR.Cuddle.CDDL (GRef (..), Name (..))
import Codec.CBOR.Cuddle.CDDL.CTree (CTree, CTreeRoot (..), XXCTree)
import Codec.CBOR.Cuddle.CDDL.Custom.Core (MonadCddl (..), RuleTerm)
import Control.Monad.Reader (MonadReader (..), ReaderT (..), asks, mapReaderT)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Optics.Lens (Lens')
import Test.AntiGen (AntiGen)
import Test.QuickCheck.GenT (MonadGen (..))

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

liftAntiGen :: AntiGen a -> CBORGen a
liftAntiGen m = CBORGen . ReaderT $ const m

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
withAntiGen f (CBORGen m) = CBORGen $ ReaderT $ \env -> f (runReaderT m env)

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
  | GenGenerator (CBORGen RuleTerm) (CTree GenPhase)

class HasGenerator a where
  generatorL :: Lens' a (Maybe (CBORGen RuleTerm))
