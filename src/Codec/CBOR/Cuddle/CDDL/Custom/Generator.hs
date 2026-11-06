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

  -- * Twiddling
  CodecConfig (..),
  LengthPolicy (..),
  isIndefiniteAllowed,
  isDefiniteAllowed,
  uniformLengthPolicy,
  twiddleAll,
  twiddleNothing,
  withCodecConfig,
  disableTwiddle,
) where

import Codec.CBOR.Cuddle.CDDL (GRef (..), Name (..))
import Codec.CBOR.Cuddle.CDDL.CTree (CTree, CTreeRoot (..), XXCTree)
import Codec.CBOR.Cuddle.CDDL.Custom.Core (MonadCddl (..), RuleTerm)
import Codec.CBOR.Cuddle.CDDL.Custom.Validator (TermValidator)
import Control.Monad.Reader (MonadReader (..), MonadTrans (..), ReaderT (..), asks, mapReaderT)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import GHC.Generics (Generic)
import Optics.Lens (Lens')
import Test.AntiGen (AntiGen, MonadAntiGen (..))
import Test.QuickCheck.GenT (MonadGen (..))

type data GenPhase

data LengthPolicy
  = DefiniteOnly
  | IndefiniteOnly
  | DefiniteAndIndefinite
  deriving (Generic, Show, Eq, Ord, Enum)

isDefiniteAllowed :: LengthPolicy -> Bool
isDefiniteAllowed IndefiniteOnly = False
isDefiniteAllowed _ = True

isIndefiniteAllowed :: LengthPolicy -> Bool
isIndefiniteAllowed DefiniteOnly = False
isIndefiniteAllowed _ = True

data CodecConfig = CodecConfig
  { ccBytesLengthPolicy :: !LengthPolicy
  , ccArraysLengthPolicy :: !LengthPolicy
  , ccTextLengthPolicy :: !LengthPolicy
  , ccMapsLengthPolicy :: !LengthPolicy
  }
  deriving (Generic, Show, Eq, Ord)

uniformLengthPolicy :: LengthPolicy -> CodecConfig
uniformLengthPolicy policy =
  CodecConfig
    { ccBytesLengthPolicy = policy
    , ccArraysLengthPolicy = policy
    , ccTextLengthPolicy = policy
    , ccMapsLengthPolicy = policy
    }

twiddleAll :: CodecConfig
twiddleAll = uniformLengthPolicy DefiniteAndIndefinite

twiddleNothing :: CodecConfig
twiddleNothing = uniformLengthPolicy DefiniteOnly

-- | User-supplied configuration for the generator monad.
data GenConfig = GenConfig
  { gcRoot :: CTreeRoot GenPhase
  , gcTwiddle :: !CodecConfig
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

withCodecConfig :: (CodecConfig -> CodecConfig) -> CBORGen a -> CBORGen a
withCodecConfig f =
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
disableTwiddle = withCodecConfig $ const twiddleNothing

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
  | GenValidator TermValidator (CTree GenPhase)

class HasGenerator a where
  generatorL :: Lens' a (Maybe (CBORGen RuleTerm))
