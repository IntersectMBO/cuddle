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
  disableTwiddle,
  enableTwiddle,

  -- * Lifted QuickCheck functions
  arbitrary,
  scale,
  shuffle,

  -- * Custom generator helpers
  genArrayTerm,
  genBytesTerm,
  genStringTerm,
  genMapTerm,
  ifTwiddle,
) where

import Codec.CBOR.Cuddle.CDDL (GRef (..), Name (..))
import Codec.CBOR.Cuddle.CDDL.CTree (CTree, CTreeRoot (..), XXCTree)
import Codec.CBOR.Cuddle.CDDL.Custom.Core (MonadCddl (..), RuleTerm)
import Codec.CBOR.Term (Term (..))
import Control.Monad.Reader (MonadReader (..), ReaderT (..), asks, mapReaderT)
import Data.ByteString (ByteString)
import Data.ByteString.Lazy qualified as LBS
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import Data.Text.Lazy qualified as LT
import GHC.Generics (Generic)
import Optics.Lens (Lens')
import Test.AntiGen (AntiGen)
import Test.QuickCheck (Arbitrary)
import Test.QuickCheck qualified as QC
import Test.QuickCheck.GenT (MonadGen (..))
import Test.QuickCheck.GenT qualified as GenT

type data GenPhase

-- | User-supplied configuration for the generator monad. Set once at the
-- top level when calling 'runCBORGen'.
data GenConfig = GenConfig
  { gcRoot :: CTreeRoot GenPhase
  , gcTwiddle :: !Bool
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

withTwiddle :: Bool -> CBORGen a -> CBORGen a
withTwiddle t =
  local (\env -> env {geConfig = (geConfig env) {gcTwiddle = t}})

disableTwiddle :: CBORGen a -> CBORGen a
disableTwiddle = withTwiddle False

enableTwiddle :: CBORGen a -> CBORGen a
enableTwiddle = withTwiddle True

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

-- Lifted Gen functions

arbitrary :: forall a m. (MonadGen m, Arbitrary a) => m a
arbitrary = liftGen QC.arbitrary

scale :: MonadGen m => (Int -> Int) -> m a -> m a
scale f m = sized $ \sz -> resize (f sz) m

shuffle :: MonadGen m => [a] -> m [a]
shuffle = liftGen . QC.shuffle

-- Term generators

genArrayTerm :: [Term] -> CBORGen Term
genArrayTerm es =
  ifTwiddle (GenT.elements [TList es, TListI es]) (pure $ TList es)

genBytesTerm :: ByteString -> CBORGen Term
genBytesTerm bs =
  ifTwiddle (GenT.elements [TBytes bs, TBytesI $ LBS.fromStrict bs]) (pure $ TBytes bs)

genStringTerm :: T.Text -> CBORGen Term
genStringTerm t =
  ifTwiddle (GenT.elements [TString t, TStringI $ LT.fromStrict t]) (pure $ TString t)

genMapTerm :: [(Term, Term)] -> CBORGen Term
genMapTerm m =
  ifTwiddle (GenT.elements [TMap m, TMapI m]) (pure $ TMap m)

ifTwiddle :: CBORGen a -> CBORGen a -> CBORGen a
ifTwiddle yes no = do
  twiddle <- asks (gcTwiddle . geConfig)
  if twiddle then yes else no
