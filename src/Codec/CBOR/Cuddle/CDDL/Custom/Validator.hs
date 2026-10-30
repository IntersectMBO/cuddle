{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}

module Codec.CBOR.Cuddle.CDDL.Custom.Validator (
  TermValidator,
  ValidatorPhase,
  Validator,
  CustomValidatorResult (..),
  XXCTree (..),
  HasValidator (..),
  ValidateEnv (..),
  withLocalValidateBindings,
  runValidator,
) where

import Codec.CBOR.Cuddle.CDDL (GRef (..), Name (..))
import Codec.CBOR.Cuddle.CDDL.CTree (CTree, CTreeRoot (..), XXCTree)
import Codec.CBOR.Cuddle.CDDL.Custom.Core (MonadCddl (..), RuleTerm)
import Control.Monad.Reader (MonadReader (..), ReaderT (..), asks)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import GHC.Generics (Generic)
import Optics.Lens (Lens')

type data ValidatorPhase

data instance XXCTree ValidatorPhase
  = VRuleRef Name
  | VValidator TermValidator (CTree ValidatorPhase)

class HasValidator a where
  validatorL :: Lens' a (Maybe TermValidator)

data CustomValidatorResult
  = CustomValidatorSuccess
  | CustomValidatorFailure Text
  deriving (Generic, Show, Eq)

data ValidateEnv = ValidateEnv
  { veRoot :: CTreeRoot ValidatorPhase
  , veLocal :: Map Name (CTree ValidatorPhase)
  }

newtype Validator a = Validator (ReaderT ValidateEnv (Either Text) a)
  deriving (Functor, Applicative, Monad, MonadReader ValidateEnv)

type TermValidator = RuleTerm -> Validator ()

instance MonadCddl Validator where
  type Phase Validator = ValidatorPhase

  lookupCddl n = do
    CTreeRoot root <- asks veRoot
    pure $ Map.lookup n root

  lookupGRef (GRef t) = do
    binds <- asks veLocal
    pure $ Map.lookup (Name t) binds

instance MonadFail Validator where
  fail msg = Validator . ReaderT $ \_ -> Left $ T.pack msg

-- | Run an action with the given local generic bindings installed.
withLocalValidateBindings ::
  Map Name (CTree ValidatorPhase) -> Validator a -> Validator a
withLocalValidateBindings binds =
  local (\env -> env {veLocal = binds `Map.union` veLocal env})

runValidator ::
  Validator () -> CTreeRoot ValidatorPhase -> CustomValidatorResult
runValidator (Validator m) cddl =
  either CustomValidatorFailure (const CustomValidatorSuccess) $
    runReaderT m ValidateEnv {veRoot = cddl, veLocal = Map.empty}
