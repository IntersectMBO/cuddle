{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}

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

  -- * Custom validator helpers
  validateInt,
  validateUInt,
  validateNInt,
  validateArrayTerm,
  validateBytesTerm,
  validateStringTerm,
  validateMapTerm,
  validateNonEmpty,
  validateUniqueList,
  unwrapSingle,
) where

import Codec.CBOR.Cuddle.CBOR.Canonical (toCanonical)
import Codec.CBOR.Cuddle.CDDL (GRef (..), Name (..))
import Codec.CBOR.Cuddle.CDDL.CTree (CTree, CTreeRoot (..), nintMin, uintMax)
import Codec.CBOR.Cuddle.CDDL.Custom.Core (MonadCddl (..), RuleTerm (..))
import Codec.CBOR.Cuddle.CDDL.Custom.Generator (XXCTree)
import Codec.CBOR.Term (Term (..))
import Control.Monad.Reader (MonadReader (..), ReaderT (..), asks)
import Data.Bifunctor (Bifunctor (..))
import Data.ByteString (ByteString)
import Data.ByteString.Lazy qualified as LBS
import Data.Foldable (Foldable (..))
import Data.List.NonEmpty (NonEmpty, nonEmpty)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as T
import Data.Text.Lazy qualified as LT
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

-- * Helpers

validateInt :: Term -> Validator Integer
validateInt (TInt (toInteger -> x))
  | x >= nintMin && x <= uintMax = pure x
  | otherwise = fail "Number not in int range"
validateInt _ = fail "Expected int"

validateUInt :: Term -> Validator Integer
validateUInt (TInt (toInteger -> x))
  | x >= 0 && x <= uintMax = pure x
  | otherwise = fail "Number not in uint range"
validateUInt _ = fail "Expected uint"

validateNInt :: Term -> Validator Integer
validateNInt (TInt (toInteger -> x))
  | x >= nintMin && x < 0 = pure x
  | otherwise = fail "Number not in nint range"
validateNInt _ = fail "Expected nint"

validateArrayTerm :: Term -> Validator [Term]
validateArrayTerm (TList xs) = pure xs
validateArrayTerm (TListI xs) = pure xs
validateArrayTerm _ = fail "Expected list"

validateBytesTerm :: Term -> Validator ByteString
validateBytesTerm (TBytes bs) = pure bs
validateBytesTerm (TBytesI bs) = pure $ LBS.toStrict bs
validateBytesTerm _ = fail "Expected bytes"

validateStringTerm :: Term -> Validator Text
validateStringTerm (TString x) = pure x
validateStringTerm (TStringI x) = pure $ LT.toStrict x
validateStringTerm _ = fail "Expected string"

validateMapTerm :: Term -> Validator [(Term, Term)]
validateMapTerm (TMap xs) = validateUniqueMap xs >> pure xs
validateMapTerm (TMapI xs) = validateUniqueMap xs >> pure xs
validateMapTerm _ = fail "Expected map"

-- | Fail if the collection is empty. A custom-validator stand-in for the CDDL
-- @1*@ (non-empty) occurrence constraint, which is no longer enforced once a
-- custom validator replaces the built-in array/map validation for a rule.
validateNonEmpty :: Foldable t => t a -> Validator (NonEmpty a)
validateNonEmpty = maybe (fail "Expected at least one element") pure . nonEmpty . toList

validateUniqueMap :: [(Term, Term)] -> Validator ()
validateUniqueMap xs
  | Map.size m == length xs = pure ()
  | otherwise = fail "Map contains duplicate keys"
  where
    m = Map.fromList $ first toCanonical <$> xs

validateUniqueList :: [Term] -> Validator ()
validateUniqueList xs
  | Set.size s == length xs = pure ()
  | otherwise = fail "List contains duplicate keys"
  where
    s = Set.fromList $ toCanonical <$> xs

unwrapSingle :: RuleTerm -> Validator Term
unwrapSingle (SingleTerm x) = pure x
unwrapSingle _ = fail "Expected a single term"
