{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

module Codec.CBOR.Cuddle.CDDL.Custom.Core (
  MonadCddl (..),
  RuleTerm (..),
  LengthEncoding (..),
  evalBool,
  evalInteger,
  evalDouble,
  evalArray,
  evalInterval,
  evalBytes,
  evalText,
) where

import Codec.CBOR.Cuddle.CDDL (GRef, Name, RangeBound (..), Value (..), ValueVariant (..))
import Codec.CBOR.Cuddle.CDDL.CTree (CTree (..), XXCTree)
import Codec.CBOR.Cuddle.Interval (Interval (..), IntervalBound (..))
import Codec.CBOR.Cuddle.Interval qualified as Interval
import Codec.CBOR.Term (Term)
import Data.ByteString (ByteString)
import Data.Kind (Type)
import Data.Text (Text)
import GHC.Float (float2Double)

class Monad m => MonadCddl m where
  type Phase m :: Type

  -- | Look up a top-level rule by name.
  lookupCddl :: Name -> m (Maybe (CTree (Phase m)))

  -- | Look up the rule bound to a generic parameter at the enclosing rule.
  -- Returns 'Nothing' outside of a custom generator/validator that was
  -- attached to a generic rule.
  lookupGRef :: GRef -> m (Maybe (CTree (Phase m)))

  resolveExt :: XXCTree (Phase m) -> m (Maybe (CTree (Phase m)))

data RuleTerm
  = SingleTerm Term
  | PairTerm Term Term
  | GroupTerm [RuleTerm]
  deriving (Eq, Ord, Show)

data LengthEncoding
  = DefiniteLength
  | IndefiniteLength

evalExt ::
  MonadCddl m =>
  XXCTree (Phase m) ->
  (CTree (Phase m) -> m (Maybe a)) ->
  m (Maybe a)
evalExt ext f = do
  res <- resolveExt ext
  case res of
    Just x -> f x
    Nothing -> pure Nothing

evalBool :: MonadCddl m => CTree (Phase m) -> m (Maybe Bool)
evalBool = \case
  Literal (Value (VBool b) _) -> pure $ Just b
  CTreeE ext -> evalExt ext evalBool
  _ -> pure Nothing

evalDouble :: MonadCddl m => CTree (Phase m) -> m (Maybe Double)
evalDouble = \case
  Literal (Value var _)
    | VFloat16 x <- var -> pure $ Just $ float2Double x
    | VFloat32 x <- var -> pure $ Just $ float2Double x
    | VFloat64 x <- var -> pure $ Just x
  CTreeE ext -> evalExt ext evalDouble
  _ -> pure Nothing

evalInteger :: MonadCddl m => CTree (Phase m) -> m (Maybe Integer)
evalInteger = \case
  Literal (Value var _)
    | VUInt x <- var -> pure $ Just $ toInteger x
    | VNInt x <- var -> pure $ Just $ negate $ toInteger x
    | VBignum x <- var -> pure $ Just x
  CTreeE ext -> evalExt ext evalInteger
  _ -> pure Nothing

evalArray ::
  MonadCddl m =>
  (CTree (Phase m) -> m (Maybe a)) ->
  CTree (Phase m) ->
  m (Maybe [a])
evalArray f = \case
  Array es -> sequence <$> traverse f es
  CTreeE ext -> evalExt ext $ evalArray f
  _ -> pure Nothing

evalBytes ::
  MonadCddl m =>
  CTree (Phase m) ->
  m (Maybe ByteString)
evalBytes = \case
  Literal (Value (VBytes bs) _) -> pure $ Just bs
  CTreeE ext -> evalExt ext evalBytes
  _ -> pure Nothing

evalText ::
  MonadCddl m =>
  CTree (Phase m) ->
  m (Maybe Text)
evalText = \case
  Literal (Value (VText t) _) -> pure $ Just t
  CTreeE ext -> evalExt ext evalText
  _ -> pure Nothing

evalInterval ::
  MonadCddl m =>
  (CTree (Phase m) -> m (Maybe a)) ->
  CTree (Phase m) ->
  m (Maybe (Interval a))
evalInterval f = \case
  Range loRule hiRule bound -> do
    lo <- f loRule
    hi <- f hiRule
    let
      lBound = ClosedBound <$> lo
      uBound = case bound of
        ClOpen -> OpenBound <$> hi
        Closed -> ClosedBound <$> hi
      interval = Interval <$> lBound <*> uBound
    pure interval
  CTreeE ext -> evalExt ext $ evalInterval f
  x -> fmap Interval.singleton <$> f x
