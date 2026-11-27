{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}

module Codec.CBOR.Cuddle.Comments (
  HasComment (..),
  CollectComments (..),
  hasComment,
  (//-),
  appendComment,
  (<*!),
  (!*>),
  WithComment (..),
  (!$>),
  Comment,
  unComment,
  toComment,
  commentLine,
  withComment,

  -- * Pretty
  CommentRender (..),
  prettyCommentNoBreak,
  prettyCommentNoBreakWS,
) where

import Data.ByteString (ByteString)
import Data.Default.Class (Default (..))
import Data.Hashable (Hashable)
import Data.List.NonEmpty (NonEmpty (..))
import Data.String (IsString (..))
import Data.Text qualified as T
import Data.Void (Void, absurd)
import Data.Word (Word16, Word32, Word64, Word8)
import GHC.Generics (Generic (..), K1 (..), M1 (..), U1 (..), V1, (:*:) (..), (:+:) (..))
import Optics.Core (Lens', lens, view, (%~), (&), (.~), (^.))
import Prettyprinter

newtype Comment = Comment [T.Text]
  deriving (Eq, Ord, Generic, Show)
  deriving newtype (Semigroup, Monoid)
  deriving anyclass (Hashable)

unComment :: Comment -> [T.Text]
unComment (Comment c) = c

toComment :: T.Text -> Comment
toComment = Comment . T.lines

-- | Wrap a single line of text (possibly empty) as a one-line comment.
-- Unlike 'toComment', this does not split on newlines and preserves an empty
-- input as a single empty comment line.
commentLine :: T.Text -> Comment
commentLine t = Comment [t]

instance Default Comment where def = mempty

class HasComment a where
  commentL :: Lens' a Comment

class GCollectComments f where
  collectCommentsG :: f a -> [Comment]

instance GCollectComments V1 where
  collectCommentsG = \case {}

instance GCollectComments U1 where
  collectCommentsG U1 = []

instance
  ( GCollectComments a
  , GCollectComments b
  ) =>
  GCollectComments (a :+: b)
  where
  collectCommentsG (L1 x) = collectCommentsG x
  collectCommentsG (R1 x) = collectCommentsG x

instance
  ( GCollectComments a
  , GCollectComments b
  ) =>
  GCollectComments (a :*: b)
  where
  collectCommentsG (a :*: b) = collectCommentsG a <> collectCommentsG b

instance CollectComments a => GCollectComments (K1 s a) where
  collectCommentsG (K1 x) = collectComments x

instance GCollectComments a => GCollectComments (M1 i c a) where
  collectCommentsG (M1 x) = collectCommentsG x

class CollectComments a where
  collectComments :: a -> [Comment]
  default collectComments :: (Generic a, GCollectComments (Rep a)) => a -> [Comment]
  collectComments = collectCommentsG . from

instance CollectComments Void where collectComments = absurd

instance CollectComments () where collectComments = mempty

instance CollectComments a => CollectComments (Maybe a) where
  collectComments Nothing = []
  collectComments (Just x) = collectComments x

instance CollectComments a => CollectComments [a]

instance CollectComments a => CollectComments (NonEmpty a)

instance CollectComments Word8 where collectComments = mempty

instance CollectComments Word16 where collectComments = mempty

instance CollectComments Word32 where collectComments = mempty

instance CollectComments Word64 where collectComments = mempty

instance CollectComments Integer where collectComments = mempty

instance CollectComments Float where collectComments = mempty

instance CollectComments Double where collectComments = mempty

instance CollectComments T.Text where collectComments = mempty

instance CollectComments ByteString where collectComments = mempty

instance CollectComments Bool where collectComments = mempty

instance CollectComments Comment where
  collectComments x = [x]

hasComment :: HasComment a => a -> Bool
hasComment = (/= mempty) . view commentL

-- | This operator is used to attach comments to terms. It will not overwrite
-- any comments that are already present, but will add the new comments on a
-- new line
-- ```
-- arr [0, 1] //- "This is an array with two values"
-- ```
(//-) :: HasComment a => a -> Comment -> a
x //- c = x & commentL %~ (<> Comment ((" " <>) <$> unComment c))

infixl 1 //-

-- | Raw comment append without adding space or newline. Used by parser
-- combinators where the comment text is already formatted.
appendComment :: HasComment a => a -> Comment -> a
appendComment x c = x & commentL %~ (<> c)

-- | This operator will parse the values from left to right and then append the
-- parsed comment on the right to the parsed value on the left.
(<*!) :: (HasComment a, Applicative m) => m a -> m Comment -> m a
(<*!) x c = appendComment <$> x <*> c

-- | This operator will parse the values from left to right and then append the
-- parsed comment on the left to the parsed value on the right.
(!*>) :: (HasComment a, Applicative m) => m Comment -> m a -> m a
(!*>) c x = flip appendComment <$> c <*> x

data WithComment a = WithComment
  { unWithComment :: Comment
  , stripComment :: a
  }
  deriving (Functor)

instance Applicative WithComment where
  pure = withComment
  WithComment cmt f <*> WithComment cmt' x = WithComment (cmt <> cmt') $ f x

instance Monad WithComment where
  WithComment cmt x >>= f = let WithComment cmt' y = f x in WithComment (cmt <> cmt') y

instance HasComment (WithComment a) where
  commentL = lens (\(WithComment x _) -> x) (\(WithComment _ b) x -> WithComment x b)

instance CollectComments a => CollectComments (WithComment a) where
  collectComments (WithComment c x) = c : collectComments x

withComment :: a -> WithComment a
withComment = WithComment mempty

-- | This operator maps a function over a functor containing a `WithComment` and
-- applies the comment within to the output of the applied function.
-- ```
-- (\x -> LInt x "a") !$> WithComment "b" (1 :: Integer) == Literal (LInt 1) "a\nb"
-- ```
(!$>) :: (HasComment b, Functor f) => (a -> b) -> f (WithComment a) -> f b
f !$> wc = fmap (\(WithComment c x) -> appendComment (f x) c) wc

instance HasComment a => HasComment (NonEmpty a) where
  commentL = lens (\(x :| _) -> x ^. commentL) (\(x :| xs) y -> (x & commentL .~ y) :| xs)

instance HasComment Comment where
  commentL = lens id const

instance IsString Comment where
  fromString = toComment . T.pack

data CommentRender
  = PreComment
  | PostComment

prettyCommentNoBreak :: Comment -> Doc ann
prettyCommentNoBreak = align . vsep . fmap (pretty . (";" <>)) . unComment

prettyCommentNoBreakWS :: Comment -> Doc ann
prettyCommentNoBreakWS cmt
  | cmt == mempty = mempty
  | otherwise = space <> prettyCommentNoBreak cmt

instance Pretty Comment where
  pretty c
    | c == mempty = mempty
    | otherwise = prettyCommentNoBreak c <> hardline
