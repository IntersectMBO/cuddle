{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Codec.CBOR.Cuddle.CDDL.CTree (
  XXCTree (..),
  CTree (..),
  traverseCTree,
  foldCTree,
  Node,
  CTreeRoot (..),
  PTerm (..),
  uintMax,
  nintMin,
) where

import Codec.CBOR.Cuddle.CBOR.Canonical (nintMin, uintMax)
import Codec.CBOR.Cuddle.CDDL (
  Name,
  OccurrenceIndicator (..),
  RangeBound (..),
  Value,
 )
import Codec.CBOR.Cuddle.CDDL.CtlOp
import Codec.CBOR.Cuddle.CDDL.Phase (MonoSimplePhase)
import Control.Monad.Identity (Identity (..))
import Data.Hashable (Hashable)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Word (Word64)
import GHC.Generics (Generic)
import Generic.Random (genericArbitraryU)
import Prettyprinter
import Test.QuickCheck (Arbitrary (..))

--------------------------------------------------------------------------------

-- * Resolved CDDL Tree

--
-- This is a simplified representation of CDDL. It is technically more general -
-- that is, the structure can represent invalid CDDL - but is in that way easier
-- to manipulate.
--------------------------------------------------------------------------------

data family XXCTree i

data CTree i
  = Literal Value
  | Postlude PTerm
  | Map [CTree i]
  | Array [CTree i]
  | Choice (NE.NonEmpty (CTree i))
  | Group [CTree i]
  | KV {key :: CTree i, value :: CTree i, cut :: Bool}
  | Occur {item :: CTree i, occurs :: OccurrenceIndicator}
  | Range {from :: CTree i, to :: CTree i, inclusive :: RangeBound}
  | Control {op :: CtlOp, target :: CTree i, controller :: CTree i}
  | Enum (CTree i)
  | Unwrap (CTree i)
  | Tag Word64 (CTree i)
  | CTreeE (XXCTree i)
  deriving (Generic)

deriving instance Eq (Node f) => Eq (CTree f)

deriving instance Show (Node f) => Show (CTree f)

instance Hashable (Node f) => Hashable (CTree f)

instance Pretty (XXCTree p) => Pretty (CTree p) where
  pretty = \case
    Literal v -> pretty v
    Postlude v -> pretty v
    Range lo hi ClOpen -> pretty lo <+> "..." <+> pretty hi
    Range lo hi Closed -> pretty lo <+> ".." <+> pretty hi
    KV k v _ -> pretty k <+> "==>" <+> pretty v
    CTreeE x -> pretty x
    Occur v oi ->
      case oi of
        OIOptional -> "?" <+> pretty v
        OIZeroOrMore -> "*" <+> pretty v
        OIOneOrMore -> "+" <+> pretty v
        OIBounded lo hi -> foldMap pretty lo <> "*" <> foldMap pretty hi <+> pretty v
    Map m -> encloseSep "{" "}" "," $ pretty <$> m
    Array e -> list $ pretty <$> e
    Choice c -> group . vsep . punctuate "//" $ pretty <$> NE.toList c
    Group g -> tupled $ pretty <$> g
    Control op tgt ctl -> pretty tgt <+> pretty op <+> pretty ctl
    Enum e -> "&" <> pretty e
    Unwrap x -> "~" <> pretty x
    Tag t x -> "#6." <> pretty t <> "(" <> pretty x <> ")"

-- | Traverse the CTree, carrying out the given operation at each node
traverseCTree ::
  Monad m => (XXCTree i -> m (CTree j)) -> (CTree i -> m (CTree j)) -> CTree i -> m (CTree j)
traverseCTree _ _ (Literal a) = pure $ Literal a
traverseCTree _ _ (Postlude a) = pure $ Postlude a
traverseCTree _ atNode (Map xs) = Map <$> traverse atNode xs
traverseCTree _ atNode (Array xs) = Array <$> traverse atNode xs
traverseCTree _ atNode (Group xs) = Group <$> traverse atNode xs
traverseCTree _ atNode (Choice xs) = Choice <$> traverse atNode xs
traverseCTree _ atNode (KV k v c) = do
  k' <- atNode k
  v' <- atNode v
  pure $ KV k' v' c
traverseCTree _ atNode (Occur i occ) = flip Occur occ <$> atNode i
traverseCTree _ atNode (Range f t inc) = do
  f' <- atNode f
  t' <- atNode t
  pure $ Range f' t' inc
traverseCTree _ atNode (Control o t c) = do
  t' <- atNode t
  c' <- atNode c
  pure $ Control o t' c'
traverseCTree _ atNode (Enum ref) = Enum <$> atNode ref
traverseCTree _ atNode (Unwrap ref) = Unwrap <$> atNode ref
traverseCTree _ atNode (Tag i ref) = Tag i <$> atNode ref
traverseCTree atExt _ (CTreeE x) = atExt x

foldCTree ::
  (XXCTree i -> CTree j) ->
  (CTree i -> CTree j) ->
  CTree i ->
  CTree j
foldCTree atExt atNode x = runIdentity $ traverseCTree (pure . atExt) (pure . atNode) x

type Node i = XXCTree i

newtype CTreeRoot i = CTreeRoot (Map.Map Name (CTree i))
  deriving (Generic)

deriving instance Show (CTree i) => Show (CTreeRoot i)

-- |
--
--  CDDL predefines a number of names.  This subsection summarizes these
--  names, but please see Appendix D for the exact definitions.
--
--  The following keywords for primitive datatypes are defined:
--
--  "bool"  Boolean value (major type 7, additional information 20
--    or 21).
--
--  "uint"  An unsigned integer (major type 0).
--
--  "nint"  A negative integer (major type 1).
--
--  "int"  An unsigned integer or a negative integer.
--
--  "float16"  A number representable as a half-precision float [IEEE754]
--    (major type 7, additional information 25).
--
--  "float32"  A number representable as a single-precision float
--    [IEEE754] (major type 7, additional information 26).
--
--
--  "float64"  A number representable as a double-precision float
--    [IEEE754] (major type 7, additional information 27).
--
--  "float"  One of float16, float32, or float64.
--
--  "bstr" or "bytes"  A byte string (major type 2).
--
--  "tstr" or "text"  Text string (major type 3).
--
--  (Note that there are no predefined names for arrays or maps; these
--  are defined with the syntax given below.)
data PTerm
  = PTBool
  | PTUInt
  | PTNInt
  | PTInt
  | PTHalf
  | PTFloat
  | PTDouble
  | PTBytes
  | PTText
  | PTAny
  | PTNil
  | PTUndefined
  deriving (Eq, Generic, Ord, Show, Enum, Bounded)

instance Pretty PTerm where
  pretty = \case
    PTBool -> "bool"
    PTUInt -> "uint"
    PTNInt -> "nint"
    PTInt -> "int"
    PTHalf -> "half"
    PTFloat -> "float"
    PTDouble -> "double"
    PTBytes -> "bytes"
    PTText -> "text"
    PTAny -> "any"
    PTNil -> "nil"
    PTUndefined -> "undefined"

instance Arbitrary PTerm where
  arbitrary = genericArbitraryU

instance Hashable PTerm

-- | A simplified phase reachable from any of the function-bearing post-mono
-- phases ('MonoReferenced', 'GenPhase', 'ValidatorPhase'). It strips the
-- generator/validator extensions so the tree can be `Show`n, `Eq`-compared,
-- and pretty-printed for debug output.
newtype instance XXCTree MonoSimplePhase = MSimpleRef Name
  deriving (Generic, Show, Eq)

instance Pretty (XXCTree MonoSimplePhase) where
  pretty (MSimpleRef n) = pretty n
