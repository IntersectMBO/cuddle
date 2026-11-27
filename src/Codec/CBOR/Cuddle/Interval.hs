{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}

module Codec.CBOR.Cuddle.Interval (
  Interval (..),
  IntervalBound (..),
  (...),
  (..=),
  boundary,
  greaterThanOrEqual,
  greaterThan,
  lessThanOrEqual,
  lessThan,
  isEmpty,
  intersect,
  singleton,
  contains,
  universe,
) where

data IntervalBound a
  = OpenBound a
  | ClosedBound a
  | Unbounded
  deriving (Eq, Show, Functor, Foldable, Traversable)

boundary :: IntervalBound a -> Maybe a
boundary = \case
  Unbounded -> Nothing
  OpenBound x -> Just x
  ClosedBound x -> Just x

data Interval a = Interval (IntervalBound a) (IntervalBound a)
  deriving (Eq, Show, Functor, Foldable, Traversable)

greaterThanOrEqual :: a -> Interval a
greaterThanOrEqual x = Interval (ClosedBound x) Unbounded

greaterThan :: a -> Interval a
greaterThan x = Interval (OpenBound x) Unbounded

lessThanOrEqual :: a -> Interval a
lessThanOrEqual x = Interval Unbounded (ClosedBound x)

lessThan :: a -> Interval a
lessThan x = Interval Unbounded (OpenBound x)

(...) :: a -> a -> Interval a
lo ... hi = Interval (ClosedBound lo) (OpenBound hi)

infix 5 ...

(..=) :: a -> a -> Interval a
lo ..= hi = Interval (ClosedBound lo) (ClosedBound hi)

infix 5 ..=

-- | This function checks whether the interval contains any elements. It does
-- not take the bounds of the type into account, it only checks whether the
-- lower bound is smaller than the upper bound
isEmpty :: Ord a => Interval a -> Bool
isEmpty = \case
  Interval (ClosedBound lo) (ClosedBound hi) -> lo > hi
  Interval lo hi
    | Just l <- boundary lo
    , Just h <- boundary hi ->
        l >= h
  _ -> False

-- | Computes the intersection of two intervals. The result may be empty (see
-- 'isEmpty').
intersect :: Ord a => Interval a -> Interval a -> Interval a
intersect (Interval lo1 hi1) (Interval lo2 hi2) =
  Interval (tighter (>) lo1 lo2) (tighter (<) hi1 hi2)
  where
    -- Picks the more restrictive of two bounds. @better x y@ holds when @x@
    -- is strictly more restrictive than @y@. On equal boundaries an open bound
    -- is more restrictive than a closed one.
    tighter _ Unbounded b = b
    tighter _ a Unbounded = a
    tighter better a b
      | Just x <- boundary a
      , Just y <- boundary b =
          if
            | better x y -> a
            | better y x -> b
            | OpenBound _ <- a -> a
            | otherwise -> b
    tighter _ a _ = a

singleton :: a -> Interval a
singleton x = Interval (ClosedBound x) (ClosedBound x)

contains :: Ord a => Interval a -> a -> Bool
contains (Interval lo hi) x = satisifesUpper && satisfiesLower
  where
    satisifesUpper = case hi of
      Unbounded -> True
      OpenBound y -> x < y
      ClosedBound y -> x <= y
    satisfiesLower = case lo of
      Unbounded -> True
      OpenBound y -> y < x
      ClosedBound y -> y <= x

universe :: Interval a
universe = Interval Unbounded Unbounded
