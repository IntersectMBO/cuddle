{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}

module Test.Codec.CBOR.Cuddle.CDDL.Examples.Huddle (
  huddleRangeArray,
  huddleArray,
  huddleMap,
  huddleRangeMap,
  customGenRule,
  customGenExample,
  refTermExample,
  bytesExample,
  opCertExample,
  sizeTextExample,
  sizeBytesExample,
  rangeListExample,
  rangeMapExample,
  optionalMapExample,
  choicesExample,
  cborControlExample,
  listTooShortExample,
  listSkippedRuleExample,
  listSkippedRuleNestedExample,
  mapLeftoverKVExample,
  mapNoMatchingKeyExample,
  listZeroOrMoreExample,
  mapNestedValueExample,
  deeplyNestedRefExample,
  taggedUintExample,
  tagRangeExample,
) where

import Codec.CBOR.Cuddle.CBOR.Generator (generateFromGRef)
import Codec.CBOR.Cuddle.CBOR.Validator (validateFromGRef)
import Codec.CBOR.Cuddle.CDDL (Name)
import Codec.CBOR.Cuddle.CDDL.Custom.Core (RuleTerm (..))
import Codec.CBOR.Cuddle.Huddle (
  CanQuantify (..),
  Huddle,
  HuddleItem (..),
  Rule,
  Value (..),
  a,
  arr,
  asKey,
  binding,
  collectFrom,
  idx,
  mp,
  opt,
  tag,
  withCBORGen,
  withValidator,
  (...),
  (=:=),
  (==>),
 )
import Codec.CBOR.Cuddle.Huddle qualified as H
import Codec.CBOR.Term qualified as C
import Data.Word (Word64)
import Test.QuickCheck.GenT (MonadGen (..), frequency)

huddleRangeArray :: Huddle
huddleRangeArray =
  collectFrom
    [ HIRule $
        "a"
          =:= arr
            [ opt $ a VInt
            , 2 <+ a VInt +> 3
            , a VBool +> 3
            , 3 <+ a VText
            ]
    ]

huddleArray :: Huddle
huddleArray =
  collectFrom
    [ HIRule $
        "a"
          =:= arr
            [ 0 <+ a VBool
            , 1 <+ a VInt
            , opt $ a VText
            , a VUInt
            ]
    ]

huddleMap :: Huddle
huddleMap =
  collectFrom
    [ HIRule $
        "a"
          =:= mp
            [ idx 1 ==> arr [0 <+ a VUInt]
            , 1 <+ asKey VBytes ==> VAny
            , opt $ idx 2 ==> VBool
            , 0 <+ asKey VText ==> VInt
            ]
    ]

huddleRangeMap :: Huddle
huddleRangeMap =
  collectFrom
    [ HIRule $
        "a"
          =:= mp
            [ 5 <+ asKey VInt ==> VBool +> 10
            ]
    ]

simpleRule :: Name -> Rule
simpleRule n = n =:= arr [1, 2, 3]

customGenRule :: Name -> Rule
customGenRule = withCBORGen (SingleTerm . C.TInt <$> choose (4, 6)) . simpleRule

customGenExample :: Huddle
customGenExample =
  collectFrom
    [ HIRule $ customGenRule "root"
    ]

refTermExample :: Huddle
refTermExample =
  collectFrom
    [ HIRule $ "root" =:= arr [0, a $ customGenRule "bar"]
    ]

bytesExample :: Huddle
bytesExample =
  collectFrom
    [ HIRule $ "root" =:= H.bstr "010203ff"
    ]

opCertExample :: Huddle
opCertExample =
  collectFrom
    [ HIRule $
        "root"
          =:= arr
            [ a (VBytes `H.sized` (32 :: Word64))
            , a VUInt
            , a VUInt
            , a (VBytes `H.sized` (64 :: Word64))
            ]
    ]

sizeTextExample :: Huddle
sizeTextExample =
  collectFrom
    [HIRule $ "root" =:= VText `H.sized` (0 :: Word64, 32 :: Word64)]

sizeBytesExample :: Huddle
sizeBytesExample =
  collectFrom
    [HIRule $ "root" =:= VBytes `H.sized` (0 :: Word64, 32 :: Word64)]

rangeListExample :: Huddle
rangeListExample =
  collectFrom
    [ HIRule $
        "root"
          =:= arr
            [ 3 <+ a VInt +> 7
            ]
    ]

rangeMapExample :: Huddle
rangeMapExample =
  collectFrom
    [ HIRule $
        "root"
          =:= mp
            [ 3 <+ asKey VInt ==> VBool +> 7
            ]
    ]

optionalMapExample :: Huddle
optionalMapExample =
  collectFrom
    [ HIRule $
        "root"
          =:= mp
            [ 10 <+ asKey ((1 :: Integer) ... (10 :: Integer)) ==> VBool
            ]
    ]

choicesExample :: Huddle
choicesExample =
  collectFrom
    [ HIRule $
        "root"
          =:= arr [1, a VInt, 3]
          H./ arr [1, a VBool, 6]
          H./ arr [1, a VText]
    ]

cborControlExample :: Huddle
cborControlExample =
  collectFrom
    [ HIRule $
        "root"
          =:= VBytes
          `H.cbor` simpleRule "simpleRule"
    ]

listTooShortExample :: Huddle
listTooShortExample =
  collectFrom
    [ HIRule $
        "root"
          =:= arr
            [ a VInt
            , a VText
            , a VBool
            ]
    ]

listSkippedRuleExample :: Huddle
listSkippedRuleExample =
  let bar = "bar" =:= VText
   in collectFrom
        [ HIRule $
            "root"
              =:= arr
                [ a VInt
                , opt $ a bar
                ]
        , HIRule bar
        ]

listSkippedRuleNestedExample :: Huddle
listSkippedRuleNestedExample =
  let baz = "baz" =:= arr [a VInt, a VText]
      qux = "qux" =:= VText
      quux = "quux" =:= VInt
   in collectFrom
        [ HIRule $
            "root"
              =:= arr
                [ a VInt
                , opt $ a qux
                , opt $ a baz
                , opt $ a quux
                ]
        , HIRule baz
        , HIRule qux
        , HIRule quux
        ]

mapLeftoverKVExample :: Huddle
mapLeftoverKVExample =
  collectFrom
    [ HIRule $
        "root"
          =:= mp
            [ opt $ idx 1 ==> VText
            , opt $ idx 2 ==> VInt
            , opt $ idx 3 ==> VBool
            ]
    ]

mapNoMatchingKeyExample :: Huddle
mapNoMatchingKeyExample =
  collectFrom
    [ HIRule $
        "root"
          =:= mp
            [ opt $ idx 1 ==> VText
            , opt $ idx 2 ==> VInt
            ]
    ]

listZeroOrMoreExample :: Huddle
listZeroOrMoreExample =
  collectFrom
    [ HIRule $
        "root"
          =:= arr
            [ 0 <+ a VInt
            , a VText
            ]
    ]

mapNestedValueExample :: Huddle
mapNestedValueExample =
  let bar = "bar" =:= arr [a VInt, a VText]
   in collectFrom
        [ HIRule $
            "root"
              =:= mp
                [ opt $ idx 1 ==> bar
                ]
        , HIRule bar
        ]

-- | A rule with deeply nested references competing against a rule that makes
-- actual term progress. Used to test that stacked references don't incorrectly
-- beat rules with real progress.
deeplyNestedRefExample :: Huddle
deeplyNestedRefExample =
  collectFrom
    [ HIRule $ "root" =:= arr [a VInt, opt $ a aRef, opt $ a listRule]
    , HIRule aRef
    , HIRule barRef
    , HIRule bazRef
    , HIRule listRule
    ]
  where
    bazRef = "baz" =:= VText
    barRef = "bar" =:= bazRef
    aRef = "a_ref" =:= barRef
    listRule = "list_rule" =:= arr [a VInt, a VInt]

taggedUintExample :: Huddle
taggedUintExample =
  collectFrom
    [ HIRule $ "root" =:= tag 42 VBytes
    ]

-- | @foo<a> = #6.1280(a) / #6.1400(a)@ with a custom generator that picks
-- any tag in @1280..1400@ (broader than what the schema literally allows)
-- and a custom validator that accepts the same range. Exercised at two
-- different generic instantiations to make sure the bound type is
-- resolved correctly per call.
tagRangeExample :: Huddle
tagRangeExample =
  collectFrom
    [ HIRule $
        "root" =:= arr [a (fooTagRange VUInt), a (fooTagRange VNInt)]
    ]
  where
    fooTagRange :: H.IsType0 t0 => t0 -> H.GRuleCall
    fooTagRange = binding $ \x ->
      withCBORGen (generator x)
        . withValidator (validator x)
        $ "foo" =:= tag 1280 x H./ tag 1400 x
      where
        generator x = do
          tagN <-
            frequency
              [ (1, pure 1280)
              , (1, pure 1400)
              , (4, choose (1281, 1399))
              ]
          generateFromGRef x >>= \case
            SingleTerm inner -> pure $ SingleTerm (C.TTagged tagN inner)
            _ -> error "tagRangeExample: generic argument must be a single term"

        validator x = \case
          SingleTerm (C.TTagged t inner)
            | t >= 1280 && t <= 1400 -> validateFromGRef x inner
            | otherwise -> fail $ "Tag out of range 1280..1400: " <> show t
          wt -> fail $ "Expected a tagged term, got: " <> show wt
