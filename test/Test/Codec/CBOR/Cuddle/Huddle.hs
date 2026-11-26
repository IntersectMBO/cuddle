{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}

{- HLINT ignore "Redundant bracket" -}

module Test.Codec.CBOR.Cuddle.Huddle where

import Codec.CBOR.Cuddle.CDDL (CDDL, fromRules, sortCDDL)
import Codec.CBOR.Cuddle.CDDL.Phase (HuddleStage)
import Codec.CBOR.Cuddle.Comments (Comment)
import Codec.CBOR.Cuddle.Huddle
import Codec.CBOR.Cuddle.IndexMappable (IndexMappable (..))
import Codec.CBOR.Cuddle.Parser
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.Text qualified as T
import Data.Void (Void)
import GHC.Generics (Generic)
import Test.Codec.CBOR.Cuddle.CDDL.Pretty qualified as Pretty
import Test.Hspec
import Test.Hspec.Megaparsec
import Text.Megaparsec
import Prelude hiding ((/))

type data TestStage

newtype instance XCddl TestStage = TestXCddl [Comment]
  deriving (Generic, Show, Eq)

instance IndexMappable XCddl ParserStage TestStage where
  mapIndex (ParserXCddl x) = TestXCddl x

instance IndexMappable XCddl HuddleStage TestStage where
  mapIndex (HuddleXCddl x) = TestXCddl x

newtype instance XTerm TestStage = TestXTerm Comment
  deriving (Generic, Show, Eq)

instance IndexMappable XTerm ParserStage TestStage where
  mapIndex (ParserXTerm x) = TestXTerm x

instance IndexMappable XTerm HuddleStage TestStage where
  mapIndex (HuddleXTerm x) = TestXTerm x

newtype instance XRule TestStage = TestXRule Comment
  deriving (Generic, Show, Eq)

instance IndexMappable XRule ParserStage TestStage where
  mapIndex (ParserXRule x) = TestXRule x

instance IndexMappable XRule HuddleStage TestStage where
  mapIndex (HuddleXRule x _ _) = TestXRule x

newtype instance XXTopLevel TestStage = TestXXTopLevel Comment
  deriving (Generic, Show, Eq)

instance IndexMappable XXTopLevel ParserStage TestStage where
  mapIndex (ParserXXTopLevel x) = TestXXTopLevel x

instance IndexMappable XXTopLevel HuddleStage TestStage where
  mapIndex (HuddleXXTopLevel x) = TestXXTopLevel x

newtype instance XXType2 TestStage = TestXXType2 Void
  deriving (Generic, Show, Eq)

instance IndexMappable XXType2 ParserStage TestStage where
  mapIndex (ParserXXType2 x) = TestXXType2 x

instance IndexMappable XXType2 HuddleStage TestStage where
  mapIndex (HuddleXXType2 x) = TestXXType2 x

huddleSpec :: Spec
huddleSpec = describe "huddle" $ do
  basicAssign
  arraySpec
  mapSpec
  grpSpec
  nestedSpec
  genericSpec
  constraintSpec
  choiceSpec
  Pretty.spec

basicAssign :: Spec
basicAssign = describe "basic assignment" $ do
  it "Can assign a primitive" $
    toSortedCDDL ["port" =:= VUInt]
      `shouldMatchParseCDDL` "port = uint"
  it "Can assign an int" $
    toSortedCDDL ["one" =:= (int 1)]
      `shouldMatchParseCDDL` "one = 1"
  -- it "Can assign a float" $
  --   toSortedCDDL ["onepointone" =:= (1.1 :: Float)]
  --     `shouldMatchParseCDDL` "onepointone = 1.1"
  it "Can assign `true` " $
    toSortedCDDL ["isValid" =:= (bool True)]
      `shouldMatchParseCDDL` "isValid = true"
  it "Can assign `false` " $
    toSortedCDDL ["isValid" =:= (bool False)]
      `shouldMatchParseCDDL` "isValid = false"
  it "Can assign a text string" $
    toSortedCDDL ["hello" =:= ("Hello World" :: T.Text)]
      `shouldMatchParseCDDL` "hello = \"Hello World\""
  it "Can handle multiple assignments" $
    toSortedCDDL ["age" =:= VUInt, "location" =:= VText]
      `shouldMatchParseCDDL` "age = uint\n location = text"

arraySpec :: Spec
arraySpec = describe "Arrays" $ do
  it "Can assign a small array" $
    toSortedCDDL ["asl" =:= arr [a VUInt, a VBool, a VText, a (bool True)]]
      `shouldMatchParseCDDL` "asl = [ uint, bool, text, true ]"
  it "Can quantify an upper bound" $
    toSortedCDDL ["age" =:= arr [a VUInt +> 64]]
      `shouldMatchParseCDDL` "age = [ *64 uint ]"
  it "Can quantify an optional" $
    toSortedCDDL ["age" =:= arr [0 <+ a VUInt +> 1, 0 <+ a (bool False) +> 1]]
      `shouldMatchParseCDDL` "age = [ ? uint, ? false ]"
  it "Can handle a choice" $
    toSortedCDDL ["ageOrSex" =:= arr [a VUInt] / arr [a VBool]]
      `shouldMatchParseCDDL` "ageOrSex = [ uint // bool ]"
  it "Can handle choices of groups" $
    toSortedCDDL
      [ "asl"
          =:= arr [a VUInt, a VBool, a VText, a (bool True)]
          / arr
            [ a (int 1)
            , a ("Hello" :: T.Text)
            ]
      ]
      `shouldMatchParseCDDL` "asl = [ uint, bool, text, true // 1, \"Hello\" ]"

mapSpec :: Spec
mapSpec = describe "Maps" $ do
  it "Can assign a small map" $
    toSortedCDDL ["asl" =:= mp ["age" ==> VUInt, "sex" ==> VBool, "location" ==> VText]]
      `shouldMatchParseCDDL` "asl = { age : uint, sex : bool, location : text }"
  it "Can quantify a lower bound" $
    toSortedCDDL ["age" =:= mp [0 <+ "years" ==> VUInt]]
      `shouldMatchParseCDDL` "age = { * years : uint }"
  it "Can quantify an upper bound" $
    toSortedCDDL ["age" =:= mp ["years" ==> VUInt +> 64]]
      `shouldMatchParseCDDL` "age = { *64 years : uint }"
  it "Can handle a choice" $
    toSortedCDDL ["ageOrSex" =:= mp ["age" ==> VUInt] / mp ["sex" ==> VBool]]
      `shouldMatchParseCDDL` "ageOrSex = { age : uint // sex : bool }"
  it "Can handle a choice with an entry" $
    toSortedCDDL ["mir" =:= arr [a (int 0 / int 1), a $ mp [0 <+ "test" ==> VUInt]]]
      `shouldMatchParseCDDL` "mir = [ 0 / 1, { * test : uint }]"

grpSpec :: Spec
grpSpec = describe "Groups" $ do
  it "Can handle a choice in a group entry" $
    let g1 = "g1" =:~ grp [a (VUInt / VBytes), a VUInt, a (bool False)]
     in toSortedCDDL (collectFrom [HIRule $ "a1" =:= arr [a g1]])
          `shouldMatchParseCDDL` "a1 = [g1]\n g1 = ( uint / bytes, uint, false)"
  it "Can handle keys in a group entry" $
    let g1 = "g1" =:~ grp ["bytes" ==> VBytes]
     in toSortedCDDL (collectFrom [HIRule $ "a1" =:= arr [a g1]])
          `shouldMatchParseCDDL` "a1 = [g1]\n g1 = (bytes : bytes)"

-- it "Can handle a group in a map" $
--   let g1 = "g1" =:~ grp ["bytes"==> VBytes]
--   in toSortedCDDL (collectFrom ["a1" =:= mp [g1]])
--     `shouldMatchParseCDDL` "a1 = [g1]\n g1 = (bytes : bytes)"

nestedSpec :: Spec
nestedSpec =
  describe "Nesting" $
    it "Handles references" $
      let headerBody = "header_body" =:= arr ["block_number" ==> VUInt, "slot" ==> VUInt]
       in toSortedCDDL
            [ headerBody
            , "header" =:= arr [a headerBody, "body_signature" ==> VBytes]
            ]
            `shouldMatchParseCDDL` "header = [header_body, body_signature : bytes]\n header_body = [block_number : uint, slot : uint]"

genericSpec :: Spec
genericSpec =
  describe "Generics" $
    let set :: IsType0 t0 => t0 -> GRuleCall
        set = binding $ \x -> "set" =:= arr [0 <+ a x]

        dict :: (IsType0 t0, IsType0 t1) => t0 -> t1 -> GRuleCall
        dict = binding2 $ \k v -> "dict" =:= mp [0 <+ asKey k ==> v]
     in do
          it "Should bind a single parameter" $
            toSortedCDDL (collectFrom [HIRule $ "intset" =:= set VUInt])
              `shouldMatchParseCDDL` "intset = set<uint>\n set<a0> = [* a0]"
          it "Should bind two parameters" $
            toSortedCDDL (collectFrom [HIRule $ "mymap" =:= dict VUInt VText])
              `shouldMatchParseCDDL` "dict<a0, b0> = {* a0 => b0}\n mymap = dict<uint, text>"

constraintSpec :: Spec
constraintSpec =
  describe "Constraints" $ do
    it "Size can take a Word" $
      toSortedCDDL (collectFrom [HIRule $ "sz" =:= VUInt `sized` (2 :: Word)])
        `shouldMatchParseCDDL` "sz = uint .size 2"

    it "Range bound can take a reference" $
      let b = "b" =:= (16 :: Integer)
       in toSortedCDDL (collectFrom [HIRule $ "b" =:= (16 :: Integer), HIRule $ "c" =:= int 0 ... b])
            `shouldMatchParseCDDL` "b = 16\n c = 0 .. b"

choiceSpec :: Spec
choiceSpec =
  describe "Choice" $ do
    describe "choiceFromList" $ do
      it "produces expected CDDL for 3-element list" $
        toSortedCDDL ["foo" =:= choiceFromList (int 1 :| [int 2, int 3])]
          `shouldMatchParseCDDL` "foo = 1 / 2 / 3"

      it "singleton is equivalent to direct assignment" $
        toSortedCDDL ["foo" =:= choiceFromList (int 1 :| [])]
          `shouldMatchParseCDDL` "foo = 1"

--------------------------------------------------------------------------------
-- Helper functions
--------------------------------------------------------------------------------

shouldMatchParse ::
  (Text.Megaparsec.ShowErrorComponent e, Show a, Eq a) =>
  a ->
  Text.Megaparsec.Parsec e T.Text a ->
  String ->
  Expectation
shouldMatchParse x parseFun input = parse parseFun "" (T.pack input) `shouldParse` x

shouldMatchParseCDDL ::
  CDDL TestStage ->
  String ->
  Expectation
shouldMatchParseCDDL x = shouldMatchParse x . fmap mapIndex $ pCDDL

toSortedCDDL :: Huddle -> CDDL TestStage
toSortedCDDL = mapIndex . fromRules . sortCDDL . toCDDLNoRoot
