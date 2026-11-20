{-# LANGUAGE DefaultSignatures #-}

module Codec.CBOR.Cuddle.IndexMappable (IndexMappable (..), mapCDDLDropExt) where

import Codec.CBOR.Cuddle.CDDL (
  CDDL (..),
  GenericArg (..),
  GenericParameter (..),
  GenericParameters (..),
  Group (..),
  GroupEntry (..),
  GroupEntryVariant (..),
  GrpChoice (..),
  MemberKey (..),
  Rule (..),
  TopLevel (..),
  Type0 (..),
  Type1 (..),
  Type2 (..),
  TypeOrGroup (..),
  XCddl,
  XRule,
  XTerm,
  XXTopLevel,
  XXType2,
 )
import Codec.CBOR.Cuddle.CDDL.CTreePhase (
  CTreePhase,
  XCddl (..),
  XRule (..),
  XTerm (..),
 )
import Codec.CBOR.Cuddle.Huddle (
  HuddleStage,
  XCddl (..),
  XRule (..),
  XTerm (..),
  XXTopLevel (..),
  XXType2 (..),
 )
import Codec.CBOR.Cuddle.Parser (
  ParserStage,
  XCddl (..),
  XRule (..),
  XTerm (..),
  XXTopLevel (..),
  XXType2 (..),
 )
import Codec.CBOR.Cuddle.Pretty (PrettyStage, XCddl (..), XRule (..), XTerm (..), XXTopLevel (..))
import Data.Bifunctor (Bifunctor (..))
import Data.Coerce (Coercible, coerce)
import Data.Void (absurd)

class IndexMappable f i j where
  mapIndex :: f i -> f j
  default mapIndex :: Coercible (f i) (f j) => f i -> f j
  mapIndex = coerce

mapCDDLDropExt ::
  ( IndexMappable XXType2 i j
  , IndexMappable XTerm i j
  , IndexMappable XRule i j
  ) =>
  CDDL i ->
  CDDL j
mapCDDLDropExt (CDDL r tls _) = CDDL (mapIndex r) (foldMap mapTopLevelDropExt tls) []
  where
    mapTopLevelDropExt (TopLevelRule x) = [TopLevelRule $ mapIndex x]
    mapTopLevelDropExt (XXTopLevel _) = []

instance
  ( IndexMappable XCddl i j
  , IndexMappable XXTopLevel i j
  , IndexMappable XXType2 i j
  , IndexMappable XTerm i j
  , IndexMappable XRule i j
  ) =>
  IndexMappable CDDL i j
  where
  mapIndex (CDDL r tls e) = CDDL (mapIndex r) (mapIndex <$> tls) (mapIndex <$> e)

instance
  ( IndexMappable XXType2 i j
  , IndexMappable XTerm i j
  , IndexMappable XRule i j
  ) =>
  IndexMappable Rule i j
  where
  mapIndex (Rule n mg a t c) = Rule n (mapIndex <$> mg) a (mapIndex t) (mapIndex c)

instance
  ( IndexMappable XXTopLevel i j
  , IndexMappable XXType2 i j
  , IndexMappable XTerm i j
  , IndexMappable XRule i j
  ) =>
  IndexMappable TopLevel i j
  where
  mapIndex (TopLevelRule r) = TopLevelRule $ mapIndex r
  mapIndex (XXTopLevel e) = XXTopLevel $ mapIndex e

instance IndexMappable XTerm i j => IndexMappable GenericParameter i j where
  mapIndex (GenericParameter n e) = GenericParameter n $ mapIndex e

instance IndexMappable XTerm i j => IndexMappable GenericParameters i j where
  mapIndex (GenericParameters ns) = GenericParameters $ mapIndex <$> ns

instance
  ( IndexMappable XXType2 i j
  , IndexMappable XTerm i j
  ) =>
  IndexMappable TypeOrGroup i j
  where
  mapIndex (TOGType t) = TOGType $ mapIndex t
  mapIndex (TOGGroup g) = TOGGroup $ mapIndex g

instance
  ( IndexMappable XTerm i j
  , IndexMappable XXType2 i j
  ) =>
  IndexMappable GroupEntry i j
  where
  mapIndex (GroupEntry mo gev e) = GroupEntry mo (mapIndex gev) (mapIndex e)

instance
  ( IndexMappable XXType2 i j
  , IndexMappable XTerm i j
  ) =>
  IndexMappable GroupEntryVariant i j
  where
  mapIndex (GEType mk t) = GEType (mapIndex <$> mk) $ mapIndex t
  mapIndex (GERef n ma) = GERef n (mapIndex <$> ma)
  mapIndex (GEGroup g) = GEGroup (mapIndex g)

instance
  ( IndexMappable XXType2 i j
  , IndexMappable XTerm i j
  ) =>
  IndexMappable MemberKey i j
  where
  mapIndex (MKType t) = MKType $ mapIndex t
  mapIndex (MKBareword n) = MKBareword n
  mapIndex (MKValue x) = MKValue x

instance
  ( IndexMappable XXType2 i j
  , IndexMappable XTerm i j
  ) =>
  IndexMappable Type0 i j
  where
  mapIndex (Type0 ts) = Type0 $ mapIndex <$> ts

instance
  ( IndexMappable XXType2 i j
  , IndexMappable XTerm i j
  ) =>
  IndexMappable Type1 i j
  where
  mapIndex (Type1 t mo e) = Type1 (mapIndex t) (second mapIndex <$> mo) (mapIndex e)

instance
  ( IndexMappable XXType2 i j
  , IndexMappable XTerm i j
  ) =>
  IndexMappable Type2 i j
  where
  mapIndex (T2Value v) = T2Value v
  mapIndex (T2Name n mg) = T2Name n (mapIndex <$> mg)
  mapIndex (T2Group t) = T2Group $ mapIndex t
  mapIndex (T2Map g) = T2Map $ mapIndex g
  mapIndex (T2Array a) = T2Array $ mapIndex a
  mapIndex (T2Unwrapped n mg) = T2Unwrapped n (mapIndex <$> mg)
  mapIndex (T2Enum g) = T2Enum $ mapIndex g
  mapIndex (T2EnumRef n mg) = T2EnumRef n (mapIndex <$> mg)
  mapIndex (T2Tag mt t) = T2Tag mt $ mapIndex t
  mapIndex (T2DataItem t mt) = T2DataItem t mt
  mapIndex T2Any = T2Any
  mapIndex (XXType2 e) = XXType2 $ mapIndex e

instance
  ( IndexMappable XXType2 i j
  , IndexMappable XTerm i j
  ) =>
  IndexMappable GenericArg i j
  where
  mapIndex (GenericArg g) = GenericArg $ mapIndex <$> g

instance
  ( IndexMappable XTerm i j
  , IndexMappable XXType2 i j
  ) =>
  IndexMappable Group i j
  where
  mapIndex (Group g) = Group $ mapIndex <$> g

instance
  ( IndexMappable XTerm i j
  , IndexMappable XXType2 i j
  ) =>
  IndexMappable GrpChoice i j
  where
  mapIndex (GrpChoice gs e) = GrpChoice (mapIndex <$> gs) $ mapIndex e

-- ParserStage ~ PrettyStage

instance IndexMappable XCddl ParserStage PrettyStage where
  mapIndex (ParserXCddl c) = PrettyXCddl c

instance IndexMappable XTerm ParserStage PrettyStage where
  mapIndex (ParserXTerm c) = PrettyXTerm c

instance IndexMappable XRule ParserStage PrettyStage where
  mapIndex (ParserXRule c) = PrettyXRule c

instance IndexMappable XXType2 ParserStage PrettyStage where
  mapIndex (ParserXXType2 v) = absurd v

instance IndexMappable XXTopLevel ParserStage PrettyStage where
  mapIndex (ParserXXTopLevel c) = PrettyXXTopLevel c

-- ParserStage -> CTreePhase

instance IndexMappable XCddl ParserStage CTreePhase where
  mapIndex _ = CTreeXCddl

instance IndexMappable XXType2 ParserStage CTreePhase where
  mapIndex (ParserXXType2 c) = case c of {}

instance IndexMappable XTerm ParserStage CTreePhase where
  mapIndex _ = CTreeXTerm

instance IndexMappable XRule ParserStage CTreePhase where
  mapIndex _ = CTreeXRule id Nothing

-- ParserStage -> HuddleStage

instance IndexMappable XCddl ParserStage HuddleStage where
  mapIndex (ParserXCddl c) = HuddleXCddl c

instance IndexMappable XXTopLevel ParserStage HuddleStage where
  mapIndex (ParserXXTopLevel c) = HuddleXXTopLevel c

instance IndexMappable XXType2 ParserStage HuddleStage where
  mapIndex (ParserXXType2 c) = HuddleXXType2 c

instance IndexMappable XTerm ParserStage HuddleStage where
  mapIndex (ParserXTerm c) = HuddleXTerm c

-- HuddleStage -> CTreePhase

instance IndexMappable XCddl HuddleStage CTreePhase where
  mapIndex _ = CTreeXCddl

instance IndexMappable XXType2 HuddleStage CTreePhase where
  mapIndex (HuddleXXType2 c) = case c of {}

instance IndexMappable XTerm HuddleStage CTreePhase where
  mapIndex _ = CTreeXTerm

instance IndexMappable XRule HuddleStage CTreePhase where
  mapIndex (HuddleXRule _ g v) = CTreeXRule g v

-- HuddleStage -> PrettyStage

instance IndexMappable XCddl HuddleStage PrettyStage where
  mapIndex (HuddleXCddl c) = PrettyXCddl c

instance IndexMappable XXTopLevel HuddleStage PrettyStage where
  mapIndex (HuddleXXTopLevel c) = PrettyXXTopLevel c

instance IndexMappable XXType2 HuddleStage PrettyStage where
  mapIndex (HuddleXXType2 c) = absurd c

instance IndexMappable XTerm HuddleStage PrettyStage where
  mapIndex (HuddleXTerm c) = PrettyXTerm c

instance IndexMappable XRule HuddleStage PrettyStage where
  mapIndex (HuddleXRule c _ _) = PrettyXRule c

-- ParserStage ~ ParserStage

instance IndexMappable XCddl ParserStage ParserStage

instance IndexMappable XXTopLevel ParserStage ParserStage

instance IndexMappable XXType2 ParserStage ParserStage

instance IndexMappable XTerm ParserStage ParserStage

instance IndexMappable XRule ParserStage ParserStage
