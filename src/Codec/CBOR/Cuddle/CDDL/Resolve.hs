{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedLabels #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns #-}

-- | Module containing tools for 'resolving' CDDL
--
-- Resolving the CDDL is a process of simplifying the representation to make
-- further operations, such as CBOR generation or validation, easier. We operate
-- with a number of passes:
--
-- 1. First, we deal with any rule extensions and create a single map from
--    identifiers to (potentially parametrised) entities.
-- 2. Second, we flatten the structure to a 'CTree', which discards a lot of the
--    extrenuous information.
-- 3. Then we resolve identifiers. Specifically, we do three things:
--    - Resolve identifiers that map to the postlude.
--    - Differentiate between generic args and references to top-level rules.
--    - Validate that all references exist. Note that we cannot resolve all
--    references since they may be circular.
-- 4. Finally, we monomorphise, synthesizing instances of rules with their
--    generic arguments bound.
module Codec.CBOR.Cuddle.CDDL.Resolve (
  buildResolvedCTree,
  buildRefCTree,
  asMap,
  buildMonoCTree,
  fullResolveCDDL,
  NameResolutionFailure (..),
  MonoReferenced,
  MonoSimplePhase,
  showSimple,
  XXCTree (..),
)
where

import Capability.Accessors (Field (..), Lift (..))
import Capability.Error (HasThrow, MonadError (..), throw)
import Capability.Reader (HasReader, MonadReader (..), ask)
import Capability.Reader qualified as Reader (local)
import Capability.Sink (HasSink)
import Capability.Source (HasSource)
import Capability.State (HasState, MonadState (..), modify)
import Codec.CBOR.Cuddle.CDDL as CDDL
import Codec.CBOR.Cuddle.CDDL.CTree (
  CTree (..),
  CTreeRoot (..),
  PTerm (..),
  XXCTree,
  foldCTree,
 )
import Codec.CBOR.Cuddle.CDDL.CTree qualified as CTree
import Control.Monad.Except (ExceptT (..), runExceptT)
import Control.Monad.Reader (Reader, ReaderT (..), runReader)
import Control.Monad.State.Strict (StateT (..))
import Data.Generics.Product
import Data.Generics.Sum
import Data.Hashable
#if __GLASGOW_HASKELL__ < 910
import Data.List (foldl')
#endif
import Codec.CBOR.Cuddle.CDDL.CTreePhase (CTreePhase, XRule (..))
import Codec.CBOR.Cuddle.CDDL.Custom.Core (RuleTerm)
import Codec.CBOR.Cuddle.CDDL.Custom.Generator (
  CBORGen,
  GenPhase,
  XXCTree (..),
  withLocalGenBindings,
 )
import Codec.CBOR.Cuddle.CDDL.Custom.Validator (
  TermValidator,
  ValidatorPhase,
  XXCTree (..),
  withLocalValidateBindings,
 )
import Codec.CBOR.Cuddle.IndexMappable (IndexMappable (..))
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict qualified as Map
import Data.Text qualified as T
import GHC.Generics (Generic)
import Optics.Core
import Prettyprinter (Pretty (..), encloseSep, layoutCompact)
import Prettyprinter.Render.Text (renderStrict)

data ProvidedParameters a = ProvidedParameters
  { parameters :: [Name]
  , underlying :: a
  }
  deriving (Generic, Functor, Show, Eq, Foldable, Traversable)

instance Hashable a => Hashable (ProvidedParameters a)

--------------------------------------------------------------------------------
-- 1. Rule extensions
--------------------------------------------------------------------------------

newtype PartialCTreeRoot i = PartialCTreeRoot (Map.Map Name (ProvidedParameters (CTree i)))
  deriving (Generic)

data CDDLMapEntry = CDDLMapEntry
  { cmeProvidedParameters :: ProvidedParameters (TypeOrGroup CTreePhase)
  , cmeCustomGenerator :: Maybe (CBORGen RuleTerm)
  , cmeCustomValidator :: Maybe TermValidator
  }
  deriving (Generic)

type CDDLMap = Map.Map Name CDDLMapEntry

toParametrised ::
  TypeOrGroup CTreePhase ->
  Maybe (GenericParameters CTreePhase) ->
  ProvidedParameters (TypeOrGroup CTreePhase)
toParametrised a Nothing = ProvidedParameters [] a
toParametrised a (Just (GenericParameters gps)) = ProvidedParameters (gpName <$> NE.toList gps) a

asMap :: CDDL CTreePhase -> CDDLMap
asMap cddl = foldl' go Map.empty rules
  where
    rules = cddlTopLevel cddl
    go x (XXTopLevel _) = x
    go x (TopLevelRule r) = assignOrExtend x r

    assignOrExtend :: CDDLMap -> Rule CTreePhase -> CDDLMap
    assignOrExtend m (Rule n gps assign tog (CTreeXRule g v)) = case assign of
      -- Equals assignment
      AssignEq -> Map.insert n (CDDLMapEntry (toParametrised tog gps) g v) m
      AssignExt ->
        Map.alter (extend tog gps) n m

    extend ::
      TypeOrGroup CTreePhase ->
      Maybe (GenericParameters CTreePhase) ->
      Maybe CDDLMapEntry ->
      Maybe CDDLMapEntry
    extend tog _gps (Just cme) = case (underlying $ cmeProvidedParameters cme, tog) of
      (TOGType _, TOGType (Type0 new)) ->
        Just $
          cme
            & #cmeProvidedParameters
            % field @"underlying"
            % _Ctor @"TOGType"
            % _Ctor @"Type0"
            %~ (<> new)
      -- From the CDDL spec, I don't see how one is meant to extend a group.
      -- According to the description, it's meant to add a group choice, but the
      -- assignment to a group takes a 'GrpEntry', not a Group, and there is no
      -- ability to add a choice. For now, we simply ignore attempt at
      -- extension.
      (TOGGroup _, TOGGroup _new) -> Just cme
      (TOGType _, _) -> error "Attempting to extend a type with a group"
      (TOGGroup _, _) -> error "Attempting to extend a group with a type"
    extend tog gps Nothing =
      Just $ CDDLMapEntry (toParametrised tog gps) Nothing Nothing

--------------------------------------------------------------------------------
-- 2. Conversion to CTree
--------------------------------------------------------------------------------

type data OrReferenced

data instance XXCTree OrReferenced
  = -- | Reference to another node with possible generic arguments supplied
    OrRef Name [CTree OrReferenced]
  | OGenerator (CBORGen RuleTerm) (CTree OrReferenced)
  | OValidator TermValidator (CTree OrReferenced)

type data OrReferencedSimple

data instance XXCTree OrReferencedSimple = DGOrRef Name [CTree OrReferencedSimple]
  deriving (Eq, Show)

instance IndexMappable CTree OrReferenced OrReferencedSimple where
  mapIndex = foldCTree mapExt mapIndex
    where
      mapExt (OrRef n xs) = CTreeE $ DGOrRef n (mapIndex <$> xs)
      mapExt (OGenerator _ x) = mapIndex x
      mapExt (OValidator _ x) = mapIndex x

instance IndexMappable CTree MonoReferenced GenPhase where
  mapIndex = foldCTree mapExt mapIndex
    where
      mapExt (MRuleRef n) = CTreeE $ GenRef n
      mapExt (MGenerator g x) = CTreeE $ GenGenerator g (mapIndex x)
      mapExt (MValidator v x) = CTreeE $ GenValidator v (mapIndex x)

instance IndexMappable CTreeRoot MonoReferenced GenPhase where
  mapIndex (CTreeRoot m) = CTreeRoot $ mapIndex <$> m

instance IndexMappable CTree MonoReferenced ValidatorPhase where
  mapIndex = foldCTree mapExt mapIndex
    where
      mapExt (MRuleRef n) = CTreeE $ VRuleRef n
      mapExt (MGenerator _ x) = mapIndex x
      mapExt (MValidator v x) = CTreeE $ VValidator v (mapIndex x)

instance IndexMappable CTreeRoot MonoReferenced ValidatorPhase where
  mapIndex (CTreeRoot m) = CTreeRoot $ mapIndex <$> m

-- | Build a CTree incorporating references.
--
-- This translation cannot fail.
buildRefCTree :: CDDLMap -> PartialCTreeRoot OrReferenced
buildRefCTree rules = PartialCTreeRoot $ toCTreeRule <$> rules
  where
    toCTreeRule :: CDDLMapEntry -> ProvidedParameters (CTree OrReferenced)
    toCTreeRule CDDLMapEntry {..} =
      applyValidator . applyGenerator . toCTreeTOG <$> cmeProvidedParameters
      where
        applyGenerator = case cmeCustomGenerator of
          Just g -> CTreeE . OGenerator g
          Nothing -> id
        applyValidator = case cmeCustomValidator of
          Just v -> CTreeE . OValidator v
          Nothing -> id

    toCTreeTOG :: TypeOrGroup CTreePhase -> CTree OrReferenced
    toCTreeTOG (TOGType t0) = toCTreeT0 t0
    toCTreeTOG (TOGGroup ge) = toCTreeGroupEntry ge

    toCTreeT0 :: Type0 CTreePhase -> CTree OrReferenced
    toCTreeT0 (Type0 (t1 NE.:| [])) = toCTreeT1 t1
    toCTreeT0 (Type0 xs) = CTree.Choice $ toCTreeT1 <$> xs

    toCTreeT1 :: Type1 CTreePhase -> CTree OrReferenced
    toCTreeT1 (Type1 t2 Nothing _) = toCTreeT2 t2
    toCTreeT1 (Type1 t2 (Just (op, t2')) _) = case op of
      RangeOp bound ->
        CTree.Range
          { CTree.from = toCTreeT2 t2
          , CTree.to = toCTreeT2 t2'
          , CTree.inclusive = bound
          }
      CtrlOp ctlop ->
        CTree.Control
          { CTree.op = ctlop
          , CTree.target = toCTreeT2 t2
          , CTree.controller = toCTreeT2 t2'
          }

    toCTreeT2 :: Type2 CTreePhase -> CTree OrReferenced
    toCTreeT2 (T2Value v) = CTree.Literal v
    toCTreeT2 (T2Name n garg) = CTreeE $ OrRef n (fromGenArgs garg)
    toCTreeT2 (T2Group t0) =
      -- This behaviour seems questionable, but I don't really see how better to
      -- interpret the spec here.
      toCTreeT0 t0
    toCTreeT2 (T2Map g) = toCTreeMap g
    toCTreeT2 (T2Array g) = toCTreeArray g
    toCTreeT2 (T2Unwrapped n margs) =
      CTree.Unwrap . CTreeE $
        OrRef n (fromGenArgs margs)
    toCTreeT2 (T2Enum g) = toCTreeEnum g
    toCTreeT2 (T2EnumRef n margs) = CTreeE . OrRef n $ fromGenArgs margs
    toCTreeT2 (T2Tag Nothing t0) =
      -- Currently not validating tags
      toCTreeT0 t0
    toCTreeT2 (T2Tag (Just tag) t0) =
      CTree.Tag tag $ toCTreeT0 t0
    toCTreeT2 (T2DataItem 7 (Just mmin)) =
      toCTreeDataItem mmin
    toCTreeT2 (T2DataItem _maj _mmin) =
      -- We don't validate numerical items yet
      CTree.Postlude PTAny
    toCTreeT2 T2Any = CTree.Postlude PTAny
    toCTreeT2 (XXType2 v) = case v of {}

    toCTreeDataItem 20 =
      CTree.Literal $ Value (VBool False) mempty
    toCTreeDataItem 21 =
      CTree.Literal $ Value (VBool True) mempty
    toCTreeDataItem 25 =
      CTree.Postlude PTHalf
    toCTreeDataItem 26 =
      CTree.Postlude PTFloat
    toCTreeDataItem 27 =
      CTree.Postlude PTDouble
    toCTreeDataItem 23 =
      CTree.Postlude PTUndefined
    toCTreeDataItem _ =
      CTree.Postlude PTAny

    toCTreeGroupEntry :: GroupEntry CTreePhase -> CTree OrReferenced
    toCTreeGroupEntry (GroupEntry (Just occi) (GEType mmkey t0) _) =
      CTree.Occur
        { CTree.item = toKVPair mmkey t0
        , CTree.occurs = occi
        }
    toCTreeGroupEntry (GroupEntry Nothing (GEType mmkey t0) _) = toKVPair mmkey t0
    toCTreeGroupEntry (GroupEntry (Just occi) (GERef n margs) _) =
      CTree.Occur
        { CTree.item = CTreeE $ OrRef n (fromGenArgs margs)
        , CTree.occurs = occi
        }
    toCTreeGroupEntry (GroupEntry Nothing (GERef n margs) _) = CTreeE $ OrRef n (fromGenArgs margs)
    toCTreeGroupEntry (GroupEntry (Just occi) (GEGroup g) _) =
      CTree.Occur
        { CTree.item = groupToGroup g
        , CTree.occurs = occi
        }
    toCTreeGroupEntry (GroupEntry Nothing (GEGroup g) _) = groupToGroup g

    fromGenArgs :: Maybe (GenericArg CTreePhase) -> [CTree OrReferenced]
    fromGenArgs = maybe [] (\(GenericArg xs) -> NE.toList $ fmap toCTreeT1 xs)

    -- Interpret a group as an enumeration. Note that we float out the
    -- choice options
    toCTreeEnum :: Group CTreePhase -> CTree OrReferenced
    toCTreeEnum (CDDL.Group (a NE.:| [])) =
      CTree.Enum . CTree.Group $ toCTreeGroupEntry <$> gcGroupEntries a
    toCTreeEnum (CDDL.Group xs) =
      CTree.Choice $ CTree.Enum . CTree.Group . fmap toCTreeGroupEntry <$> groupEntries
      where
        groupEntries = fmap gcGroupEntries xs

    -- Embed a group in another group, again floating out the choice options
    groupToGroup :: Group CTreePhase -> CTree OrReferenced
    groupToGroup (CDDL.Group (a NE.:| [])) =
      CTree.Group $ fmap toCTreeGroupEntry (gcGroupEntries a)
    groupToGroup (CDDL.Group xs) =
      CTree.Choice $ fmap (CTree.Group . fmap toCTreeGroupEntry) (gcGroupEntries <$> xs)

    toKVPair :: Maybe (MemberKey CTreePhase) -> Type0 CTreePhase -> CTree OrReferenced
    toKVPair Nothing t0 = toCTreeT0 t0
    toKVPair (Just mkey) t0 =
      CTree.KV
        { CTree.key = toCTreeMemberKey mkey
        , CTree.value = toCTreeT0 t0
        , -- TODO Handle cut semantics
          CTree.cut = False
        }

    -- Interpret a group as a map. Note that we float out the choice options
    toCTreeMap :: Group CTreePhase -> CTree OrReferenced
    toCTreeMap (CDDL.Group (a NE.:| [])) = CTree.Map $ fmap toCTreeGroupEntry (gcGroupEntries a)
    toCTreeMap (CDDL.Group xs) =
      CTree.Choice $
        fmap (CTree.Map . fmap toCTreeGroupEntry) (gcGroupEntries <$> xs)

    -- Interpret a group as an array. Note that we float out the choice
    -- options
    toCTreeArray :: Group CTreePhase -> CTree OrReferenced
    toCTreeArray (CDDL.Group (a NE.:| [])) =
      CTree.Array $ fmap toCTreeGroupEntry (gcGroupEntries a)
    toCTreeArray (CDDL.Group xs) =
      CTree.Choice $
        fmap (CTree.Array . fmap toCTreeGroupEntry) (gcGroupEntries <$> xs)

    toCTreeMemberKey :: MemberKey CTreePhase -> CTree OrReferenced
    toCTreeMemberKey (MKValue v) = CTree.Literal v
    toCTreeMemberKey (MKBareword n) = CTree.Literal (Value (VText $ unName n) mempty)
    toCTreeMemberKey (MKType t1) = toCTreeT1 t1

--------------------------------------------------------------------------------
-- 3. Name resolution
--------------------------------------------------------------------------------

data NameResolutionFailure
  = UnboundReference Name
  | MismatchingArgs Name [Name]
  | ArgsToPostlude PTerm [CTree OrReferencedSimple]
  deriving (Show, Eq)

postludeBinding :: Map.Map Name PTerm
postludeBinding =
  Map.fromList
    [ ("bool", PTBool)
    , ("uint", PTUInt)
    , ("nint", PTNInt)
    , ("int", PTInt)
    , ("half", PTHalf)
    , ("float", PTFloat)
    , ("double", PTDouble)
    , ("bytes", PTBytes)
    , ("bstr", PTBytes)
    , ("text", PTText)
    , ("tstr", PTText)
    , ("any", PTAny)
    , ("nil", PTNil)
    , ("null", PTNil)
    ]

data BindingEnv i j = BindingEnv
  { global :: Map.Map Name (ProvidedParameters (CTree i))
  -- ^ Global name bindings via 'RuleDef'
  , local :: Map.Map Name (CTree j)
  -- ^ Local bindings for generic parameters
  }
  deriving (Generic)

type data DistReferenced

data DistRef i
  = -- | Reference to a generic parameter
    GenericRef Name
  | -- | Reference to a rule definition, possibly with generic arguments
    RuleRef Name [CTree i]
  deriving (Generic)

deriving instance Eq (CTree.Node i) => Eq (DistRef i)

deriving instance Show (CTree.Node i) => Show (DistRef i)

instance Hashable (CTree.Node i) => Hashable (DistRef i)

instance Pretty (XXCTree i) => Pretty (DistRef i) where
  pretty (GenericRef n) = pretty n
  pretty (RuleRef rule []) = pretty rule
  pretty (RuleRef rule args) = pretty rule <> encloseSep "<" ">" "," (pretty <$> args)

data instance XXCTree DistReferenced
  = DRef (DistRef DistReferenced)
  | DGenerator (CBORGen RuleTerm) (CTree DistReferenced)
  | DValidator TermValidator (CTree DistReferenced)

type data DistReferencedNoGen

newtype instance XXCTree DistReferencedNoGen = DHRef (DistRef DistReferencedNoGen)
  deriving (Eq, Hashable, Show)
  deriving newtype (Pretty)

resolveRef ::
  BindingEnv OrReferenced OrReferenced ->
  CTree.Node OrReferenced ->
  Either NameResolutionFailure (CTree DistReferenced)
resolveRef env (OrRef n args) = case Map.lookup n postludeBinding of
  Just pterm -> case args of
    [] -> Right $ CTree.Postlude pterm
    xs -> Left . ArgsToPostlude pterm $ mapIndex <$> xs
  Nothing -> case Map.lookup n (global env) of
    Just (parameters -> params') ->
      if length params' == length args
        then
          let localBinds = Map.fromList $ zip params' args
              newEnv = env & #local %~ Map.union localBinds
           in CTreeE . DRef . RuleRef n <$> traverse (resolveCTree newEnv) args
        else Left $ MismatchingArgs n params'
    Nothing -> case Map.lookup n (local env) of
      Just _ -> Right . CTreeE . DRef $ GenericRef n
      Nothing -> Left $ UnboundReference n
resolveRef env (OGenerator g x) = CTreeE . DGenerator g <$> resolveCTree env x
resolveRef env (OValidator v x) = CTreeE . DValidator v <$> resolveCTree env x

resolveCTree ::
  BindingEnv OrReferenced OrReferenced ->
  CTree OrReferenced ->
  Either NameResolutionFailure (CTree DistReferenced)
resolveCTree e = CTree.traverseCTree (resolveRef e) (resolveCTree e)

buildResolvedCTree ::
  PartialCTreeRoot OrReferenced ->
  Either NameResolutionFailure (PartialCTreeRoot DistReferenced)
buildResolvedCTree (PartialCTreeRoot ct) = PartialCTreeRoot <$> traverse go ct
  where
    go pn =
      let args = parameters pn
          localBinds = Map.fromList $ zip args (CTreeE . flip OrRef [] <$> args)
          env = BindingEnv @OrReferenced @OrReferenced ct localBinds
       in traverse (resolveCTree env) pn

--------------------------------------------------------------------------------
-- 4. Monomorphisation
--------------------------------------------------------------------------------

type data MonoReferenced

data instance XXCTree MonoReferenced
  = MRuleRef Name
  | MGenerator (CBORGen RuleTerm) (CTree MonoReferenced)
  | MValidator TermValidator (CTree MonoReferenced)

type MonoEnv = BindingEnv DistReferenced MonoReferenced

-- | We introduce additional bindings in the state
type MonoState = Map.Map Name (CTree MonoReferenced)

-- | A simplified phase reachable from any of the function-bearing post-mono
-- phases ('MonoReferenced', 'GenPhase', 'ValidatorPhase'). It strips the
-- generator/validator extensions so the tree can be `Show`n, `Eq`-compared,
-- and pretty-printed for debug output.
type data MonoSimplePhase

newtype instance XXCTree MonoSimplePhase = MSimpleRef Name
  deriving (Generic, Show, Eq)

instance Pretty (XXCTree MonoSimplePhase) where
  pretty (MSimpleRef n) = pretty n

instance IndexMappable CTree MonoReferenced MonoSimplePhase where
  mapIndex = foldCTree mapExt mapIndex
    where
      mapExt (MRuleRef n) = CTreeE $ MSimpleRef n
      mapExt (MGenerator _ x) = mapIndex x
      mapExt (MValidator _ x) = mapIndex x

instance IndexMappable CTreeRoot MonoReferenced MonoSimplePhase where
  mapIndex (CTreeRoot m) = CTreeRoot $ mapIndex <$> m

instance IndexMappable CTree GenPhase MonoSimplePhase where
  mapIndex = foldCTree mapExt mapIndex
    where
      mapExt (GenRef n) = CTreeE $ MSimpleRef n
      mapExt (GenGenerator _ x) = mapIndex x
      mapExt (GenValidator _ x) = mapIndex x

instance IndexMappable CTreeRoot GenPhase MonoSimplePhase where
  mapIndex (CTreeRoot m) = CTreeRoot $ mapIndex <$> m

instance IndexMappable CTree ValidatorPhase MonoSimplePhase where
  mapIndex = foldCTree mapExt mapIndex
    where
      mapExt (VRuleRef n) = CTreeE $ MSimpleRef n
      mapExt (VValidator _ x) = mapIndex x

instance IndexMappable CTreeRoot ValidatorPhase MonoSimplePhase where
  mapIndex (CTreeRoot m) = CTreeRoot $ mapIndex <$> m

-- | Project any phase that maps to 'MonoSimplePhase' down to a `Show`able
-- representation. Used for debug output by `Gen`, `Validator`, etc.
showSimple ::
  forall a phase.
  ( IndexMappable a phase MonoSimplePhase
  , Show (a MonoSimplePhase)
  ) =>
  a phase -> String
showSimple = show . mapIndex @_ @_ @MonoSimplePhase

-- | Monad to run the monomorphisation process. We need some additional
-- capabilities for this, so 'Either' doesn't fully cut it anymore.
newtype MonoM a = MonoM
  { runMonoM ::
      ExceptT
        NameResolutionFailure
        (StateT MonoState (Reader MonoEnv))
        a
  }
  deriving (Functor, Applicative, Monad)
  deriving
    (HasThrow "nameResolution" NameResolutionFailure)
    via MonadError
          ( ExceptT
              NameResolutionFailure
              (StateT MonoState (Reader MonoEnv))
          )
  deriving
    ( HasSource
        "local"
        (Map.Map (Name) (CTree MonoReferenced))
    , HasReader
        "local"
        (Map.Map (Name) (CTree MonoReferenced))
    )
    via Field
          "local"
          ()
          ( Lift
              ( ExceptT
                  NameResolutionFailure
                  (Lift (StateT MonoState (MonadReader (Reader MonoEnv))))
              )
          )
  deriving
    ( HasSource
        "global"
        (Map.Map (Name) (ProvidedParameters (CTree DistReferenced)))
    , HasReader
        "global"
        (Map.Map (Name) (ProvidedParameters (CTree DistReferenced)))
    )
    via Field
          "global"
          ()
          ( Lift
              ( ExceptT
                  NameResolutionFailure
                  (Lift (StateT MonoState (MonadReader (Reader MonoEnv))))
              )
          )
  deriving
    ( HasSource "synth" MonoState
    , HasSink "synth" MonoState
    , HasState "synth" MonoState
    )
    via Lift
          ( ExceptT
              NameResolutionFailure
              (MonadState (StateT MonoState (Reader MonoEnv)))
          )

throwNR :: NameResolutionFailure -> MonoM a
throwNR = throw @"nameResolution"

-- | Synthesize a monomorphic rule definition, returning the name
synthMono :: Name -> [CTree DistReferenced] -> MonoM Name
synthMono origName args =
  let dropGenerator = fmap $ mapIndex @_ @DistReferenced @DistReferencedNoGen
      argsName = Name (T.intercalate "," $ renderStrict . layoutCompact . pretty <$> dropGenerator args)
      -- We use % to mark a monomorphised generic rule, '%' is not allowed in
      -- CDDL names, so there should be no conflicts
      fresh = "%" <> origName <> "<" <> argsName <> ">"
   in do
        -- Lookup the original name in the global bindings
        globalBinds <- ask @"global"
        case Map.lookup origName globalBinds of
          Just (ProvidedParameters [] _) -> throwNR $ MismatchingArgs origName []
          Just (ProvidedParameters params' r) ->
            if length params' == length args
              then do
                rargs <- traverse resolveGenericCTree args
                let localBinds = Map.fromList $ zip params' rargs
                Reader.local @"local" (Map.union localBinds) $ do
                  foo <- resolveGenericCTree r
                  modify @"synth" $ Map.insert fresh foo
              else throwNR $ MismatchingArgs origName params'
          Nothing -> throwNR $ UnboundReference origName
        pure fresh

resolveGenericRef ::
  CTree.Node DistReferenced ->
  MonoM (CTree MonoReferenced)
resolveGenericRef (DRef (RuleRef n [])) = pure . CTreeE $ MRuleRef n
resolveGenericRef (DRef (RuleRef n args)) = do
  fresh <- synthMono n args
  pure . CTreeE $ MRuleRef fresh
resolveGenericRef (DRef (GenericRef n)) = do
  localBinds <- ask @"local"
  case Map.lookup n localBinds of
    Just node -> pure node
    Nothing -> throwNR $ UnboundReference n
resolveGenericRef (DGenerator g x) = do
  binds <- ask @"local"
  body <- resolveGenericCTree x
  let bindsGen = mapIndex @CTree @MonoReferenced @GenPhase <$> binds
      g' = withLocalGenBindings bindsGen g
  pure . CTreeE $ MGenerator g' body
resolveGenericRef (DValidator v x) = do
  binds <- ask @"local"
  body <- resolveGenericCTree x
  let bindsVal = mapIndex @CTree @MonoReferenced @ValidatorPhase <$> binds
      v' = withLocalValidateBindings bindsVal . v
  pure . CTreeE $ MValidator v' body

resolveGenericCTree ::
  CTree DistReferenced ->
  MonoM (CTree MonoReferenced)
resolveGenericCTree = CTree.traverseCTree resolveGenericRef resolveGenericCTree

-- | Monomorphise the CTree
--
-- Concretely, for each reference in the tree to a generic rule, we synthesize a
-- new monomorphic instance of that rule at top-level with the correct
-- parameters applied.
buildMonoCTree ::
  PartialCTreeRoot DistReferenced ->
  Either NameResolutionFailure (CTreeRoot MonoReferenced)
buildMonoCTree (PartialCTreeRoot ct) = do
  let a1 = runExceptT $ runMonoM (traverse resolveGenericCTree monoC)
      a2 = runStateT a1 mempty
      (r, newBindings) = runReader a2 initBindingEnv
  CTreeRoot . (`Map.union` newBindings) <$> r
  where
    initBindingEnv = BindingEnv ct mempty
    monoC =
      Map.mapMaybe
        ( \case
            ProvidedParameters [] f -> Just f
            _ -> Nothing
        )
        ct

--------------------------------------------------------------------------------
-- Combined resolution
--------------------------------------------------------------------------------

fullResolveCDDL :: CDDL CTreePhase -> Either NameResolutionFailure (CTreeRoot MonoReferenced)
fullResolveCDDL cddl = do
  let refCTree = buildRefCTree (asMap cddl)
  rCTree <- buildResolvedCTree refCTree
  buildMonoCTree rCTree

instance IndexMappable CTree DistReferenced DistReferencedNoGen where
  mapIndex = foldCTree mapExt mapIndex
    where
      mapExt (DRef x) = CTreeE . DHRef $ mapIndex x
      mapExt (DGenerator _ x) = mapIndex x
      mapExt (DValidator _ x) = mapIndex x

instance IndexMappable DistRef DistReferenced DistReferencedNoGen where
  mapIndex (GenericRef n) = GenericRef n
  mapIndex (RuleRef n args) = RuleRef n $ mapIndex <$> args
