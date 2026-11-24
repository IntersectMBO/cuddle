{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TypeData #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module Codec.CBOR.Cuddle.CDDL.Custom.Validator (
  TermValidator,
  ValidatorPhase,
  Validator,
  XXCTree (..),
  HasValidator (..),
  ValidateEnv (..),
  withLocalValidateBindings,
  runValidator,
  mapTrace,
  isValid,
  compareEvidencedProgress,
  nestContainer,
  TraceOptions (..),
  defaultTraceOptions,
  prettyListValidationResult,
  showValidationTrace,

  -- * Trace
  SValidity (..),
  Validity (..),
  Progress (..),
  Evidenced (..),
  ControlInfo (..),
  ValidationTrace (..),
  ListValidationTrace (..),
  MapValidationTrace (..),
  evidence,
  fromEither,
  foldEvidenced,
  measureProgress,
  prettyValidationTrace,
) where

import Codec.CBOR.Cuddle.CBOR.Canonical (CanonicalTerm)
import Codec.CBOR.Cuddle.CDDL (GRef (..), Name (..))
import Codec.CBOR.Cuddle.CDDL.CTree (CTree (..), CTreeRoot (..), XXCTree (..), foldCTree)
import Codec.CBOR.Cuddle.CDDL.CtlOp (CtlOp)
import Codec.CBOR.Cuddle.CDDL.Custom.Core (MonadCddl (..), RuleTerm)
import Codec.CBOR.Cuddle.CDDL.Phase (MonoSimplePhase)
import Codec.CBOR.Cuddle.IndexMappable (IndexMappable (..))
import Codec.CBOR.Term (Term)
import Control.Applicative (Alternative (..))
import Control.Monad.Except (ExceptT, MonadError (..), runExceptT, tryError)
import Control.Monad.Reader (MonadReader (..), ReaderT (..), asks)
import Control.Monad.State.Strict (MonadState (..), State, modify, runState)
import Data.Foldable (Foldable (..))
import Data.Function (on)
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as T
import Data.Type.Equality (TestEquality (..), type (:~:) (..))
import Data.Word (Word64)
import Optics.Lens (Lens')
import Prettyprinter (
  Doc,
  Pretty (..),
  annotate,
  defaultLayoutOptions,
  hang,
  indent,
  layoutPretty,
  vsep,
  (<+>),
 )
import Prettyprinter.Render.Terminal (AnsiStyle, Color (..), color, italicized)
import Prettyprinter.Render.Terminal qualified as Ansi

type data ValidatorPhase

data instance XXCTree ValidatorPhase
  = VRuleRef Name
  | VValidator TermValidator (CTree ValidatorPhase)

class HasValidator a where
  validatorL :: Lens' a (Maybe TermValidator)

data ValidateEnv = ValidateEnv
  { veRoot :: CTreeRoot ValidatorPhase
  , veLocal :: Map Name (CTree ValidatorPhase)
  }

newtype Validator a
  = Validator
      (ReaderT ValidateEnv (ExceptT (ValidationTrace IsInvalid) (State [ValidationTrace IsValid])) a)
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
  fail msg = failWith $ CustomFailure $ T.pack msg

instance Alternative Validator where
  Validator x <|> Validator y = Validator $ do
    initialSt <- get
    xRes <- tryError x
    case xRes of
      Right res -> pure res
      Left AlternativeFail -> put initialSt >> y
      Left xFail -> do
        xSt <- get
        put initialSt
        yRes <- tryError y
        ySt <- get
        case yRes of
          Right res -> pure res
          Left AlternativeFail -> put xSt >> throwError xFail
          Left yFail -> do
            let
              xTrc = closeSteps xSt $ StepFailed xFail
              yTrc = closeSteps ySt $ StepFailed yFail
            case compareInvalidProgress xTrc yTrc of
              GT -> put xSt >> throwError xFail
              _ -> put ySt >> throwError yFail
  empty = failWith AlternativeFail

closeSteps :: [ValidationTrace IsValid] -> StepTrace v -> StepTrace v
closeSteps steps cap = foldl' (flip Step) cap steps

capture :: Validator a -> Validator (Either (StepTrace IsInvalid) (a, StepTrace IsValid))
capture (Validator m) = Validator $ do
  saved <- get
  put []
  r <- tryError m
  steps <- get
  put saved
  pure $ case r of
    Left err -> Left $ closeSteps steps (StepFailed err)
    Right x -> Right (x, closeSteps steps StepsDone)

accept :: CTree ValidatorPhase -> Validator ()
accept rule = Validator $ modify (TerminalRule (mapIndex rule) :)

failWith :: ValidationTrace IsInvalid -> Validator a
failWith err = Validator $ throwError err

-- | Run an action with the given local generic bindings installed.
withLocalValidateBindings ::
  Map Name (CTree ValidatorPhase) -> Validator a -> Validator a
withLocalValidateBindings binds =
  local (\env -> env {veLocal = binds `Map.union` veLocal env})

runValidator :: ValidateEnv -> Validator a -> Evidenced StepTrace
runValidator env (Validator m) = mkStepTrace $ runState (runExceptT $ runReaderT m env) []
  where
    mkStepTrace (eFail, st) =
      case eFail of
        Right _ -> evidence $ closeSteps st StepsDone
        Left err -> evidence $ closeSteps st (StepFailed err)

type data Validity
  = IsValid
  | IsInvalid

data SValidity (v :: Validity) where
  SInvalid :: SValidity IsInvalid
  SValid :: SValidity IsValid

deriving instance Eq (SValidity v)

deriving instance Ord (SValidity v)

deriving instance Show (SValidity v)

instance TestEquality SValidity where
  testEquality SValid SValid = Just Refl
  testEquality SInvalid SInvalid = Just Refl
  testEquality _ _ = Nothing

data Evidenced t where
  Evidenced ::
    { eValidity :: SValidity v
    , eTrace :: t v
    } ->
    Evidenced t

mapTrace :: (forall v. Show (u v)) => (forall v. t v -> u v) -> Evidenced t -> Evidenced u
mapTrace f (Evidenced v t) = Evidenced v $ f t

foldEvidenced :: (forall v. t v -> a) -> Evidenced t -> a
foldEvidenced f (Evidenced v t) =
  case v of
    SValid -> f t
    SInvalid -> f t

fromEither ::
  ( IsValidationTrace t
  , Show (t IsInvalid)
  , Show (t IsValid)
  ) =>
  Either (t IsInvalid) (t IsValid) -> Evidenced t
fromEither = either evidence evidence

deriving instance (forall v. Show (t v)) => Show (Evidenced t)

class IsValidationTrace (t :: Validity -> Type) where
  traceValidity :: t v -> SValidity v
  measureProgress :: t v -> Progress

instance IsValidationTrace t => Semigroup (Evidenced t) where
  x@(Evidenced SValid _) <> _ = x
  _ <> y@(Evidenced SValid _) = y
  Evidenced SInvalid x <> Evidenced SInvalid y =
    Evidenced SInvalid $ case compareInvalidProgress x y of
      GT -> x
      _ -> y

data Progress = Progress {termProgress :: !Int, refProgress :: !Int}
  deriving (Eq, Ord)

instance Semigroup Progress where
  Progress t1 r1 <> Progress t2 r2 = Progress (t1 + t2) (r1 + r2)

instance Monoid Progress where
  mempty = Progress 0 0

increaseTermProgress :: Progress -> Progress
increaseTermProgress p = p <> Progress 1 0

increaseRefProgress :: Progress -> Progress
increaseRefProgress p = p <> Progress 0 1

--------------------------------------------------------------------------------
-- Validation result

data ControlInfo = ControlInfo
  { ciOp :: CtlOp
  , ciRule :: CTree MonoSimplePhase
  }
  deriving (Show)

instance Pretty ControlInfo where
  pretty ControlInfo {..} = pretty ciOp <+> pretty ciRule

data StepTrace v where
  StepsDone :: StepTrace IsValid
  Step :: ValidationTrace IsValid -> StepTrace v -> StepTrace v
  StepFailed :: ValidationTrace IsInvalid -> StepTrace IsInvalid

deriving instance Show (StepTrace v)

instance IsValidationTrace StepTrace where
  traceValidity = \case
    StepsDone -> SValid
    StepFailed _ -> SInvalid
    Step _ next -> traceValidity next
  measureProgress = \case
    StepsDone -> Progress 1 0
    StepFailed x -> measureProgress x
    Step this next -> measureProgress this <> measureProgress next

data ValidationTrace (v :: Validity) where
  AlternativeFail :: ValidationTrace IsInvalid
  UnapplicableRule :: CTree MonoSimplePhase -> ValidationTrace IsInvalid
  TerminalRule :: CTree MonoSimplePhase -> ValidationTrace IsValid
  ControlTrace :: ControlInfo -> ValidationTrace IsValid -> ValidationTrace IsValid
  ReferenceRule :: Name -> ValidationTrace v -> ValidationTrace v
  CustomFailure :: Text -> ValidationTrace IsInvalid
  UnsatisfiedControl :: CtlOp -> CTree MonoSimplePhase -> ValidationTrace IsInvalid
  ChoiceBranch :: Int -> ValidationTrace IsValid -> ValidationTrace IsValid
  ListTrace :: ListValidationTrace v -> ValidationTrace v
  MapTrace :: MapValidationTrace v -> ValidationTrace v
  TagTrace :: Word64 -> ValidationTrace v -> ValidationTrace v
  InvalidTag :: Word64 -> Word64 -> ValidationTrace IsInvalid

deriving instance Show (ValidationTrace v)

data ListValidationTrace (v :: Validity) where
  ListValidationDone :: ListValidationTrace IsValid
  ListValidationLeftoverTerms ::
    NonEmpty Term ->
    Maybe (CTree MonoSimplePhase, ValidationTrace IsInvalid) ->
    ListValidationTrace IsInvalid
  ListValidationUnappliedRule ::
    CTree MonoSimplePhase ->
    ListValidationTrace IsInvalid
  ListValidationConsume ::
    CTree MonoSimplePhase ->
    ValidationTrace IsValid ->
    ListValidationTrace v ->
    ListValidationTrace v
  ListValidationMissingRequired ::
    CTree MonoSimplePhase ->
    ValidationTrace IsInvalid ->
    ListValidationTrace IsInvalid
  ListValidationConsumeGroup ::
    [Name] ->
    ListValidationTrace IsValid ->
    ListValidationTrace v ->
    ListValidationTrace v
  ListValidationBadGroup ::
    [Name] ->
    ListValidationTrace IsInvalid ->
    ListValidationTrace IsInvalid

deriving instance Show (ListValidationTrace v)

data MapValidationTrace (v :: Validity) where
  MapValidationDone :: MapValidationTrace IsValid
  MapValidationLeftoverKVs ::
    (Term, Term) ->
    Maybe (CTree MonoSimplePhase, MapValidationTrace IsInvalid) ->
    MapValidationTrace IsInvalid
  MapValidationUnappliedRules :: NonEmpty (CTree MonoSimplePhase) -> MapValidationTrace IsInvalid
  MapValidationInvalidValue ::
    CTree MonoSimplePhase ->
    ValidationTrace IsValid ->
    ValidationTrace IsInvalid ->
    MapValidationTrace IsInvalid
  MapValidationConsume ::
    CTree MonoSimplePhase ->
    ValidationTrace IsValid ->
    ValidationTrace IsValid ->
    MapValidationTrace v ->
    MapValidationTrace v
  MapValidationDuplicateKeys ::
    CTree MonoSimplePhase ->
    CanonicalTerm ->
    ValidationTrace IsValid ->
    MapValidationTrace IsInvalid

deriving instance Show (MapValidationTrace v)

instance IsValidationTrace ValidationTrace where
  traceValidity = \case
    TerminalRule {} -> SValid
    ControlTrace {} -> SValid
    ChoiceBranch {} -> SValid
    UnapplicableRule {} -> SInvalid
    CustomFailure {} -> SInvalid
    UnsatisfiedControl {} -> SInvalid
    InvalidTag {} -> SInvalid
    ReferenceRule _ x -> traceValidity x
    ListTrace x -> traceValidity x
    MapTrace x -> traceValidity x
    TagTrace _ x -> traceValidity x
    AlternativeFail -> SInvalid

  measureProgress = \case
    TerminalRule {} -> Progress 1 0
    ControlTrace _ x -> measureProgress x
    ChoiceBranch _ x -> measureProgress x
    UnapplicableRule {} -> mempty
    CustomFailure {} -> mempty
    UnsatisfiedControl {} -> mempty
    InvalidTag {} -> mempty
    AlternativeFail -> mempty
    ReferenceRule _ x -> increaseRefProgress $ measureProgress x
    ListTrace x -> measureProgress x
    MapTrace x -> measureProgress x
    TagTrace _ x -> increaseTermProgress $ measureProgress x

instance IsValidationTrace ListValidationTrace where
  traceValidity = \case
    ListValidationDone -> SValid
    ListValidationLeftoverTerms {} -> SInvalid
    ListValidationUnappliedRule {} -> SInvalid
    ListValidationMissingRequired {} -> SInvalid
    ListValidationBadGroup _ _ -> SInvalid
    ListValidationConsume _ _ x -> traceValidity x
    ListValidationConsumeGroup _ _ x -> traceValidity x

  measureProgress = \case
    ListValidationDone -> Progress 1 0
    ListValidationConsume _ _ x -> increaseTermProgress $ measureProgress x
    ListValidationLeftoverTerms _ Nothing -> mempty
    ListValidationLeftoverTerms _ (Just (_, trc)) -> measureProgress trc
    ListValidationMissingRequired _ _ -> mempty
    ListValidationUnappliedRule _ -> mempty
    ListValidationConsumeGroup rs g x -> Progress 0 (length rs) <> measureProgress g <> measureProgress x
    ListValidationBadGroup rs x -> Progress 0 (length rs) <> measureProgress x

instance IsValidationTrace MapValidationTrace where
  traceValidity = \case
    MapValidationDone -> SValid
    MapValidationLeftoverKVs _ _ -> SInvalid
    MapValidationUnappliedRules _ -> SInvalid
    MapValidationInvalidValue {} -> SInvalid
    MapValidationDuplicateKeys {} -> SInvalid
    MapValidationConsume _ _ _ x -> traceValidity x

  measureProgress = \case
    MapValidationDone -> Progress 1 0
    MapValidationLeftoverKVs _ Nothing -> mempty
    MapValidationLeftoverKVs _ (Just (_, trc)) -> measureProgress trc
    MapValidationUnappliedRules _ -> mempty
    MapValidationConsume _ kTrc vTrc x ->
      measureProgress kTrc <> measureProgress vTrc <> measureProgress x
    MapValidationInvalidValue _ kTrc vTrc ->
      measureProgress kTrc <> measureProgress vTrc
    MapValidationDuplicateKeys _ _ trc -> measureProgress trc

evidence :: (Show (t v), IsValidationTrace t) => t v -> Evidenced t
evidence x = Evidenced (traceValidity x) x

isValid :: Evidenced t -> Bool
isValid Evidenced {eValidity = SValid} = True
isValid _ = False

compareEvidencedProgress :: IsValidationTrace t => Evidenced t -> Evidenced t -> Ordering
compareEvidencedProgress (Evidenced SValid _) (Evidenced SValid _) = EQ
compareEvidencedProgress (Evidenced SInvalid _) (Evidenced SValid _) = LT
compareEvidencedProgress (Evidenced SValid _) (Evidenced SInvalid _) = GT
compareEvidencedProgress (Evidenced SInvalid x) (Evidenced SInvalid y) =
  x `compareInvalidProgress` y

compareInvalidProgress :: IsValidationTrace t => t IsInvalid -> t IsInvalid -> Ordering
compareInvalidProgress = compare `on` measureProgress

nestContainer :: Doc AnsiStyle -> Doc AnsiStyle
nestContainer = hang 2 . ("└ " <>)

newtype TraceOptions = TraceOptions
  { toFoldValid :: Bool
  }

defaultTraceOptions :: TraceOptions
defaultTraceOptions = TraceOptions {toFoldValid = False}

prettyListValidationResult :: TraceOptions -> ListValidationTrace v -> Doc AnsiStyle
prettyListValidationResult opts@TraceOptions {..} = \case
  ListValidationDone -> mempty
  ListValidationLeftoverTerms _ Nothing ->
    annotate (color Red) "leftover elements not matched by any rule"
  ListValidationLeftoverTerms _ (Just (rule, trc)) ->
    hang 2 $
      vsep
        [ annotate (color Red) "leftover elements, closest matching rule:"
        , annotate (color Green) $ pretty $ show rule
        , nestContainer $ prettyValidationTrace opts trc
        ]
  ListValidationUnappliedRule r ->
    hang 2 $
      vsep
        [ annotate (color Red) "required rule not satisfied:"
        , pretty r
        ]
  ListValidationConsume _ t c
    | toFoldValid -> foldValid 1 c
    | otherwise -> vsep $ continue c [prettyValidationTrace opts t]
  ListValidationMissingRequired _ t ->
    vsep
      [ annotate (color Red) "failed to apply required rule:"
      , nestContainer $ prettyValidationTrace opts t
      ]
  ListValidationConsumeGroup refs x c -> vsep . continue c $ prettyGroup SValid refs x
  ListValidationBadGroup refs x -> vsep $ prettyGroup SInvalid refs x
  where
    -- This prevents unnecessary empty lines
    continue ListValidationDone l = l
    continue x l = l <> [prettyListValidationResult opts x]

    prettyGroup :: SValidity v -> [Name] -> ListValidationTrace v -> [Doc AnsiStyle]
    prettyGroup v refs x = go refs
      where
        go (n : ns) =
          [ "ref" <+> pretty n
          , nestContainer . vsep $ go ns
          ]
        go [] =
          [ case v of
              SValid -> "grp"
              SInvalid -> "grp" <+> annotate (color Red) "(fail)"
          , nestContainer $ prettyListValidationResult opts x
          ]

    foldValid !n (ListValidationConsume _ _ c) = foldValid (n + 1) c
    foldValid !n t =
      vsep $ continue t [annotate italicized $ pretty (n :: Int) <> " valid elements"]

prettyMapValidationResult :: TraceOptions -> MapValidationTrace v -> Doc AnsiStyle
prettyMapValidationResult opts@TraceOptions {..} = \case
  MapValidationDone -> mempty
  MapValidationLeftoverKVs _ Nothing ->
    annotate (color Red) "leftover key-value pairs not matched by any rule"
  MapValidationLeftoverKVs _ (Just (rule, trc)) ->
    hang 2 $
      vsep
        [ annotate (color Red) "leftover key-value pairs, closest matching rule:"
        , annotate (color Green) $ pretty rule
        , nestContainer $ prettyMapValidationResult opts trc
        ]
  MapValidationUnappliedRules rs ->
    hang 2 $
      vsep
        [ annotate (color Red) "not all required rules have been applied:"
        , vsep (NE.toList $ pretty <$> rs)
        ]
  MapValidationConsume _ k v c
    | toFoldValid -> foldValid 1 c
    | otherwise ->
        vsep $
          continue
            c
            [ "key:"
            , nestContainer $ prettyValidationTrace opts k
            , "value:"
            , nestContainer $ prettyValidationTrace opts v
            ]
  MapValidationInvalidValue _ k v ->
    vsep
      [ "key:"
      , nestContainer $ prettyValidationTrace opts k
      , "value:" <+> annotate (color Red) "(fail)"
      , nestContainer $ prettyValidationTrace opts v
      ]
  MapValidationDuplicateKeys _ _ trc ->
    vsep
      [ "key: " <> annotate (color Red) "(duplicate)"
      , nestContainer $ prettyValidationTrace opts trc
      ]
  where
    foldValid !n (MapValidationConsume _ _ _ c) = foldValid (n + 1) c
    foldValid !n t =
      vsep . continue t $
        [ annotate italicized $ pretty (n :: Int) <> " valid key-value pairs"
        , "..."
        ]

    -- This prevents unnecessary empty lines
    continue MapValidationDone l = l
    continue x l = l <> [prettyMapValidationResult opts x]

prettyValidationTrace :: TraceOptions -> ValidationTrace v -> Doc AnsiStyle
prettyValidationTrace opts = \case
  UnapplicableRule x -> annotate (color Red) $ vsep ["failed to apply: ", indent 2 $ pretty x]
  TerminalRule x -> "app: " <> annotate (color Green) (pretty x)
  ControlTrace ci x ->
    vsep
      [ prettyValidationTrace opts x
      , nestContainer $ "ctrl:" <+> annotate (color Yellow) ("." <> pretty ci)
      ]
  ChoiceBranch i c ->
    vsep
      [ "choice (idx: " <> pretty i <> ")"
      , nestContainer $ prettyValidationTrace opts c
      ]
  ReferenceRule (Name n) x ->
    vsep
      [ "ref: " <> annotate (color Blue) (pretty n)
      , nestContainer $ prettyValidationTrace opts x
      ]
  CustomFailure e -> annotate (color Red) $ pretty e
  UnsatisfiedControl op ctl ->
    annotate (color Red) $
      vsep
        [ "unsatisfied control:"
        , indent 2 $ "." <> pretty op <+> pretty ctl
        ]
  ListTrace l ->
    vsep
      [ "array"
      , nestContainer $ prettyListValidationResult opts l
      ]
  MapTrace m ->
    vsep
      [ "map"
      , nestContainer $ prettyMapValidationResult opts m
      ]
  TagTrace t x ->
    vsep
      [ "tag:" <+> annotate (color Green) ("#6." <> pretty t)
      , nestContainer $ prettyValidationTrace opts x
      ]
  InvalidTag expected actual ->
    "expected tag #6." <> pretty expected <> ", got #6." <> pretty actual
  AlternativeFail -> mempty

showValidationTrace :: ValidationTrace v -> String
showValidationTrace =
  T.unpack
    . Ansi.renderStrict
    . layoutPretty defaultLayoutOptions
    . prettyValidationTrace defaultTraceOptions

instance IndexMappable CTree ValidatorPhase MonoSimplePhase where
  mapIndex = foldCTree mapExt mapIndex
    where
      mapExt (VRuleRef n) = CTreeE $ MSimpleRef n
      mapExt (VValidator _ x) = mapIndex x
