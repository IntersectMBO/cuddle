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
  ValidatorT,
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
  showValidationTrace,
  accept,
  reject,
  failWith,
  withChoice,
  withTag,
  withArray,
  withMap,
  controlVerdict,
  element,
  entry,
  runBlock,

  -- * Trace
  SValidity (..),
  Validity (..),
  Progress (..),
  Evidenced (..),
  ControlInfo (..),
  ValidationTrace (..),
  StepTrace (..),
  Block (..),
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
import Control.Monad.State.Strict (MonadState (..), State, modify', runState)
import Data.Foldable (Foldable (..))
import Data.Function (on)
import Data.Kind (Type)
import Data.List.NonEmpty (NonEmpty)
import Data.List.NonEmpty qualified as NE
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (maybeToList)
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

newtype ValidatorT (b :: Block) a
  = Validator
      (ReaderT ValidateEnv (ExceptT (ValidationTrace b IsInvalid) (State [ValidationTrace b IsValid])) a)
  deriving (Functor, Applicative, Monad, MonadReader ValidateEnv)

type Validator = ValidatorT TermBlock

type TermValidator = RuleTerm -> Validator ()

instance MonadCddl (ValidatorT b) where
  type Phase (ValidatorT b) = ValidatorPhase

  lookupCddl n = do
    CTreeRoot root <- asks veRoot
    pure $ Map.lookup n root

  lookupGRef (GRef t) = do
    binds <- asks veLocal
    pure $ Map.lookup (Name t) binds

instance MonadFail (ValidatorT b) where
  fail msg = failWith $ CustomFailure $ T.pack msg

instance Alternative (ValidatorT b) where
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

closeSteps :: [ValidationTrace b IsValid] -> StepTrace b v -> StepTrace b v
closeSteps steps cap = foldl' (flip Step) cap steps

pushStep :: ValidationTrace b IsValid -> ValidatorT b ()
pushStep step = Validator $ modify' (step :)

accept :: CTree ValidatorPhase -> Validator ()
accept = pushStep . TerminalRule . mapIndex

reject :: CTree ValidatorPhase -> Validator ()
reject = failWith . UnapplicableRule . mapIndex

failWith :: ValidationTrace b IsInvalid -> ValidatorT b a
failWith err = Validator $ throwError err

failWithSteps :: StepTrace b IsInvalid -> ValidatorT b a
failWithSteps = \case
  Step t rest -> pushStep t >> failWithSteps rest
  StepFailed e -> failWith e

withChoice :: Int -> Validator () -> Validator ()
withChoice i m =
  runBlock m >>= \case
    Right (_, trc) -> pushStep $ ChoiceBranch i trc
    Left trc -> failWithSteps trc

withTag :: Word64 -> Validator () -> Validator ()
withTag t = wrapBlock $ TagTrace t

withArray :: ValidatorT ListBlock () -> Validator ()
withArray = wrapBlock ArrayTrace

withMap :: ValidatorT MapBlock () -> Validator ()
withMap = wrapBlock MapTrace

element :: Validator () -> ValidatorT ListBlock ()
element m =
  runBlock m >>= \case
    Right (_, trc) -> pushStep $ ArrayElement trc
    Left trc -> failWith $ ArrayMissingRequired trc

entry :: Validator () -> Validator () -> ValidatorT MapBlock ()
entry mk mv =
  runBlock mk >>= \case
    Right (_, kTrc) ->
      runBlock mv >>= \case
        Right (_, vTrc) -> pushStep $ MapEntry kTrc vTrc
        Left trc -> failWith $ MapInvalidValue kTrc trc
    Left trc -> failWith $ MapInvalidKey trc

controlVerdict :: CtlOp -> CTree ValidatorPhase -> Bool -> Validator ()
controlVerdict op ctrl = \case
  True -> pushStep $ ControlTrace info SValid
  False -> failWith $ ControlTrace info SInvalid
  where
    info = ControlInfo op $ mapIndex ctrl

wrapBlock ::
  (forall v. StepTrace b' v -> ValidationTrace b v) ->
  ValidatorT b' a ->
  ValidatorT b a
wrapBlock r m =
  runBlock m >>= \case
    Right (x, steps) -> pushStep (r steps) >> pure x
    Left steps -> failWith $ r steps

runBlockWith ::
  ValidatorT b' a -> ValidateEnv -> Either (StepTrace b' IsInvalid) (a, StepTrace b' IsValid)
runBlockWith (Validator m) env = case runState (runExceptT $ runReaderT m env) [] of
  (Right x, trc) -> Right (x, closeSteps trc StepsDone)
  (Left err, trc) -> Left $ closeSteps trc $ StepFailed err

runBlock ::
  ValidatorT b' a ->
  ValidatorT b (Either (StepTrace b' IsInvalid) (a, StepTrace b' IsValid))
runBlock m = asks $ runBlockWith m

-- | Run an action with the given local generic bindings installed.
withLocalValidateBindings ::
  Map Name (CTree ValidatorPhase) -> Validator a -> Validator a
withLocalValidateBindings binds =
  local (\env -> env {veLocal = binds `Map.union` veLocal env})

runValidator :: ValidatorT b a -> ValidateEnv -> Evidenced (StepTrace b)
runValidator m env = mkStepTrace $ runBlockWith m env
  where
    mkStepTrace eFail =
      case eFail of
        Right (_, trc) -> evidence trc
        Left trc -> evidence trc

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

data StepTrace (b :: Block) (v :: Validity) where
  StepsDone :: StepTrace b IsValid
  Step :: ValidationTrace b IsValid -> StepTrace b v -> StepTrace b v
  StepFailed :: ValidationTrace b IsInvalid -> StepTrace b IsInvalid

toEvidencedList :: StepTrace b v -> [Evidenced (ValidationTrace b)]
toEvidencedList = \case
  StepsDone -> []
  StepFailed x -> [evidence x]
  Step x next -> evidence x : toEvidencedList next

stepsTakeValid :: StepTrace b v -> [ValidationTrace b IsValid]
stepsTakeValid = \case
  Step x next -> x : stepsTakeValid next
  _ -> []

stepFailure :: StepTrace b v -> Maybe (ValidationTrace b IsInvalid)
stepFailure = \case
  StepFailed x -> Just x
  StepsDone -> Nothing
  Step _ next -> stepFailure next

deriving instance Show (StepTrace b v)

instance IsValidationTrace (StepTrace b) where
  traceValidity = \case
    StepsDone -> SValid
    StepFailed _ -> SInvalid
    Step _ next -> traceValidity next
  measureProgress = \case
    StepsDone -> mempty
    StepFailed x -> measureProgress x
    Step this next -> measureProgress this <> measureProgress next

type data Block = TermBlock | ListBlock | MapBlock

data ValidationTrace (b :: Block) (v :: Validity) where
  AlternativeFail :: ValidationTrace b IsInvalid
  UnapplicableRule :: CTree MonoSimplePhase -> ValidationTrace TermBlock IsInvalid
  TerminalRule :: CTree MonoSimplePhase -> ValidationTrace TermBlock IsValid
  ControlTrace :: ControlInfo -> SValidity v -> ValidationTrace TermBlock v
  ReferenceRule :: Name -> StepTrace TermBlock v -> ValidationTrace TermBlock v
  CustomSuccess :: ValidationTrace TermBlock IsValid
  CustomFailure :: Text -> ValidationTrace b IsInvalid
  UnsatisfiedControl :: CtlOp -> CTree MonoSimplePhase -> ValidationTrace TermBlock IsInvalid
  ChoiceBranch :: Int -> StepTrace TermBlock IsValid -> ValidationTrace TermBlock IsValid
  TagTrace :: Word64 -> StepTrace TermBlock v -> ValidationTrace TermBlock v
  InvalidTag :: Word64 -> Word64 -> ValidationTrace TermBlock IsInvalid
  ArrayTrace :: StepTrace ListBlock v -> ValidationTrace TermBlock v
  ArrayElement ::
    StepTrace TermBlock IsValid ->
    ValidationTrace ListBlock IsValid
  ArrayLeftoverTerms ::
    NonEmpty Term ->
    Maybe (CTree MonoSimplePhase, StepTrace TermBlock IsInvalid) ->
    ValidationTrace ListBlock IsInvalid
  ArrayLeftoverRule ::
    CTree MonoSimplePhase ->
    ValidationTrace ListBlock IsInvalid
  ArrayMissingRequired ::
    StepTrace TermBlock IsInvalid ->
    ValidationTrace ListBlock IsInvalid
  ArrayConsumeGroup ::
    [Name] ->
    StepTrace ListBlock v ->
    ValidationTrace ListBlock v
  MapTrace :: StepTrace MapBlock v -> ValidationTrace TermBlock v
  MapEntry ::
    StepTrace TermBlock IsValid ->
    StepTrace TermBlock IsValid ->
    ValidationTrace MapBlock IsValid
  MapInvalidKey ::
    StepTrace TermBlock IsInvalid ->
    ValidationTrace MapBlock IsInvalid
  MapInvalidValue ::
    StepTrace TermBlock IsValid ->
    StepTrace TermBlock IsInvalid ->
    ValidationTrace MapBlock IsInvalid
  MapDuplicateKeys ::
    CanonicalTerm ->
    ValidationTrace MapBlock IsInvalid
  MapUnappliedRules :: NonEmpty (CTree MonoSimplePhase) -> ValidationTrace MapBlock IsInvalid
  MapLeftoverEntries ::
    NonEmpty (Term, Term) ->
    Maybe (CTree MonoSimplePhase, StepTrace MapBlock IsInvalid) ->
    ValidationTrace MapBlock IsInvalid

deriving instance Show (ValidationTrace b v)

instance IsValidationTrace (ValidationTrace b) where
  traceValidity = \case
    TerminalRule {} -> SValid
    ControlTrace _ v -> v
    AlternativeFail -> SInvalid
    UnapplicableRule {} -> SInvalid
    ReferenceRule _ x -> traceValidity x
    CustomSuccess -> SValid
    CustomFailure {} -> SInvalid
    UnsatisfiedControl {} -> SInvalid
    ChoiceBranch {} -> SValid
    TagTrace _ x -> traceValidity x
    InvalidTag {} -> SInvalid
    ArrayTrace x -> traceValidity x
    ArrayElement {} -> SValid
    ArrayLeftoverTerms {} -> SInvalid
    ArrayLeftoverRule {} -> SInvalid
    ArrayMissingRequired {} -> SInvalid
    ArrayConsumeGroup _ x -> traceValidity x
    MapTrace x -> traceValidity x
    MapEntry {} -> SValid
    MapInvalidKey {} -> SInvalid
    MapInvalidValue {} -> SInvalid
    MapDuplicateKeys {} -> SInvalid
    MapUnappliedRules {} -> SInvalid
    MapLeftoverEntries {} -> SInvalid

  measureProgress = \case
    TerminalRule {} -> Progress 1 0
    ControlTrace _ SValid -> Progress 0 1
    ControlTrace _ SInvalid -> mempty
    AlternativeFail -> mempty
    UnapplicableRule {} -> mempty
    ReferenceRule _ x -> increaseRefProgress $ measureProgress x
    CustomSuccess -> Progress 1 0
    CustomFailure {} -> mempty
    UnsatisfiedControl {} -> mempty
    ChoiceBranch _ x -> measureProgress x
    TagTrace _ x -> increaseTermProgress $ measureProgress x
    InvalidTag {} -> mempty
    ArrayTrace x -> increaseTermProgress $ measureProgress x
    ArrayElement {} -> Progress 1 0
    ArrayLeftoverTerms _ Nothing -> mempty
    ArrayLeftoverTerms _ (Just (_, x)) -> measureProgress x
    ArrayLeftoverRule {} -> mempty
    ArrayMissingRequired {} -> mempty
    ArrayConsumeGroup ns x -> Progress 0 (length ns) <> measureProgress x
    MapTrace x -> increaseTermProgress $ measureProgress x
    MapEntry k v -> measureProgress k <> measureProgress v
    MapInvalidKey k -> measureProgress k
    MapInvalidValue k v -> measureProgress k <> measureProgress v
    MapDuplicateKeys x -> measureProgress x
    MapUnappliedRules {} -> mempty
    MapLeftoverEntries _ Nothing -> mempty
    MapLeftoverEntries _ (Just (_, x)) -> measureProgress x

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

prettyStepTrace :: Bool -> TraceOptions -> StepTrace b v -> Doc AnsiStyle
prettyStepTrace mayFold opts@TraceOptions {..} steps
  | toFoldValid && mayFold =
      vsep $
        [ annotate italicized $ "... " <> pretty (length validInit) <> " valid entries not shown"
        | not $ null validInit
        ]
          <> [ prettyValidationTrace opts f
             | f <- maybeToList $ stepFailure steps
             ]
  | otherwise =
      vsep $ foldEvidenced (prettyValidationTrace opts) <$> toEvidencedList steps
  where
    validInit = stepsTakeValid steps

prettyValidationTrace :: TraceOptions -> ValidationTrace b v -> Doc AnsiStyle
prettyValidationTrace opts = \case
  TerminalRule x -> "app: " <> annotate (color Green) (pretty x)
  AlternativeFail -> mempty
  UnapplicableRule x -> annotate (color Red) $ vsep ["failed to apply: ", indent 2 $ pretty x]
  ControlTrace ci v ->
    let col = case v of
          SValid -> Green
          SInvalid -> Red
     in vsep
          [ "ctrl:" <+> annotate (color col) ("." <> pretty ci) <+> case v of
              SValid -> mempty
              SInvalid -> "(failed)"
          ]
  ChoiceBranch i c ->
    vsep
      [ "choice (idx: " <> pretty i <> ")"
      , nestContainer $ prettyStepTrace False opts c
      ]
  ReferenceRule (Name n) x ->
    vsep
      [ "ref: " <> annotate (color Blue) (pretty n)
      , nestContainer $ prettyStepTrace False opts x
      ]
  CustomSuccess -> "<custom validator>"
  CustomFailure e -> annotate (color Red) $ pretty e
  UnsatisfiedControl op ctl ->
    annotate (color Red) $
      vsep
        [ "unsatisfied control:"
        , indent 2 $ "." <> pretty op <+> pretty ctl
        ]
  ArrayTrace l ->
    vsep
      [ "array"
      , nestContainer $ prettyStepTrace False opts l
      ]
  MapTrace m ->
    vsep
      [ "map"
      , nestContainer $ prettyStepTrace False opts m
      ]
  TagTrace t x ->
    vsep
      [ "tag:" <+> annotate (color Green) ("#6." <> pretty t)
      , nestContainer $ prettyStepTrace False opts x
      ]
  InvalidTag expected actual ->
    "expected tag #6." <> pretty expected <> ", got #6." <> pretty actual
  ArrayLeftoverTerms _ Nothing ->
    annotate (color Red) "leftover elements not matched by any rule"
  ArrayLeftoverTerms _ (Just (rule, trc)) ->
    hang 2 $
      vsep
        [ annotate (color Red) "leftover elements, closest matching rule:"
        , annotate (color Green) $ pretty $ show rule
        , nestContainer $ prettyStepTrace True opts trc
        ]
  ArrayLeftoverRule r ->
    hang 2 $
      vsep
        [ annotate (color Red) "required rule not satisfied:"
        , pretty r
        ]
  ArrayElement steps -> vsep [prettyStepTrace True opts steps]
  ArrayMissingRequired t ->
    vsep
      [ annotate (color Red) "failed to apply required rule:"
      , nestContainer $ prettyStepTrace True opts t
      ]
  ArrayConsumeGroup refs x -> vsep $ prettyGroup refs x
  MapLeftoverEntries _ Nothing ->
    annotate (color Red) "leftover key-value pairs not matched by any rule"
  MapLeftoverEntries _ (Just (rule, trc)) ->
    hang 2 $
      vsep
        [ annotate (color Red) "leftover key-value pairs, closest matching rule:"
        , annotate (color Green) $ pretty rule
        , nestContainer $ prettyStepTrace True opts trc
        ]
  MapUnappliedRules rs ->
    hang 2 $
      vsep
        [ annotate (color Red) "not all required rules have been applied:"
        , vsep (NE.toList $ pretty <$> rs)
        ]
  MapEntry k v ->
    vsep
      [ "key:"
      , nestContainer $ prettyStepTrace True opts k
      , "value:"
      , nestContainer $ prettyStepTrace True opts v
      ]
  MapInvalidKey k ->
    vsep
      [ "key:" <+> annotate (color Red) "(fail)"
      , nestContainer $ prettyStepTrace False opts k
      ]
  MapInvalidValue k v ->
    vsep
      [ "key:"
      , nestContainer $ prettyStepTrace False opts k
      , "value:" <+> annotate (color Red) "(fail)"
      , nestContainer $ prettyStepTrace False opts v
      ]
  MapDuplicateKeys _ ->
    vsep
      [ "key: " <> annotate (color Red) "(duplicate)"
      ]
  where
    prettyGroup :: [Name] -> StepTrace ListBlock v -> [Doc AnsiStyle]
    prettyGroup refs x = go refs
      where
        go (n : ns) =
          [ "ref" <+> pretty n
          , nestContainer . vsep $ go ns
          ]
        go [] =
          [ case traceValidity x of
              SValid -> "grp"
              SInvalid -> "grp" <+> annotate (color Red) "(fail)"
          , nestContainer $ prettyStepTrace True opts x
          ]

showValidationTrace :: ValidationTrace b v -> String
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

instance IndexMappable CTreeRoot ValidatorPhase MonoSimplePhase where
  mapIndex (CTreeRoot m) = CTreeRoot $ mapIndex <$> m
