{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}

module GHC.Types.Error
   ( -- * Messages
     Messages
   , WarningMessages
   , ErrorMessages
   , mkMessages
   , emptyMessages
   , isEmptyMessages
   , addMessage
   , unionMessages
   , MsgEnvelope (..)
   , WarnMsg

   -- * Classifying Messages

   , MessageClass (..)
   , Severity (..)
   , Diagnostic (..)
   , DiagnosticMessage (..)
   , DiagnosticReason (..)
   , DeferStatus (..)

    -- * Rendering Messages

   , SDoc
   , DecoratedSDoc (unDecorated)
   , pprMessageBag
   , mkDecorated
   , mkLocMessage
   , mkLocMessageAnn
   , getCaretDiagnostic
   -- * Queries
   , isErrorMessage
   , isWarningMessage
   , getErrorMessages
   , getWarningMessages
   , partitionMessages
   , errorsFound
   )
where

import GHC.Prelude

import GHC.Driver.Flags

import GHC.Data.Bag
import GHC.Utils.Outputable as Outputable
import qualified GHC.Utils.Ppr.Colour as Col
import GHC.Types.SrcLoc as SrcLoc
import GHC.Data.FastString (unpackFS)
import GHC.Data.StringBuffer (atLine, hGetStringBuffer, len, lexemeToString)
import GHC.Utils.Json

import System.IO.Error  ( catchIOError )

{-
Note [Messages]
~~~~~~~~~~~~~~~

We represent the 'Messages' as a single bag of warnings and errors.

The reason behind that is that there is a fluid relationship between errors and warnings and we want to
be able to promote or demote errors and warnings based on certain flags (e.g. -Werror, -fdefer-type-errors
or -XPartialTypeSignatures). More specifically, every diagnostic has a 'DiagnosticReason', but a warning
'DiagnosticReason' might be associated with 'SevError', in the case of -Werror.

We rely on the 'Severity' to distinguish between a warning and an error.

'WarningMessages' and 'ErrorMessages' are for now simple type aliases to retain backward compatibility, but
in future iterations these can be either parameterised over an 'e' message type (to make type signatures
a bit more declarative) or removed altogether.
-}

-- | A collection of messages emitted by GHC during error reporting. A diagnostic message is typically
-- a warning or an error. See Note [Messages].
newtype Messages e = Messages (Bag (MsgEnvelope e))

instance Functor Messages where
  fmap f (Messages xs) = Messages (mapBag (fmap f) xs)

emptyMessages :: Messages e
emptyMessages = Messages emptyBag

mkMessages :: Bag (MsgEnvelope e) -> Messages e
mkMessages = Messages

isEmptyMessages :: Messages e -> Bool
isEmptyMessages (Messages msgs) = isEmptyBag msgs

addMessage :: MsgEnvelope e -> Messages e -> Messages e
addMessage x (Messages xs) = Messages (x `consBag` xs)

-- | Joins two collections of messages together.
unionMessages :: Messages e -> Messages e -> Messages e
unionMessages (Messages msgs1) (Messages msgs2) = Messages (msgs1 `unionBags` msgs2)

type WarningMessages = Bag (MsgEnvelope DiagnosticMessage)
type ErrorMessages   = Bag (MsgEnvelope DiagnosticMessage)

type WarnMsg         = MsgEnvelope DiagnosticMessage

-- | A 'DecoratedSDoc' is isomorphic to a '[SDoc]' but it carries the invariant that the input '[SDoc]'
-- needs to be rendered /decorated/ into its final form, where the typical case would be adding bullets
-- between each elements of the list.
-- The type of decoration depends on the formatting function used, but in practice GHC uses the
-- 'formatBulleted'.
newtype DecoratedSDoc = Decorated { unDecorated :: [SDoc] }

-- | Creates a new 'DecoratedSDoc' out of a list of 'SDoc'.
mkDecorated :: [SDoc] -> DecoratedSDoc
mkDecorated = Decorated

{-
Note [Rendering Messages]
~~~~~~~~~~~~~~~~~~~~~~~~~

Turning 'Messages' into something that renders nicely for the user is one of the last steps, and it
happens typically at the application's boundaries (i.e. from the 'Driver' upwards).

For now (see #18516) this class has few instance, but the idea is that as
the more domain-specific types are defined, the more instances we would get. For example, given something like:

  data TcRnDiagnostic
    = TcRnOutOfScope ..
    | ..

  newtype TcRnMessage = TcRnMessage (DiagnosticMessage TcRnDiagnostic)

We could then define how a 'TcRnDiagnostic' is displayed to the user. Rather than scattering pieces of
'SDoc' around the codebase, we would write once for all:

  instance Diagnostic TcRnDiagnostic where
    diagnosticMessage (TcRnMessage msg) = case diagMessage msg of
      TcRnOutOfScope .. -> Decorated [text "Out of scope error ..."]
      ...

This way, we can easily write generic rendering functions for errors that all they care about is the
knowledge that a given type 'e' has a 'Diagnostic' constraint.

-}

-- | A class identifying a diagnostic.
-- Dictionary.com defines a diagnostic as:
--
-- \"a message output by a computer diagnosing an error in a computer program, computer system,
-- or component device\".
--
-- A 'Diagnostic' carries the /actual/ description of the message (which, in GHC's case, it can be
-- an error or a warning) and the /reason/ why such message was generated in the first place.
-- See also Note [Rendering Messages].
class Diagnostic a where
  diagnosticMessage :: a -> DecoratedSDoc
  diagnosticReason  :: a -> DiagnosticReason

-- | A generic 'Diagnostic' message, without any further classification or provenance:
-- By looking at a 'DiagnosticMessage' we don't know neither /where/ it was generated nor how to
-- intepret its payload (as it's just a structured document). All we can do is to print it out and
-- look at its 'DiagnosticReason'.
data DiagnosticMessage = DiagnosticMessage
  { diagMessage :: !DecoratedSDoc
  , diagReason  :: !DiagnosticReason
  }

instance Diagnostic DiagnosticMessage where
  diagnosticMessage = diagMessage
  diagnosticReason  = diagReason

-- | The reason /why/ a 'Diagnostic' was emitted in the first place. Diagnostic messages
-- are born within GHC with a very precise reason, which can be completely statically-computed
-- (i.e. this is an error or a warning no matter what), or influenced by the specific state
-- of the 'DynFlags' at the moment of the creation of a new 'Diagnostic'. For example, a parsing
-- error is /always/ going to be an error, whereas a 'WarningWithoutFlag Opt_WarnUnusedImports' might turn
-- into an error due to '-Werror' or '-Werror=warn-unused-imports'. Interpreting a 'DiagnosticReason'
-- together with its associated 'Severity' gives us the full picture.
data DiagnosticReason
  = WarningWithoutFlag
  -- ^ Born as a warning.
  | WarningWithFlag !WarningFlag
  -- ^ Warning was enabled with the flag.
  | ErrorWithoutFlag
  -- ^ Born as an error.
  deriving (Eq, Show)

data DeferStatus
  = ReportError
  | DeferError
  deriving (Eq, Show)

instance Outputable DeferStatus where
  ppr = \case
    ReportError -> text "ReportError"
    DeferError  -> text "DeferError"

instance Outputable DiagnosticReason where
  ppr = \case
    WarningWithoutFlag  -> text "WarningWithoutFlag"
    WarningWithFlag wf  -> text ("WarningWithFlag " ++ show wf)
    ErrorWithoutFlag    -> text "ErrorWithoutFlag"

-- | An envelope for GHC's facts about a running program, parameterised over the
-- /domain-specific/ (i.e. parsing, typecheck-renaming, etc) diagnostics.
--
-- To say things differently, GHC emits /diagnostics/ about the running program, each of which is wrapped
-- into a 'MsgEnvelope' that carries specific information like where the error happened, etc.
-- Finally, multiple 'MsgEnvelope's are aggregated into 'Messages' that are returned to the user.
data MsgEnvelope e = MsgEnvelope
   { errMsgSpan        :: SrcSpan
      -- ^ The SrcSpan is used for sorting errors into line-number order
   , errMsgContext     :: PrintUnqualified
   , errMsgDiagnostic  :: e
   , errMsgSeverity    :: Severity
   } deriving Functor

-- | The class for a diagnostic message. The main purpose is to classify a message within GHC,
-- to distinguish it from a debug/dump message vs a proper diagnostic, for which we include a 'DiagnosticReason'.
data MessageClass
  = MCOutput
  | MCFatal
  | MCInteractive

  | MCDump
    -- ^ Log message intended for compiler developers
    -- No file\/line\/column stuff

  | MCInfo
    -- ^ Log messages intended for end users.
    -- No file\/line\/column stuff.

  | MCDiagnostic Severity DiagnosticReason
    -- ^ Diagnostics from the compiler. This constructor
    -- is very powerful as it allows the construction
    -- of a 'MessageClass' with a completely arbitrary
    -- permutation of 'Severity' and 'DiagnosticReason'. As such,
    -- users are encouraged to use the 'mkMCDiagnostic' smart constructor instead.
    -- Use this constructor directly only if you need to construct and manipulate diagnostic
    -- messages directly, for example inside 'GHC.Utils.Error'. In all the other circumstances,
    -- /especially/ when emitting compiler diagnostics, use the smart constructor.
  deriving (Eq, Show)


-- | Used to describe warnings and errors
--   o The message has a file\/line\/column heading,
--     plus "warning:" or "error:",
--     added by mkLocMessage
--   o Output is intended for end users
data Severity
  = SevWarning
  | SevError
  deriving (Eq, Show)

instance Outputable Severity where
  ppr = \case
    SevWarning -> text "SevWarning"
    SevError   -> text "SevError"

instance ToJson Severity where
  json s = JSString (show s)

instance ToJson MessageClass where
  json MCOutput = JSString "MCOutput"
  json MCFatal  = JSString "MCFatal"
  json MCInteractive = JSString "MCInteractive"
  json MCDump = JSString "MCDump"
  json MCInfo = JSString "MCInfo"
  json (MCDiagnostic sev reason) =
    JSString $ renderWithContext defaultSDocContext (ppr $ text "MCDiagnostic" <+> ppr sev <+> ppr reason)

instance Show (MsgEnvelope DiagnosticMessage) where
    show = showMsgEnvelope

-- | Shows an 'MsgEnvelope'.
showMsgEnvelope :: Diagnostic a => MsgEnvelope a -> String
showMsgEnvelope err =
  renderWithContext defaultSDocContext (vcat (unDecorated . diagnosticMessage $ errMsgDiagnostic err))

pprMessageBag :: Bag SDoc -> SDoc
pprMessageBag msgs = vcat (punctuate blankLine (bagToList msgs))

-- | Make an unannotated error message with location info.
mkLocMessage :: MessageClass -> SrcSpan -> SDoc -> SDoc
mkLocMessage = mkLocMessageAnn Nothing

-- | Make a possibly annotated error message with location info.
mkLocMessageAnn
  :: Maybe String                       -- ^ optional annotation
  -> MessageClass                       -- ^ What kind of message?
  -> SrcSpan                            -- ^ location
  -> SDoc                               -- ^ message
  -> SDoc
  -- Always print the location, even if it is unhelpful.  Error messages
  -- are supposed to be in a standard format, and one without a location
  -- would look strange.  Better to say explicitly "<no location info>".
mkLocMessageAnn ann msg_class locn msg
    = sdocOption sdocColScheme $ \col_scheme ->
      let locn' = sdocOption sdocErrorSpans $ \case
                     True  -> ppr locn
                     False -> ppr (srcSpanStart locn)

          msgColour = getMessageClassColour msg_class col_scheme

          -- Add optional information
          optAnn = case ann of
            Nothing -> text ""
            Just i  -> text " [" <> coloured msgColour (text i) <> text "]"

          -- Add prefixes, like    Foo.hs:34: warning:
          --                           <the warning message>
          header = locn' <> colon <+>
                   coloured msgColour msgText <> optAnn

      in coloured (Col.sMessage col_scheme)
                  (hang (coloured (Col.sHeader col_scheme) header) 4
                        msg)

  where
    msgText =
      case msg_class of
        MCDiagnostic SevError _reason   -> text "error:"
        MCDiagnostic SevWarning _reason -> text "warning:"
        MCFatal                         -> text "fatal:"
        _                               -> empty

getMessageClassColour :: MessageClass -> Col.Scheme -> Col.PprColour
getMessageClassColour (MCDiagnostic SevError _reason)   = Col.sError
getMessageClassColour (MCDiagnostic SevWarning _reason) = Col.sWarning
getMessageClassColour MCFatal                           = Col.sFatal
getMessageClassColour _                                 = const mempty

getCaretDiagnostic :: MessageClass -> SrcSpan -> IO SDoc
getCaretDiagnostic _ (UnhelpfulSpan _) = pure empty
getCaretDiagnostic msg_class (RealSrcSpan span _) =
  caretDiagnostic <$> getSrcLine (srcSpanFile span) row
  where
    getSrcLine fn i =
      getLine i (unpackFS fn)
        `catchIOError` \_ ->
          pure Nothing

    getLine i fn = do
      -- StringBuffer has advantages over readFile:
      -- (a) no lazy IO, otherwise IO exceptions may occur in pure code
      -- (b) always UTF-8, rather than some system-dependent encoding
      --     (Haskell source code must be UTF-8 anyway)
      content <- hGetStringBuffer fn
      case atLine i content of
        Just at_line -> pure $
          case lines (fix <$> lexemeToString at_line (len at_line)) of
            srcLine : _ -> Just srcLine
            _           -> Nothing
        _ -> pure Nothing

    -- allow user to visibly see that their code is incorrectly encoded
    -- (StringBuffer.nextChar uses \0 to represent undecodable characters)
    fix '\0' = '\xfffd'
    fix c    = c

    row = srcSpanStartLine span
    rowStr = show row
    multiline = row /= srcSpanEndLine span

    caretDiagnostic Nothing = empty
    caretDiagnostic (Just srcLineWithNewline) =
      sdocOption sdocColScheme$ \col_scheme ->
      let sevColour = getMessageClassColour msg_class col_scheme
          marginColour = Col.sMargin col_scheme
      in
      coloured marginColour (text marginSpace) <>
      text ("\n") <>
      coloured marginColour (text marginRow) <>
      text (" " ++ srcLinePre) <>
      coloured sevColour (text srcLineSpan) <>
      text (srcLinePost ++ "\n") <>
      coloured marginColour (text marginSpace) <>
      coloured sevColour (text (" " ++ caretLine))

      where

        -- expand tabs in a device-independent manner #13664
        expandTabs tabWidth i s =
          case s of
            ""        -> ""
            '\t' : cs -> replicate effectiveWidth ' ' ++
                         expandTabs tabWidth (i + effectiveWidth) cs
            c    : cs -> c : expandTabs tabWidth (i + 1) cs
          where effectiveWidth = tabWidth - i `mod` tabWidth

        srcLine = filter (/= '\n') (expandTabs 8 0 srcLineWithNewline)

        start = srcSpanStartCol span - 1
        end | multiline = length srcLine
            | otherwise = srcSpanEndCol span - 1
        width = max 1 (end - start)

        marginWidth = length rowStr
        marginSpace = replicate marginWidth ' ' ++ " |"
        marginRow   = rowStr ++ " |"

        (srcLinePre,  srcLineRest) = splitAt start srcLine
        (srcLineSpan, srcLinePost) = splitAt width srcLineRest

        caretEllipsis | multiline = "..."
                      | otherwise = ""
        caretLine = replicate start ' ' ++ replicate width '^' ++ caretEllipsis

--
-- Queries
--

isErrorMessage :: Diagnostic e => MsgEnvelope e -> Bool
isErrorMessage = (==) ErrorWithoutFlag . diagnosticReason . errMsgDiagnostic

isWarningMessage :: Diagnostic e => MsgEnvelope e -> Bool
isWarningMessage = not . isErrorMessage

errorsFound :: Diagnostic e => Messages e -> Bool
errorsFound (Messages msgs) = any isErrorMessage msgs

getWarningMessages :: Diagnostic e => Messages e -> Bag (MsgEnvelope e)
getWarningMessages (Messages xs) = fst $ partitionBag isWarningMessage xs

getErrorMessages :: Diagnostic e => Messages e -> Bag (MsgEnvelope e)
getErrorMessages (Messages xs) = fst $ partitionBag isErrorMessage xs

-- | Partitions the 'Messages' and returns a tuple which first element are the warnings, and the
-- second the errors.
partitionMessages :: Diagnostic e => Messages e -> (Bag (MsgEnvelope e), Bag (MsgEnvelope e))
partitionMessages (Messages xs) = partitionBag isWarningMessage xs
