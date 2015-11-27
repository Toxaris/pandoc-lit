-- Copyright (c) 2010-13 Tillmann Rendel <rendel@informatik.uni-marburg.de>
-- This code can be used under the terms of a 3-clause BSD license.
-- See LICENSE for details.

{-# LANGUAGE PatternGuards, NamedFieldPuns #-}
{-# LANGUAGE RecordWildCards #-}
module Text.Pandoc.Lit(main) where

import Text.Pandoc
import Text.Pandoc.Error
import Text.CSL.Pandoc
import Text.CSL hiding (abstract, bibliography, references, processBibliography)

import Control.Monad (liftM, ap)

import qualified Data.Set as Set
import System.IO.Error

import System.Environment (getArgs)
import System.Console.GetOpt
import System.Exit (exitFailure, exitSuccess)
import System.IO (stdout, stderr, hPutStrLn, openFile, IOMode(ReadMode), hSetEncoding, utf8, hSetNewlineMode, universalNewlineMode, hGetContents)
import System.Directory (doesFileExist, getAppUserDataDirectory)
import System.FilePath ((</>), (<.>))
import System.Process (readProcess)

import Data.List (intersperse, stripPrefix)
import Data.Maybe (fromMaybe)
import Data.Char (isSpace)

import Text.RegexPR

import Text.Pandoc.Scripting.Structure (Structure (Block, Section),  onStructure)

import Paths_pandoc_lit (getDataFileName)

-- transformation

transformAbstract :: String -> Structure -> [Structure]
transformAbstract abstract (Section _ header contents)
  |   isText abstract header
  =   [Block $ RawBlock (Format "latex") "\\begin{abstract}"]
  ++  contents
  ++  [Block $ RawBlock (Format "latex") "\\end{abstract}"]
transformAbstract _ content
  = [content]

transformToc :: String -> Structure -> Structure
transformToc toc (Section _ header _)
  |   isText toc header
  =   Block $ RawBlock (Format "tex") "\\clearpage\\tableofcontents\\clearpage"
transformToc _ content
  =   content

transformBeamer :: Config -> Structure -> [Structure]
transformBeamer config (Section _ header contents)
  |   Just tp <- configTitlePage config
  ,   isText tp header
  =   [Block $ RawBlock (Format "tex") "\\begin{frame}\n\\titlepage"]
  ++  transformFrameBlocks config 1 contents
  ++  [Block $ RawBlock (Format "tex") "\\end{frame}"]

transformBeamer config (Section 2 header contents)
  |   Block HorizontalRule `elem` contents
  =   [Block $ Plain
      $   [RawInline (Format "tex") "\\begin{frame}{"]
      ++  header
      ++ [RawInline (Format "tex") "}"]]
  ++  [Block $ RawBlock (Format "tex") $ "\\begin{columns}[T]"]
  ++  [Block $ RawBlock (Format "tex") $ "\\begin{column}{0.45\\textwidth}"]
  ++  transformFrameBlocks config 1 leftStructures
  ++  [Block $ RawBlock (Format "tex") $ "\\end{column}"]
  ++  [Block $ RawBlock (Format "tex") $ "\\begin{column}{0.45\\textwidth}"]
  ++  transformFrameBlocks config 1 rightStructures
  ++  [Block $ RawBlock (Format "tex") $ "\\end{column}"]
  ++  [Block $ RawBlock (Format "tex") $ "\\end{columns}"]
  ++  [Block $ RawBlock (Format "tex") $ "\\end{frame}"] where
    leftStructures   =  takeWhile (/= Block HorizontalRule) contents
    rightStructures  =  drop 1 $ dropWhile (/= Block HorizontalRule) contents

transformBeamer config (Section 2 header contents)
  =   [Block $ Plain
      $   [RawInline (Format "tex") "\\begin{frame}{"]
      ++  header
      ++  [RawInline (Format "tex") "}"]]
  ++  transformFrameBlocks config 1 contents
  ++  [Block $ RawBlock (Format "tex") $ "\\end{frame}"]

transformBeamer _ content
  = [content]

transformFrameBlocks :: Config -> Int -> [Structure] -> [Structure]
transformFrameBlocks config i (Block HorizontalRule : rest)
  | configPause config
  =   [Block $ RawBlock (Format "tex") $ "\\pause"]
  ++  transformFrameBlocks config (succ i) rest

transformFrameBlocks config i (Block (BlockQuote blocks) : rest)
  | configNotes config
  =   [Block $ RawBlock (Format "tex") $ "\\note<alert@@" ++ show i ++ ">{"]
  ++  map Block blocks
  ++  [Block $ RawBlock (Format "tex") $ "}"]
  ++  transformFrameBlocks config i rest

transformFrameBlocks config i (content : rest)
  =   [content]
  ++  transformFrameBlocks config i rest

transformFrameBlocks _ _ []
  =   []

transformBlock :: Config -> Block -> Block
transformBlock config (CodeBlock (_identifier, classes, _attributes) code)
  |   "literate" `elem` classes
  =   RawBlock (Format "latex") $ "\\begin{code}\n" ++ escapeCodeBlock config code ++ "\n\\end{code}"
  |   otherwise
  =   RawBlock (Format "latex") $ "\\begin{spec}\n" ++ escapeCodeBlock config code ++ "\n\\end{spec}"
transformBlock _ (RawBlock (Format "tex") text)
  =   RawBlock (Format "tex") (unescapeComments $ text)
transformBlock _ (RawBlock (Format "latex") text)
  =   RawBlock (Format "latex") (unescapeComments $ text)
transformBlock _ x
  =   x

escapeCodeBlock :: Config -> String -> String
escapeCodeBlock config
  | configTh config = escapeInComments . escapeTH
  | otherwise = escapeInComments

transformInline :: Config -> Inline -> Inline
transformInline _config (Str text) = Str (escapeBar text)
transformInline config (Code _attr code)
  |  configHyperref config
  =  RawInline (Format "tex") ("\\texorpdfstring{|" ++ escapeCodeInline config code ++ "|}{" ++ escapeCodePDF code ++ "}")
  |  otherwise
  =  RawInline (Format "tex") ("|" ++ escapeCodeInline config code ++ "|")
transformInline _config (Math t m) = Math t (escapeBar m)
transformInline _config (RawInline (Format "tex") text) = RawInline (Format "tex") $ unescapeComments $ text
transformInline _config (RawInline (Format "latex") text) = RawInline (Format "latex") $ unescapeComments $ text
transformInline _config (RawInline (Format format) text) = error $ "raw " ++ format ++ " not supported by pandoc-lit (" ++ text ++ ")"
transformInline _config (Link text (s1, s2)) = Link text (escapeBar s1, escapeBar s2)
transformInline _config x = x

transformFloats :: [Block] -> [Block]
transformFloats = begin where
  begin (Para [RawInline (Format "tex") "\\figure ", Str tag] : rest)
    =  Plain [RawInline (Format "tex") "\\begin{figure}"]
    :  Plain [RawInline (Format "tex") "\\begin{minipage}{\\linewidth}"]
    :  Plain [RawInline (Format "tex") "\\renewcommand{\\footnoterule}{}"]
    :  caption "figure" tag rest
  begin (Para [RawInline (Format "tex") "\\figure*", Space, Str tag] : rest)
    =  Plain [RawInline (Format "tex") "\\begin{figure*}"]
    :  Plain [RawInline (Format "tex") "\\begin{minipage}{\\linewidth}"]
    :  Plain [RawInline (Format "tex") "\\renewcommand{\\footnoterule}{}"]
    :  caption "figure*" tag rest
  begin (block : rest)
    =  block : begin rest
  begin []
    =  []

  caption env tag (Para (RawInline (Format "tex") "\\caption " : text) : rest)
    =  Plain  [RawInline (Format "tex") $ "\\end{minipage}"]
    :  Plain  (concat
                [  [RawInline (Format "tex") $ "\\caption{"]
                ,  text
                ,  [RawInline (Format "tex") $ "}"]])
    :  Plain  [RawInline (Format "tex") $ "\\label{" ++ tag ++ "}"]
    :  Plain  [RawInline (Format "tex") $ "\\end{" ++ env ++ "}"]
    :  begin rest

  caption env tag (block : rest)
    =  block : caption env tag rest

  caption env tag []
    =  error ("Missing \\caption for \\" ++ env ++ " " ++ tag)

escapeCodePDF :: String -> String
escapeCodePDF
   = escapeBar . escapePDF

escapePDF :: String -> String
escapePDF ('_' : rest) = '\\' : '_' : escapePDF rest
escapePDF ('$' : rest) = '\\' : '$' : escapePDF rest
escapePDF (c : rest) = c : escapePDF rest
escapePDF [] = []

escapeCodeInline :: Config -> String -> String
escapeCodeInline config
  | configTh config = escapeBar . escapeTH
  | otherwise = escapeBar

escapeInComments :: String -> String
escapeInComments = code where
  code [] = []
  code ('-' : '-' : text)          =  '-' : '-' : lineComment text
  code ('{' : '-' : '"' : text)    =  '{' : '-' : '"' : texEscape text
  code ('{' : '-' : text)          =  '{' : '-' : rangeComment text
  code (c : text)                  =  c : code text

  lineComment []                   =  []
  lineComment ('\n' : text)        =  '\n' : code text
  lineComment ('|' : text)         =  '|' : '|' : lineComment text
  lineComment ('$' : text)         =  '\\' : '$' : lineComment text
  lineComment ('<' : text)         =  '$' : '<' : '$' : lineComment text
  lineComment ('>' : text)         =  '$' : '>' : '$' : lineComment text
  lineComment ('\\' : text)        =  "\\textbackslash" ++ lineComment text
  lineComment ('{' : text)         =  '\\' : '{' : lineComment text
  lineComment ('}' : text)         =  '\\' : '}' : lineComment text
  lineComment (c : text)           =  c : lineComment text

  rangeComment []                  =  []
  rangeComment ('|' : text)        =  '|' : '|' : rangeComment text
  rangeComment ('$' : text)        =  '\\' : '$' : rangeComment text
  rangeComment ('<' : text)        =  '$' : '<' : '$' : rangeComment text
  rangeComment ('>' : text)        =  '$' : '>' : '$' : rangeComment text
  rangeComment ('\\' : text)       =  "\\textbackslash " ++ rangeComment text
  rangeComment ('{' : text)        =  '\\' : '{' : rangeComment text
  rangeComment ('}' : text)        =  '\\' : '}' : rangeComment text
  rangeComment ('-' : '}' : text)  =  '-' : '}' : code text
  rangeComment (c : text)          =  c : rangeComment text

  texEscape []                     =  []
  texEscape ('"' : '-' : '}' : text) = '"' : '-' : '}' : code text
  texEscape (c : text ) = c : texEscape text

escapeBarBOL :: String -> String
escapeBarBOL = latexBOL where
  latexBOL []                      =  []
  latexBOL ('|' : text)            =  '|' : '|' : escapeBar text
  latexBOL ('\n' : text)           =  '\n' : latexBOL text
  latexBOL ('>' : text)            =  '>' : escapeCode text
  latexBOL ('<' : text)            =  '<' : escapeCode text
  latexBOL (c : text)              =  c : escapeBar text

escapeBar :: String -> String
escapeBar = latex where
  latex []                         =  []
  latex ('|' : text)               =  '|' : '|' : escapeBar text
  latex ('\n' : text)              =  '\n' : escapeBarBOL text
  latex (c : text)                 =  c : escapeBar text

escapeCode :: String -> String
escapeCode = code where
  code []                          =  []
  code ('\n' : text)               =  '\n' : escapeBarBOL text
  code (c : text)                  =  c : code text

escapeTH :: String -> String
escapeTH
  = gsubRegexPR "\\$\\((.*)\\)" "(SPLICE(\\1))"
  . gsubRegexPR "\\$([a-z][A-Za-z_']*)" "(SPLICE1(\\1))"
  . gsubRegexPR "\\[\\|(.*)\\|\\]" "(QUOTE(\\1))"
  . gsubRegexPR "'([A-Z]([a-zA-Z0-9_']*[a-zA-Z0-9_])?)(?![a-zA-Z0-9_'])" "(CONSTR(\\1))"
  . gsubRegexPR "''([A-Z]([a-zA-Z0-9_']*[a-zA-Z0-9_])?)(?![a-zA-Z0-9_'])" "(TYPE(\\1))"

-- escape ('|' : rest) = '|' : '|' : escape rest
-- escape (x : rest) = x : escape rest
-- escape [] = []

isText :: String -> [Inline] -> Bool
isText text inlines = inlines == (intersperse Space . map Str . words $ text)

transformDoc :: Config -> Pandoc -> Pandoc
transformDoc config@Config{configBeamer, configToc, configFigures, configAbstract}
  = onStructure
    (  if configBeamer then bottomUp (concatMap (transformBeamer config)) else id
    .  maybe id (bottomUp . concatMap . transformAbstract)   configAbstract
    .  maybe id (bottomUp . transformToc)                    configToc
    )
  . bottomUp (transformBlock config)
  . bottomUp (transformInline config)
  . if configFigures then onBlocks transformFloats else id

onBlocks :: ([Block] -> [Block]) -> Pandoc -> Pandoc
onBlocks f (Pandoc meta blocks) = Pandoc meta (f blocks)

parserState :: ReaderOptions
parserState = def
  { readerExtensions = Ext_literate_haskell `Set.insert` readerExtensions def
  , readerParseRaw = True
  , readerSmart = True
  , readerApplyMacros = False
  }

readDoc :: Config -> String -> Pandoc
readDoc _ = handleError . readMarkdown parserState
{-
  parserState { stateCitations = case references config of
                                   Just refs  ->  map refId refs
                                   Nothing    ->  [] }
                                   -}

writeDoc :: Config -> Pandoc -> String
writeDoc Config{..} = writeLaTeX opts where
  opts
    = def
      { writerStandalone = maybe False (const True) configTemplate
      , writerTemplate = fromMaybe "" (configTemplate)
      , writerVariables = configVariables
      , writerNumberSections = True
      , writerCiteMethod = configCiteMethod
      }

-- escaping of TeX comments

escapeComments :: String -> String
escapeComments = unlines . skipFirst 3 . lines where
  skipFirst :: Int -> [String] -> [String]
  skipFirst 0 text                =  outside text
  skipFirst n (x@('%' : _) : xs)  =  x : skipFirst (pred n) xs
  skipFirst _ text                =  outside text

  outside []                =  []
  outside (x@('%' : _) : xs)  =  inside [x] xs
  outside (x : xs)          =  x : outside xs

  inside acc (x@('%' : _) : xs)  =  inside (x : acc) xs
  inside acc xs                =  concat [ [ignoreTag "begin"]
                                         , reverse acc
                                         , [ignoreTag "end"]
                                         , outside xs ]

ignoreTag :: String -> String
ignoreTag c = "\\" ++ c ++ "{pandocShouldIgnoreTheseTeXComments}"

unescapeComments :: String -> String
unescapeComments text
  |  Just text'    <-  stripPrefix (ignoreTag "begin") text
  ,  text''        <-  reverse text'
  ,  Just text'''  <-  stripPrefix (reverse (ignoreTag "end")) text''
  =  unlines . map handleFigures . lines . reverse $ text'''
unescapeComments text
  =  escapeBar text

handleFigures :: String -> String
handleFigures "%figure"
  =  "\\begin{figure*}"
handleFigures "%caption"
  =  "\\caption{"
handleFigures text | Just text' <- stripPrefix "%endfigure " text
  =  "}\\label{" ++ takeWhile (/= '\n') text' ++ "}\\end{figure*}"
handleFigures text
  = text

-- includes
includeIncludes :: Config -> String -> IO String
includeIncludes config = fmap unlines . mapM go . lines where
  go line
    | Just rest <- stripPrefix "%include " $ line = do
      let filename = dropWhile isSpace rest
      exist <- doesFileExist filename
      if exist
        then do text <- readFileUTF8 filename
                text' <- transformEval config filename text
                includeIncludes config text'
        else do
          return line

  go line = do
    return line

-- option processing
data Config
  =  Config
     { configIncludes          ::  [String]
     , configFiles             ::  [FilePath]
     , configAbstract          ::  Maybe String
     , configToc               ::  Maybe String
     , configTemplate          ::  Maybe String
     , configVariables         ::  [(String, String)]
     , configPreserveComments  ::  Bool
     , configStandalone        ::  Bool
     , configBeamer            ::  Bool
     , configProcessIncludes   ::  Bool
     , configEval              ::  Maybe String
     , configTitlePage         ::  Maybe String
     , configNotes             ::  Bool
     , configPause             ::  Bool
     , configTh                ::  Bool
     , configFigures           ::  Bool
     , configBibliography      ::  Maybe String
     , configReferences        ::  Maybe [Reference]
     , configCsl               ::  Maybe String
     , configCiteMethod        ::  CiteMethod
     , configIncludeInHeader   ::  [FilePath]
     , configIncludeBeforeBody ::  [FilePath]
     , configHyperref          ::  Bool
     }
  deriving Show

defaultConfig :: Config
defaultConfig
  =  Config
     { configIncludes          =  []
     , configFiles             =  []
     , configAbstract          =  Nothing
     , configToc               =  Nothing
     , configTemplate          =  Nothing
     , configVariables         =  []
     , configPreserveComments  =  False
     , configStandalone        =  False
     , configBeamer            =  False
     , configProcessIncludes   =  False
     , configEval              =  Nothing
     , configTitlePage         =  Nothing
     , configNotes             =  False
     , configPause             =  False
     , configTh                =  False
     , configFigures           =  False
     , configBibliography      =  Nothing
     , configReferences        =  Nothing
     , configCsl               =  Nothing
     , configCiteMethod        =  Citeproc
     , configIncludeInHeader   =  []
     , configIncludeBeforeBody =  []
     , configHyperref          =  False
     }

data Command
  =  Transform Config
  |  Help
  deriving Show

optInclude, optIncludeInHeader, optProcessIncludes, optHelp, optFile, optAbstract, optTitlePage, optToc, optComments, optNotes, optPause, optTH, optFigures  :: OptDescr (Command -> Command)


optInclude     =  Option  ""   ["include"]     (ReqArg processInclude "FILE")
                          "emit a lhs2tex \"%include FILE\" directive"

optIncludeInHeader
               =  Option  "H"  ["include-in-header"]     (ReqArg processIncludeInHeader "FILE")
                          "include the contents of FILE into the LaTeX header"

optProcessIncludes
               = Option   ""   ["process-includes"] (NoArg processProcessIncludes)
                          "process lhs2tex %include directives by pandoc-lit"

optHelp        =  Option  ""   ["help"]        (NoArg (const Help))
                          "display this help and exit"

optFile        =  Option  ""   ["file"]        (ReqArg processFile "FILE")
                          "process FILE"

optAbstract    =  Option  ""   ["abstract"]    (OptArg processAbstract "HEADER")
                          "transform the first section named HEADER into an \"abstract\" environment"

optTitlePage    =  Option  ""   ["title-page"] (OptArg processTitlePage "HEADER")
                          "transform the first section named HEADER into a title page"

optToc         =  Option  ""   ["toc"]         (OptArg processToc "HEADER")
                          "replace the first section named HEADER by a table of contents"

optComments    =  Option  ""   ["comments"]    (NoArg processComments)
                          "preserve TeX comments (lines starting with %)"

optNotes       =  Option  ""   ["notes"]       (NoArg processNotes)
                          "convert block quotes into beamer notes"

optPause       =  Option  ""   ["pause"]       (NoArg processPause)
                          "convert horizontal rules into beamer pauses"

optTH          =  Option  ""   ["escape-template-haskell"] (NoArg processTH)
                          "escape Template Haskell splices, quotes and names"

optFigures     =  Option  ""   ["figures"]       (NoArg processFigures)
                          "enable support for floating figures"

optTemplate    =  Option  ""   ["template"]    (ReqArg processTemplate "FILE")
                          "produce standalone output and use FILE as template"

optVariables   =  Option  ""   ["variable"]    (ReqArg processVariable "KEY:VALUE")
                          "set template variable KEY to VALUE"

optStandalone  =  Option  "s"  ["standalone"]  (NoArg processStandalone)
                          "produce standalone output"

optTemplate, optVariables, optStandalone, optBeamer, optEval, optBibliography, optCSL, optNatbib, optBiblatex, optHyperref :: OptDescr (Command -> Command)

processStandalone :: Command -> Command
processStandalone (Transform config)
  =  Transform (config {configStandalone = True})
processStandalone x
  =  x

optBeamer      =  Option  ""   ["beamer"]      (NoArg processBeamer)
                          "produce output for beamer package"

optEval        =  Option  ""   ["eval"]        (ReqArg processEval "DIR")
                          "handle \\eval{...} by calling ghci -iDIR"

optBibliography=  Option  ""   ["bibliography"](ReqArg processBibliography "BIB")
                          "use bibliography BIB for references"

optCSL         =  Option  ""   ["csl"](ReqArg processCSL "CSL")
                          "use style sheet CSL for references"

optNatbib      =  Option  ""   ["natbib"]      (NoArg processNatbib)
                          "use natbib for references"

optBiblatex    =  Option  ""   ["biblatex"]    (NoArg processBiblatex)
                          "use biblatex for references"

optHyperref    = Option   ""   ["hyperref"] (NoArg processHyperref)
                          "better support hyperref package"
processVariable :: String -> Command -> Command
processVariable arg (Transform (config@Config {configVariables = old}))
  = case break (`elem` ":=") arg of
      (k, _ : v)  ->  Transform (config {configVariables = old ++ [(k, v)]})
      _           ->  error ("Could not parse `" ++ arg ++ "' as a key/value pair (k=v or k:v)")
processVariable _ x
  = x

processInclude :: String -> Command -> Command
processInclude file (Transform (config@Config {configIncludes = old}))
  =  Transform (config {configIncludes = old ++ [file]})
processInclude _ x
  =  x

processFile :: String -> Command -> Command
processFile file (Transform (config@Config {configFiles = old}))
  =  Transform (config {configFiles = old ++ [file]})
processFile _ x
  =  x

processComments :: Command -> Command
processComments (Transform (config))
  =  Transform (config {configPreserveComments = True})
processComments x
  =  x

processNotes :: Command -> Command
processNotes (Transform (config))
  =  Transform (config {configNotes = True})
processNotes x
  =  x

processPause :: Command -> Command
processPause (Transform config)
  =  Transform (config {configPause = True})
processPause x
  =  x

processTH :: Command -> Command
processTH (Transform (config))
  =  Transform (config {configTh = True})
processTH x
  =  x

processFigures :: Command -> Command
processFigures (Transform (config))
  =  Transform (config {configFigures = True})
processFigures x
  =  x

processEval :: String -> Command -> Command
processEval dir (Transform config)
  = Transform (config {configEval = Just dir})
processEval _ x
  = x

processAbstract :: Maybe String -> Command -> Command
processAbstract (Just section) (Transform config)
  =  Transform (config {configAbstract = Just section})
processAbstract Nothing (Transform config)
  =  Transform (config {configAbstract = Just "Abstract"})
processAbstract _ x
  =  x

processTitlePage :: Maybe String -> Command -> Command
processTitlePage (Just section) (Transform config)
  =  Transform (config {configTitlePage = Just section})
processTitlePage Nothing (Transform config)
  =  Transform (config {configTitlePage = Just "Title Page"})
processTitlePage _ x
  =  x

processToc :: Maybe String -> Command -> Command
processToc (Just section) (Transform config)
  =  Transform (config {configToc = Just section})
processToc Nothing (Transform config)
  =  Transform (config {configToc = Just "Contents"})
processToc _ x
  =  x

processTemplate :: String -> Command -> Command
processTemplate file (Transform config)
  =  Transform (config {configTemplate = Just file, configStandalone = True})
processTemplate _ x
  =  x

processBeamer :: Command -> Command
processBeamer (Transform config)
  = Transform (config {configBeamer = True})
processBeamer x
  = x

processProcessIncludes :: Command -> Command
processProcessIncludes (Transform config)
  = Transform (config {configProcessIncludes = True})
processProcessIncludes x
  = x

processBibliography :: String -> Command -> Command
processBibliography bib (Transform config)
  = Transform (config {configBibliography = Just bib})
processBibliography _ x
  = x

processCSL :: String -> Command -> Command
processCSL filename (Transform config)
  = Transform (config {configCsl = Just filename,
                       configCiteMethod = Citeproc})
processCSL _ x
  = x

processNatbib :: Command -> Command
processNatbib (Transform config)
  = Transform (config {configCiteMethod = Natbib})
processNatbib x
  = x

processBiblatex :: Command -> Command
processBiblatex (Transform config)
  = Transform (config {configCiteMethod = Biblatex})
processBiblatex x
  = x

processIncludeInHeader :: String -> Command -> Command
processIncludeInHeader file (Transform (config@Config {configIncludeInHeader = old}))
  =  Transform (config {configIncludeInHeader = old ++ [file]})
processIncludeInHeader _ x
  =  x

processHyperref :: Command -> Command
processHyperref (Transform config)
  = Transform (config {configHyperref = True})
processHyperref x
  = x

options :: [OptDescr (Command -> Command)]
options
  = [ optInclude
    , optHelp
    , optFile
    , optAbstract
    , optToc
    , optTemplate
    , optVariables
    , optComments
    , optStandalone
    , optBeamer
    , optProcessIncludes
    , optEval
    , optTitlePage
    , optNotes
    , optPause
    , optTH
    , optFigures
    , optBibliography
    , optCSL
    , optNatbib
    , optBiblatex
    , optIncludeInHeader
    , optHyperref
    ]

-- main program

usageHeader :: String
usageHeader = "Usage: pandoc-lit [OPTION...] files..."

main :: IO ()
main = do
  args <- getArgs

  case getOpt (ReturnInOrder processFile) options args of
    (configT, [], [])
      -> case foldr (.) id configT (Transform defaultConfig) of
           Transform config  -> transform config
           Help              -> help >> exitSuccess
    (_, _, errors)
      -> do mapM_ (hPutStrLn stderr) errors
            usage
            exitFailure

help :: IO ()
help = hPutStrLn stdout (usageInfo usageHeader options)

usage :: IO ()
usage = do
  hPutStrLn stderr "Usage: pandoc-lit [options] [files]"
  hPutStrLn stderr "pandoc-lit --help for more information."

readDefaultTemplate :: IO String
readDefaultTemplate
  = readDataFile ("templates" </> "lhs2tex"  <.> "template")

readDataFile :: FilePath -> IO String
readDataFile fname
  = do u <- getAppUserDataDirectory "pandoc"
       (readFileUTF8 $ u </> fname)
         `catchIOError` (\_ -> getDataFileName fname >>= readFileUTF8)
  `catchIOError` (\_ -> getDataFileName fname >>= readFileUTF8)

readTemplate :: Config -> IO (Maybe String)
readTemplate Config{..} = do
  case configTemplate of
    Just filename
      -> return Just `ap` readFileOrGetContents filename

    Nothing
      -> if configStandalone
           then return Just `ap` readDefaultTemplate
           else return Nothing

transform :: Config -> IO ()
transform (config@Config {configFiles = []})
  = transform (config {configFiles = ["-"]})

transform config = do
  -- read template
  templateText <- readTemplate config
  let config' = config {configTemplate = templateText}

  -- output include directives
  mapM_ (\x -> putStrLn ("%include " ++ x)) (configIncludes config')

  -- read bibliography
  refs  <-  case configBibliography config of
              Just bib  ->  liftM Just (readBiblioFile bib)
              Nothing   ->  return Nothing
  let config'' = config' {configReferences = refs}

  mapM_ (transformFile config'') (configFiles config'')

-- A variant of readFile forcing UTF8 encoding and accepting any newline style.
readFileUTF8 :: FilePath -> IO String
readFileUTF8 name = do
  handle <- openFile name ReadMode
  hSetEncoding handle utf8
  hSetNewlineMode handle universalNewlineMode
  hGetContents handle

readFileOrGetContents :: String -> IO String
readFileOrGetContents "-" = getContents
readFileOrGetContents file = readFileUTF8 file

transformFile :: Config -> FilePath -> IO ()
transformFile config file = do
  text         <-  readFileOrGetContents file
  text'        <-  transformEval config file text
  text''       <-  if configProcessIncludes config
                     then includeIncludes config text'
                     else return text'
  let text'''  =   if configPreserveComments config
                     then escapeComments text''
                     else text''

  cslfile    <-  case configCsl config of
                   Just filename  ->  return filename
                   Nothing        ->  return "default.csl"

  let doc    =   readDoc config text'''
  let doc'   =   transformDoc config doc
  cslstyle <- readCSLFile Nothing cslfile
  let doc''  = case configReferences config of
                   Just refs | configCiteMethod config == Citeproc
                              ->  processCites cslstyle refs doc'
                   _          ->  doc'

  headerIncludes <- mapM readFile (configIncludeInHeader config)
  includeBefore <- mapM readFile (configIncludeBeforeBody config)
  let config' = config {configVariables = configVariables config ++
                        map ((,) "header-includes") headerIncludes ++
                        map ((,) "include-before") includeBefore}

  putStrLn . avoidUTF8 . writeDoc config' $ doc''

avoidUTF8 :: String -> String
avoidUTF8 = concatMap f where
  f c  =  if c <= toEnum 128
            then [c]
            else encodeCharForLatex c

encodeCharForLatex :: Char -> String
encodeCharForLatex c = case fromEnum c of
  -- LATIN EXTENDED
  0x00C0  ->  "\\`{A}"
  0x00C1  ->  "\\'{A}"
  0x00C2  ->  "\\^{A}"
  0x00C3  ->  "\\~{A}"
  0x00C4  ->  "\\\"{A}"
  0x00C5  ->  "\\r{A}"
  0x00C6  ->  "\\AE "
  0x00C7  ->  "\\c{C}"
  0x00C8  ->  "\\`{E}"
  0x00C9  ->  "\\'{E}"
  0x00CA  ->  "\\^{E}"
  0x00CB  ->  "\\\"{E}"
  0x00CC  ->  "\\`{I}"
  0x00CD  ->  "\\'{I}"
  0x00CE  ->  "\\^{I}"
  0x00CF  ->  "\\\"{I}"

  -- 0x00D0  -> -- What is this?
  0x00D1  ->  "\\~{N}"
  0x00D2  ->  "\\`{O}"
  0x00D3  ->  "\\'{O}"
  0x00D4  ->  "\\^{O}"
  0x00D5  ->  "\\~{O}"
  0x00D6  ->  "\\\"{O}"
  -- 0x00D7  ->  -- What is this?
  0x00D8  ->  "\\O "
  0x00D9  ->  "\\`{U}"
  0x00DA  ->  "\\'{U}"
  0x00DB  ->  "\\^{U}"
  0x00DC  ->  "\\\"{U}"
  0x00DD  ->  "\\'{Y}"
  -- 0x00DE  ->  -- What is this?
  0x00DF  ->  "\\ss "

  0x00E0  ->  "\\`{a}"
  0x00E1  ->  "\\'{a}"
  0x00E2  ->  "\\^{a}"
  0x00E3  ->  "\\~{a}"
  0x00E4  ->  "\\\"{a}"
  0x00E5  ->  "\\r{a}"
  0x00E6  ->  "\\ae "
  0x00E7  ->  "\\c{c}"
  0x00E8  ->  "\\`{e}"
  0x00E9  ->  "\\'{e}"
  0x00EA  ->  "\\^{e}"
  0x00EB  ->  "\\\"{e}"
  0x00EC  ->  "\\`{\\i}"
  0x00ED  ->  "\\'{\\i}"
  0x00EE  ->  "\\^{\\i}"
  0x00EF  ->  "\\\"{\\i}"
  -- 0x00F0  -> -- What is this?
  0x00F1  ->  "\\~{n}"
  0x00F2  ->  "\\`{o}"
  0x00F3  ->  "\\'{o}"
  0x00F4  ->  "\\^{o}"
  0x00F5  ->  "\\~{o}"
  0x00F6  ->  "\\\"{o}"
  -- 0x00F7  ->  -- What is this?
  0x00F8  ->  "\\o "
  0x00F9  ->  "\\`{u}"
  0x00FA  ->  "\\'{u}"
  0x00FB  ->  "\\^{u}"
  0x00FC  ->  "\\\"{u}"
  0x00FD  ->  "\\'{y}"
  -- 0x00FE  ->  -- What is this?
  0x00FF  ->  "\\\"{y} "

  -- GREEK
  0x03BB  ->  "\\ensuremath{\\lambda}"

  -- GENERAL INTERPUNCTUATION
  0x2013  ->  "--"

  -- all others
  code    ->  "{\\char" ++ show code ++ "}"

transformEval :: Config -> FilePath -> String -> IO String
transformEval Config {configEval = Just dir} path text = result where
  result :: IO String
  result = process text (gmatchRegexPR "\\\\eval{([^\\}]*)}" text)

  process :: String -> [((String, (String, String)),[(Int, String)])] -> IO String
  process post [] = do
    return post

  process _ (((_, (pre, post)), [(1, arg)]) : rest) = do
    this <- execute arg
    that <- process post rest
    return (pre ++ "`" ++ this ++ "`" ++ that)
  process _ _ = error "transformEval"

  execute arg = do
    readProcess "ghci" ["-v0", "-i" ++ dir, path] arg

transformEval _ _ text = return text
