-- Copyright (c) 2010 Tillmann Rendel <rendel@informatik.uni-marburg.de>
-- This code can be used under the terms of a 3-clause BSD license.
-- See LICENSE for details.

{-# LANGUAGE PatternGuards, DeriveDataTypeable #-}
module Main where

import Text.Pandoc hiding (processWith)

import Control.Monad (liftM, ap)

import System.Environment (getArgs)
import System.Console.GetOpt
import System.Exit (exitFailure, exitSuccess)
import System.IO (stdout, stderr, hPutStrLn)
import System.Directory (getCurrentDirectory, doesFileExist, getAppUserDataDirectory)
import System.FilePath (pathSeparator, (</>), (<.>))
import System.Process (readProcess)

import qualified System.IO.UTF8 as UTF8

import Data.List (intersperse, stripPrefix)
import Data.Data (Data, Typeable)
import Data.Maybe (fromMaybe)
import Data.Char (isSpace)

import Text.RegexPR

import Text.Pandoc.Scripting.Structure (Structure (Block, Section), fromStructure, toStructure, onStructure)

import Paths_pandoc_lit (getDataFileName)

-- helper

stripSuffix suffix = fmap reverse . stripPrefix (reverse suffix) . reverse

-- transformation

transformAbstract :: String -> Structure -> [Structure]
transformAbstract abstract (Section _ header contents)
  |   isText abstract header
  =   [Block $ RawBlock "latex" "\\begin{abstract}"]
  ++  contents
  ++  [Block $ RawBlock "latex" "\\end{abstract}"]
transformAbstract abstract content
  = [content]

transformToc :: String -> Structure -> Structure
transformToc toc (Section _ header contents)
  |   isText toc header
  =   Block $ RawBlock "tex" "\\clearpage\\tableofcontents\\clearpage"
transformToc toc content
  =   content

transformBeamer :: Config -> Structure -> [Structure]
transformBeamer config (Section _ header contents)
  |   Just tp <- titlePage config
  ,   isText tp header
  =   [Block $ RawBlock "tex" "\\begin{frame}\n\\titlepage"]
  ++  transformFrameBlocks config 1 contents
  ++  [Block $ RawBlock "tex" "\\end{frame}"]

transformBeamer config (Section 2 header contents)
  |   Block HorizontalRule `elem` contents
  =   [Block $ Plain
      $   [RawInline "tex" "\\begin{frame}{"] 
      ++  header 
      ++ [RawInline "tex" "}"]]
  ++  [Block $ RawBlock "tex" $ "\\begin{columns}[T]"]
  ++  [Block $ RawBlock "tex" $ "\\begin{column}{0.45\\textwidth}"]
  ++  transformFrameBlocks config 1 leftStructures
  ++  [Block $ RawBlock "tex" $ "\\end{column}"]
  ++  [Block $ RawBlock "tex" $ "\\begin{column}{0.45\\textwidth}"]
  ++  transformFrameBlocks config 1 rightStructures
  ++  [Block $ RawBlock "tex" $ "\\end{column}"]
  ++  [Block $ RawBlock "tex" $ "\\end{columns}"]
  ++  [Block $ RawBlock "tex" $ "\\end{frame}"] where
    leftStructures   =  takeWhile (/= Block HorizontalRule) contents
    rightStructures  =  drop 1 $ dropWhile (/= Block HorizontalRule) contents

transformBeamer config (Section 2 header contents)
  =   [Block $ Plain
      $   [RawInline "tex" "\\begin{frame}{"] 
      ++  header 
      ++  [RawInline "tex" "}"]]
  ++  transformFrameBlocks config 1 contents
  ++  [Block $ RawBlock "tex" $ "\\end{frame}"]

transformBeamer _ content
  = [content]

transformFrameBlocks :: Config -> Int -> [Structure] -> [Structure]
transformFrameBlocks config i (Block HorizontalRule : rest)
  | pause config
  =   [Block $ RawBlock "tex" $ "\\pause"]
  ++  transformFrameBlocks config (succ i) rest

transformFrameBlocks config i (Block (BlockQuote blocks) : rest)
  | notes config
  =   [Block $ RawBlock "tex" $ "\\note<alert@@" ++ show i ++ ">{"]
  ++  map Block blocks
  ++  [Block $ RawBlock "tex" $ "}"]
  ++  transformFrameBlocks config i rest

transformFrameBlocks config i (content : rest)
  =   [content]
  ++  transformFrameBlocks config i rest

transformFrameBlocks config i []
  =   []

transformBlock :: Config -> Block -> [Block]
transformBlock _ (CodeBlock (identifier, classes, attributes) code)
  |   "literate" `elem` classes
  =   [RawBlock "latex" $ "\\begin{code}\n" ++ escapeCodeBlock code ++ "\n\\end{code}"]
  |   otherwise
  =   [RawBlock "latex" $ "\\begin{spec}\n" ++ escapeCodeBlock code ++ "\n\\end{spec}"]
transformBlock _ (RawBlock "tex" text)
  =   [RawBlock "tex" (unescapeComments $ text)]
transformBlock _ (RawBlock "latex" text)
  =   [RawBlock "latex" (unescapeComments $ text)]
transformBlock _ (RawBlock format text)
  =   error $ "raw " ++ format ++ " not supported by pandoc-lit"
transformBlock _ x
  = [x]

transformInline :: Inline -> Inline
transformInline (Str text) = Str (escapeBar text)
transformInline (Code attr code) = RawInline "tex" $ ("|" ++ escapeCodeInline code ++ "|")
transformInline (Math t m) = Math t (escapeBar m)
transformInline (RawInline "tex" text) = RawInline "tex" $ unescapeComments $ text
transformInline (RawInline "latex" text) = RawInline "latex" $ unescapeComments $ text
transformInline (RawInline format text) = error $ "raw " ++ format ++ " not supported by pandoc-lit (" ++ text ++ ")"
transformInline (Link text (s1, s2)) = Link text (escapeBar s1, escapeBar s2)
transformInline x = x

transformFloats :: [Block] -> [Block]
transformFloats = begin where
  begin (Para [RawInline "tex" "\\figure", Space, Str tag] : rest)
    =  Plain [RawInline "tex" "\\begin{figure}"]
    :  caption "figure" tag rest
  begin (Para [RawInline "tex" "\\figure*", Space, Str tag] : rest)
    =  Plain [RawInline "tex" "\\begin{figure*}"]
    :  caption "figure*" tag rest
  begin (block : rest)
    =  block : begin rest
  begin []
    =  []
  
  caption env tag (Para (RawInline "tex" "\\caption" : text) : rest)
    =  Plain  (concat
                [  [RawInline "tex" $ "\\caption{"]
                ,  text
                ,  [RawInline "tex" $ "}"]])
    :  Plain  [RawInline "tex" $ "\\label{" ++ tag ++ "}"]
    :  Plain  [RawInline "tex" $ "\\end{" ++ env ++ "}"]
    :  begin rest
  
  caption env tag (block : rest)
    =  block : caption env tag rest

escapeCodeInline = escapeBar . escapeTH
escapeCodeBlock = escapeInComments . escapeTH

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
  lineComment ('>' : text)         =  '$' : '>' : '$' : rangeComment text
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

escapeBar :: String -> String
escapeBar = gsubRegexPR "\\|" "\\|\\|"

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

addIncludes :: Pandoc -> Pandoc
addIncludes (Pandoc meta blocks)
  = Pandoc meta (RawBlock "tex" "%include polycode.fmt" : blocks)

isText text inlines = inlines == (intersperse Space . map Str . words $ text)

transformDoc :: Config -> Pandoc -> Pandoc
transformDoc config
  = onStructure
    (  if beamer config then bottomUp (concatMap (transformBeamer config)) else id
    .  maybe id (bottomUp . concatMap . transformAbstract)   (abstract config)
    .  maybe id (bottomUp . transformToc)                    (toc config)
    )
  . bottomUp (concatMap (transformBlock config))
  . bottomUp transformInline
  . onBlocks transformFloats 

onBlocks :: ([Block] -> [Block]) -> Pandoc -> Pandoc
onBlocks f (Pandoc meta blocks) = Pandoc meta (f blocks)

parserState = defaultParserState
  { stateLiterateHaskell = True
  , stateSmart = True
  }

readDoc :: Config -> String -> Pandoc
readDoc config = readMarkdown parserState

writeDoc :: Config -> Pandoc -> String
writeDoc config = writeLaTeX options where
  options
    = defaultWriterOptions
      { writerStandalone = maybe False (const True) (template config)
      , writerTemplate = fromMaybe "" (template config)
      , writerVariables = variables config
      , writerNumberSections = True
      }

-- escaping of TeX comments

escapeComments :: String -> String
escapeComments = unlines . skipFirst 3 . lines where
  skipFirst 0 text                =  outside text
  skipFirst n (x@('%' : _) : xs)  =  x : skipFirst (pred n) xs
  skipFirst n text                =  outside text

  outside []                =  []
  outside (x@('%' : _) : xs)  =  inside [x] xs
  outside (x : xs)          =  x : outside xs

  inside acc (x@('%' : _) : xs)  =  inside (x : acc) xs
  inside acc xs                =  concat [ [ignoreTag "begin"]
                                         , reverse acc
                                         , [ignoreTag "end"]
                                         , outside xs ]

ignoreTag c = "\\" ++ c ++ "{pandocShouldIgnoreTheseTeXComments}"
ignoreBegin = ignoreTag "begin"
ignoreEnd = ignoreTag "end"

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
        then do text <- UTF8.readFile filename
                text' <- transformEval config filename text
                includeIncludes config text'
        else do
          return line
          
  go line = do
    return line

-- option processing
data Config
  =  Config
     { includes          ::  [String]
     , files             ::  [FilePath]
     , abstract          ::  Maybe String
     , toc               ::  Maybe String
     , template          ::  Maybe String
     , variables         ::  [(String, String)]
     , preserveComments  ::  Bool
     , standalone        ::  Bool
     , beamer            ::  Bool
     , processIncludes   ::  Bool
     , eval              ::  Maybe String
     , titlePage         ::  Maybe String
     , notes             ::  Bool
     , pause             ::  Bool
     }
  deriving Show

defaultConfig
  =  Config
     { includes          =  []
     , files             =  []
     , abstract          =  Nothing
     , toc               =  Nothing
     , template          =  Nothing
     , variables         =  []
     , preserveComments  =  False
     , standalone        =  False
     , beamer            =  False
     , processIncludes   =  False
     , eval              =  Nothing
     , titlePage         =  Nothing
     , notes             =  False
     , pause             =  False
     }

data Command
  =  Transform Config
  |  Help
  deriving Show

optInclude     =  Option  ""   ["include"]     (ReqArg processInclude "FILE")
                          "emit a lhs2tex \"%include FILE\" directive"

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

optTemplate    =  Option  ""   ["template"]    (ReqArg processTemplate "FILE")
                          "produce standalone output and use FILE as template"

optVariables   =  Option  ""   ["variable"]    (ReqArg processVariable "KEY:VALUE")
                          "set template variable KEY to VALUE"

optStandalone  =  Option  "s"  ["standalone"]  (NoArg processStandalone)
                          "produce standalone output"


processStandalone (Transform config)
  =  Transform (config {standalone = True})
processStandalone x
  =  x

optBeamer      =  Option  ""   ["beamer"]      (NoArg processBeamer)
                          "produce output for beamer package"

optEval        =  Option  ""   ["eval"]        (ReqArg processEval "DIR")
                          "handle \\eval{...} by calling ghci -iDIR"

processVariable arg (Transform (config@Config {variables = old}))
  = case break (`elem` ":=") arg of
      (k, _ : v)  ->  Transform (config {variables = old ++ [(k, v)]})
      _           ->  error ("Could not parse `" ++ arg ++ "' as a key/value pair (k=v or k:v)")
processVariable arg x
  = x

processInclude file (Transform (config@Config {includes = old}))
  =  Transform (config {includes = old ++ [file]})
processInclude file x
  =  x

processFile file (Transform (config@Config {files = old}))
  =  Transform (config {files = old ++ [file]})
processFile file x
  =  x

processComments (Transform (config))
  =  Transform (config {preserveComments = True})
processComments x
  =  x


processNotes (Transform (config))
  =  Transform (config {notes = True})
processNotes x
  =  x

processPause (Transform (config))
  =  Transform (config {pause = True})
processPause x
  =  x

processEval dir (Transform config)
  = Transform (config {eval = Just dir})
processEval dir x
  = x

processAbstract (Just section) (Transform config)
  =  Transform (config {abstract = Just section})
processAbstract Nothing (Transform config)
  =  Transform (config {abstract = Just "Abstract"})
processAbstract section x
  =  x

processTitlePage (Just section) (Transform config)
  =  Transform (config {titlePage = Just section})
processTitlePage Nothing (Transform config)
  =  Transform (config {titlePage = Just "Title Page"})
processTitlePage section x
  =  x


processToc (Just section) (Transform config)
  =  Transform (config {toc = Just section})
processToc Nothing (Transform config)
  =  Transform (config {toc = Just "Contents"})
processToc section x
  =  x

processTemplate file (Transform config)
  =  Transform (config {template = Just file, standalone = True})
processTemplate _ x
  =  x

processBeamer (Transform config)
  = Transform (config {beamer = True})
processBeamer x
  = x

processProcessIncludes (Transform config)
  = Transform (config {processIncludes = True})
processProcessIncludes x
  = x

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
    ]

-- main program

usageHeader = "Usage: pandoc-lit [OPTION...] files..."

main :: IO ()
main = do
  args <- getArgs

  case getOpt (ReturnInOrder processFile) options args of
    (configT, [], [])
      -> case foldr (.) id configT (Transform defaultConfig) of
           Transform config  -> transform config
           Help              -> help stdout >> exitSuccess
    (_, _, errors)
      -> do mapM_ (hPutStrLn stderr) errors
            usage stderr
            exitFailure

help h = hPutStrLn h (usageInfo usageHeader options)

usage h = do
  hPutStrLn h "Usage: pandoc-lit [options] [files]"
  hPutStrLn h "pandoc-lit --help for more information."

readDefaultTemplate :: IO String
readDefaultTemplate
  = readDataFile ("templates" </> "lhs2tex"  <.> "template")

readDataFile :: FilePath -> IO String
readDataFile fname
  = do u <- getAppUserDataDirectory "pandoc"
       (UTF8.readFile $ u </> fname)
         `catch` (\_ -> getDataFileName fname >>= UTF8.readFile)
  `catch` (\_ -> getDataFileName fname >>= UTF8.readFile)

readTemplate :: Config -> IO (Maybe String)
readTemplate config = do
  case template config of
    Just filename
      -> return Just `ap` readFileOrGetContents filename

    Nothing
      -> if standalone config
           then return Just `ap` readDefaultTemplate
           else return Nothing

transform :: Config -> IO ()
transform (config@Config {files = []})
  = transform (config {files = ["-"]})

transform config = do
  templateText <- readTemplate config
  let config' = config {template = templateText}
  mapM_ (\x -> putStrLn ("%include " ++ x)) (includes config')
  mapM_ (transformFile config') (files config)

readFileOrGetContents "-" = getContents
readFileOrGetContents file = UTF8.readFile file

transformFile :: Config -> FilePath -> IO ()
transformFile config file = do
  text         <-  readFileOrGetContents file
  text'        <-  transformEval config file text
  text''       <-  if processIncludes config 
                     then includeIncludes config text' 
                     else return text'
  let text'''  =   if preserveComments config
                     then escapeComments text'' 
                     else text''
  putStrLn . avoidUTF8 . writeDoc config . transformDoc config . readDoc config $ text'''

avoidUTF8 :: String -> String
avoidUTF8 = concatMap f where
  f c  =  if c <= toEnum 128
            then [c]
            else "{\\char" ++ show (fromEnum c) ++ "}"

transformEval :: Config -> FilePath -> String -> IO String
transformEval Config {eval = Just dir} path text = result where
  result :: IO String
  result = process text (gmatchRegexPR "\\\\eval{([^\\}]*)}" text)

  process :: String -> [((String, (String, String)),[(Int, String)])] -> IO String
  process post [] = do
    return post

  process _ (((_, (pre, post)), [(1, arg)]) : rest) = do
    this <- execute arg
    that <- process post rest
    return (pre ++ "`" ++ this ++ "`" ++ that)

  execute arg = do
    readProcess "ghci" ["-v0", "-i" ++ dir, path] arg

transformEval _ _ text = return text
