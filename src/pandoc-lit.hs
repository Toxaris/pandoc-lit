{-# LANGUAGE PatternGuards, DeriveDataTypeable #-}
module Main where

import Text.Pandoc

import Control.Monad (liftM, ap)

import System.Environment (getArgs)
import System.Console.GetOpt
import System.Exit (exitFailure, exitSuccess)
import System.IO (stdout, stderr, hPutStrLn)
import System.Directory (doesFileExist, getAppUserDataDirectory)
import System.FilePath (pathSeparator, (</>), (<.>))
import System.Process (readProcess)

import qualified System.IO.UTF8 as UTF8 

import Data.List (intersperse, stripPrefix)
import Data.Data (Data, Typeable)
import Data.Maybe (fromMaybe)
import Data.Char (isSpace)

import Text.RegexPR

import Paths_pandoc_lit (getDataFileName)

-- helper

stripSuffix suffix = fmap reverse . stripPrefix (reverse suffix) . reverse

-- view as hierarchy

data Content
  = Block Block
  | Section Int [Inline] [Content]
  deriving (Eq, Show, Typeable, Data)
 
toContent :: [Block] -> [Content]
toContent = fst . go 0 
  where
  go outer [] = ([], [])
  
  go outer rest@(Header inner _ : _) | inner <= outer  
    =  ([], rest)
  
  go outer (Header inner text : rest)                  
    =  (section : content'', rest'') 
    where (content', rest') = go inner rest
          (content'',  rest'') = go outer rest'
          section = Section inner text content'
        
  go outer (first : rest)                              
    =  (block : content', rest')
    where (content', rest') = go outer rest
          block = Block first
  
fromContent :: Content -> [Block]
fromContent (Block block) 
  = [block]
fromContent (Section level header content) 
  = Header level header : concatMap fromContent content 

-- transformation

transformAbstract :: String -> Content -> [Content]
transformAbstract abstract (Section _ header contents) 
  |   isText abstract header
  =   Block (Plain [TeX "\\begin{abstract}"]) 
  :   contents 
  ++  [Block (Plain [TeX "\\end{abstract}"])]
transformAbstract abstract content 
  = [content]

transformToc :: String -> Content -> Content
transformToc toc (Section _ header contents)
  |   isText toc header
  =   Block (Plain [TeX "\\clearpage\\tableofcontents\\clearpage"])
transformToc toc content
  =   content

transformBeamer :: Config -> Content -> [Content]
transformBeamer config (Section _ header contents)
  |   Just tp <- titlePage config
  ,   isText tp header
  =   Block (Plain [TeX "\\begin{frame}\n\\titlepage"])
  :   transformFrameBlocks config 1 contents
  ++  [Block (Plain [TeX "\\end{frame}"])]
  
transformBeamer config (Section 2 header contents)
  |   Block HorizontalRule `elem` contents
  =   [Block (Plain (TeX "\\begin{frame}{" : header ++ [TeX "}"]))]
  ++  [Block (Plain [TeX "\\begin{columns}[T]"])]
  ++  [Block (Plain [TeX "\\begin{column}{0.45\\textwidth}"])]
  ++  transformFrameBlocks config 1 leftContents
  ++  [Block (Plain [TeX "\\end{column}"])]
  ++  [Block (Plain [TeX "\\begin{column}{0.45\\textwidth}"])]
  ++  transformFrameBlocks config 1 rightContents
  ++  [Block (Plain [TeX "\\end{column}"])]
  ++  [Block (Plain [TeX "\\end{columns}"])]
  ++  [Block (Plain [TeX "\\end{frame}"])] where
    leftContents   =  takeWhile (/= Block HorizontalRule) contents
    rightContents  =  drop 1 $ dropWhile (/= Block HorizontalRule) contents
  
transformBeamer config (Section 2 header contents)
  =   [Block (Plain (TeX "\\begin{frame}{" : header ++ [TeX "}"]))]
  ++  transformFrameBlocks config 1 contents
  ++  [Block (Plain [TeX "\\end{frame}"])]

transformBeamer _ content
  = [content]
  
transformFrameBlocks config i (Block HorizontalRule : rest)
  | pause config
  =   [Block $ Plain [TeX "\\pause"]] 
  ++  transformFrameBlocks config (succ i) rest

transformFrameBlocks config i (Block (BlockQuote blocks) : rest)
  | notes config
  =   [Block $ Plain  [TeX $ "\\note<alert@@" ++ show i ++ ">{"]]
  ++  map Block blocks
  ++  [Block $ Plain  [TeX "}"]]
  ++  transformFrameBlocks config i rest

transformFrameBlocks config i (content : rest)
  =   [content]
  ++  transformFrameBlocks config i rest
  
transformFrameBlocks config i []
  =   []
  
transformBlock :: Config -> Block -> [Block]
transformBlock _ (CodeBlock (identifier, classes, attributes) code)
  |   "literate" `elem` classes  
  =   [Plain [TeX ("\\begin{code}\n" ++ escapeCodeBlock code ++ "\n\\end{code}")]]
  
  |   otherwise
  =   [Plain [TeX ("\\begin{spec}\n" ++ escapeCodeBlock code ++ "\n\\end{spec}")]]
transformBlock _ (RawHtml s)
  =   error "raw html not supported by pandoc-lit"
transformBlock _ x
  = [x]

transformInline :: Inline -> Inline 
transformInline (Str text) = Str (escapeBar text)
transformInline (Code code) = TeX ("|" ++ escapeCodeInline code ++ "|")
transformInline (Math t m) = Math t (escapeBar m)	
transformInline (TeX text) = TeX (unescapeComments $ text)
transformInline (HtmlInline text) = error "raw html not supported by pandoc-lit"
transformInline (Link text (s1, s2)) = Link text (escapeBar s1, escapeBar s2)
transformInline x = x
 
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
  = Pandoc meta (Plain [TeX "%include polycode.fmt"] : blocks)

isText text inlines = inlines == (intersperse Space . map Str . words $ text)

onContent :: ([Content] -> [Content]) -> Pandoc -> Pandoc
onContent f (Pandoc meta blocks) 
  = Pandoc meta . concatMap fromContent . f . toContent $ blocks

transformDoc :: Config -> Pandoc -> Pandoc
transformDoc config
  = onContent 
    (  if beamer config then processWith (concatMap (transformBeamer config)) else id
    .  maybe id (processWith . concatMap . transformAbstract)   (abstract config)
    .  maybe id (processWith . transformToc)                    (toc config)
    )
  . processWith (concatMap (transformBlock config))
  . processWith transformInline

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
  | Just text'    <-  stripPrefix (ignoreTag "begin") text
  , text''        <-  reverse text'
  , Just text'''  <-  stripPrefix (reverse (ignoreTag "end")) text''
  = reverse text'''
unescapeComments text
  = escapeBar text
  
-- includes
includeIncludes :: Config -> String -> IO String
includeIncludes config = fmap unlines . mapM go . lines where
  go line 
    | Just rest <- stripPrefix "%include " $ line = do
      let filename = dropWhile isSpace rest
      let filename' = map f filename ++ ".lhs" where
            f '.' = pathSeparator
            f c   = c
      exist <- doesFileExist filename' 
      if exist
        then do text <- UTF8.readFile filename'
                text' <- transformEval config filename' text
                includeIncludes config text'
        else return line
  go line
    = return line
    
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
  text <- readFileOrGetContents file
  text' <- transformEval config file text
  text'' <- if processIncludes config then includeIncludes config text' else return text'
  let text''' | preserveComments config = escapeComments text'' | otherwise = text''  
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
