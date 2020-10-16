module CedilleCore where
import Check
import Trie
import Norm
import Parser
import Types
import CoreToPrim
import ElaborationChecker

import System.FilePath
import System.Directory
import System.Environment
import System.Exit

notM = maybe (Just ()) $ const Nothing
maybV e v = maybe (Left (e ++ v)) Right

-- ModInfo (Module scope) (Filepath) (Context) (Binary?, Verbose?, Indentation)
data ModInfo = ModInfo (Trie [String]) FilePath Ctxt (Bool, Bool, Int)

addDef (ModInfo fs fp (Ctxt decls types defs scope) o) v def =
  maybV "Multiple definitions of " v (notM (trieLookup defs v)) >>
  let fs' = trieInsert fs fp $ maybe [v] ((:) v) (trieLookup fs fp)
      c' = Ctxt decls types (trieInsert defs v def) (trieInsert scope v ()) in
  Right (ModInfo fs' fp c' o)

putMsg tab fp msg = putStrLn $ replicate tab ' ' ++ "[" ++ fp ++ "] " ++ msg
putMsgVrb (ModInfo _ fp _ (False, True, tab)) msg = putMsg tab fp msg
putMsgVrb _ _ = return ()

ctxtShowAll (Ctxt decls types defs scope) =
  Ctxt decls types defs . foldr (\ v s -> trieInsert s v ()) emptyTrie
ctxtShown (Ctxt decls types defs scope) = scope

--checkCmd :: Cmd -> ModInfo -> IO (Either String ModInfo)
checkCmd (TermCmd v tm) mi@(ModInfo _ _ c (_,ver,_)) =
  putMsgVrb mi ("Checking " ++ v) >> do
  res <- if ver then inferTrmV c tm 1 else inferTrm c tm 1
  case res of
    Nothing -> return $ maybV "Error while infering of" v Nothing 
    _       -> return
      (maybV "Error in the definition of " v (synthTerm c tm) >>= \ tp ->
      addDef mi v (Left (hnfeTerm c tm, hnfType c tp)))
checkCmd (TypeCmd v kd tp) mi@(ModInfo _ _ c _) =
  putMsgVrb mi ("Checking " ++ v) >> return
    (maybV "Error in the definition of " v (synthType c tp) >>= \ kd' ->
     maybV "Error in the declared kind of " v (synthKind c kd) >>
     maybV "The declared kind does not match the synthesized kind of " v
       (ifM $ convKind c (eraseKind kd) kd') >>
     addDef mi v (Right (hnfeType c tp, hnfeKind c kd)))
checkCmd (ImportCmd ifp) (ModInfo fs fp c o) =
  checkFile (ModInfo fs ifp (ctxtShowAll c []) o) >>= maybe (return $ Left "")
    (\ (ModInfo fs' _ c' _) -> return $ Right $
       let ds = trieStrings (ctxtShown c) ++ trieStrings (ctxtShown c') in
       ModInfo fs' fp (ctxtShowAll c' ds) o)

--checkCmds :: Cmds -> ModInfo -> IO (Either String ModInfo)
checkCmds [] m = return $ Right m
checkCmds (c : cs) m = checkCmd c m >>= either (return . Left) (checkCmds cs)

--checkFile :: ModInfo -> IO (Maybe ModInfo)
checkFile (ModInfo fs fp c (b, v, i)) =
  getCurrentDirectory >>= \ cd ->
  makeAbsolute (cd </> fp -<.> "cdle") >>= \ fp' ->
  setCurrentDirectory (takeDirectory fp') >>
  case trieLookup fs fp' of
    Just ds -> return (Just $ ModInfo fs fp (ctxtShowAll c ds) (b, v, i))
    Nothing ->
      let msg s e = if b then e else putMsg i fp' s
          checks = msg "No errors" (return ())
          nchecks = flip msg $ exitWith exitTypeError
          nexists = msg "File does not exist" $ exitWith exitFileDoesNotExist
          nparses = msg "Parse error" $ exitWith exitParseError
          fs' = trieInsert fs fp' [] in
      msg "Checking" (return ()) >>
      doesFileExist fp' >>= \ exists ->
      if not exists
        then nexists >> return Nothing
        else readFile fp' >>= \ s -> maybe
          (nparses >> return Nothing)
          (\ (cs, _) ->
             checkCmds cs (ModInfo fs' fp' c (b, v, succ i)) >>= \ r -> case r of
               Left ""  -> return Nothing
               Left err -> nchecks err >> return Nothing
               Right c' -> checks >> return (Just c'))
          (parseFile s)

exitOptionsError = ExitFailure 1
exitParseError = ExitFailure 2
exitFileDoesNotExist = ExitFailure 3
exitTypeError = ExitFailure 4
exitTypeChecks = ExitSuccess

helpStr =
  maybe "" id $ foldr (\ ln -> Just . maybe ln (ln ++)) Nothing
    ["cedille-core [OPTIONS] [FILE]",
     "  -b --binary    exit with error code if an error is encountered",
     "                 (0 = type checks; 1 = options error; 2 = parse error;",
     "                  3 = file does not exist; 4 = type error)",
     "  -v --verbose   enable verbose messages",
     "  -h --help      print this help message"]

--             Options File Binary Verbose
data Options = Options FilePath Bool Bool | Help | Unknown String

mapOpts f o@(Options _ _ _) = f o
mapOpts _ o = o

mkOption short long opt opts = trieInsert (trieInsert opts long opt) short opt

--options :: Trie Option
options =
  mkOption "-b" "--binary"  (\ (Options f b v) -> Options f True v) $
  mkOption "-v" "--verbose" (\ (Options f b v) -> Options f b True) $
  mkOption "-h" "--help"    (\ _ -> Help) $
  emptyTrie

--readArgs :: [String] -> Options
readArgs as = case h (Options "" False False) as of
  Options "" b v -> Help
  opts           -> opts
  where
    h opts (a@('-' : _) : as) =
      maybe (Unknown a) (\ f -> mapOpts (flip h as . f) opts) (trieLookup options a)
    h (Options "" b v) (fp : as) = h (Options fp b v) as
    h (Options _ _ _) (fp : as) = Help
    h opts _ = opts

main =
  getArgs >>= \ as ->
  case readArgs as of
    opts@(Options f b v) ->
      checkFile (ModInfo emptyTrie f emptyCtxt (b, v, 0)) >>
      if b then exitWith exitTypeChecks else return ()
    Help -> putStrLn helpStr
    Unknown a -> putStrLn ("Unknown option \"" ++ a ++ "\"") >> putStrLn helpStr

