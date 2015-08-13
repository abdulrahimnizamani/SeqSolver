module Main where
import Amath.Types
import Amath.Proof
import Amath.Expr.AbsExp
import Amath.Expr.ExprFuncs

import Data.Maybe
import Sequence5

import System (getArgs, getProgName)
import Control.Monad.State
import Data.List
import qualified Data.Map as Map
import Data.Char
--import Amath.Expr.ExprFuncs
import System.Directory as Dir

outFile = "result.txt"

printErrMsg :: String -> IO ()
printErrMsg prgname =
    error $ "Version: 0.1" ++ "\nThis program generates the proof of a numeric sequence." ++ "\n\n" ++
            "Usage:\n\n> " ++ prgname ++ " \"expression\" Min-len Max-len dm-file pm-file WM-size ...\n"

main :: IO ()
main = do
   args <- getArgs
   progName <- getProgName
   --start <- getCurrentTime
   if length args >= 6
        then do let [sq, starts, fins, dmfile, pmfile, wms] = take 6 args
                let options = drop 6 args
                let isSMWMdigit = all isDigit wms
                if not isSMWMdigit || read wms < 0
                   then printErrMsg progName
                   else return ()
                dmStr   <- readFile dmfile   -- read ltm file
                let dm  = parseDM (dmStr)    -- parse the ltm file
                --writeFile "dmfile.txt" $ show dm
                let dmmap = Map.fromList dm
                
                
                pmStr <- readFile pmfile
                let (Pmem pm') = parsePM pmStr
                if null pm'
                   then putStrLn "Could not parse pm-file."
                   else return ()
                let pm = dropZeroWeighted (Pmem pm')
                
                --writeFile "pmfile.txt" (show pm)
                let wm = read wms
                let fin = read fins
                let start = read starts
                if (not . null $ sq) && (head sq == '[')
                    then do
                      let seq = (read sq :: [Int] )
                      --putStrLn $ show seq
                      solveSeq dmmap pm wm start fin options (1,seq)
                      return ()
                    else do
                      seqs <- getSeqs sq
                      results <- mapM (solveSeq dmmap pm wm start fin options) $ zip [1..] (map fst seqs)
                      matchResults results seqs
                    
        else do putStrLn "\nThe number of arguments is wrong!"
                putStrLn ""
                printErrMsg progName

matchResults :: [(Maybe Int)] -> [([Int],Int)] -> IO ()
matchResults results seqs = do
    let tmp = (map (\(_,x) -> (Just x)) seqs)
    if (results == tmp)
      then putStrLn "\nAll answers correct."
      else do
            let count' = filter (\(b1,b2) -> isJust b1) $ zip results tmp
            let count = length $ filter (/=True) $ map (\(b1,b2) -> (fromJust b1) == (fromJust b2)) count'
            let countn = length $ filter (isNothing) results 
            putStrLn $ "\n" ++ show count ++ " wrong predictions" 
            putStrLn $         show countn ++ " failed attempts\n" 
            mapM_ (\(pred, (seq,ans)) -> putStrLn (show seq ++ ": answer=" ++ show ans ++ ", prediction=" ++ show pred)) $ zip results seqs

getRules :: [PRule] -> [PRule]
getRules xs = filter check' xs
  where
    check' x@(Rule name value []) = True
    --check' x@(Rule name value (y@(EEqual (EFunc _ _) _):ys)) = False
    check' _ = True

func = EAdd (EFunc (Ident "f") (EInt 3)) (EFunc (Ident "f") (EInt 4) )

-- read list of integer sequences from a file
-- return blank list if file does not exist or does not contain sequences
getSeqs :: FilePath -> IO [([Int],Int)]
getSeqs filename = do
    fileExists <- Dir.doesFileExist filename
    if fileExists then do
        --putStrLn $ "Reading file: " ++ filename
        file <- readFile filename
        result' <- mapM parseSeq (lines file)
        let result = (filter (not . null) result')
        let seqs = map (\x -> (init x, last x)) result
        return seqs
      else do
        putStrLn $ "File " ++ filename ++ " does not exist."
        return []

parseSeq :: String -> IO [Int]
parseSeq s = do
    let s' = dropWhile (/='[') s
    let s'' = takeWhile (/=']') s'
    if null s || null s''
        then return []
        else do
            let sq = read (s'' ++ "]")
            --putStrLn $ "Read line: " ++ (show sq)
            return sq

solveSeq :: Map.Map Exp Exp -> [PRule] -> Int -> Int -> Int -> [String] -> (Int,[Int]) -> IO (Maybe Int)
solveSeq dmmap pm wm start fin options (no,seq) = do
                      let seqlen = length seq
                      let closure = getClosure seq
                      let line = "Problem " ++ show no ++ ": " ++ show seq
                      putStrLn $ take (length line) $ repeat '='
                      putStrLn $ line
                      putStrLn $ take (length line) $ repeat '='
                      let pctx = (PCtx (5, wm, dmmap, getRules pm, [], func, [], seq))
                      let sctx = SCtx (closure, seq, [(i-1) | i <- [1..seqlen]], pctx,options)
                      result <- evalStateT (solveInterative start fin) sctx
                      return result
    
