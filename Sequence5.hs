module Sequence5 where

import Amath.Types
import Amath.Proof 
import Amath.Expr.AbsExp
--import Amath.Expr.ErrM
import Amath.Expr.ExprFuncs
import Control.Monad.State
import Data.List
import Debug.Trace
import Data.Maybe

-- Options
limitRecLength = True  -- limit k in f(n-k) for every 2nd and every 3rd simplifications

type Length = Int
type IndexShift = Bool
type Start = Int -- starting value of n
type Dir   = Int -- dir=1 for increaing and dir=-1 for decreasing values of n
type Index = Int -- index position of an element
type Indices = [Index] -- set of indices for evaluation of formulas
type Element = Int
type Sequence = [Element]
type Prediction = Int

type TClosure = [Int]

newtype SContext = SCtx (TClosure, Seq, Indices, PContext, [String])

type GenerateFunc = Int -> Int -> IndexShift -> StateT SContext IO [(Exp, Int, Dir)]

type POrder = Int   -- 1 -> apply pattern over every element
                    -- 2 -> apply pattern over every 2nd
                    -- 3 -> apply pattern over every 3rd
                    -- 4 -> apply pattern over every 4th
data Pattern = Pattern POrder Start Dir [Exp]
        deriving (Eq)

instance Show Pattern where
    show (Pattern o s d xs) = "Order " ++ show o ++ ", n>=" ++ show s ++ ": " ++ (foldr (\x y -> show x ++ "," ++  y) "" xs)

pOrder :: Pattern -> POrder
pOrder (Pattern o _ _ xs) = o

-- data PApplication = PA {apply :: Sequence -> Pattern -> (Indices, Prediction)}

minN = -9 -- minimum value of n for shift
maxN =  9 -- maximum value of n for shift
f = "f"

-- maxOrder gives the maximum order of patterns
--   for the given length of a sequence
maxOrder :: Int -> Int
maxOrder len | len < 3 = 0
maxOrder len | even len = (len - 2) `div` 2
maxOrder len            = (len - 1) `div` 2

--staticFuncs = f : ["g", "h", "i", "j", "k"] -- list of function names
                                             -- f stands for recursive
staticFuncs = [f]
n = "n" -- variable for increasing/decreasing values
ind = "i" -- variable to represent indices

iIdent = Ident ind
nIdent = Ident n
fIdent = Ident f

getBaseCases :: Int -> [[Int]]
getBaseCases i = combine (replicate i [0,1])

combine :: [[t]] -> [[t]]
combine [] = [[]]
combine [x] = [[el1] | el1 <- x]
combine [x, y] = [[el1, el2] | el1 <- x, el2 <- y]
combine (x:xs) = [el:ellst | el <- x, ellst <- combine xs]

-- replace the "x" variable to "n" in the given expression
varConvert :: Exp -> String -> Exp
varConvert e fn = substAll e (EVar (Ident "x"), EVar nIdent)
--  let e1 = subst (EPattern (Pattern "x")) [(EVar nIdent, 0)] e
--  in subst (EFunc (Ident fn) (EDiff (EPattern (Pattern "x")) (EInt (toInteger 1)))) [(ESR fn 1,0)] e1

ops :: Exp -> Exp -> [Exp]
ops a b = [EAdd a b,ESub a b,EMul a b,EDiv a b]

getFuncs2 :: TClosure -> [Int] -> Int -> Int -> POrder -> Exp -> [Exp]
getFuncs2 closure sq i b o seed
    | i < 1 = []
    | seed == ENull = (getInts closure i b f) ++ (getBins2 closure i b seed)
    | i <= (expSize seed + 1) = [seed]
    | otherwise =
        let funcs = getFuncs2 closure sq ((i - 1) - expSize seed) b o ENull
            seed' = removeRec (seed)
            result = concat [ops seed' e | e <- (funcs)]
                      -- concatMap (getFuncs2 closure i b) $ 
        in  map applyRec $ result

removeRec :: Exp -> Exp
removeRec (ERec _ e) = e
removeRec e = e

applyRec :: Exp -> Exp
applyRec e@(ERec _ _) = e
applyRec e  =  let r = findMaxRec e
               in  if r <= 0 then e else ERec r e

findMaxRec :: Exp -> Integer
findMaxRec (EF i) = i
findMaxRec (ENeg e) = findMaxRec e
findMaxRec (EFunc fIdent (ESub nIdent (EInt i))) = i
findMaxRec (EFunc _ e) = findMaxRec e
findMaxRec (EAdd e1 e2) = max (findMaxRec e1) (findMaxRec e2)
findMaxRec (ESub e1 e2) = max (findMaxRec e1) (findMaxRec e2)
findMaxRec (EMul e1 e2) = max (findMaxRec e1) (findMaxRec e2)
findMaxRec (EDiv e1 e2) = max (findMaxRec e1) (findMaxRec e2)
findMaxRec (EExp e1 e2) = max (findMaxRec e1) (findMaxRec e2)
findMaxRec (EEqual e1 e2) = max (findMaxRec e1) (findMaxRec e2)
findMaxRec _ = 0

-- returns single digits, numbers and one-length functions ( n and f(n-x) )
getInts2 :: TClosure -> Int -> [Exp]
getInts2       _ 0 = []
getInts2       _ 1 = [EInt (toInteger nr) | nr <- [1..9]] ++ [EVar nIdent]
getInts2 closure i = [EInt (toInteger nr) | nr <- closure, length (show nr) == i]

-- returns formulas made of binary operators
getBins2 :: TClosure -> Int -> Int -> Exp -> [Exp]
getBins2 _ 2 _ _ = []
getBins2 _ 1 _ _ = []
getBins2 _ 0 _ _ = []
getBins2 closure i b'' seed =
    let abpairs = [let a = getFuncs closure asize b'' f
                       b = getFuncs closure bsize b'' f
                   in (a, b, asize, bsize)
                        | [asize, bsize] <- transpose [[1..(i-2)], [(i-2) , (i-3)..1]]]
        cmpfunc as' bs' a b = if as' == bs' then (show a >= show b) else True
        commutative =
           concat [
              concat [case (a', b') of
                (EInt 1, _) -> [EAdd a' b']
                (_, EInt 1) -> [EAdd a' b']
                _           ->
                    [EAdd a' b', EMul a' b'] | a' <- a,
                                               b' <- b,
                                               mf (EAdd a' b') True &&
                                               mf (EMul a' b') True &&
                                               cmpfunc asize bsize a' b'
                                               ]
                    | (a, b, asize, bsize) <- abpairs, asize >= bsize]
        noncommutativesub =
           concat [
              concat [case b' of
                EInt 1 -> [ESub a' b']
                _      ->
                               [ESub a' b'] | a' <- a,
                                              b' <- b,
                                              mf (ESub a' b') True] | (a, b, _, _) <- abpairs]
        noncommunicativediv =
           concat [
              concat [case b' of
                EInt 1 -> []
                _      ->
                          [EDiv a' b'] | a' <- a,
                                         b' <- b,
                                         mf (EDiv a' b') True] | (a, b, _, _) <- abpairs]
    --in (trace (show $ length commutative) commutative) ++ noncommutative
    in commutative ++ noncommutativesub ++ noncommunicativediv

-- Generates a list of all possible functions of given length
         -- Closure -> Length -> Int -> Func -> Expressions
getFuncs :: TClosure -> Int -> Int -> String -> [Exp]
getFuncs closure i b fn
    | i < 1     = []
    | otherwise = (getInts closure i b fn) ++ (getBins closure i b fn)

-- returns single digits, numbers and one-length functions ( n and f(n-x) )
getInts :: TClosure -> Int -> Int -> String -> [Exp]
getInts _ 0 _ _ = []
getInts _ 1 b fn =
    [EInt (toInteger nr) | nr <- [1..9]] ++
     [EVar nIdent] ++
      (if fn == f then [EF (toInteger b') | b' <- [1..b]] else [] )
getInts closure i b _ = [EInt (toInteger nr) | nr <- closure, length (show nr) == i]

-- returns formulas made of binary operators
getBins :: TClosure -> Int -> Int -> String -> [Exp]
getBins _ 2 _ _ = []
getBins _ 1 _ _ = []
getBins _ 0 _ _ = []
getBins closure i b'' fn =
    let abpairs = [let a = getFuncs closure asize b'' fn
                       b = getFuncs closure bsize b'' fn
                   in (a, b, asize, bsize)
                        | [asize, bsize] <- transpose [[1..(i-2)], [(i-2) , (i-3)..1]]]
        cmpfunc as' bs' a b = if as' == bs' then (show a >= show b) else True
        commutative =
           concat [
              concat [case (a', b') of
                (EInt 1, _) -> [EAdd a' b']
                (_, EInt 1) -> [EAdd a' b']
                _           ->
                    [EAdd a' b', EMul a' b'] | a' <- a,
                                               b' <- b,
                                               mf (EAdd a' b') True &&
                                               mf (EMul a' b') True &&
                                               cmpfunc asize bsize a' b'
                                               ]
                    | (a, b, asize, bsize) <- abpairs, asize >= bsize]
        noncommutative =
           concat [
              concat [case b' of
                EInt 1 -> [ESub a' b']
                _      ->
                   [EDiv a' b', ESub a' b'] | a' <- a,
                                              b' <- b,
                                              mf (ESub a' b') True &&
                                              mf (EDiv a' b') True] | (a, b, _, _) <- abpairs]
    --in (trace (show $ length commutative) commutative) ++ noncommutative
    in commutative ++ noncommutative

-- checks if there are multiple integer operations
mf :: Exp -> Bool -> Bool
mf exp switch =
  case exp of
    EAdd (EInt a) (EInt b) -> False
    EMul (EInt a) (EInt b) -> False
    ESub (EInt a) (EInt b) -> False
    EDiv (EInt a) (EInt b) -> False
    EAdd (EAdd a' b') c ->
       mf (EAdd a' b') True && mf c True && if switch then mf (EAdd a' (EAdd b' c)) False else True
    EAdd c (EAdd a' b') ->
       mf (EAdd a' b') True && mf c True && if switch then mf (EAdd (EAdd c a') b') False else True
    -- EAdd (ESub a' b') c ->
       -- mf (ESub a' b') True && mf c True && if switch then mf (ESub (EAdd a' c) b') False else True
    EMul (EMul a' b') c ->
       mf (EMul a' b') True && mf c True && if switch then mf (EMul a' (EMul b' c)) False else True
    EMul c (EMul a' b') ->
       mf (EMul a' b') True && mf c True && if switch then mf (EMul a' (EMul b' c)) False else True
    -- EMul (EDiv a' b') c ->
       -- mf (EDiv a' b') True && mf c True && if switch then mf (EDiv (EMul a' c) b') False && mf (EMul a' (EDiv c b')) False else True
    -- ESub (EAdd a' b') c ->
       -- mf (EAdd a' b') True && mf c True && if switch then mf (EAdd a' (ESub b' c)) False && mf (EAdd b' (ESub a' c)) False else True
    EAdd a b -> mf a True && mf b True
    EMul a b -> mf a True && mf b True
    ESub a b -> mf a True && mf b True
    EDiv a b -> mf a True && mf b True
    EFunc _ arg -> mf arg True
    _ -> True

validReferences' :: Exp                 -- expression to check
                    -> [String]
                    -> Int
                    -> [(String, Exp)]
                    -> [String]
                    -> String
                    -> ([String], [String])
validReferences' exp frefs b' flkup nrefs currfunc =
    case exp of
        EAdd a b     -> let (frefs1, nrefs1) = validReferences' a frefs b' flkup nrefs currfunc
                        in validReferences' b frefs1 b' flkup nrefs1 currfunc
        EMul a b     -> let (frefs1, nrefs1) = validReferences' a frefs b' flkup nrefs currfunc
                        in validReferences' b frefs1 b' flkup nrefs1 currfunc
        EExp a b     -> let (frefs1, nrefs1) = validReferences' a frefs b' flkup nrefs currfunc
                        in validReferences' b frefs1 b' flkup nrefs1 currfunc
        EDiv a b     -> let (frefs1, nrefs1) = validReferences' a frefs b' flkup nrefs currfunc
                        in validReferences' b frefs1 b' flkup nrefs1 currfunc
        ESub a b     -> let (frefs1, nrefs1) = validReferences' a frefs b' flkup nrefs currfunc
                        in validReferences' b frefs1 b' flkup nrefs1 currfunc
        ENeg a       -> validReferences' a frefs b' flkup nrefs currfunc
        EF b         ->
            if (toInteger b') == b
               then (delete (head staticFuncs) frefs, if elem currfunc nrefs then delete currfunc nrefs else nrefs)
               else (frefs, nrefs)
        EFunc (Ident fn) a ->
            if elem fn frefs
               then case lookup fn flkup of
                      Just e -> let (frefs1, nrefs1) = validReferences' a frefs b' flkup nrefs currfunc
                                in validReferences' e (delete fn frefs1) b' flkup nrefs1 fn
                      _      -> error "error in validReferences'"
               else validReferences' a frefs b' flkup nrefs currfunc
        EVar _      -> if elem currfunc nrefs
                           then (frefs, delete currfunc nrefs)
                           else (frefs, nrefs)
        _           -> (frefs, nrefs)

validReferences :: [Exp] -> Int -> Bool
validReferences exps b =
    let nrefs = take (length exps) staticFuncs
        frefs = if b == 0 then tail nrefs else nrefs
        (fr, nr) = validReferences' (head exps) frefs b (zip nrefs exps) nrefs (head staticFuncs)
    in null fr && null nr

-- Check if the given integer value exceeds
--   the max value of Int (32-bit integer)
overflowCheck :: Integer -> (Bool, Int)
overflowCheck a = if a > (toInteger (maxBound :: Int))
                      || a < (toInteger (minBound :: Int))
                     then (True, 0)
                     else (False, fromInteger a)

getPatternMapping :: Exp -> Exp -> [(String,Exp)] -> Maybe [(String,Exp)]
getPatternMapping (EAdd e1 e2) (EAdd p1 p2) c =
    do m1 <- getPatternMapping e1 p1 c
       m2 <- getPatternMapping e2 p2 m1
       return m2
getPatternMapping (ESub e1 e2) (ESub p1 p2) c =
    do m1 <- getPatternMapping e1 p1 c
       m2 <- getPatternMapping e2 p2 m1
       return m2
getPatternMapping (EMul e1 e2) (EMul p1 p2) c = 
    do m1 <- getPatternMapping e1 p1 c
       m2 <- getPatternMapping e2 p2 m1
       return m2
getPatternMapping (EDiv e1 e2) (EDiv p1 p2) c =
    do m1 <- getPatternMapping e1 p1 c
       m2 <- getPatternMapping e2 p2 m1
       return m2
getPatternMapping (EExp e1 e2) (EExp p1 p2) c = 
    do m1 <- getPatternMapping e1 p1 c
       m2 <- getPatternMapping e2 p2 m1
       return m2
getPatternMapping (ENeg e1) (ENeg p1) c =
    do m1 <- getPatternMapping e1 p1 c
       return m1
getPatternMapping (EFunc f1 e1) (EFunc fp1 p1) c =
    if f1 == fp1
        then do m1 <- getPatternMapping e1 p1 c
                return m1
        else Nothing
getPatternMapping (EInt a) (EInt p) c = if a == p then return c else Nothing
getPatternMapping e (EVar (Ident v)) c =
    let patternLkUp = (\var ctx -> case (lookup var ctx) of
                                       Just exp -> return c
                                       Nothing -> {- if expSize e > 3
                                                      then Bad "Subexp too large"
                                                      else -} return $ (v, e):c)
    in patternLkUp v c 
getPatternMapping _ _ _ = Nothing

-- evaluate the sequence with given functions to predict the answer
-- without anthropomorphic computations

eval ::    Exp   -- expression to evaluate
        -> [Int] -- number sequence
        -> Int   -- element number in sequence
        -> Int   -- starting value for index variable n
        -> Int   -- 
        -> (Bool, Int) -- returns false if evaluation successful
eval e sq i start rc =
    case (e) of
        EAdd a b -> let (b1, a1) = eval a sq i start rc
                        (b2, a2) = eval b sq i start rc
                    in if (b1 || b2) then (True, 0) else overflowCheck ((toInteger a1) + (toInteger a2))
        EMul a b -> let (b1, a1) = eval a sq i start rc
                        (b2, a2) = eval b sq i start rc
                    in if (b1 || b2) then (True, 0) else overflowCheck ((toInteger a1) * (toInteger a2))
        ESub a b -> let (b1, a1) = eval a sq i start rc
                        (b2, a2) = eval b sq i start rc
                    in if (b1 || b2) then (True, 0) else overflowCheck ((toInteger a1) - (toInteger a2))
        EDiv a b  -> let (b1, a1) = eval a sq i start rc
                         (b2, a2) = eval b sq i start rc
                     in if (b1 || b2 || a2 == 0 || rem a1 a2 /= 0)
                            then (True, 0)
                            else (False, div a1 a2)
        EExp a b -> let (b1, a1) = eval a sq i start rc
                        (b2, a2) = eval b sq i start rc
                    in if (b1 || b2 || (a1 > 1 && a2 > 10) || a2 < 0) then (True, 0) else overflowCheck ((toInteger a1) ^ (toInteger a2))
        EInt a -> (False, fromInteger a)
        -- EVar nIdent -> (sq !! i /= i, sq !! i)
        -- ENeg a -> let (b1, a1) = eval a sq i rc
        ENeg a -> let sq' = (map (* (-1)) sq)
                      (b1, a1) = eval a sq' i start rc
                  in if (b1) then (True, 0) else overflowCheck (toInteger ((-1) * a1))
        ERec b exp@(ENeg a) ->
            if i < fromInteger b
                then (False, sq !! i)
                else let sq' = (map (* (-1)) sq)
                         (b1, a1) = eval a sq' i start rc
                     in if (b1) then (True, 0) else overflowCheck (toInteger a1)
                     -- eval exp sq i rc
        
        ERec b exp -> if i < fromInteger b
                          then (False, sq !! i)
                          else eval exp sq i start rc
        EF b ->
            if i < fromInteger b
                     then (False, sq !! i)
                     else (False, sq !! (i - fromInteger b))
        EFunc name arg -> if name == fIdent
         then
            case (evalExpr arg) of
                    Nothing -> (True,0)
                    Just v  -> if ((fromInteger v) + start) < length sq
                        then (False, sq !! ((fromInteger v) + start))
                        else (True, 0)
                    -- eval (EF (toInteger i - v)) sq i rc
         else
          let z@(b1, a1) = eval (arg) sq i start (rc + 1)
          in let q = if (b1 || rc > 20)
                       then (True, 0)
                       else let e' = EFunc name (EInt (toInteger a1))
                                mappings = [(getPatternMapping e' a [], b) | (a, b) <- []]
                                emptymappings = [b | (Just [], b) <- mappings]
                                emptymapping = if null emptymappings then ENull else head emptymappings
                                realmappings = [replace m b | (Just m, b) <- mappings, not $ null m]
                                realmapping = if null realmappings
                                     then ENull
                                     else if null (realmappings)
                                            then ENull
                                            else (head realmappings)
                            in if emptymapping /= ENull
                                  then eval emptymapping sq i start (rc + 1)
                                  else if realmapping /= ENull
                                         then eval realmapping sq i start (rc + 1)
                                         else (True, 0)
          in seq z q
        _ -> (True,0)

diffs :: TClosure -> TClosure
diffs [] = []
diffs [x] = []
diffs (a:(x:xs)) = (x-a):(diffs (x:xs))

replace :: [(String,Exp)] -> Exp -> Exp
replace m p = 
    case p of
        EAdd a b            -> EAdd (replace m a) (replace m b)
        ESub a b            -> ESub (replace m a) (replace m b)
        EMul a b            -> EMul (replace m a) (replace m b)
        EDiv a b            -> EDiv (replace m a) (replace m b)
        EExp a b            -> EExp (replace m a) (replace m b)
        ENeg a              -> ENeg (replace m a)
        EFunc fn arg        -> EFunc fn (replace m arg)
        EVar (Ident v)  -> case lookup v m of
                                     Just e  -> e
                                     _       -> p
        n'                  -> n'

ratios :: TClosure -> TClosure
ratios [] = []
ratios [x] = []
ratios (a:(x:xs))
    | a /= 0 = (x `div` a):(ratios (x:xs))
    | otherwise = ratios (x:xs)

getClosure :: TClosure -> TClosure
getClosure [] = []
getClosure xs =
    let diffs' = diffs xs
        ratios' = ratios xs
    in nub $ filter (/=0) $ map abs $ xs ++ diffs' ++ ratios' ++ getClosure diffs' ++ getClosure ratios'

-- returns list of lists where sum of each list is same
funcLengths :: Int        -- sum
               -> Int     -- size of lists
               -> [[Int]] -- list of lists where each list's elements add up to sum
funcLengths 0 _ = []
funcLengths _ 0 = []
funcLengths a 1 = [[a]]
funcLengths a 2 = [[x,y] | (x, y) <- zip [1..(a-1)] [(a-1),(a-2)..1]]
funcLengths a b = concat [map ([i]++) (funcLengths (a - i) (b - 1)) | i <- [1..a]]

-- Generate non-recursive candidate functions
generateNonRec :: Int -> StateT SContext IO [(Exp)]
generateNonRec explen =
    do SCtx (closure,sq,_,_,_) <- get
       let nonrecfuncs' =
               [[getFuncs closure fl 0 fn | (fl, fn) <- zip d staticFuncs] |
                     c <- [1..3],
                     d <- funcLengths explen c]
       let result = concat [[(head h) | h <- combine x] | x <- nonrecfuncs']
       return result

-- Generate recursive candidate functions
generateRec :: Int -> Int -> StateT SContext IO [(Exp)]
generateRec explen maxrec =
    do  SCtx (closure,sq,_,_,_) <- get
        let recfuncs' =
               [([getFuncs closure fl b fn | (fl, fn) <- zip d staticFuncs], b) |
                     b <- [1..maxrec],
                     c <- [1..3],
                     -- d <- funcLengths (explen - b + 1) c]
                     d <- funcLengths (explen) c]
        let recfuncs = recfuncs'
        return $
              concat [[(ERec (toInteger b) (head h)) | 
                           h <- combine x, bc <- getBaseCases (length x - 1), validReferences h b] | (x, b) <- recfuncs]

generateRec2 :: Int -> Int -> POrder -> StateT SContext IO [(Exp)]
generateRec2 explen maxrec order =
    do  SCtx (closure,sq,_,_,_) <- get
        if explen < 3
          then do
            let recfuncs =
                 [([getFuncs closure fl b fn | (fl, fn) <- zip d staticFuncs], b) |
                     b <- [1..maxrec],
                     c <- [1..3],
                     -- d <- funcLengths (explen - b + 1) c]
                     d <- funcLengths (explen) c]
            return $
              concat [[(ERec (toInteger b) (head h)) |
                           h <- combine x, bc <- getBaseCases (length x - 1), validReferences h b] | (x, b) <- recfuncs]
          else do
               --if explen < 5
               --   then do
                    let result = concat [f (EF (toInteger n)) | n <- [1..maxrec], x <- [0..(n)], f <- [getFuncs2 sq closure explen x order]]
                    return result
               --   else do
               --     let explen' = explen - 2
               --     let result' = concat [f (EF (toInteger n)) | n <- [1..maxrec], x <- [0..(n)], f <- [getFuncs2 sq closure explen' x order]]
               --     let result  = concat [f r | r <- result', f <- [getFuncs2 sq closure explen 0 order]]
               --     return result

-- generateCandidates :: Int -> Int -> IndexShift -> POrder -> StateT SContext IO [(Exp, Start, Dir, TFuncs)]
generateCandidates :: Int -> Int -> IndexShift -> POrder -> StateT SContext IO [Pattern]
generateCandidates maxrec explen shift order =
    do SCtx (_,sq,indices,_,_) <- get
       let param = if order > maxOrder (length sq) then 1 else 2
       cands    <- generateRec2    explen maxrec order
       let result' = [ Pattern order start dir [f] |
                        f <- cands,
                        (start,dir,e) <- evaluate f sq indices shift,
                        and e && length e >= param   ]
       result <-
        if order > 1 && order <= maxOrder (length sq)
          then do let ind' = mapIndices (length sq) order
                  let fs' = drop 1 [ [f | f <- cands, (start,dir,e) <- evaluate f sq ind shift, and e && length e >= 2 ] | ind <- (ind') ]
                  let fs = [ (if length f >= 1 then head f else (ENull) ) | f <- fs']
                  if (any (== ENull) fs)
                      then return []
                      else return [ (Pattern order start dir (f++fs)) | (Pattern order start dir f) <- result']
          else
            if order > 1 && order > maxOrder (length sq)
              then do
                let ind' = mapIndices (length sq) order
                let fs' = drop 1 [ [f | f <- cands, (start,dir,e) <- evaluate f sq ind shift, and e && length e >= 1 ] | ind <- ind' ]
                let fs = [ (if length f >= 1 then head f else (ENull) ) | f <- fs']
                let lastlength = if (length fs) == 0
                                    then 0
                                    else length $ dropWhile (< fromInteger (getRec (last fs))) (last ind')
                if (any (== ENull) fs) || (lastlength <= 1)
                  then return []
                  else do
                    let p1 = [ (Pattern order start dir (f++fs)) | (Pattern order start dir f) <- result']
                    let p2 = filter (\p@(Pattern _ _ _ fs) -> (hamming p) <= 7
                                                              && (length $ last ind') > 1
                                                              && sameRec fs) p1
                    return p2
              else return result'
       return $ result

getRec :: Exp -> Integer
getRec (ERec n _) = n
getRec _          = 0

sameRec :: [Exp] -> Bool
sameRec [] = True
sameRec (x:xs) = and (map (\y -> getRec y == recx) xs)
    where recx = getRec x

-- Humming distance between multiple expressions in a pattern
hamming :: Pattern -> Int
hamming (Pattern _ _ _ []) = 0
hamming (Pattern order start dir (x:xs)) = x' + y'
    where   x' = expLength x
            y' = sum (map hamming' $ zip (x:xs) xs)

hamming' :: (Exp,Exp) -> Int -- hamming distance between two expressions
hamming' (ENeg e1, ENeg e2) = hamming' (e1,e2)
hamming' (EFunc i1 e1,EFunc i2 e2) = if i1==i2 then hamming' (e1,e2)
                                               else hamming' (e1,e2) + 1
hamming' (ERec _ e1,ERec _ e2) = hamming' (e1,e2)
hamming' (EAdd e11 e12, EAdd e21 e22) = hamming' (e11,e21) + hamming' (e12,e22)
hamming' (ESub e11 e12, ESub e21 e22) = hamming' (e11,e21) + hamming' (e12,e22)
hamming' (EMul e11 e12, EMul e21 e22) = hamming' (e11,e21) + hamming' (e12,e22)
hamming' (EDiv e11 e12, EDiv e21 e22) = hamming' (e11,e21) + hamming' (e12,e22)
hamming' (EExp e11 e12, EExp e21 e22) = hamming' (e11,e21) + hamming' (e12,e22)
hamming' (EEqual e11 e12, EEqual e21 e22) = hamming' (e11,e21) + hamming' (e12,e22)
hamming' (e1,e2) = if e1==e2 then 0 else 1

mapIndices :: Int -> POrder -> [Indices]
mapIndices len order | order < 1 = []
mapIndices len order = takeWhile (\x -> length x > 0) $ map (mapIndices' len order) [0..]

-- debug for order 4
mapIndices' :: Int -> POrder -> Int -> Indices
mapIndices' sqlen' order n | order <= n = []
mapIndices' sqlen' order n =
    let sqlen = sqlen' - 1
        ind = reverse [(sqlen - i) | i <- [0..sqlen], (i+n) `mod` order == (order-1) ]
    in case length ind of
        0 -> ind
        _ -> case head ind of
                0 -> tail ind
                _ -> ind

-- returns [(start,dir,tests)], where dir=+1 for increasing and -1 for decreasing
evaluate :: Exp -> [Int] -> [Int] -> IndexShift -> [(Start,Dir,[Bool])]
evaluate (ERec b f) sq indices shift =
            [(start,dir,
                    [ let (b1, a1)  =
                            eval (substAll f (EVar nIdent, EInt (toInteger (start+dir*i))))  sq i start 0
                      in  if b1 then False else a1 == (sq !! i) | i <- indices, i >= (fromInteger b)  ] )
                      --in  if b1 then False else a1 == (sq !! i) | (i,i') <- (zip indices [0..]), i >= (fromInteger b)  ] )
                -- | start <- [minN..maxN], dir <- [1,-1] ]
                | start <- (if shift then [minN..maxN] else [0]), dir <- [1] ]
evaluate f sq indices shift =
            [(start,1,
                    [ let (b1, a1)  = eval (substAll f (EVar nIdent, EInt (toInteger (start+dir*i)))) sq i start 0
                      in  if b1 then False else a1 == (sq !! i) | i <- indices ])
                      --in  if b1 then False else a1 == (sq !! i) | (i,i') <- (zip indices [0..]) ])
                -- | start <- [minN..maxN], dir <- [1,-1]  ]
                | start <- (if shift then [minN..maxN] else [0]), dir <- [1]  ]

-- predict  :: predict the answer without using anthropomorphism
--             from the given candidates
predict ::    Int          -- length for formulas
           -> [Pattern] -- generated candidates
           -> StateT SContext IO [(Pattern, Int)]  -- [(formula,userfuncs),prediction]
predict d cands = do
    SCtx (_,sq,indices,_,_) <- get
    if not (null cands) then do
        let lensq = length sq
        let lenid = length indices
        let ps1 = [( p, map ((flip substAll) (EVar nIdent, (EInt (toInteger (start+dir*lensq))))) cs )
                            | p@(Pattern order start dir cs) <- cands]
        let ps = [(p, eval (head s) sq lensq start 0)  |  (p@(Pattern _ start _ _), s) <- ps1]
        let ps' = [(p, a) | (p, (b, a)) <- ps, not b]
        -- let ps'' = nubBy (\((a,_),_) ((b,_),_) -> a == b) $ ps'
        let ps'' = nubBy nubPatterns . sortBy sortCand $ ps'
        io $ putStrLn ("Found " ++ show (length ps'') ++ " candidates of length " ++ show (d))
        io $ sequence_ $ map putStrLn (map (\(pat@(Pattern ord start dir (cand:_)),p) -> show pat ++ ", start: " ++ show start ++ ", dir: " ++ show dir ++ ", prediction: " ++ (show p)) ps'')
        -- return [((cand,udfs),p) | ((cand,_,_,udfs),p) <- ps'']-- ps''
        return ps''
      else return []

--nubPatterns :: ((Exp, Int, Dir, TFuncs), Int) -> ((Exp, Int, Dir, TFuncs), Int) -> Bool
--nubPatterns ((e1,_,_,_),p1) ((e2,_,_,_),p2) =
nubPatterns :: (Pattern, Int) -> (Pattern, Int) -> Bool
nubPatterns ((Pattern _ _ _ (e1:_)),p1) ((Pattern _ _ _ (e2:_)),p2) =
    case (p1 == p2) of
        True -> e1 == e2 || similar (linearize e1) (linearize e2)
        False -> False

similar (ERec _ x) (ERec _ y) = similar x y
similar x@(EAdd (ESub x1 x2) x3) y@(ESub x4 (ESub x5 x6)) =
    x1==x4 && x2==x5 && x3==x6
similar x@(EAdd x11 x12) y@(EAdd x21 x22) = x == y || (EAdd x12 x11) == y
similar x@(EMul x11 x12) y@(EMul x21 x22) = x == y || (EMul x12 x11) == y
similar x y = x == y

-- Sort candidates whose predictions are available
-- sort first by lesser recursions, then by smaller predictions
--sortCand :: ((Exp, Int, Dir, TFuncs), Int) -> ((Exp, Int, Dir, TFuncs), Int) -> Ordering
--sortCand ((ERec n' p1, _, _, _),a) ((ERec m p2, _, _, _),b)
sortCand :: (Pattern, Int) -> (Pattern, Int) -> Ordering
sortCand ((Pattern _ _ _ ((ERec n' p1):_)),a) ((Pattern _ _ _ ((ERec m p2):_)),b)
    | n' > m = GT -- prefer less recursive
    | n' < m = LT -- prefer less recursive
    | n' == m && containsN p1 && (not (containsN p2)) = GT
    | n' == m && containsN p2 && (not (containsN p1)) = LT
    | otherwise = if a > b then GT else LT -- prefer short answers
sortCand ((Pattern _ _ _ (c:_)),a)   ((Pattern _ _ _ ((ERec _ p2):_)),b) = GT
--            if (not (containsN p2)) then GT else LT -- prefer recursive
sortCand ((Pattern _ _ _ ((ERec _ p1):_)),a)    ((Pattern _ _ _ (d:_)),b) = LT
--             if not (containsN p1) then LT else GT -- prefer recursive
sortCand ((Pattern _ _ _ (c:_)),a) ((Pattern _ _ _ (d:_)),b) = if a > b then GT else LT -- prefer short answers

io :: IO a -> StateT SContext IO a
io = liftIO

-- replace all occurences of EF x with f(n-x)
expandEF :: Exp -> Exp
expandEF (EF i) = EFunc fIdent (ESub (EVar nIdent) (EInt i))
expandEF (EEqual e1 e2) = EEqual (expandEF e1) (expandEF e2)
expandEF (EAdd e1 e2) = EAdd (expandEF e1) (expandEF e2)
expandEF (ESub e1 e2) = ESub (expandEF e1) (expandEF e2)
expandEF (EMul e1 e2) = EMul (expandEF e1) (expandEF e2)
expandEF (EDiv e1 e2) = EDiv (expandEF e1) (expandEF e2)
expandEF (EExp e1 e2) = EExp (expandEF e1) (expandEF e2)
expandEF (ENeg e1) = ENeg (expandEF e1)
expandEF (EFunc fn e1) = EFunc fn (expandEF e1)
expandEF (ERec n e1) = ERec n (expandEF e1)
expandEF e = e

evenSeq :: [Int] -> [Int]
evenSeq sq = if even (length sq)
                then [] -- [sq !! i | i <- [0..length sq - 1], even i]
                else [sq !! i | i <- [0..length sq - 1], odd i]

exceptionSeq :: [Int] -> [[Int]]
exceptionSeq sq = let iter = [x | x <- [1..(length sq - 2)]]
                  in [[i |(i,j) <- zip sq [0..], j /= x ] | x <- iter ]

lastSeq :: [Int] -> [[Int]]
lastSeq sq = let half = length sq `div` 2
             in [drop x sq | x <- [1..half]]

-- evaluate all f(n-k) terms with the sequence terms
-- evalF candidate N Start Sequence -> Exp
evalF :: Exp -> Int -> Int -> [Int] -> Exp
evalF e n' start sq = case e of
    (EF i) -> let n1 = toInteger n'
                  n2 = i
              in if (n1 >= n2 && (n1-n2) < toInteger (length sq))
                    then EInt (toInteger (sq !! (fromIntegral (n1-n2))))
                    else e
    (EFunc fIdent (ESub (EVar nIdent) (EInt n2)))
        -> let n1 = toInteger n'
           in if (n1 >= n2 && (n1-n2) < toInteger (length sq))
                then EInt (toInteger (sq !! (fromIntegral (n1-n2))))
                else e
    (EFunc fIdent (ESub (EInt n1) (EInt n2)))
        -> if (n1 >= n2 && (n1-n2) < toInteger (length sq))
             then EInt (toInteger (sq !! (fromIntegral (n1-n2))))
             else e
    (EFunc f e') -> EFunc f (evalF e' n' start sq)
    (ENeg e')    -> ENeg (evalF e' n' start sq)
    (ERec i e')  -> ERec i (evalF e' n' start sq)
    (EAdd e1 e2) -> EAdd (evalF e1 n' start sq) (evalF e2 n' start sq)
    (ESub e1 e2) -> ESub (evalF e1 n' start sq) (evalF e2 n' start sq)
    (EMul e1 e2) -> EMul (evalF e1 n' start sq) (evalF e2 n' start sq)
    (EDiv e1 e2) -> EDiv (evalF e1 n' start sq) (evalF e2 n' start sq)
    (EExp e1 e2) -> EExp (evalF e1 n' start sq) (evalF e2 n' start sq)
    (EEqual e1 e2) -> EEqual (evalF e1 n' start sq) (evalF e2 n' start sq)
    (EVar nIdent)   -> EInt (toInteger (n' + start))
    _  ->  e

snd3 (_,y,_) = y

-- Iteratively solve, with increasing formula lengths
-- print the output
seqSolve ::    Int      -- starting length of formulas
                  -> IndexShift   -- Bool: if true, apply index shifting
                  -> POrder
                  -> StateT SContext IO (Maybe Int)
seqSolve flen shift order = do
  SCtx (_,sq,ind,_,options) <- get
  if length sq < 3 || length ind < 1
    then return Nothing
    else do
          let maxrec =
                if length sq == length ind || (not limitRecLength)
                  then ceiling $ (fromInteger (toInteger (length sq - 1))) / 2.0
                  else length sq `div` length ind
          
          cands <- generateCandidates maxrec flen shift order

          candidates <- predict flen cands
          let candidates' = map (\((Pattern o s d xs),i) -> ((Pattern o s d (map expandEF xs)),i)) candidates
          let func = (\(pat@(Pattern o s d xs),p) ->  show pat  ++ ", prediction: " ++ (show p))
          if (length candidates') > 0
            then do
              io $ putStrLn "\nResult:"
              let h = head candidates'
              io $ putStrLn $ func h
              return (Just $ snd h)
            else return Nothing

----------------------------------------------------------
-- Calls seqIterativeSolve for the whole sequence
-- if not successful, applies other strategies to solve it
----------------------------------------------------------
 -- | length sq < 3 = do io $ putStrLn "Too short sequence!"
    --                     return ()
    -- | otherwise = do
solveInterative ::    Int      -- starting length of formulas
            -> Int      -- max length of formulas
            -> StateT SContext IO (Maybe Int)
solveInterative flen maxflen
    | flen > maxflen = do   io $ putStrLn "\nSorry! Failed to solve the sequence!"
                            return Nothing
    | otherwise = do
    SCtx (closure,sq,_,pctx,options) <- get
	
    if length sq < 3
      then do io $ putStrLn "Too short sequence!"
              return Nothing
      else do
        io $ putStrLn $ "\nTrying all formulas of length " ++ (show flen)
        io $ putStrLn $ "\nTrying with full sequence"
        let indices = [0..(length sq - 1)]
        put $ SCtx (closure,sq,indices,pctx,options)
        result <- seqSolve flen False 1
        case (result) of
          Just _  -> return result
          Nothing ->
            do io $ putStrLn "\nTrying simplified sequence: every second element"
               let indices = if even (length sq)
                               then [i | i <- [0..(length sq - 1)], even i ]
                               else [i | i <- [0..(length sq - 1)], odd  i ]
               put $ SCtx (closure,sq,indices,pctx,options)
               result1 <- seqSolve flen False 2
               case (result1) of
                 Just _  -> return result1
                 Nothing ->
                   do io $ putStrLn "\nTrying simplified sequence: every third element"
                      let len = (length sq - 1)
                      let indices' = reverse [(len - i) | i <- [0..len], i `mod` 3 == 2 ]
                      put $ SCtx (closure,sq,indices',pctx,options)
                      result2 <- seqSolve flen False 3
                      case result2 of
                        Just _  -> return result2
                        Nothing ->
                            do io $ putStrLn "\nTrying simplified sequence: every forth element"
                               let len = (length sq - 1)
                               let indices' = reverse [(len - i) | i <- [0..len], i `mod` 4 == 3 ]
                               put $ SCtx (closure,sq,indices',pctx,options)
                               result4 <- seqSolve flen False 4
                               case result4 of
                                Just _  -> return result4
                                Nothing ->
                                    do
                                      io $ putStrLn "\nTrying sequence with shifted index values (-9 to 9)"
                                      put $ SCtx (closure,sq,[0..(length sq - 1)],pctx,options)
                                      result3 <- seqSolve flen True 1
                                      case result3 of
                                        Just _  -> return result3
                                        Nothing -> solveInterative (flen + 1) maxflen

