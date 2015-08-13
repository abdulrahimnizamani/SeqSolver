module Amath.Expr.ExprFuncs
            ( numop
            , wmSize
			, expSize
			, expLength
			, evalExpr
			, matches
			, applyPattern
			, getVarBinding
            , getVarBinding'
			, getVars
			, linearize
			, subExpr
			, isubExpr
            , transformExpr
			, substExpr
            , substAll
			, isPattern
            , parseExp
            , parsePM
            , argChanged
            , containsN
            , simplifyExp
            , parseDM
            , dropZeroWeighted
			  ) where

import Amath.Expr.LexExp
import Amath.Expr.ParExp
import Amath.Expr.AbsExp
import Amath.Expr.ErrM
import Amath.Expr.Digits as Dg

import Data.List
import qualified Data.Map as Map
import Control.Monad (liftM2)


{-
type ParseFun a = [Token] -> Err a

fromOK :: Err a -> a
fromOK (Ok e) = e
fromOK (Bad e) = error "fromOK: cannot be parsed."

isOk :: Err a -> Bool
isOk (Ok o)  = True
isOK (Bad b) = False

isBad :: Err a -> Bool
isBad (Bad _) = True
isBad _       = False

-}

myLLexer = myLexer  -- :: String -> [Token]

parseExp :: String -> Maybe Exp
parseExp str = case (pExp (myLLexer str)) of
                Ok a  -> Just a
                Bad _ -> Nothing

parsePM :: String -> Pmemory
parsePM s = case (pPmemory (myLLexer s)) of
                Ok a  -> a
                Bad _ -> Pmem []
{-
instance Show Exp where
   show = showExp

showExp :: Exp -> String
showExp (EAdd e1 e2) = showExp e1 ++ "+" ++ showExp e2
showExp (ESub e1 e2) = showExp e1 ++ "-" ++ showExp' e2
showExp (EMul e1 e2) = showFactor e1 ++ "*" ++ showFactor e2
showExp (EDiv e1 e2) = showFactor e1 ++ "/" ++ showExp' e2
showExp (EInt n) = show n
showExp (EVar v) = show v
showExp (EEqual e1 e2) = showExp e1 ++ "=" ++ showExp e2
showExp (EExp e1 e2) = "(" ++ showExp e1 ++ "^" ++ showExp e2 ++ ")"
showExp (ENeg e) = "-(" ++ showExp e ++ ")"
showExp (EFunc (Ident n) e1) = n ++ "(" ++ showExp e1 ++ ")"
showExp (ERec i e) = "Rec:(" ++ show i ++ "," ++ showExp e ++ ")" 
showExp (EF i) = "f(n-" ++ show i ++ ")"
showExp' (EInt n) = show n
showExp' (EVar v) = show v
showExp' e = "(" ++ showExp e ++ ")"

showExp' (EInt n) = show n
showExp' (EVar v) = show v
showExp' e = "(" ++ showExp e ++ ")"

showFactor :: Exp -> String
showFactor (EAdd e1 e2) = "(" ++ showExp e1 ++ "+" ++ showExp e2 ++ ")"
showFactor (ESub e1 e2) = "(" ++ showExp e1 ++ "-" ++ showExp e2 ++ ")"
showFactor     exp      = showExp exp
-}
numop :: Exp -> Int      -- Number of binary operators in the expression
numop (EAdd exp1 exp2) = 1 + numop exp1 + numop exp2
numop (ESub exp1 exp2) = 1 + numop exp1 + numop exp2
numop (EMul exp1 exp2) = 1 + numop exp1 + numop exp2
numop (EDiv exp1 exp2) = 1 + numop exp1 + numop exp2
numop (EExp exp1 exp2) = 1 + numop exp1 + numop exp2
numop (EEqual exp1 exp2) = 1 + numop exp1 + numop exp2
numop (ENeg exp1) = 1 + numop exp1
numop (EFunc _ exp1) = numop exp1
numop    _             = 0

expLength :: Exp -> Int  -- length, including lengths of integers
expLength e = expSize' e 1 (\n -> length (show n)) (\x -> length x)

intsize :: Integer -> Int
intsize n = length $ filter (/=0) $ Dg.digitsRev 10 n

wmSize :: Exp -> Int
wmSize e = expSize' e 1 (fromIntegral . intsize) (\_ -> 1)

expSize :: Exp -> Int
expSize = wmSize
--expSize e = expSize' e 1 (\x -> 1) (\x -> 1)

expSize' :: Exp -> Int -> (Integer -> Int) -> (String -> Int) -> Int    -- size of an expression
expSize' (EAdd exp1 exp2) op i v = op + expSize' exp1 op i v + expSize' exp2 op i v
expSize' (ESub exp1 exp2) op i v = op + expSize' exp1 op i v + expSize' exp2 op i v
expSize' (EMul exp1 exp2) op i v = op + expSize' exp1 op i v + expSize' exp2 op i v
expSize' (EDiv exp1 exp2) op i v = op + expSize' exp1 op i v + expSize' exp2 op i v
expSize' (EExp exp1 exp2) op i v = op + expSize' exp1 op i v + expSize' exp2 op i v
expSize' (EEqual exp1 exp2) op i v = op + expSize' exp1 op i v + expSize' exp2 op i v
--expSize' (EInt n)         t = if t then length (show n) else 1
expSize' (ENeg exp1) op i v = 1 + expSize' exp1 op i v
expSize' (EInt n)      op   i v = i n
expSize' (EVar (Ident str)) op i v = v str
expSize' (EFunc (Ident "f") xs) op i v = 1
expSize' (EFunc (Ident f) xs) op i v = op + expSize' xs op i v
expSize' (EF n) op i v = 1 -- fromInteger n
expSize' (ERec _ n) op i v = expSize' n op i v
expSize' ENull op i v = 0

evalExpr = eval
eval :: Exp -> Maybe Integer   -- evaluates an expression
eval (EAdd e1 e2) = liftM2 (+) (eval e1) (eval e2)
eval (ESub e1 e2) = liftM2 (-) (eval e1) (eval e2)
eval (EMul e1 e2) = liftM2 (*) (eval e1) (eval e2)
eval (EDiv e1 e2) = liftM2 div (eval e1) (eval e2)
eval (EExp e1 e2) = liftM2 (^) (eval e1) (eval e2)
eval (EInt n) = Just n
eval _ = Nothing

isPattern :: Exp -> Bool  -- an expression is a pattern if it contains variables
isPattern (EInt n) = False
isPattern (ENeg e1) = isPattern e1
isPattern (ERec i e1) = isPattern e1
isPattern (EVar _) = True
isPattern ENull = False
isPattern (EAdd e1 e2) = isPattern e1 || isPattern e2
isPattern (ESub e1 e2) = isPattern e1 || isPattern e2
isPattern (EDiv e1 e2) = isPattern e1 || isPattern e2
isPattern (EMul e1 e2) = isPattern e1 || isPattern e2
isPattern (EExp e1 e2) = isPattern e1 || isPattern e2
isPattern (EFunc name arg) = isPattern arg
isPattern (EEqual e1 e2) = isPattern e1 || isPattern e2


transformExpr :: Exp -> [(Exp,Exp)] -> [Exp]
transformExpr exp [] = []
transformExpr exp xs = map (applyPattern' exp) (filter (matchExpr exp . fst)  xs)

--transformExpr exp (x:xs) = if matches' exp (fst x)
--                            then (applyPattern' exp x):(transformExpr exp xs)
--                            else transformExpr exp xs
--transformExpr exp (x:xs) = (applyPattern exp x):(transformExpr exp xs)


-- rewrite an expression from a list of equivalent expressions (ltm)
rewriteExpr = expRewrite
exprewrite :: Exp -> [(Exp,Exp)] -> [Exp]
exprewrite exp [] = []
--exprewrite exp (x:xs) = if exp == fst x
exprewrite exp (x:xs) = if exp `matches` fst x
                            then (applyPattern exp x):(exprewrite exp xs)
                            else exprewrite exp xs

expRewrite :: Exp -> Map.Map Exp Exp -> [Exp]
--expRewrite exp [] = []
--exprewrite exp (x:xs) = if exp == fst x
expRewrite exp dmmap = case Map.lookup exp dmmap of
                            (Just x) -> [x]
                            Nothing -> []

matches :: Exp -> Exp -> Bool -- match a pattern to an expression
matches e1 e2 = if isPattern e2 then matches' e1 e2 else e1 == e2

matchExpr :: Exp -> Exp -> Bool
matchExpr e lhs = matches' e lhs && (clearBinding b == b)
 where
  b = nub $ binding e lhs []
  binding e (EInt _ ) xs = xs
  binding e (EVar id) xs = (id,e):xs
  binding (ENeg e1) (ENeg e2) xs = binding e1 e2 xs ++ xs
  binding (ERec i1 e1) (ERec i2 e2) xs = if i1 == i2 then binding e1 e2 xs ++ xs else xs
  binding (EAdd e1 e2) (EAdd exp1 exp2) xs = binding e1 exp1 xs ++ binding e2 exp2 xs ++ xs
  binding (ESub e1 e2) (ESub exp1 exp2) xs = binding e1 exp1 xs ++ binding e2 exp2 xs ++ xs
  binding (EMul e1 e2) (EMul exp1 exp2) xs = binding e1 exp1 xs ++ binding e2 exp2 xs ++ xs
  binding (EDiv e1 e2) (EDiv exp1 exp2) xs = binding e1 exp1 xs ++ binding e2 exp2 xs ++ xs
  binding (EExp e1 e2) (EExp exp1 exp2) xs = binding e1 exp1 xs ++ binding e2 exp2 xs ++ xs
  binding (EFunc n1 e1) (EFunc n2 exp1) xs =
      if n1 == n2 then binding e1 exp1 xs ++ xs else xs
  

matches' :: Exp -> Exp -> Bool
matches' (EAdd e11 e12) (EAdd e21 e22) = matches' e11 e21 && matches' e12 e22
matches' (ESub e11 e12) (ESub e21 e22) = matches' e11 e21 && matches' e12 e22
matches' (EMul e11 e12) (EMul e21 e22) = matches' e11 e21 && matches' e12 e22
matches' (EDiv e11 e12) (EDiv e21 e22) = matches' e11 e21 && matches' e12 e22
matches' (EExp e11 e12) (EExp e21 e22) = matches' e11 e21 && matches' e12 e22
matches' (EFunc n1 e1) (EFunc n2 e2)   = n1 == n2 && matches' e1 e2
matches' (ENeg e1) (ENeg e2)           = matches' e1 e2
matches' (ERec i1 e1) (ERec i2 e2)     = i1 == i2 && matches' e1 e2
matches' e1 (EVar id) = True
matches' e1 e2 = e1 == e2

applyPattern :: Exp -> (Exp,Exp) -> Exp
applyPattern e (lhs,rhs) =
   if isPattern lhs && length binding > 0
        then if isPattern rhs then apply'' rhs binding else rhs
        else if (e == lhs) then rhs else e
   where
     binding = getVarBinding e lhs
--apply (EAdd e1 e2) ((EAdd exp1 exp2),rhs)

applyPattern' :: Exp -> (Exp,Exp) -> Exp
applyPattern' e (lhs,rhs) =
   if length binding > 0
        then apply'' rhs binding
        else e
   where
     binding = getVarBinding e lhs

getVarBinding' :: Exp -> Exp -> [(Exp,Exp)]
getVarBinding' e lhs = map (\(x,y) -> (EVar x, y)) (getVarBinding e lhs)

getVarBinding :: Exp -> Exp -> [(Ident,Exp)]
getVarBinding e lhs = clearBinding . nub $ binding e lhs []
 where
  binding e (EInt _ ) xs = xs
  binding e (EVar id) xs = (id,e):xs
  binding (ENeg e1) (ENeg e2) xs = binding e1 e2 xs
  binding (ERec i1 e1) (ERec i2 e2) xs = if i1 == i2 then binding e1 e2 xs ++ xs else xs
  binding (EAdd e1 e2) (EAdd exp1 exp2) xs = binding e1 exp1 xs ++ binding e2 exp2 xs ++ xs
  binding (ESub e1 e2) (ESub exp1 exp2) xs = binding e1 exp1 xs ++ binding e2 exp2 xs ++ xs
  binding (EMul e1 e2) (EMul exp1 exp2) xs = binding e1 exp1 xs ++ binding e2 exp2 xs ++ xs
  binding (EDiv e1 e2) (EDiv exp1 exp2) xs = binding e1 exp1 xs ++ binding e2 exp2 xs ++ xs
  binding (EExp e1 e2) (EExp exp1 exp2) xs = binding e1 exp1 xs ++ binding e2 exp2 xs ++ xs
  binding (EEqual e1 e2) (EEqual exp1 exp2) xs = binding e1 exp1 xs ++ binding e2 exp2 xs ++ xs
  binding (EFunc n1 e1) (EFunc n2 e2) xs =
     if n1 == n2 then binding e1 e2 xs ++ xs else xs

apply' :: Exp -> Exp -> Ident -> Exp
apply' e exp id =
  case e of
    (EVar id')   -> if id == id' then exp else (EVar id')
    (EInt n)     -> (EInt n)
    (ENeg e1)    -> ENeg (apply' e1 exp id)
    (EAdd e1 e2) -> EAdd (apply' e1 exp id) (apply' e2 exp id)
    (ESub e1 e2) -> ESub (apply' e1 exp id) (apply' e2 exp id)
    (EMul e1 e2) -> EMul (apply' e1 exp id) (apply' e2 exp id)
    (EDiv e1 e2) -> EDiv (apply' e1 exp id) (apply' e2 exp id)
    (EFunc n e1) -> EFunc n (apply' e1 exp id)
    (EF n)       -> EF n

apply'' :: Exp -> [(Ident,Exp)] -> Exp
apply'' e [] = e
apply'' e ((id,exp):xs) = apply'' e' xs
  where
    e' = apply' e exp id

getVars :: Exp -> [Ident]
getVars (EVar id) = [id]
getVars (EInt _ ) = []
getVars (EAdd e1 e2) = getVars e1 ++ getVars e2
getVars (ESub e1 e2) = getVars e1 ++ getVars e2
getVars (EMul e1 e2) = getVars e1 ++ getVars e2
getVars (EDiv e1 e2) = getVars e1 ++ getVars e2

first = fst $ head ltm
second = snd $ head ltm

bind :: [(Ident, Exp)]
bind = [(Ident "x",EInt 25),(Ident "y",EInt 25),(Ident "x",EInt 5),(Ident "y",EInt 6),(Ident "z",EInt 30)]

clearBinding :: [(Ident, Exp)] -> [(Ident, Exp)]
clearBinding xs = nubBy' (\(x,y) (p,q) -> x==p) xs
  where
    nubBy' eq []      =  []
    nubBy' eq (x:xs)  =  if (length nubbed == length (xs))
                             then x : nubbed
                             else nubbed
      where
        nubbed = nubBy' eq (filter (\ y -> not (eq x y)) xs)

-- Linearize an expression
linearize = lin
lin :: Exp -> Exp
lin e = case e of
   (EAdd (EAdd a b) (ESub c d)) -> lin $ EAdd (lin a) (lin (EAdd b (ESub c d)))
   (EAdd (EAdd a b) c)          -> lin $ EAdd (lin a) (lin (EAdd b c))
   (EMul (EMul a b) (EDiv c d)) -> lin $ EMul (lin a) (lin (EMul b (EDiv c d)))
   (EMul (EMul a b) c)          -> lin $ EMul (lin a) (lin (EMul b c))
   (EAdd a b)          -> EAdd (lin a) (lin b)
   (ESub a b)          -> ESub (lin a) (lin b)
   (EDiv a b)          -> EDiv (lin a) (lin b)
   (EMul a b)          -> EMul (lin a) (lin b)
   (EFunc name exp)    -> EFunc name (lin exp)
   e                   -> e

-- indexed list of sub expressions
isubExpr :: Exp -> Bool -> [(Exp,Int)]
isubExpr e atomic = indexedList $ subExpr e atomic

indexedList :: Ord t => [t] -> [(t, Int)]
indexedList explst = concat $ map ((flip zip) [1..]) (group $ sort explst)

-- Subexpressions of an expression
-- Requies the input to be linearized before calling this function
subExpr = sub
sub :: Exp       -- input expression, linearized
       -> Bool   -- whether atomic expressions are to be included
       -> [Exp]  -- list of all subexpressions
sub exp t = map lin $ case exp of
  (EAdd a e@(EAdd b c)) -> sub a t ++ sub (EAdd a b) t ++ sub e t ++ [exp] ++ subAdd (EAdd a b) c
  (EAdd a e@(ESub b c)) -> sub a t ++ sub (EAdd a b) t ++ sub e t ++ [exp]
  (EAdd a b)            -> sub a t ++ sub b t ++ [exp]
  (EMul a e@(EMul b c)) -> sub a t ++ sub (EMul a b) t ++ sub e t ++ [exp] ++ subMul (EMul a b) c
  (EMul a e@(EDiv b c)) -> sub a t ++ sub (EMul a b) t ++ sub e t ++ [exp]
  (EMul a b)            -> sub a t ++ sub b t ++ [exp]
  (ESub (EAdd a b) c)   -> sub a t ++ sub (EAdd a b) t ++ sub (ESub b c) t ++ [exp]
  (ESub a b)            -> sub a t ++ sub b t ++ [exp]
  (EDiv (EMul a b) c)   -> sub a t ++ sub (EMul a b) t ++ sub (EDiv b c) t ++ [exp]
  (EDiv a b)            -> sub a t ++ sub b t ++ [exp]
  (EFunc name expr)     -> sub expr t ++ [exp]
  --(ENeg (EInt n))       -> if t then [exp] else []
  --(ENeg (EVar v))       -> if t then [exp] else []
  (ENeg a)              -> sub a t ++ [exp]
  (EInt n)              -> if t then [exp] else []
  (EVar v)              -> if t then [exp] else []
  (EF i)                -> [exp]

subAdd :: Exp -> Exp -> [Exp]
subAdd e1 e2 = case e2 of
  (EAdd a b) -> [EAdd e1 a] ++ subAdd (EAdd e1 a) b
  _          -> []

subMul :: Exp -> Exp -> [Exp]
subMul e1 e2 = case e2 of
  (EMul a b) -> [EMul e1 a] ++ subMul (EAdd e1 a) b
  _          -> []

-- substitute all occurences of an expression with another in the given exp
-- return the original exp if no occurence found
substAll :: Exp          -- exp in which to substitute
            -> (Exp, Exp) -- replace all occurences of first with second
            -> Exp        -- return the new exp
substAll wm p@(fst,snd) = if wm == fst then snd else case wm of
   (EAdd a b) -> EAdd (substAll a p) (substAll b p)
   (ESub a b) -> ESub (substAll a p) (substAll b p)
   (EMul a b) -> EMul (substAll a p) (substAll b p)
   (EDiv a b) -> EDiv (substAll a p) (substAll b p)
   (EExp a b) -> EExp (substAll a p) (substAll b p)
   (EFunc n a) -> EFunc n (substAll a p)
   (EEqual a b) -> EEqual (substAll a p) (substAll b p)
   (ENeg a)   -> ENeg (substAll a p)
   (ERec i a) -> ERec i (substAll a p)
   e          -> if e == fst then snd else e
  
-- substitute an expression, return multiple expressions each with one substitution
substExpr :: Exp             -- expression into which to substitute, linearized
             -> (Exp, Exp)   -- look for first expression, and replace with the second if found
             -> [Exp]          -- list of expressions with substitution
substExpr wm p =   nub
                 . filter (/= wm)
                 . map lin $ substExpr' wm p
substExpr' :: Exp -> (Exp,Exp) -> [Exp]
substExpr' wm p@(fst,snd) = if wm == fst then [snd] else case wm of
  (EAdd a (EAdd b c)) -> constructAdd a (EAdd b c) p ++ constructAdd (EAdd a b) c p
  (EAdd a (ESub b c)) -> constructAdd a (ESub b c) p ++ constructSub (EAdd a b) c p
  (EAdd a b)          -> constructAdd a b p
  (EMul a (EMul b c)) -> constructMul a (EMul b c) p ++ constructMul (EMul a b) c p
  (EMul a (EDiv b c)) -> constructMul a (EDiv b c) p ++ constructDiv (EMul a b) c p
  (EMul a b)          -> constructMul a b p
  (ESub (EAdd a b) c) -> constructAdd a (ESub b c) p ++ constructSub (EAdd a b) c p
  (ESub a b)          -> constructSub a b p
  (EDiv (EMul a b) c) -> constructMul a (EDiv b c) p ++ constructDiv (EMul a b) c p
  (EDiv a b)          -> constructDiv a b p
  (EFunc name arg)    -> map (\x -> EFunc name x) (substExpr arg p)
  (ENeg a)            -> map (\x -> ENeg x) (substExpr a p)
  e -> if e == fst then [snd] else [e]

constructAdd a b p = -- :: Exp -> Exp -> (Exp,Exp) -> [Exp]
  let a' = substExpr a p
      b' = substExpr b p
  in map (\e -> EAdd e b) a' ++ map (\e -> EAdd a e) b'

constructSub a b p = 
  let a' = substExpr a p
      b' = substExpr b p
  in map (\e -> ESub e b) a' ++ map (\e -> ESub a e) b'

constructMul a b p = -- :: Exp -> Exp -> (Exp,Exp) -> [Exp]
  let a' = substExpr a p
      b' = substExpr b p
  in map (\e -> EMul e b) a' ++ map (\e -> EMul a e) b'

constructDiv a b p = -- :: Exp -> Exp -> (Exp,Exp) -> [Exp]
  let a' = substExpr a p
      b' = substExpr b p
  in map (\e -> EDiv e b) a' ++ map (\e -> EDiv a e) b'

subst :: Exp -> [(Exp,Int)] -> Exp -> Exp
subst e1 e2s e3 = fst $ subst' 1 e1 e2s e3

subst' :: Int -> Exp -> [(Exp,Int)] -> Exp -> (Exp,Int)
subst' occ expr1 expr2s e =
    let (incr, found) = if fst (head expr2s) == e && (any (==occ) (map snd expr2s) || snd (head expr2s) == 0)
                            then (occ + 1, True) 
                            else (if fst (head expr2s) == e then (occ + 1) else occ, False)
    in if found
        then (expr1, incr)
        else case e of
                 EAdd a (EAdd b c) -> let (e1, i1) = subst' incr expr1 expr2s a
                                          (e2, i2) = subst' i1 expr1 expr2s (EAdd b c)
                                      in (EAdd e1 e2, i2)
                 EAdd a b          -> let (e1, i1) = subst' incr expr1 expr2s a
                                          (e2, i2) = subst' i1 expr1 expr2s b
                                      in (EAdd e1 e2, i2)
                 ESub a b          -> let (e1, i1) = subst' incr expr1 expr2s a
                                          (e2, i2) = subst' i1 expr1 expr2s b
                                      in (ESub e1 e2, i2)
                 EMul a (EMul b c) -> let (e1, i1) = subst' incr expr1 expr2s (EMul a b)
                                          (e2, i2) = subst' i1 expr1 expr2s c
                                      in (EMul e1 e2, i2)
                 EMul a b          -> let (e1, i1) = subst' incr expr1 expr2s a
                                          (e2, i2) = subst' i1 expr1 expr2s b
                                      in (EMul e1 e2, i2)
                 EDiv a b          -> let (e1, i1) = subst' incr expr1 expr2s a
                                          (e2, i2) = subst' i1 expr1 expr2s b
                                      in (EDiv e1 e2, i2)
                 _                 -> (e, incr)


-- some example expressions for testing
ex :: Exp
ex = EMul (EMul (EInt 1) (EInt 10)) (EMul (EMul (EInt 2) (EInt 3)) (EDiv (EInt 5) (EInt 9)))

{-
ex2 = fromOK $ parseExp "(50+3)/2"
ex2' = fromOK $ parseExp "(50+3)-20"

ex3 = fromOK $ parseExp "(x+y)/z"

ex4 = fromOK $ parseExp "x/z+y/z"
-}

ltm :: [(Exp,Exp)]
ltm = [(EDiv (EVar (Ident "x")) (EVar (Ident "x")),EInt 1)]

-- check if the argument of any function is changed in the two expressions
argChanged :: Exp -> Exp -> Bool
argChanged (EFunc f1 e1) (EFunc f2 e2) = if f1 == f2 then e1 /= e2 else False
argChanged (EF n1) (EF n2) = n1 /= n2
argChanged (EEqual e1 e2) (EEqual n1 n2) = argChanged e1 n1 || argChanged e2 n2
argChanged (EAdd e1 e2) (EAdd n1 n2) = argChanged e1 n1 || argChanged e2 n2
argChanged (ESub e1 e2) (ESub n1 n2) = argChanged e1 n1 || argChanged e2 n2
argChanged (EMul e1 e2) (EMul n1 n2) = argChanged e1 n1 || argChanged e2 n2
argChanged (EDiv e1 e2) (EDiv n1 n2) = argChanged e1 n1 || argChanged e2 n2
argChanged (EExp e1 e2) (EExp n1 n2) = argChanged e1 n1 || argChanged e2 n2
argChanged (ERec n1 e1) (ERec n2 e2) = if n1 == n2 then argChanged e1 e2 else False
argChanged _ _ = False

containsN :: Exp -> Bool
containsN e = case e of
  (EEqual a b)       -> containsN a || containsN b
  (EAdd a b)         -> containsN a || containsN b
  (EMul a b)         -> containsN a || containsN b
  (ESub a b)         -> containsN a || containsN b
  (EDiv a b)         -> containsN a || containsN b
  (EExp a b)         -> containsN a || containsN b
  (EFunc name expr)  -> if name == (Ident "f") then False else containsN expr
  (ENeg a)           -> containsN a
  (ERec _ a)         -> containsN a
  (EInt n)           -> False
  (EVar v)           -> v == Ident "n"
  (EF i)             -> False
  ENull              -> False

-- simplify an expression by adding, subtracting, multiplying or
-- dividing any constants (integers)
simplifyExp = simplify

simplify :: Exp -> Exp
simplify (ENeg e) = ENeg (simplify e)
simplify (EFunc f e) = EFunc f (simplify e)
simplify (ERec i e) = ERec i (simplify e)
simplify (EAdd (EInt i1) (EInt i2)) = EInt (i1+i2)
simplify (EAdd (EInt i1) (EAdd (EInt i2) e1)) = simplify $ EAdd (EInt (i1+i2)) e1
simplify (EAdd (EAdd e1 (EInt i1)) (EInt i2)) = simplify $ EAdd e1 (EInt (i1+i2)) 
simplify (EAdd e1 e2)   = EAdd (simplify e1) (simplify e2)
simplify (ESub (EInt i1) (EInt i2)) =
        if (i1-i2 >= 0) then (EInt (i1-i2)) else (ENeg (EInt (i2-i1)))
simplify (ESub e1 e2)   = ESub (simplify e1) (simplify e2)
simplify (EMul (EInt i1) (EInt i2)) = EInt (i1*i2)
simplify (EMul (EInt i1) (EMul (EInt i2) e1)) = simplify $ EMul (EInt (i1*i2)) e1
simplify (EMul (EMul e1 (EInt i1)) (EInt i2)) = simplify $ EMul e1 (EInt (i1*i2)) 
simplify (EMul e1 e2)   = EMul (simplify e1) (simplify e2)
simplify (EDiv (EInt i1) (EInt 0)) = EDiv (EInt i1) (EInt 0)
simplify e@(EDiv (EInt i1) (EInt i2)) =
        if (i1 `mod` i2 == 0) then EInt (i1 `div` i2) else e
simplify (EDiv e1 e2)   = EDiv (simplify e1) (simplify e2)
simplify (EExp (EInt i1) (EInt i2)) = EInt (i1 ^ i2)
simplify (EExp e1 e2)   = EExp (simplify e1) (simplify e2)
simplify (EEqual e1 e2) = EEqual (simplify e1) (simplify e2)
simplify e = e

-- parses the Ltm file, generating a list of equations.
-- an equation is a pair of expressions, i.e. left and right expression
parseDM :: String -> [(Exp,Exp)]
parseDM dmstr = [(e1,e2) | x@(Just (EEqual e1 e2)) <- temp]
   where temp = map (parseExp) (lines dmstr)

dropZeroWeighted :: Pmemory -> [PRule]
dropZeroWeighted (Pmem xs) = filter check' xs
  where
    check' x@(Rule name value list) = value > 0
