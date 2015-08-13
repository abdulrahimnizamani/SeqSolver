module Amath.Rules ( applyRule
                   , transformExp
                     ) where
import Amath.Expr.AbsExp
import Amath.Types
import Amath.Expr.ExprFuncs
import Control.Monad.State
import qualified Data.Set as Set
import qualified Amath.Expr.Digits as Dg
import qualified Data.Map as Map
import Data.List

-- apply a rule to a state, using the specific rule application function
-- and return the set of possible states resulting from this application
applyRule :: PRule -> ContextMonad (Set.Set PState)
applyRule r@(Rule (Ident "Inspect") _ _)       = inspectSeq "Inspect"
applyRule r@(Rule (Ident "Compress") _ _)      =
   do
      a <- compressAdd "Compress"
      b <- compressMul "Compress"
      return (Set.union a b)
applyRule r@(Rule (Ident "CommonFactor") _ _)  = cfactorRule "CommonFactor"
applyRule r@(Rule (Ident "Recall") _ _)        = recallRule "Recall"
applyRule r@(Rule (Ident "Expand") _ _)        = expandRule "Expand"
applyRule r@(Rule (Ident "Expand'") _ _)       = expandRule' "Expand'"
applyRule r@(Rule (Ident "ExpandDiv") _ _)     = expandDivRule "ExpandDiv"
applyRule r@(Rule (Ident "SimpleAdd") _ _)     = simpleAddRule "SimpleAdd"
applyRule r@(Rule (Ident "PowerAdd") _ _)      = powerAddRule "PowerAdd"
applyRule r@(Rule (Ident "UnitAdd") _ _)       = unitAddRule "UnitAdd"
applyRule r@(Rule (Ident "PowerMultiply") _ _) = pmulRule "PowerMultiply"
applyRule r@(Rule (Ident "Factors") _ _)       = factorRule "Factors"
applyRule r@(Rule (Ident "PowerSubtract") _ _) = psubRule "PowerSubtract"
applyRule r@(Rule (Ident "UnitSubtract") _ _)  = unitSubRule "UnitSubtract"
applyRule r@(Rule (Ident "PowerDivide") _ _)   = pdivRule "PowerDivide"
applyRule r@(Rule (Ident "Borrow") _ _)        = borrowRule "Borrow"
applyRule r@(Rule (Ident "Simplify") _ _)      = simplifyRule "Simplify"
applyRule r@(Rule (Ident name) _ xs) = transformExp (r)

-- Rule Application functions, one function for every rule

-- a general function for apply patterns
-- takes an equation with variables as a pattern
transformExp :: PRule -> ContextMonad (Set.Set PState)
transformExp (Rule _ 0 _)  = do return Set.empty -- don't apply
transformExp (Rule _ _ []) = do return Set.empty -- nothing to apply
transformExp (Rule (Ident ruleName) value rules) = do
   PCtx (_, wmsize, _, _, subexp,lwm,pwm,_) <- get
   --let rewlookup = [(exp, rewriteExpr exp rules) | exp <- subexp]
   let sub = subexp \\ [x | x@(EInt _) <- subexp]
   let rewlookup = [(exp, transformExpr exp (map makePair rules)) | exp <- sub]
   let rm   = [(se, lookup se rewlookup) | se <- sub]
   let rm'  = [(se, m) | (se, Just m) <- rm]
   let rm'' = concat [[(se, m') | m' <- m] | (se, m) <- rm']
   let fappl = (\(se, rew) -> 
         let rewritten = substExpr lwm (se, rew)
             rewritten' = [x | x <- rewritten, not $ x `elem` pwm, expSize x <= wmsize]
         in map (\x -> PState (Just (se, rew)) Nothing x ruleName (x:pwm)) rewritten')
   let states = Set.fromList $ concatMap fappl rm''
   return states

makePair :: Exp -> (Exp,Exp)
makePair x@(EEqual e1 e2) = (e1,e2)

identitySub :: String -> ContextMonad (Set.Set PState)
identitySub ruleName = do
  PCtx (smsize, wmsize, _, _, sub', lwm, pwm,_) <- get
  let sub1 = [(e,x) | e@(ESub (EInt x) (EInt 0)) <- sub']
  let sub2 = [e | e@(ESub (EInt x) (EInt y)) <- sub', x == y]
  let fappl1 = (\(e,x) -> 
        let rewritten = substExpr lwm (e, (EInt x))
            rewritten' = [x | x <- rewritten, not $ x `elem` pwm, expSize x <= wmsize]
        in map (\x -> PState Nothing Nothing x ruleName (x:pwm)) rewritten')
  let fappl2 = (\e -> 
        let rewritten = substExpr lwm (e, (EInt 0))
            rewritten' = [x | x <- rewritten, not $ x `elem` pwm, expSize x <= wmsize]
        in map (\x -> PState Nothing Nothing x ruleName (x:pwm)) rewritten')
  let states = Set.fromList $ (concatMap fappl1 sub1 ++ concatMap fappl2 sub2)
  return states --(trace (show states) states)

borrowRule :: String -> ContextMonad (Set.Set PState)
borrowRule ruleName = do
  PCtx (smsize, wmsize, _, _, sub', lwm, pwm,_) <- get
  let sub = [e | e@(ESub (EInt x) (EInt y)) <- sub',
                  length (Dg.digitsRev 10 x) > length (Dg.digitsRev 10 y)]
  let fappl = (\e@(ESub (EInt p) (EInt q)) -> 
        let qlen = length $ Dg.digitsRev 10 q
            val2 = 10 ^ qlen
            val1 = p - val2
            rewritten = substExpr lwm (e, (ESub (EAdd (EInt val1) (EInt val2)) (EInt q)))
            rewritten' = if val1 < 1 then [] else [x | x <- rewritten, not $ x `elem` pwm, expSize x <= wmsize]
        in map (\x -> PState Nothing Nothing x ruleName (x:pwm)) rewritten')
  let states = Set.fromList $ concatMap fappl sub
  return states --(trace (show states) states)

-- PowerDivide rule. e.g. 60/3 = 20 if 6/3=2 is in DM
pdivRule :: String -> ContextMonad (Set.Set PState)
pdivRule ruleName = do
  PCtx (_, wmsize, ltm, _, sub',lwm,pwm,_) <- get
  let sub = [(x, powerDiv x) | x@(EDiv (EInt n1) (EInt n2)) <- sub'] -- shortlist subexpressions
  let psub   = [(se, m) | (se, Just m) <- sub]
  -- let psub = [y | Just y <- [powerDiv x | x <- sub]] -- get Just values from powerMul
  let rewlookup = [(exp, Map.lookup exp ltm) | (org,(exp,n)) <- psub]
  let rewlookup' = [(exp,e) | (exp,Just e) <- rewlookup]
  let rm   = [(org,(se,n), lookup se rewlookup') | (org,(se,n)) <- psub]
  let rm'  = [(org,n,m) | (org,(se,n), Just m) <- rm]
  --let rm'' = concat [[(se, (EInt (m' * n))) | (EInt m') <- m] | (se,n, m) <- rm']
  let rm'' = [(se, (EInt (m' * n))) | (se,n, (EInt m')) <- rm']
  
  let result = concatMap (fppl ruleName wmsize pwm lwm) rm''
  return $ Set.fromList result

-- Helper for pdivRule function. e.g. extracts 9/9 from 90/9
powerDiv :: Exp -> Maybe (Exp,Integer) -- returns (Exp,Power)
powerDiv e@(EDiv (EInt n1) (EInt n2)) =
        -- count number of digits
        let digits1 = Dg.digitsRev 10 n1
            digits2 = Dg.digitsRev 10 n2
            len1 = length digits1
            len2 = length digits2
        -- count number of leading zeros (e.g. two in 100)
            zeros1 = length $ takeWhile (==0) digits1
            zeros2 = length $ takeWhile (==0) digits2
            n1' = Dg.unDigits 10 . reverse $ dropWhile (==0) digits1
            n2' = Dg.unDigits 10 . reverse $ dropWhile (==0) digits2
        in if zeros1 > zeros2 && n1 /= n1' && n1 /=0 && n2 /= 0
               then Just ( (EDiv (EInt n1') (EInt n2)), 10 ^ zeros1)
               else if zeros1 > 0 && zeros2 > 0
                       then Just ( (EDiv (EInt n1') (EInt n2)), 10 ^ zeros1)
                       else Nothing

-- PowerMultiply rule. e.g. 3*40 = 120 if 3*4=12 is in DM
pmulRule :: String -> ContextMonad (Set.Set PState)
pmulRule ruleName = do
  PCtx (_, wmsize, ltm, _, sub',lwm,pwm,_) <- get
  let sub = [x | x@(EMul (EInt n1) (EInt n2)) <- sub'] -- shortlist subexpressions
  let psub = [y | Just y <- [powerMul x | x <- sub]] -- get Just values from powerMul
  let rewlookup = [(exp, Map.lookup exp ltm) | (org,(exp,n)) <- psub]
  let rewlookup' = [(exp,e) | (exp,Just e) <- rewlookup]
  let rm   = [(org,(se,n), lookup se rewlookup') | (org,(se,n)) <- psub]
  let rm'  = [(org,n,m) | (org,(se,n), Just m) <- rm]
  --let rm'  = [(org,(EInt m*n)) | (org,(se,n), Just (EInt m)) <- rm]
  let rm'' = [(se, (EInt (m' * n))) | (se,n, (EInt m')) <- rm']
  --let rm'' = concat [[(se, m') | m' <- m] | (se, m) <- rm']
  
  let fappl = (\(se, rew) ->
         let rewritten = substExpr lwm (se, rew)
             rewritten' = [x | x <- rewritten, not $ x `elem` pwm, expSize x <= wmsize]
         in map (\x -> PState (Just (se, rew)) Nothing x ruleName (x:pwm)) rewritten')
  let states = Set.fromList $ concatMap fappl $ rm''
  return states --(trace (show states) states)

-- helper for pmulRule function. e.g. extracts 3*4 from 3*40
powerMul :: Exp -> Maybe (Exp, (Exp,Integer)) -- returns (Exp,Power)
powerMul e@(EMul (EInt n1) (EInt n2)) =
        -- count number of digits
        let digits1 = Dg.digitsRev 10 n1
            digits2 = Dg.digitsRev 10 n2
            len1 = length digits1
            len2 = length digits2
        -- count number of leading zeros (e.g. two in 100)
            zeros1 = length $ takeWhile (==0) digits1
            zeros2 = length $ takeWhile (==0) digits2
            n1' = Dg.unDigits 10 . reverse $ dropWhile (==0) digits1
            n2' = Dg.unDigits 10 . reverse $ dropWhile (==0) digits2
        in if zeros1 < zeros2 && n2 /= n2' && n1 /= 0 && n2 /= 0
             then Just (e, ( (EMul (EInt n1) (EInt n2')), 10 ^ zeros2))
             else if zeros1 > zeros2 && n1 /= n1' && n1 /=0 && n2 /= 0
                    then Just (e, ( (EMul (EInt n1') (EInt n2)), 10 ^ zeros1))
                    else if zeros1 > 0 && zeros2 > 0
                            then Just (e, ( (EMul (EInt n1') (EInt n2)), 10 ^ zeros1))
                            else Nothing

-- PowerSubtract rule. e.g. 50-20=30 if 5-2=3 is in DM
psubRule :: String -> ContextMonad (Set.Set PState)
psubRule ruleName = do
  PCtx (_, wmsize, ltm, _, sub',lwm,pwm,_) <- get
  let sub = [x | x@(ESub (EInt n1) (EInt n2)) <- sub'] -- shortlist subexpressions
  let psub = [y | Just y <- [powerSub x | x <- sub]] -- get Just values from powerAdd
  let rewlookup = [(exp, Map.lookup exp ltm) | (org,(exp,n)) <- psub]
  let rewlookup' = [(exp,e) | (exp,Just e) <- rewlookup]
  let rm   = [(org,(se,n), lookup se rewlookup') | (org,(se,n)) <- psub]
  let rm'  = [(org,n,m) | (org,(se,n), Just m) <- rm]
  --let rm'  = [(org,(EInt m*n)) | (org,(se,n), Just (EInt m)) <- rm]
  let rm'' = [(se, (EInt (m' * n))) | (se,n, (EInt m')) <- rm']
  --let rm'' = concat [[(se, m') | m' <- m] | (se, m) <- rm']
  
  let fappl = (\(se, rew) ->
         let rewritten = substExpr lwm (se, rew)
             rewritten' = [x | x <- rewritten, not $ x `elem` pwm, expSize x <= wmsize]
         in map (\x -> PState (Just (se, rew)) Nothing x ruleName (x:pwm)) rewritten')
  let states = Set.fromList $ concatMap fappl rm''
  return states --(trace (show states) states)

-- helper for psubRule. e.g. extracts 5-2 from 50-20
powerSub :: Exp -> Maybe (Exp, (Exp,Integer)) -- returns (Exp,Power)
powerSub e@(ESub (EInt n1) (EInt n2)) =
        -- count number of digits
        let digits1 = Dg.digitsRev 10 n1
            digits2 = Dg.digitsRev 10 n2
            len1 = length digits1
            len2 = length digits2
        -- count number of leading zeros (e.g. two in 100)
            zeros1 = length $ takeWhile (==0) digits1
            zeros2 = length $ takeWhile (==0) digits2
            minzeros = min zeros1 zeros2
            n1' = Dg.unDigits 10 . reverse $ dropWhile (==0) digits1
            n2' = Dg.unDigits 10 . reverse $ dropWhile (==0) digits2
            n1'' = n1' * 10 ^ (zeros1 - minzeros)
            n2'' = n2' * 10 ^ (zeros2 - minzeros)
        in if n1 > n2 && n1 /= n1'' && n2 /= n2'' && n1 /= 0 && n2 /= 0
             then Just (e, ( (ESub (EInt n1'') (EInt n2'')), 10 ^ minzeros))
             else Nothing

-- PowerAdd rule. e.g. 40+50=90 if 4+5=9 is in DM
simpleAddRule :: String -> ContextMonad (Set.Set PState)
simpleAddRule ruleName = do
  PCtx (_, wmsize, ltm, _, sub',lwm,pwm,_) <- get
  let sub = [x | x@(EAdd (EInt n1) (EInt n2)) <- sub'] -- shortlist subexpressions
  let psub = [y | Just y <- [simpleAdd x | x <- sub]] -- get Just values from simpleAdd
  let rewlookup = [(exp,Map.lookup exp ltm) | (org,(exp,n)) <- psub]
  let rewlookup' = [(exp,e) | (exp,Just e) <- rewlookup]
  let rm   = [(org,(se,n), lookup se rewlookup') | (org,(se,n)) <- psub]
  let rm'  = [(org,n,m) | (org,(se,n), Just m) <- rm]
  let rm'' = [(se, (EInt (m' + n)))| (se,n, (EInt m')) <- rm']
  let fappl = (\(se, rew) ->
         let rewritten = substExpr lwm (se, rew)
             rewritten' = [x | x <- rewritten, not $ x `elem` pwm, expSize x <= wmsize]
         in map (\x -> PState (Just (se, rew)) Nothing x ruleName (x:pwm)) rewritten')
  let states = Set.fromList $ concatMap fappl rm''
  return states --(trace (show states) states)

-- helper for powerAddRule function. e.g. extracts 4+5 from 40+50
simpleAdd :: Exp -> Maybe (Exp, (Exp, Integer)) -- returns (Exp,Power)
simpleAdd e@(EAdd (EInt n1) (EInt n2)) =
     let dg1 = Dg.digitsRev 10 n1
         dg2 = Dg.digitsRev 10 n2
     in  if (n1 > 0 && n1 < 10 && (head dg2) /= 0 &&
            n1 + (head dg2) <= 10 && n2 > 10) then
                Just (e, (EAdd (EInt n1) (EInt (head dg2)), n2 - (head dg2)))
            else if (n2 > 0 && n2 < 10 && (head dg1) /= 0 && 
                     n2 + (head dg1) <= 10 && n1 > 10) then
                        Just (e, (EAdd (EInt n2) (EInt (head dg1)), n1 - (head dg1)))
                    else Nothing

fppl :: String -> TMemSize -> TPrevWM -> WM ->(Exp,Exp) -> [PState]
fppl ruleName wmsize pwm lwm (se,rew) =
         let rewritten = substExpr lwm (se, rew)
             rewritten' = [x | x <- rewritten, not $ x `elem` pwm, expSize x <= wmsize]
         in map (\x -> PState (Just (se, rew)) Nothing x ruleName (x:pwm)) rewritten'

-- PowerAdd rule. e.g. 40+50=90 if 4+5=9 is in DM
powerAddRule :: String -> ContextMonad (Set.Set PState)
powerAddRule ruleName = do
  PCtx (_, wmsize, ltm, _, sub',lwm,pwm,_) <- get
  let sub = [x | x@(EAdd (EInt n1) (EInt n2)) <- sub'] -- shortlist subexpressions
  let psub = [y | Just y <- [powerAdd x | x <- sub]] -- get Just values from powerAdd
  let rewlookup = [(exp,Map.lookup exp ltm) | (org,(exp,n)) <- psub]
  let rewlookup' = [(exp,e) | (exp,Just e) <- rewlookup]
  let rm   = [(org,(se,n), lookup se rewlookup') | (org,(se,n)) <- psub]
  let rm'  = [(org,n,m) | (org,(se,n), Just m) <- rm]
  let rm'' = [(se, (EInt (m' * n))) | (se,n, (EInt m')) <- rm']
  let states = Set.fromList $ concatMap (fppl ruleName wmsize pwm lwm) rm''
  return states --(trace (show states) states)

-- helper for powerAddRule function. e.g. extracts 4+5 from 40+50
powerAdd :: Exp -> Maybe (Exp, (Exp,Integer)) -- returns (Exp,Power)
powerAdd e@(EAdd (EInt n1) (EInt n2)) =
        -- count number of digits
        let digits1 = Dg.digitsRev 10 n1
            digits2 = Dg.digitsRev 10 n2
            len1 = length digits1
            len2 = length digits2
        -- count number of leading zeros (e.g. two in 100)
            zeros1 = length $ takeWhile (==0) digits1
            zeros2 = length $ takeWhile (==0) digits2
            n1' = Dg.unDigits 10 . reverse $ dropWhile (==0) digits1
            n2' = Dg.unDigits 10 . reverse $ dropWhile (==0) digits2
        in if zeros1 == zeros2 && n1 /= n1' && n2 /= n2' && n1 /= 0 && n2 /= 0
             then Just (e, ( (EAdd (EInt n1') (EInt n2')), 10 ^ zeros1))
             else Nothing

-- UnitAdd rule. e.g. 34+5=39 if 4+5=9 is in DM
unitAddRule :: String -> ContextMonad (Set.Set PState)
unitAddRule ruleName = do
  PCtx (_, wmsize, ltm, _, sub',lwm,pwm,_) <- get
  let sub = [(x,n1 `mod` 10) | x@(EAdd (EInt n1) (EInt n2)) <- sub',
                n2 > 0, n2 < 10, n1 > 10] -- shortlist subexpressions
  let psub = [(e,((EAdd (EInt (m)) (EInt n2)),n1-m))
                 | (e@(EAdd (EInt n1) (EInt n2)),m) <- sub,
                      m/=0, m+n2 <=10] -- further shortlist
  let rewlookup = [(exp,Map.lookup exp ltm) | (org,(exp,n)) <- psub]
  let rewlookup' = [(exp,e) | (exp,Just e) <- rewlookup]
  let rm   = [(org,(se,n), lookup se rewlookup') | (org,(se,n)) <- psub]
  let rm'  = [(org,n,m) | (org,(se,n), Just m) <- rm]
  let rm'' = [(se, (EInt (m' + n))) | (se,n, (EInt m')) <- rm']
  let states = Set.fromList $ concatMap (fppl ruleName wmsize pwm lwm) rm''
  return states --(trace (show states) states)

-- UnitAdd rule. e.g. 34+5=39 if 4+5=9 is in DM
unitSubRule :: String -> ContextMonad (Set.Set PState)
unitSubRule ruleName = do
  PCtx (_, wmsize, ltm, pm, sub',lwm,pwm,_) <- get
  let sub = [(x,n1 `mod` 10) | x@(ESub (EInt n1) (EInt n2)) <- sub',
                n2 > 0, n2 < 10, n1 > 10] -- shortlist subexpressions
  let psub = [(e,((ESub (EInt m) (EInt n2)),n1-m))
                 | (e@(ESub (EInt n1) (EInt n2)),m) <- sub,
                      m/=0, m>n2] -- further shortlist
  let psub' = [(e,(EInt (n1-n2)))
                 | (e@(ESub (EInt n1) (EInt n2)),m) <- sub,
                      m/=0, m==n2]
  let rewlookup = [(exp,Map.lookup exp ltm) | (org,(exp,n)) <- psub]
  let rewlookup' = [(exp,e) | (exp,Just e) <- rewlookup]
  let rm   = [(org,(se,n), lookup se rewlookup') | (org,(se,n)) <- psub]
  let rm'  = [(org,n,m) | (org,(se,n), Just m) <- rm]
  let rm'' = [(se, (EInt (n + m'))) | (se,n, (EInt m')) <- rm']
  let rm''' = if (ifElem "IdentitySub" pm) then rm'' ++ psub' else rm''
  let states = Set.fromList $ concatMap (fppl ruleName wmsize pwm lwm) rm'''
  return states --(trace (show states) states)

ifElem :: String -> [PRule] -> Bool
ifElem s xs = if any (==s) (map (\x@(Rule (Ident n) _ _) -> n) xs) then True else False
--ifElem s (x@(Rule (Ident ruleName) _ _):xs) = if x==ruleName then True else ifElem s xs

-- TenMultiply rule. e.g. 33*100 = 3300 (similar to compress rule for addition)
compressMul :: String -> ContextMonad (Set.Set PState)
compressMul ruleName = do
  PCtx (_, wmsize, ltm, pm, sub',lwm,pwm,_) <- get
  let sub = [(x,(EInt (n1*n2))) | x@(EMul (EInt n1) (EInt n2)) <- sub',
                 n1 /= 0, powerOfTen n2] -- shortlist subexpressions
  let states = Set.fromList $ concatMap (fppl ruleName wmsize pwm lwm) sub
  return states --(trace (show states) states)

-- Factors rule. e.g. rewrites 30 as 3*10
factorRule :: String -> ContextMonad (Set.Set PState)
factorRule ruleName = do
  PCtx (smsize, wmsize, _, _, sub',lwm,pwm,_) <- get
  --let sub'' = [x | x@(EMul e1 e2) <- sub'] ++ [x | x@(EDiv e1 e2) <- sub']
  let sub = concat [[(x,EMul (EInt p) (EInt q)) | (p,q) <- factorize n] | x@(EInt n) <- sub']
  let result = concatMap (fppl ruleName wmsize pwm lwm) sub
  return $ Set.fromList result --(trace (show result) result)

-- Factorize multiples of 10. e.g. factorize 120 = (12,10)
factorize :: Integral a => a -> [(a,a)]
factorize n = 
  let digits = Dg.digitsRev 10 n
      zeros  = length $ takeWhile (==0) digits
  in  [(n `div`(10 ^ x),10^x) | x <- [1..zeros]]
  --    val    = dropWhile (==0) digits
  --in  (Dg.unDigits 10 $ reverse val,10 ^ zeros)

-- Expand rule. e.g. 39 is expanded to 30+9
expandRule :: String -> ContextMonad (Set.Set PState)
expandRule ruleName = do
  PCtx (smsize, wmsize, _, _, sub',lwm,pwm,_) <- get
  let sub = [x | x@(EInt n) <- sub']
  let fappl = (\e@(EInt n) -> 
        -- break the number into parts
        let digits = Dg.digits 10 n
        in if length digits > 1
             then let parts'' = expand [head digits] (tail digits)
                      parts' = map (\(x,y) -> (Dg.unDigits 10 x,Dg.unDigits 10 y)) parts''
                      parts = filter (\(x,y) -> if y == 0 then False else True) parts'
                      --first = fst $ fromJust parts
                      --second = snd $ fromJust parts
                      rewritten = concat $ map (\(x,y) -> [(e,(EAdd (EInt x) (EInt y)),v) | v <- substExpr lwm (e, (EAdd (EInt x) (EInt y)))]) parts
                      rewritten' = [(e1,e2,x) | (e1,e2,x) <- rewritten, not $ x `elem` pwm, expSize x <= wmsize]
                  in map (\(e1,e2,x) -> PState (Just (e1,e2)) Nothing x ruleName (x:pwm)) rewritten'
             else [])
  let states = Set.fromList $ concatMap fappl sub
  return states --(trace (show states) states)

-- helper for expandRule function. 
expand :: Integral a => [a] -> [a] -> [([a],[a])]
expand xs [] = []
expand [] ys = []
expand xs ys =
  [attachZeros xs ys]
   ++ expand (xs ++ [head ys])  (tail ys)
    where attachZeros xs ys = (xs++(take (length ys) (repeat 0)), ys)

-- Expand' rule. e.g. 39 is expanded to 40-1
expandRule' :: String -> ContextMonad (Set.Set PState)
expandRule' ruleName = do
  PCtx (smsize, wmsize, _, _, sub',lwm,pwm,_) <- get
  let sub = [(x,n `mod`10) | x@(EInt n) <- sub', n `mod` 10 >= 5, n /= 0]
  let rm = [(x,(ESub (EInt (n+10-m)) (EInt (10-m)))) | (x@(EInt n),m) <- sub]
  let states = Set.fromList $ concatMap (fppl ruleName wmsize pwm lwm) rm
  return states

-- ExpandDiv rule. e.g. 52 in (52/4) is expanded to 40+12
expandDivRule :: String -> ContextMonad (Set.Set PState)
expandDivRule ruleName = do
  PCtx (smsize, wmsize, _, _, sub',lwm,pwm,_) <- get
  let sub = [(x,expandDivRule' (m,n)) | x@(EDiv (EInt m) (EInt n)) <- sub', n > 1, n < 10, m > (n*10)]
  let sub2   = [(se, m) | (se, Just m) <- sub]
  let result = concatMap (fppl ruleName wmsize pwm lwm) sub2
  return $ Set.fromList result --(trace (show result) result)

expandDivRule' :: (Integer,Integer) -> Maybe Exp
expandDivRule' (m',n') =
  let m = fromInteger m'
      n = fromInteger n'
      dgs = Dg.digits 10 m
      mult a b = if (a * 10) < b then mult (a*10) b else a
      a = Dg.unDigits 10 $
            if (head dgs < n)
                then take 2 dgs
                else take 1 dgs
      b = a - (a `mod` n)
      c = mult b m
      d = m - c
      in Just (EDiv (EAdd (EInt c) (EInt d)) (EInt n))
        
{-
    let sub = [(x,simplifyDiv dm x) |  x@(EDiv (EInt n1) (EInt n2)) <- sub',
                                    n1 > n2,
                                    n1 < (n2*10),
                                    n1 `mod` n2 /= 0
              ]
    let sub2   = [(se, m) | (se, Just m) <- sub]
    let result = concatMap (fppl ruleName wmsize pwm lwm) sub2
    return $ Set.fromList result --(trace (show result) result)
-}
-- not used anymore. kept for reference
breakNum :: Integral a => a -> Maybe (a,a)
breakNum n
  | length (Dg.digitsRev 10 n) > 1 = 
          let dg = Dg.digits 10 n
              nonzero = filter (/=0) dg
          in if length nonzero > 1
                then let zeros = length $ takeWhile (==0) (Dg.digitsRev 10 n)
                         first = 10 ^ zeros * (foldr (\x y -> if y==0 then x else y) 0 dg)
                         revdigits = Dg.digitsRev 10 n
                         revdigits' = 0 : (tail . dropWhile (==0) $ revdigits)
                         second = Dg.unDigits 10 . reverse  $ (take zeros $ repeat 0) ++ revdigits'
                     in Just (second,first)
                else Nothing
  | otherwise = Nothing       

breakInt :: Integer -> Exp
breakInt num = foldr1 (\x y -> EAdd x y) (map (\x -> EInt x) xs)
  where
     xs = if (length y == 0) then [0] else y
     y = filter (/=0) x
     x = reverse $ zipWith (*) (Dg.digitsRev base num) powers
     base = 10
     powers = [base^y | y <- [0..]]

-- Compress Rule. e.g., 10 + 3 = 3, or 100+21=121
compressAdd :: String -> ContextMonad (Set.Set PState)
compressAdd ruleName = do
  PCtx (smsize, wmsize, _, _, sub',lwm,pwm,_) <- get
  let sub = [x | x@(EAdd (EInt n1) (EInt n2)) <- sub']
  let fappl = (\e@(EAdd (EInt n1) (EInt n2)) -> 
        -- count number of digits
        let len1 = length $ Dg.digitsRev 10 n1
            len2 = length $ Dg.digitsRev 10 n2
        -- count number of leading zeros (e.g. two in 100)
            zeros1 = length $ takeWhile (==0) (Dg.digitsRev 10 n1)
            zeros2 = length $ takeWhile (==0) (Dg.digitsRev 10 n2)
        in if n1 /= 0 && n2 /= 0
             then
               if (len2 <= zeros1) || (len1 <= zeros2)
                 then let rewritten = substExpr lwm (e, (EInt (n1+n2)))
                          rewritten' = [(e,(EInt (n1+n2)),x) | x <- rewritten, not $ x `elem` pwm, expSize x <= wmsize]
                      in map (\(e1,e2,x) -> PState (Just (e1,e2)) Nothing x ruleName (x:pwm)) rewritten'
                 else []
             else [])
  -- filter (/= []) $
  let states = Set.fromList $ concatMap fappl sub
  return states --(trace (show states) states)

-- common factor rule. e.g. extracts 3+2 from 30+20
cfactorRule :: String -> ContextMonad (Set.Set PState)
cfactorRule ruleName = do
  PCtx (smsize, wmsize, _, _, sub',lwm,pwm,_) <- get
  let sub = [x |  x@(EAdd (EInt n1) (EInt n2)) <- sub'] ++ [x |  x@(ESub (EInt n1) (EInt n2)) <- sub']
  let result = concatMap (cfactorRuleAppl ruleName wmsize lwm pwm) sub
  return $ Set.fromList result --(trace (show result) result)

-- inner rule application function for cfactorRule function. cfactorRule function above
-- is a generalized rule application function, and this generalization will be applied
-- to other functions in future to eliminate code repetition
cfactorRuleAppl :: String -> Int -> WM -> [WM] -> Exp -> [PState]
cfactorRuleAppl ruleName wmsize lwm pwm exp@(EAdd (EInt n1) (EInt n2)) =
        if powerOfTen2 n1 && powerOfTen2 n2
             then let factor = getLCM n1 n2
                      rewritten = substExpr lwm (exp, (EMul (EAdd (EInt (n1 `div` factor)) (EInt (n2 `div` factor))) (EInt factor)))
                      rewritten' = [x | x <- rewritten, not $ x `elem` pwm, expSize x <= wmsize]
                  in map (\x -> PState Nothing Nothing x ruleName (x:pwm)) rewritten'
             else []
cfactorRuleAppl ruleName wmsize lwm pwm exp@(ESub (EInt n1) (EInt n2)) =
        if powerOfTen2 n1 && powerOfTen2 n2
             then let factor = getLCM n1 n2
                      rewritten = substExpr lwm (exp, (EMul (ESub (EInt (n1 `div` factor)) (EInt (n2 `div` factor))) (EInt factor)))
                      rewritten' = [x | x <- rewritten, not $ x `elem` pwm, expSize x <= wmsize]
                  in map (\x -> PState Nothing Nothing x ruleName (x:pwm)) rewritten'
             else []

getLCM :: Integral a => a -> a -> a
getLCM a b = let adigits = length $ takeWhile (==0) $ Dg.digitsRev 10 a
                 bdigits = length $ takeWhile (==0) $ Dg.digitsRev 10 b
             in fromIntegral $ 10^ (min adigits bdigits)

-- Check if the number is 10,100,1000, ...
powerOfTen :: Integral a => a -> Bool
powerOfTen n = let s = dropWhile (==0) (Dg.digitsRev 10 n)
               in if length s /= 1 || head s /= 1 then False else True

-- Check if the number is 10,20,30 ...
powerOfTen2 :: Integral a => a -> Bool
powerOfTen2 n = let s = takeWhile (==0) (Dg.digitsRev 10 n)
                in if length s > 0 then True else False

-- Recall rule. application of Declarative Memory (dm.txt)
-- e.g., if 2*3=6 is in DM, then rewrite 2*3 into 6.
recallRule :: String -> ContextMonad (Set.Set PState)
recallRule ruleName = do
   PCtx (smsize, wmsize, ltm, _, subexp,lwm,pwm,_) <- get
   let rewlookup = [(exp, Map.lookup exp ltm) | exp <- subexp]
   let rm''   = [(se, m) | (se, Just m) <- rewlookup]
   --let rm   = [(se, lookup se rewlookup) | se <- subexp]
   --let rm'  = [(se, m) | (se, Just m) <- rm]
   --let rm'' = concat [[(se, m') | m' <- m] | (se, m) <- rm']
   let states = Set.fromList $ concatMap (fppl ruleName wmsize pwm lwm) rm''
   return states

-- Inspect rule. Recall a value from the sequence
-- e.g., replace f(5) with the 5th element of the sequence
inspectSeq :: String -> ContextMonad (Set.Set PState)
inspectSeq ruleName = do
   PCtx (smsize, wmsize, _, _, subexp,lwm,pwm,seq) <- get
   let seqlen = length seq
   let sub = [(x,(EInt (toInteger (seq!!(fromInteger i))))) | x@(EFunc (Ident f) (EInt i)) <- subexp, f == "f", (fromInteger i) < seqlen]
   
   --let sub' = [ (x,if n < 0 then (ENeg (EInt (abs(n)))) else e) | (x,e@(EInt n)) <- sub]
   let sub' =  [(x,(ENeg (EInt (abs n)))) | (x,e@(EInt n)) <- sub, n < 0] ++
               [(x,e) | (x,e@(EInt n)) <- sub, n >= 0]
   let states' = concatMap (fppl ruleName wmsize pwm lwm) sub'
   let states = if null states' then Set.empty else Set.singleton (head states')
   --return $ Set.fromList states'
   return states

-- Simplify : expands exps like (5/4) to (4+1)/4
simplifyRule :: String -> ContextMonad (Set.Set PState)
simplifyRule ruleName = do
    PCtx (smsize, wmsize, dm, _, sub',lwm,pwm,_) <- get
    let sub = [(x,simplifyDiv dm x) |  x@(EDiv (EInt n1) (EInt n2)) <- sub',
                                    n2 /= 0,
                                    n1 > n2,
                                    n1 < (n2*10),
                                    n1 `mod` n2 /= 0
              ]
    let sub2   = [(se, m) | (se, Just m) <- sub]
    let result = concatMap (fppl ruleName wmsize pwm lwm) sub2
    return $ Set.fromList result

simplifyDiv :: Map.Map Exp Exp -> Exp -> Maybe Exp
simplifyDiv dm (EDiv (EInt n1) (EInt n2)) =
    let n12 = n1 `mod` n2
        n11 = n1 - n12
        --add1 = EAdd (EInt n11) (EInt n12)
        --add2 = EAdd (EInt n12) (EInt n11)
    in --if (Map.member add1 dm || Map.member add2 dm)
        --then
        Just $ EDiv (EAdd (EInt n11) (EInt n12)) (EInt n2)
{-
ruleApply :: [String] -> ContextMonad (Set.Set PState)
ruleApply rules = do
    -- get subexpressions
    PCtx (smsize, wmsize, dm, _, sub',lwm,pwm,_) <- get
    -- apply all rules over every subexpression
    let sub = [(x,ruleName) | x <- sub', ruleName <- rules]
    let sub2 = [(x,) | (x,r) <- sub]
    let sub = concat [[(x,y) | y <- (simplifyDiv' ruleName x >>= return)] |  x <- sub']
    
    -- replace subexpressions with their newly computed equivalents
    let result = concatMap (fppl ruleName wmsize pwm lwm) sub
    -- return as a Set
    return $ Set.fromList result

simplifyDiv' :: String, Exp -> ContextMonad ([Exp],String)
simplifyDiv' rule (EDiv (EInt n1) (EInt n2))
  | n2 /= 0 && n1 > n2 && n1 < (n2*10) && n1 `mod` n2 /= 0
     = return ([EDiv (EAdd (EInt (n1 - n12)) (EInt n12)) (EInt n2)],rule)
        where n12 = n1 `mod` n2
simplifyDiv' _ = return []
-}
