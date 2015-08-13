module Amath.Proof (solve,showSol) where

--  NOTES:
--  The main program calls the proof function, providing an expression to solve.
--  The proof function uses the aStarM function from the AStar library to search
--  for a solution using the A* search algorithm.
--  
--  aStarM is the monadic verion of A* search. The StateMonad here is called
--  ContextMonad, which contains a Context as a reference. The Context contains
--  fixed parameters to be used in the search, such as the contents of ltm.txt
--  and pm.txt files (declarative memory and procedural memory).
--  
--  AStar search takes following functions to search for a goal.
--  aStarM :: (Monad m, Ord a, Ord c, Num c, Show a, Show c) =>
--     (a -> m (Set a))     -- ^ The graph we are searching through, given as a function from vertices
--                          -- to their neighbours. (ruleApplication function)
--     -> (a -> a -> m c)   -- ^ Distance function between neighbouring vertices of the graph. This will
--                          -- never be applied to vertices that are not neighbours, so may be undefined
--                          -- on pairs that are not neighbours in the graph. (stateDist function)
--     -> (a -> m c)        -- ^ Heuristic distance to the (nearest) goal. This should never overestimate the
--                          -- distance, or else the path found may not be minimal. (hDist function)
--     -> (a -> m Bool)     -- ^ The goal, specified as a boolean predicate on vertices. (isGoal function)
--     -> m a               -- ^ The vertex to start searching from. (the starting expression)
--     -> m (Maybe [a])     -- ^ Returns an optimal path, if any path exists.
--                          -- This excludes the starting vertex.
--  
--  SOLUTION:
--  The solution is a path in the graph from the initial expression to a goal.
--  A goal is a node containing solved expression (i.e., a single number). So any path
--  from the intial node to a solved expression is a valid solution. A* search
--  gives us the solution with minimum cost. The cost here is the length of a solution,
--  i.e. the number of steps to solve the expression.
--  
--  currently, there is a lot of code repetition which needs to be eliminated. Considering
--  the size of code, I hope this will not be an issue for grading the assignment.
--import Control.Parallel
--import Control.Parallel.Strategies
import Amath.Expr.AbsExp
import Amath.Types
import Amath.Rules
import Amath.Expr.ErrM
import Data.Char
import Data.List
import Data.Maybe
import qualified Data.Set as Set
import Amath.Astar
import Control.Monad.State
import Amath.Expr.ExprFuncs
import Data.Ord
import qualified Data.Map as Map
import Control.Parallel
-- import the parsing libraries
import Debug.Trace


-- Distance between two states.
-- Using size of the state as a cost. Searches for smallest proof
stateDist :: PState -> PState -> ContextMonad Int
--stateDist a@(PStart wm) b = return $ stateSize a + stateSize b
stateDist a b = return $ stateSize b -- return 1

-- Heuristic distance from a given state to the goal (solution) is the
-- minimum number of steps to achieve the goal. One possible definition
-- is the number of binary operators in the expression (WM in a state)
hDist :: PState -> ContextMonad Int
--hDist ps  = do goal <- isGoal ps
--               if goal then return 0 else return 1
-- hDist (PStart wm) = return $ (numop wm) ^ 2 + wmSize wm - numop wm - 2
hDist (PState _ _ wm _ _) = return $ (numop wm) ^ 2 + wmSize wm - numop wm - 2
-- hDist _ = return 100000

-- Determines if a state is a goal state, i.e. it is a valid solution
isGoal :: PState -> ContextMonad Bool
isGoal (PState _ _ (EInt x) _ _) = return True
isGoal (PState _ _ (EVar x) _ _) = return True
--isGoal (PState _ _ (ESub (EInt 0) (EInt x)) _ _) = return True
isGoal (PState _ _ (ENeg (EInt x)) _ _) = return True
isGoal (PState _ _ (ENeg (EVar x)) _ _) = return True
isGoal (PState _ _ (EAdd (EInt x) (EDiv (EInt y) (EInt z) )) _ _) = return (y<z)
isGoal (PState _ _ (EDiv (EInt y) (EInt z) ) _ _) = return (y<z)
isGoal _                       = return False

-- Determines if a state is a goal state, i.e. it is a Cutoff
-- this function is used if a real goal state cannot be found, so that
-- a partial solution can be generated. e.g., 25/3 does not have a valid solution,
-- but a partial solution will lead to 8+1/3
isGoal2 :: PState -> ContextMonad Bool
-- isGoal2 PCutoff = return True
isGoal2 _       = return False

-- returns the set of states returned by applying all the rules
ruleApplication :: PState -> ContextMonad (Set.Set PState)
-- ruleApplication PCutoff = return Set.empty
ruleApplication state = do
   (PCtx (_, wmsize, _, rules, _, _, pwm,_)) <- get
   let pwmlen = length pwm
   if pwmlen > 15 then return Set.empty
     else do
             let wm = getwm state
             let pwm = getpwm state
             let sub = subExpr wm True
             modify $ putSubExp wm pwm sub
             --s <- sequence $ parMap rwhnf applyRule rules
             s <- sequence $ map applyRule rules
             let union = Set.unions s --(trace (show s) s)
             let result = if Set.null union
                               then Set.empty -- Set.singleton PCutoff
                               else Set.filter (\x -> expSize (getwm x) <= wmsize) union
             return result -- (trace (show (pwmlen+1) ++ "\n") result)

-- Update the context with WM, subexpressions and previous WMs
putSubExp :: WM -> [WM] -> SubExp -> PContext -> PContext
putSubExp wm pwm sub (PCtx (a,b,c,d,_,_,_,sq)) = PCtx (a,b,c,d,sub,wm,pwm,sq)

getpwm :: PState      ->     [WM]
-- getpwm (PStart wm)          = [wm]
getpwm (PState _ _ _ _ pwm) = pwm

linState :: PState -> PState -- linearize the underlying WM
-- linState (PStart wm) = PStart (linearize wm)
linState (PState a b wm c d) = PState a b (linearize wm) c d
-- linState s = s

-- the main function that accepts an expression and returns its solution
solve :: Exp -> ContextMonad ([PState])
solve e     = do
   let lexp = linearize e
   let size = expSize lexp
   PCtx (_, wmsize, _, _, _, _, _,_) <- get
   if size > wmsize
     then return []
     else do
       --result1 <- aStarAllM ruleApplication stateDist hDist isGoal (return $ PStart lexp)
       result1 <- aStarAllM ruleApplication stateDist hDist isGoal (return $ PState Nothing Nothing lexp "" [])
       return $ if length result1 > 0 then (head result1) else []
--       if not . isNothing $ result1 then return result1
--          else aStarM ruleApplication stateDist hDist isGoal2 (return $ PStart lexp)

-- matches if the exp in the state is the same as the subgoal
isSubGoal :: Exp -> PState -> ContextMonad (Bool)
isSubGoal e (PState _ _ wm _ _) = return (e == wm)
isSubGoal _  _                  = return False

-- subgoal to reach a subgoal from the starting expression
subgoal :: Err Exp -> Err Exp -> ContextMonad (Maybe [PState])
subgoal (Ok startExp) (Ok goalExp) = do
   let lexp = linearize startExp
   let lgoal = linearize goalExp
   let size = expSize lexp
   PCtx (_, wmsize, _, _, _, _, _, _) <- get
   if size > wmsize
     then return Nothing
     else do
       --result1 <- aStarM ruleApplication stateDist hDist (isSubGoal lgoal) (return $ PStart lexp)
       result1 <- aStarM ruleApplication stateDist hDist (isSubGoal lgoal) (return $ PState Nothing Nothing lexp "" [])
       return result1
subgoal _ _ = return Nothing

search :: PState -> PState -> ContextMonad (Maybe [PState])
search start second = do
   states <- aStarM ruleApplication stateDist hDist isGoal (return second)
   if isNothing states then return (Just [second])
     else return (Just (second : fromJust states))

-- pretty printing of a solution
showSol :: Exp -> Maybe [PState] -> String -> String
showSol e Nothing   p = export [PState Nothing Nothing e "" []] p
showSol e (Just []) p = export [PState Nothing Nothing e "" []] p
-- showSol e (Just [PCutoff]) p = "showSol: Solution has zero states"
showSol e (Just xs) p = export ((PState Nothing Nothing e "" []):xs) p

export :: [PState] -> String -> String
export ps "--dm"  = "DM\n" ++ (unlines $ map ((flip export') "dm") ps)
export ps "--sm"  = "SM\n" ++ (unlines $ map ((flip export') "sm") ps)
export ps "--wm"  = "WM\n" ++ (unlines $ map ((flip export') "wm") ps)
export ps "--pm"  = "PM\n" ++ (unlines $ map ((flip export') "pm") ps)
export ps "--all" = 
  export ps "--dm" ++
  export ps "--sm" ++
  export ps "--wm" ++
  export ps "--pm"
export ps _ = showProof ps

export' :: PState -> String -> String
--export' (PStart wm)         "wm" = show wm
export' (PState _ _ wm _ _) "wm" = show wm
export' (PState _ _ wm "" _)   "pm" = "*"
export' (PState _ _ wm rule _) "pm" = show rule
-- export' (PState _ _ _ "" _) "sm" = "*"
export' (PState _ sm _ _  _) "sm" = if isNothing sm then "*" else show $ fromJust sm
-- export' (PState _ _ _ "" _)          "dm" = "*"
export' (PState dm _ _ _  _) "dm" = if isNothing dm then "*"
    else show (fst $ fromJust dm) ++ "=" ++ show (snd $ fromJust dm)

export' _  "wm" = ""

-- pretty printing of a solution
showProof :: [PState] -> String
showProof ps =
   let dm = [length (showEq dm) | PState (Just dm) _ _ _ _ <- ps]
       maxdm' = if dm == [] then 0 else maximum dm
       maxdm = max maxdm' 2
       sm = [length (show sm) | PState _ (Just sm) _ _ _ <- ps]
       maxsm' = if sm == [] then 0 else maximum sm
       maxsm = max maxsm' 2
       wm = [length (show wm) | PState _ _ wm _ _ <- ps] -- ++ [length (show wm) | PStart wm <- ps]
       maxwm' = if wm == [] then 0 else maximum wm
       maxwm = max maxwm' 2
       pm = [length (show pm) | PState (Just pm) _ _ _ _ <- ps]
       maxpm = if pm == [] then 0 else maximum pm
       maxlength = 5 + maxdm + 3 + maxsm + 3 + maxwm + 3 + maxpm
   in (showProof' ps maxdm maxsm maxwm maxpm)

showProof' :: [PState] -> Int -> Int -> Int -> Int -> String
showProof' states dm sm pm wm = unlines $ header : map (showState dm sm pm wm) states
  where
    header = stars ++"\n"++ header' ++"\n"++ stars
    header' = showFixed "DM" dm ++ " | " ++ showFixed "SM" sm ++ " | " ++
                (showFixed "WM" wm) ++ " | " ++ showFixed "PM" pm
    stars = take len (repeat '*')
    len = dm + 3 + sm + 3 + wm + 3 + pm

showState :: Int -> Int -> Int -> Int -> PState -> String
showState maxdm maxsm maxwm maxpm (PState _ _ wm "" _) =
  showFixed "*" maxdm ++ " | " ++ showFixed "*" maxsm ++ " | " ++ showWM wm maxwm ++ " | " ++ showFixed "*" maxpm
showState maxdm maxsm maxwm maxpm (PState dm sm wm pm _) =
  showDM dm maxdm ++ " | " ++ showSM sm maxsm ++ " | " ++ showWM wm maxwm ++ " | " ++ pm
-- showState maxdm maxsm maxwm maxpm (PCutoff) = ""
--  showFixed "*" maxdm ++ " | " ++ showFixed "*" maxsm ++ " | " ++ showWM wm maxwm ++ " | " ++ showFixed "*" maxpm

showDM :: Maybe Equation -> Int -> String
showDM Nothing n = "*" ++ take (n-1) (repeat ' ')
showDM (Just eq) n = showFixed (showEq eq) n

showSM :: Maybe Exp -> Int -> String
showSM Nothing n = "*" ++ take (n-1) (repeat ' ')
showSM (Just sm) n = showFixed (show sm) n

showWM :: Exp -> Int -> String
showWM wm n = showFixed (show wm) n

showPM :: PRule -> Int -> String
showPM rule n = showFixed (show rule) n

showFixed :: String -> Int -> String
showFixed str n = str ++ take (n-(length str)) (repeat ' ')

showEq :: Equation -> String
showEq (e1,e2) = show e1 ++ "=" ++ show e2
