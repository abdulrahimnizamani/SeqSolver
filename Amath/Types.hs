module Amath.Types where

import Amath.Expr.AbsExp
import Amath.Expr.ExprFuncs
import qualified Data.Map as Map
import Control.Monad.State

type Equation = (Exp,Exp) -- an equation is two equaivalent expressions, left and right

type DM = Equation -- Declarative Memory
type SM = Exp      -- Sensory Memory, not used in this version
type WM = Exp      -- Working Memory, i.e., the main expression that is manipulated
                   -- at every step in the solution
type TPrevWM = [WM]  -- Every state has to keep the previous expressions in memory,
                     -- in order to avoid a loop

type TMemSize    = Int
type TProofSize  = Int
type TExpOccPair = (Exp, Int)
type Ltm = Map.Map Exp Exp
--type Ltm = [Equation]     -- long term memory, or declarative memory contains a set of
                          -- equations, such as mathematical tables,
                          -- read from file ltm.txt

type PM = [PRule]   -- Procedural Memory (PM), the set of allowed rules, from pm.txt

-- Type for a function which implements any rule
type RuleFunc = Int -> WM -> [WM] -> Exp -> [PState]

-- Context for the StateMonad, including size of visual memory, size of working memory,
-- the contents of ltm.txt and pm.txt

type Seq = [Int]
type SubExp = [Exp] -- subexpressions to be used in context

-- Context contains: SM-size, WM-size, DM, rules,
--                   sub expressions, WM, PrevWM
newtype PContext = PCtx (TMemSize, TMemSize, Ltm, PM, SubExp, WM, [WM], Seq)
   deriving Show
type ContextMonad = State PContext  -- the StateMonad contains a Context

-- A state is a node in the search graph. The AStar search algorithm searches
-- for a path from the intial state (PStart) to a goal state where the WM
-- contains a single number. e.g. 2*3 is a start state and 6 is a goal state.
-- A path from the initial state to a goal state is a valid solution.
data PState =  PState (Maybe DM) (Maybe SM) WM String [WM]
             -- | PStart WM
             -- | PCutoff
  --deriving (Eq,Ord)

instance Eq PState where
    (==) = \x y -> getwm x == getwm y

instance Ord PState where
    compare x y = compare (getwm x) (getwm y)

stateShow :: PState -> String
-- stateShow (PStart wm)         = show wm
stateShow (PState _ _ wm _ _) = show wm
-- stateshow PCutoff             = "cutoff"

instance Show PState where
   show = stateShow

stateSize :: PState -> Int    -- size of a state
-- stateSize (PStart wm) = wmSize wm
stateSize (PState _ _ wm _ _) = wmSize wm
-- stateSize _ = 1

getwm :: PState      ->     WM
getwm (PState _ _ wm _ _) = wm
