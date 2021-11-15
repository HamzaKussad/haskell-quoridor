{-
    Module: Minimax.

    *** PART I (60pt) and PART II (10pt) *** 
-}
module Players.Minimax where 

import Data.Maybe
import Data.Graph
import Data.Ord
import Data.Tree
import Data.List
import Data.Array

import Types
import Constants
import Cell
import Action
import Board 
import Player
import Game
import Players.Dumb (dumbAction)

{-
    StateTree util.
-}

-- Map a function through the nodes of the tree.
mapStateTree :: (v -> w) -> StateTree v a -> StateTree w a
mapStateTree f (StateTree x ts) = StateTree (f x) [(a, mapStateTree f t) | (a, t)<-ts]

-- Calculate the depth of the tree (used to test pruneDepth).
stateTreeDepth :: StateTree v a -> Int 
stateTreeDepth (StateTree _ []) = 0
stateTreeDepth (StateTree _ ts) = 1 + (maximum (map (stateTreeDepth . snd) ts))

-- Calculate the breadth of the tree (used to test pruneBreadth).
stateTreeBreadth :: StateTree v a -> Int
stateTreeBreadth (StateTree _ []) = 0
stateTreeBreadth (StateTree _ ts) = max (length ts) (maximum (map (stateTreeBreadth . snd) ts))

{-
    Result util.
-}

-- Negating the result is simply negating the score. You may ignore this although it may be useful
-- to implement the minimax algorithm.
negResult :: Result -> Result
negResult (Result x as) = Result (-x) as

{- 
    *** Part I.a (10pt) ***

    First, we will generate a tree containing all the possible game states.
-}

-- Given a game, return a tree that encodes all the possible future game states.
-- [Hint: Use 'validActions' and 'performAction'.]
-- [Note: To speed things up, you may want to, at this stage, heuristically select which actions are 
--  more relevant. In particular, you probably don't want to consider every single possible wall.]
generateGameTree :: Game -> GameTree
generateGameTree v = StateTree v (map (\action -> (action, generateGameTree(fromJust(performAction v action)))) (validActions v))
    

{-
    *** PART I.b (5pt) ***

    Re-order the tree so that when traversed by the minimax algorithm, when it traverses the 
    branches at each node, finds either the higher scores or the lower scores first, depending on
    the depth of the tree.
-}

-- Higher scoring nodes go first.
-- [Hint: You should use 'lowFirst'.]
lowFirst :: (Ord v) => StateTree v a -> StateTree v a
lowFirst (StateTree v ts) = StateTree v (sortBy cmp ([(a,lowFirst t) | (a,t) <-ts]))
    where cmp (_, StateTree y _) (_, StateTree x _) = compare y x

{-
    *** Part I.c (5pt) ***

    We don't want to look at all possible future game states as that would consume too much time and
    memory. Instead, we will only look a given number of steps into the future. Formally, the future
    game states are encoded in a tree, so we need a function that reduces the depth of a tree.
-}

-- Given a depth and a tree, return the same tree but cutting off the branches when the depth is 
-- exceeded. 
-- [Hint: You may want to use guards and recursion.]
pruneDepth :: Int -> StateTree v a -> StateTree v a
pruneDepth n (StateTree v ts) 
    |n > 0 = StateTree v ([(a,pruneDepth (n-1) t) | (a,t) <- ts])
    |otherwise = StateTree v [] 
{-
    *** Part I.d (5pt) ***

    Similarly, we can also make our tree smaller by not considering all the possible game states at
    a given point. We need a function that reduces the breadth (or width) of a tree.
-}

-- Given a breadth (Int n) and a tree, return the same tree but only keeping the first n branches at
-- every node. 
-- [Hint: Use 'take'.]
pruneBreadth :: Int -> StateTree v a -> StateTree v a
pruneBreadth n (StateTree v ts) = StateTree v ([(a,pruneBreadth n t) | (a,t)<- take n ts ])

{-
    *** Part I.e (15pt) ***

    A crucial part of the minimax algorithm is defining a good utility function. It should measure
    how good a game position is for the current player. In our case, a game state should be better
    than another one if the player is closer to its winning positions.
-}

-- Assign a value to each game (from the point of view of the current player).
-- [Hint 1: You may want to calculate the distance between the player's current cell and its winning
--  positions.]
-- [Hint 2: One way would be to use 'reachableCells' repeatedly.]

utility :: Game -> Int
--utility (Game b p) = manhattanDist (reachableCells b (currentCell(head p))) (currentCell (head p))
utility (Game b p) = 25  - (astar b [] (currentCell (head p)) (winningPositions (head p)))

manhattanDist :: [Cell] -> Cell -> Int
manhattanDist ((_,w):_) (_,c) = abs(w-c)

astar :: Board -> [Cell] -> Cell ->[Cell] -> Int
astar b exploredList startPos endPos  | startPos `elem` endPos = -999
                                    | null (reachableCells b startPos) = 9999999
                                    | null (filter (`notElem` exploredList) (reachableCells b startPos)) = 99999
                                    | otherwise =  1 + minimum[(astar
                                 b updateExploredList branches endPos) + (manhattanDist updateExploredList branches) | branches <- (filter (`notElem` exploredList) (reachableCells b startPos))]
                                        where
                                            updateExploredList = exploredList ++ filter( `notElem` exploredList) (reachableCells b startPos)

-- Lifting the utility function to work on trees.
evalTree :: GameTree -> EvalTree 
evalTree = mapStateTree utility 

{-
    *** Part I.f (20pt) ***

    Finally, we ask you to implement the minimax algorithm. Given an evaluation tree, it should 
    return the a high scoring action (according to the minimax algorithm).
-}

-- Given an evaluation tree (it stores a score in the node and each branch is labelled with the 
-- action that leads to the next child) return a list of actions
-- [Hint 1: Use a helper function to keep track of the highest and lowest scores.]
-- [Hint 2: Use the 'Result' datatype.]

minimaxFromTree :: EvalTree -> Action
minimaxFromTree tree = resultToAction(minimaxFromTree' [] tree)

--minimaxFromTree :: EvalTree -> Action
--minimaxFromTree (StateTree i branches) = fst( maximumBy cmp [(m, -minimax' t) | (m,t)<-branches])
--    where cmp (_, x) (_, y) = compare x y

minimaxFromTree' :: [Action] -> EvalTree -> Result
minimaxFromTree' as (StateTree i [] ) = Result i as
minimaxFromTree' as (StateTree _ v) = negResult(minimum[(minimaxFromTree' (as ++ [a]) t) | (a,t) <- v])

resultToAction :: Result -> Action
resultToAction (Result i a) = head a

{-
    *** Part II (10pt) ***

    Extension of Part I.e, using alpha-beta pruning. You will need to change the 'minimax' function
    below to make it use this function.
-}

-- Same as above but now use alpha-beta pruning.
-- [Hint 1: Extend the helper function in I.e to keep track of alpha and beta.]
-- [Hint 2: Use the 'Result' datatype.]

minimaxABFromTree :: EvalTree -> Action
minimaxABFromTree tree = resultToAction(minimaxABFromTree' [] (Result (-9999999) []) (Result 9999999 []) tree) 

--minimaxABFromTree'Helper = Result
minimaxABFromTree' :: [Action] -> Result -> Result -> EvalTree -> Result
minimaxABFromTree' as a b (StateTree i []) =  a `max` (Result i as) `min` b 
minimaxABFromTree' as a b (StateTree _ v) = pruner a b v
    where 
        pruner x y [] = x
        pruner x y ((a,tree) : rest)
            |x'==y    = x'
            |otherwise = pruner x' y rest
                where x' =  negResult(minimaxABFromTree' (a:as) (negResult(y)) (negResult(x)) tree)

-- have been trying to fix the problem for weeks, dont know where the problem lies

{-
    Putting everything together.
-}

-- Given depth for pruning (should be even).
depth :: Int 
depth = 4

-- Given breadth for pruning.
breadth :: Int 
breadth = 10

-- Function that combines all the different parts implemented in Part I.
minimax :: Game -> Action
minimax =
      minimaxFromTree -- or 'minimaxABFromTree'
    . pruneBreadth breadth
    . lowFirst
    . evalTree
    . pruneDepth depth
    . generateGameTree 

-- Given a game state, calls minimax and returns an action.

exists :: Eq a => [a] -> [a] -> Bool
exists x y = any id $ (==) <$> x <*> y

minimaxAction :: Board -> [Player] -> String -> Int -> Maybe Action
minimaxAction b (p:ps) _ r 
                         = let g = Game b (p:ps) in minimaxAction' g (minimax g)
                            where 
                                -- Goes through the list of actions until it finds a valid one. 
                                minimaxAction' :: Game -> Action -> Maybe Action
                                minimaxAction' g' (Move s)
                                    | validStepAction g' s = Just (Move s)
                                    | otherwise = error "Minimax chose an invalid action."
                                minimaxAction' g' (Place w)
                                    | validWallAction g' w = Just (Place w)
                                    | otherwise = error "Minimax chose an invalid action."

-- Make minimaxPlayer in the usual way using 'minimaxAction'.
makeMinimaxPlayer :: String -> Cell -> Int -> [Cell] -> Player
makeMinimaxPlayer n c rws wps = Player {
    name = n,
    turn = 1,
    currentCell = c, 
    remainingWalls = rws,
    winningPositions = wps,
    isHuman = False,
    chooseAction = minimaxAction }


--stepTop (head(intersect (reachableCells b (currentCell (head ps))) (winningPositions(head ps)))))
--exists (reachableCells b (currentCell (p))) (winningPositions(p)) && (validWallAction (Game b(p:ps)) (wallTop (head(intersect (reachableCells b (currentCell (p))) (winningPositions(p))))))  = Just (Place (wallTop (head(intersect (reachableCells b (currentCell (p))) (winningPositions(p))))))