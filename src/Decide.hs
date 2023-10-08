module Decide
       ( decide )
       where

import Proposition
import Inference

import Control.Arrow (second)
import Data.List (inits, tails)
import Data.Tuple (uncurry)

{-
-------------------------------------------------------------------------------
--  Main Proof Search Logic
-------------------------------------------------------------------------------
-}

{-
-- Decide if a proposition is provable.
--   if A has a proof, return True.
--   if A has no proof, return False.
--
-- Let me break down the proof search strategy:
-- (1) take the Prop and create a Sequent out of it
-- (2) try one rule at a time to see if can pick next Rule in proof;
--     (2a) exhaust all async rules first, starting with the right rules
--     (2b) based on inversion calculus, if right rules fail, switch to left
--     (2c) finally, try the sync rules (including init/id),
--       but be sure to note the Sequent in our stack so we can reverse it
--       if we reach a dead-end later;
--       we should also try to follow a single branch all the way to end first
--       before attempting to prove remaining branches, so move left to right
--     an important point to make is that for each Rule we test, we may
--     need to cycle thru the list of assumptions gamma to be sure we exhausted
--     all possibilities. So each Rule tester should be its own function
--     that can check if the Rule applies using *any* assumption Prop before
--     moving on to the next Rule
-- (3a) if reach an Init or Identity rule, we're done!
--      can now return that the Prop is provable,
--      but remember to check any other branches first
-- (3b) if we exhaust all options before reaching an Init or Identity, then
--      the proof search failed and we return that the Prop is unprovable
-}
decide :: Prop -- proposition to prove
       -> Bool -- return True if can be proven True within this calculus
decide = right ([],[])

-- Add a proposition to the context
add :: Prop -> Context -> Context
add p ctx@(inv, other) = case p of
  Atom _ -> (inv, p : other)   -- Assume not-invertible
  TrueP -> ctx                     -- Leave out since useless
  FalseP -> ([FalseP], [])               -- Do not need anything else
  And _ _ -> (p : inv, other)
  Or _ _ -> (p : inv, other)
  Implies (Atom _) _ -> (inv, p : other)
  Implies (Implies _ _) _ -> (inv, p : other)
  Implies _ _ -> (p : inv, other)

right :: Context
      -> Prop
      -> Bool
right _ TrueP = True
right ctx (And a b) = right ctx a && right ctx b
right ctx (Implies a b) = right (add a ctx) b
right (And a b : inv, other) c = right (add a $ add b (inv, other)) c
right (FalseP : _, _) _ = True
right (Or a b : inv, other) c =
  right (add a (inv, other)) c && right (add b (inv, other)) c
right (Implies TrueP b : inv, other) c = right (add b (inv, other)) c
right (Implies FalseP _ : inv, other) c = right (inv, other) c
right (Implies (And d e) b : inv, other) c =
  right (add (Implies d $ Implies e b) (inv, other)) c
right (Implies (Or d e) b : inv, other) c =
  right (add (Implies e b) $ add (Implies d b) (inv, other)) c
right ([], other) p@(Or a b) =
  left other p || right ([], other) a || right ([], other) b
right ([], other) c = left other c


-- Non-invertible decisions. The invertible assumptions should be empty.
left :: [Prop] -> Prop -> Bool
left other c = any (`elim` c) (pulls other)


-- Reduce one non-invertible assumption and continue proof
elim :: (Prop, [Prop]) -> Prop -> Bool
elim (Atom s1, _) (Atom s2) = s1 == s2
elim (Atom s, _) _ = False
elim (Implies (Atom s) b, other) c =
  right ([], other) (Atom s) && right (add b ([], other)) c
elim (Implies (Implies d e) b, other) c =
  right (add d $ add (Implies e b) ([], other)) e && right (add b ([], other)) c


-- | Pull one element out for all elements. For example,
--
-- > pulls "abc" == [('a',"bc"),('b',"ac"),('c',"ab")]
pulls :: [a] -> [(a, [a])]
pulls xs = take (length xs) $ zipWith (second . (++)) (inits xs) breakdown
  where pull (x : xs) = (x, xs)
        breakdown = map pull (tails xs)
