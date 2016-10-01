module Decide
       ( decide )
       where

import Proposition
import Inference

import Data.List

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
       -> Bool -- return True if proved true within this calculus
decide x = proof_search False False [] [] [init_seq]
    where init_seq = ([], x) :: Sequent -- construct Sequent from Prop to prove

-- given is_done, is_failed, a history of BranchPoints = (Rule, Sequent), a history of previous Props used with ImpliesImpliesLeft Rule, and a list of Sequents to prove
--   need lists of Sequents to deal with branching in Rules, and branching in choices
proof_search :: Bool -- are we done with proof search?
             -> Bool -- did proof search fail?
             -> [(Rule, Sequent)] -- a history of BranchPoints = (Rule, Sequent)
             -> [Prop] -- a history of previous Props used with ImpliesImpliesLeft Rule
             -> [Sequent] -- list of sequents to prove
             -> Bool -- returns True if can prove all Sequents provided
-- if proof search on current branch failed, check history list:
--   if no history then we failed for sure, otherwise restart search at last branch point
proof_search _ True h hiil _ = if null h then False else proof_search False False h hiil [snd (head h)]
-- id done with no fail flags, then search succeeded
proof_search True _ _ _ _ = True
-- if more than one sequent left to prove, check first element of list, if not ok, then move on
proof_search done failed h hiil (s:s2:ss) = proof_search done failed h hiil [s] && proof_search done failed h hiil (s2:ss)
-- if down to one sequent left to prove...
proof_search done failed h hiil [s] = proof_search dn fn hn hiiln sn
    where (fn, rn, sn, iiln) = try_rules all_rules s or1fail hiil -- (Bool, Rule, [Sequent])
          all_rules = [TopRight, TopLeft, BottomLeft, AndRight, ImpliesRight, AndLeft, OrLeft, TopImpliesLeft, BottomImpliesLeft, AndImpliesLeft, OrImpliesLeft, Init, Identity, AtomImpliesLeft, OrRight1, OrRight2, ImpliesImpliesLeft]
          dn = if (rn == Init) || (rn == Identity) || (rn == TopRight) || (rn == BottomLeft) then True else False -- are we done with proof search?
          or1fail = if null h then False else (if s == snd (head h) && fst (head h) == OrRight1 then True else False)
          iilfail = if null h then False else (if s == snd (head h) && fst (head h) == ImpliesImpliesLeft then True else False)
          hn = if or1fail || iilfail then tail h else (if rn == OrRight1 then (OrRight1,s) : h else (if rn == ImpliesImpliesLeft then (ImpliesImpliesLeft, s) : h else h)) -- update history only if had to make a choice, but what if more than one?
          hiiln = if dn then [] else (if iilfail then iiln : hiil else hiil) -- add the next Prop we're trying ImpliesImpliesLeft on to the rule

-- Try using different Rules to derive a Sequent
try_rules :: [Rule] -- list of Rules to try
          -> Sequent -- Sequent to attempt to prove using list of Rules
          -> Bool -- did we return from a failed branch?
          -> [Prop]
          -> (Bool, Rule, [Sequent], Prop) -- returns 4-tuple (failed, Rule used if successful, list of resulting Sequents from Rule, Prop used if IIL Rule)
try_rules [] s or1fail hiil = (True, Init, [s], Atom "F") -- ran out of rules so completely failed
try_rules (r:r2:rs) s or1fail hiil = if fn then try_rules (r2:rs) s or1fail hiil else (fn, rn, sn, pn) -- if this rule failed, try next, otherwise stop and return
    where (fn, rn, sn, pn) = try_rules [r] s or1fail hiil
try_rules [r] (a, p) or1fail hiil
    | r == TopRight = try_top_right False (a, p)
    | r == TopLeft = try_top_left False (a) (a, p)
    | r == BottomLeft = try_bottom_left False (a) (a, p)
    | r == AndRight = try_and_right False (a, p)
    | r == ImpliesRight = try_implies_right False (a, p)
    | r == AndLeft = try_and_left False (a) (a, p)
    | r == OrLeft = try_or_left False (a) (a, p)
    | r == TopImpliesLeft = try_top_implies_left False (a) (a, p)
    | r == BottomImpliesLeft = try_bottom_implies_left False (a) (a, p)
    | r == AndImpliesLeft = try_and_implies_left False (a) (a, p)
    | r == OrImpliesLeft = try_or_implies_left False (a) (a, p)
    | r == Identity = try_id False (a) (a, p)
    | r == Init = try_init False (a) (a, p)
    | r == AtomImpliesLeft = try_atom_implies_left False (a) (a, p)
    | r == OrRight1 && not or1fail = try_or_right_one False (a,p)
    | r == OrRight2 || r == OrRight1 = try_or_right_two False (a,p) -- only get to this one if previous didn't work
    | r == ImpliesImpliesLeft = try_implies_implies_left False (a) (a, p) hiil

{-
-------------------------------------------------------------------------------
--  Individual Proof Rule functions
-------------------------------------------------------------------------------
-}

-- GENERAL NOTE:

try_rule :: Rule -- Rule we are trying
         -> Bool -- was this branch a failure?
         -> Sequent -- Sequent to prove
         -> (Bool, Rule, [Sequent], Maybe Prop) -- (failed?, rule that worked, [Sequents from rule], Prop used if IIL Rule)
try_rule = undefined

try_top_right :: Bool -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_top_right True (as, TrueP) = (True, TopRight, [(as, TrueP)], Atom "F")
try_top_right False (as, TrueP) = (False, TopRight, [(as, TrueP)], Atom "F") -- if matched, return result
try_top_right False (as, p) = (True, TopRight, [(as, p)], Atom "F") -- failed due to no match

try_top_left :: Bool -> Assumptions -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_top_left True oa (TrueP : as, p) = (True, TopLeft, [(TrueP : as, p)], Atom "F")
try_top_left False oa (TrueP : as, p) = (False, TopLeft, [(nas, p)], Atom "F") -- if matched, return result
    where nas = delete TrueP oa
try_top_left False oa (a : as, p) = try_top_left False oa (as, p)
try_top_left False oa (as, p) = (True, TopLeft, [(as, p)], Atom "F") -- failed due to no match

try_bottom_left :: Bool -> Assumptions -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_bottom_left True oa (FalseP : as, p) = (True, BottomLeft, [(FalseP : as, p)], Atom "F")
try_bottom_left False oa (FalseP : as, p) = (False, BottomLeft, [(nas, p)], Atom "F") -- if matched, return result
    where nas = delete FalseP oa
try_bottom_left False oa (a : as, p) = try_bottom_left False oa (as, p)
try_bottom_left False oa (as, p) = (True, BottomLeft, [(as, p)], Atom "F") -- failed due to no match

try_and_right :: Bool -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_and_right True (as, And b c) = (True, AndRight, [(as, And b c)], Atom "F")
try_and_right False (as, And b c) = (False, AndRight, [(as, b),(as, c)], Atom "F") -- if matched, return result
try_and_right False (as, p) = (True, AndRight, [(as, p)], Atom "F") -- failed due to no match

try_and_left :: Bool -> Assumptions -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_and_left True oa ((And b c) : as, p) = (True, AndLeft, [(oa, p)], Atom "F")
try_and_left False oa ((And b c) : as, p) = (False, AndLeft, [(c : b : nas, p)], Atom "F") -- if matched, return result
    where nas = delete (And b c) oa
try_and_left False oa (a:as, p) = try_and_left False oa (as, p)
try_and_left False oa ([], p) = (True, AndLeft, [(oa, p)], Atom "F") -- failed due to no match

try_or_left :: Bool -> Assumptions -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_or_left True oa (as, p) = (True, OrLeft, [(oa, p)], Atom "F")
try_or_left False oa ((Or b c) : as, p) = (False, OrLeft, [(b:nas, p),(c:nas, p)], Atom "F") -- if matched, return result
    where nas = delete (Or b c) oa
try_or_left False oa (a:as, p) = try_or_left False oa (as, p)
try_or_left False oa ([], p) = (True, OrLeft, [(oa, p)], Atom "F") -- failed due to no match

try_implies_right :: Bool -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_implies_right True (as, Implies b c) = (True, ImpliesRight, [(as, Implies b c)], Atom "F")
try_implies_right False (as, Implies b c) = (False, ImpliesRight, [(b:as, c)], Atom "F") -- if matched, return result
try_implies_right False (as, p) = (True, ImpliesRight, [(as, p)], Atom "F") -- failed due to no match

try_top_implies_left :: Bool -> Assumptions -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_top_implies_left True oa (as, p) = (True, TopImpliesLeft, [(oa, p)], Atom "F")
try_top_implies_left False oa ((Implies TrueP b):as, p) = (False, TopImpliesLeft, [(b:nas, p)], Atom "F") -- if matched, return result
    where nas = delete (Implies TrueP b) oa
try_top_implies_left False oa (a:as, p) = try_top_implies_left False oa (as, p)
try_top_implies_left False oa ([], p) = (True, TopImpliesLeft, [(oa, p)], Atom "F") -- failed due to no match

try_bottom_implies_left :: Bool -> Assumptions -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_bottom_implies_left True oa (as, p) = (True, BottomImpliesLeft, [(oa, p)], Atom "F")
try_bottom_implies_left False oa ((Implies FalseP b):as, p) = (False, BottomImpliesLeft, [(nas, p)], Atom "F") -- if matched, return result
    where nas = delete (Implies FalseP b) oa
try_bottom_implies_left False oa (a:as, p) = try_bottom_implies_left False oa (as, p)
try_bottom_implies_left False oa ([], p) = (True, BottomImpliesLeft, [(oa, p)], Atom "F") -- failed due to no match

try_and_implies_left :: Bool -> Assumptions -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_and_implies_left True oa (as, p) = (True, AndImpliesLeft, [(oa, p)], Atom "F")
try_and_implies_left False oa ((Implies (And d e) b):as, p) = (False, AndImpliesLeft, [((Implies d (Implies e b)):nas, p)], Atom "F") -- if matched, return result
    where nas = delete (Implies (And d e) b) oa
try_and_implies_left False oa (a:as, p) = try_and_implies_left False oa (as, p)
try_and_implies_left False oa ([], p) = (True, AndImpliesLeft, [(oa, p)], Atom "F") -- failed due to no match

try_or_implies_left :: Bool -> Assumptions -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_or_implies_left True oa (as, p) = (True, OrImpliesLeft, [(oa, p)], Atom "F")
try_or_implies_left False oa ((Implies (Or d e) b):as, p) = (False, OrImpliesLeft, [((Implies e b):(Implies d b):nas, p)], Atom "F") -- if matched, return result
    where nas = delete (Implies (Or d e) b) oa
try_or_implies_left False oa (a:as, p) = try_or_implies_left False oa (as, p)
try_or_implies_left False oa ([], p) = (True, OrImpliesLeft, [(oa, p)], Atom "F") -- failed due to no match

try_init :: Bool -> Assumptions -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_init True oa (_, Atom p) = (True, Init, [(oa, Atom p)], Atom "F")
try_init False oa ([], Atom p) = (True, Init, [(oa, Atom p)], Atom "F") -- if run out of assumptions to test, then we failed
try_init False oa ((Atom q):as, Atom p) = if p == q then (False, Init,[(oa, Atom p)], Atom "F") else try_init False oa (as, Atom p)
try_init False oa (as, p) = (True, Init, [(oa, p)], Atom "F") -- fail if top prop is not an atom

try_id :: Bool -> Assumptions -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_id True oa (_, p) = (True, Identity, [(oa, p)], Atom "F")
try_id False oa ([], p) = (True, Identity, [(oa, p)], Atom "F") -- if run out of assumptions to test, then we failed
try_id False oa (q:as, p) = if p == q then (False, Identity, [(oa, p)], Atom "F") else try_id False oa (as, p)

try_atom_implies_left :: Bool -> Assumptions -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_atom_implies_left True oa (as, p) = (True, AtomImpliesLeft, [(oa, p)], Atom "F")
try_atom_implies_left False oa ((Implies (Atom c) b):as, p) = if is_assumed then (False, AtomImpliesLeft, [(b:nas, p)], Atom "F") else try_atom_implies_left False oa (as, p) -- if matched, return result
    where nas = delete (Implies (Atom c) b) oa
          is_assumed = (Atom c) `elem` oa -- true if atom was in the list of assumptions
try_atom_implies_left False oa (a:as, p) = try_atom_implies_left False oa (as, p)
try_atom_implies_left False oa ([], p) = (True, AtomImpliesLeft, [(oa, p)], Atom "F") -- failed due to no match

try_or_right_one :: Bool -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_or_right_one True (as, Or b c) = (True, OrRight1, [(as, Or b c)], Atom "F")
try_or_right_one False (as, Or b c) = (False, OrRight1, [(as, b)], Atom "F") -- if matched, return result
try_or_right_one False (as, p) = (True, OrRight1, [(as, p)], Atom "F") -- failed due to no match

try_or_right_two :: Bool -> Sequent -> (Bool, Rule, [Sequent], Prop)
try_or_right_two True (as, Or b c) = (True, OrRight2, [(as, Or b c)], Atom "F")
try_or_right_two False (as, Or b c) = (False, OrRight2, [(as, c)], Atom "F") -- if matched, return result
try_or_right_two False (as, p) = (True, OrRight2, [(as, p)], Atom "F") -- failed due to no match

-- NOTE: probably need some way to track which Assumptions we've tried so don't get stuck in loops?
try_implies_implies_left :: Bool -> Assumptions -> Sequent -> [Prop] -> (Bool, Rule, [Sequent], Prop)
try_implies_implies_left True oa (as, p) hiil = (True, ImpliesImpliesLeft, [(oa, p)], Atom "F")
try_implies_implies_left False oa ((Implies (Implies d e) b):as, p) hiil = if was_tried_before then (try_implies_implies_left False oa (as, p) hiil) else (False, ImpliesImpliesLeft, [((Implies e b):d:nas, e), (b:nas, p)], (Implies (Implies d e) b)) -- if matched, return result
    where nas = delete (Implies (Implies d e) b) oa
          was_tried_before = (Implies (Implies d e) b) `elem` hiil
try_implies_implies_left False oa (a:as, p) hiil = try_implies_implies_left False oa (as, p) hiil
try_implies_implies_left False oa ([], p) hiil = (True, ImpliesImpliesLeft, [(oa, p)], Atom "F") -- failed due to no match

