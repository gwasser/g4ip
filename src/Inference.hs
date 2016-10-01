module Inference
    ( Rule (..),
      Sequent,
      Assumptions,
      ProofStep
    ) where

import Proposition

-- all possible rules used in G4ip
data Rule = Init -- only for use on Atoms
          | Identity -- an admissible rule, works on any Prop
          | TopRight
          | TopLeft
          | BottomLeft
          | AndRight
          | AndLeft
          | OrRight1
          | OrRight2
          | OrLeft
          | ImpliesRight
          | TopImpliesLeft
          | BottomImpliesLeft
          | AtomImpliesLeft
          | AndImpliesLeft
          | OrImpliesLeft
          | ImpliesImpliesLeft
          deriving (Eq, Show)

-- a sequent is a pair of a list of assumptions together with a proposition
type Sequent = (Assumptions, Prop)
type Assumptions = [Prop]

-- a step in the proof is the pair of a Sequent derived using a Rule
type ProofStep = (Rule, Sequent)
