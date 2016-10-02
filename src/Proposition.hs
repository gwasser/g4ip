module Proposition
    ( Prop (..),
      (==>),
      (⊃),
      (<==),
      (&),
      (∧),
      (\/),
      (∨),
      (<=>),
      n
    ) where

-- define what a logical proposition is
data Prop = Atom String -- atomic proposition like P, takes a string as a name
          | TrueP -- True Proposition, named like this to not conflict with Bool True
          | FalseP -- False Prop, named like this to not conflict with Bool False
          | And Prop Prop -- A & B for two args A and B
          | Or Prop Prop -- A | B for two args A and B
          | Implies Prop Prop -- A => B for two args A and B
          deriving (Eq) -- automatically sets up ability to compare Props with ==

instance Show Prop where -- this defines how to show this type as a String
    show (Atom s) = s
    show TrueP = "⊤"
    show FalseP = "⊥"
    show (And a b) = "(" ++ (show a) ++ " ∧ " ++ (show b) ++ ")"
    show (Or a b) = "(" ++ (show a) ++ " ∨ " ++ (show b) ++ ")"
    show (Implies a FalseP) = "¬" ++ "(" ++ (show a) ++ ")"
    show (Implies a b) = "(" ++ (show a) ++ " ⊃ " ++ (show b) ++ ")"

-- define shorthand notation for propositional connectives:
(==>) = Implies
(⊃) = Implies -- Unicode
(<==) = \a b -> Implies b a
(&) = And
(∧) = And -- Unicode 'LOGICAL AND'
(\/) = Or -- can't use v as alphanumeric chars can't be operators in Haskell
(∨) = Or -- Unicode 'LOGICAL OR'
(<=>) = \a b -> And (Implies a b) (Implies b a)
-- function to convert ~A into A => False
--   in otherwords, not is just a shorthand and not a Prop on its own
-- NOTE: haskell does not allow defining unary operators due to
--   its use of sections, so will use the "n" function in test cases
--   rather than ~ (slightly clunky notation, but not big deal)
n :: Prop -> Prop
n a = Implies a FalseP

-- set precedence of operators
infix 9 &
infix 9 ∧
infix 8 \/
infix 8 ∨
infixr 7 ==>
infixr 7 ⊃
infix 7 <==
infix 6 <=>
-- NOTE: function application is highest precedence so function n is always
--   translated first before operators are applied

