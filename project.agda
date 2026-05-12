module project where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using () renaming (¬_ to ~_) -- to avoid a clash of negations

{- -----------------------------------------------------------------------------
    Problem 1: 
    Define a type of formulas called Formula, with the following grammar:

                Formula → Var n
                        | ¬Formula
                        | Formula ∧ Formula
                        | Formula ∨ Formula
----------------------------------------------------------------------------- -}

data Formula : Set where
    Var : ℕ → Formula
    ¬_  : Formula → Formula
    _∧_ : Formula → Formula → Formula
    _∨_ : Formula → Formula → Formula

{- -----------------------------------------------------------------------------
    Problem 2: 
    Define a type of negation normal form formulas called NNF, with the following grammar:

                Literal → Var n
                        | ¬Var n
                NNF → Literal
                    | NNF ∧ NNF
                    | NNF ∨ NNF
----------------------------------------------------------------------------- -}

data Literal : Set where
  pos : ℕ → Literal
  neg : ℕ → Literal

data NNF : Set where
  lit : Literal → NNF
  _∧*_ : NNF → NNF → NNF
  _∨*_ : NNF → NNF → NNF

{- -----------------------------------------------------------------------------
    Problem 3: 
    Construct a function to-nnf of type Formula → NNF that converts a formula
    to an equivalent formula in negation normal form.
----------------------------------------------------------------------------- -}

{-
    We use De Morgan's laws:
    ¬(A ∧ B) ≡ (¬A ∨ ¬B), ¬(A ∨ B) ≡ (¬A ∧ ¬B), ¬¬A ≡ A
-}

to-nnf : Formula → NNF
to-nnf (Var x) = lit (pos x)
to-nnf (¬ Var x) = lit (neg x)
to-nnf (¬ (¬ f)) = to-nnf f                             -- ¬¬A ≡ A
to-nnf (¬ (f ∧ g)) = to-nnf (¬ f) ∨* to-nnf (¬ g)       -- ¬(A ∧ B) ≡ (¬A ∨ ¬B)
to-nnf (¬ (f ∨ g)) = to-nnf (¬ f) ∧* to-nnf (¬ g)       -- ¬(A ∨ B) ≡ (¬A ∧ ¬B)
to-nnf (f ∧ g) = to-nnf f ∧* to-nnf g
to-nnf (f ∨ g) = to-nnf f ∨* to-nnf g
    

