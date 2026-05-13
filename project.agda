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
    
{- -----------------------------------------------------------------------------
    Problem 4:
    Copy the Assocmodule from week 9 excercises and complete it to a fully
    working implementation of an associative structure you want (associative
    list, directory, etc.)
----------------------------------------------------------------------------- -}
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there)
open import Relation.Nullary using (Dec; yes; no) renaming (¬_ to ~_)
open import Relation.Binary.PropositionalEquality using (_≡_)

record DecType : Set₁ where
  field
    carr   : Set
    test-≡ : (x y : carr) → Dec (x ≡ y)

open DecType

module AssocList (K : DecType) (V : Set) where

  open DecType K

  Assoc : Set
  Assoc = List (carr × V)

  {- Elementhood relation -}
  _∈_ : carr → Assoc → Set
  k ∈ kvs = Any (λ { (k' , v) → k ≡ k' }) kvs

  {- Safe lookup -}
  lookup : {k : carr} {kvs : Assoc} → k ∈ kvs → V
  lookup {kvs = []} ()
  lookup {kvs = (_ , v) ∷ kvs} (here p) = v
  lookup {kvs = (_ , v) ∷ kvs} (there p) = lookup p

  {- The decidability of the elementhood relation -}
  _∈?_ : (k : carr) → (kvs : Assoc) → Dec (k ∈ kvs)
  k ∈? kvs = any? (λ { (k' , v) → test-≡ k k' }) kvs

  {- Lookup returning a maybe -}
  _‼_ : (kvs : Assoc) → (k : carr) → Maybe V
  kvs ‼ k with k ∈? kvs
  ... | yes p = just (lookup p)
  ... | no _  = nothing



{- -----------------------------------------------------------------------------
    Problem 5:
    Define an evaluation function eval ∶ Assignment → Formula → Maybe Bool
    assigning to each assignment of variables and formula its truth value.
    
----------------------------------------------------------------------------- -}


{- -----------------------------------------------------------------------------
    Problem 6:
    Define an evaluation function eval-nnf ∶ Assignment → NNF → Maybe Bool
    assigning to each assignment of variables and negation normal from formula 
    its truth value.
----------------------------------------------------------------------------- -}

{- -----------------------------------------------------------------------------
    Problem 7:
    Define a type of conjunction normal form formulas called CNF, with the 
    following grammar:
        Literal → Var 𝑛
                | ¬Var 𝑛
        Disjunct → Literal
                | Literal ∨ Disjunct
        CNF → Disjunct ∨ CNF
----------------------------------------------------------------------------- -}

{- -----------------------------------------------------------------------------
    Problem 8:
    Define an evaluation function eval-cnf ∶ Assignment → CNF → Maybe Bool
    assigning to each assignment of variables and conjunction normal from 
    formula its truth value.
----------------------------------------------------------------------------- -}

