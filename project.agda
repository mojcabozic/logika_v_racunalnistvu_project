module project where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using () renaming (¬_ to ~_) -- to avoid a clash of negations


open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there)
open import Relation.Nullary using (Dec; yes; no) renaming (¬_ to ~_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Data.Bool using (Bool; true; false; not) renaming (_∧_ to _∧b_; _∨_ to _∨b_)
open import Data.Nat.Properties using (_≟_)

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

record DecType : Set₁ where
  field
    carr   : Set
    test-≡ : (x y : carr) → Dec (x ≡ y)

module Assoc (K : DecType) (V : Set) where
  open DecType K

  Assoc : Set
  Assoc = List (carr × V)

  _∈_ : carr → Assoc → Set
  k ∈ kvs = Any (λ { (k' , _) → k ≡ k' }) kvs

  lookup : {k : carr} {kvs : Assoc} → k ∈ kvs → V
  lookup (here {x = (_ , v)} _) = v
  lookup (there p)               = lookup p

  _∈?_ : (k : carr) → (kvs : Assoc) → Dec (k ∈ kvs)
  k ∈? kvs = any? (λ { (k' , _) → test-≡ k k' }) kvs

  _‼_ : (kvs : Assoc) → (k : carr) → Maybe V
  kvs ‼ k with k ∈? kvs
  ... | yes p = just (lookup p)
  ... | no  _ = nothing

  _[_]≔_ : Assoc → carr → V → Assoc
  []              [ k ]≔ v = (k , v) ∷ []
  ((k' , v') ∷ kvs) [ k ]≔ v with test-≡ k k'
  ... | yes _ = (k , v) ∷ kvs    -- spremeni
  ... | no  _ = (k' , v') ∷ (kvs [ k ]≔ v)  -- se naprej isce


{- -----------------------------------------------------------------------------
    Problem 5:
    Define an evaluation function eval ∶ Assignment → Formula → Maybe Bool
    assigning to each assignment of variables and formula its truth value.
    
----------------------------------------------------------------------------- -}

-- definiramo DecType za naravna števila
NatDecType : DecType
NatDecType = record { carr = ℕ ; test-≡ = _≟_ }

-- odpremo nas modul s konkretnimi tipi
open Assoc NatDecType Bool

-- definiramo tip Assignment
Assignment : Set
Assignment = Assoc

eval : Assignment → Formula → Maybe Bool
eval env (Var x) = env ‼ x
eval env (¬ f) with eval env f
... | just v  = just (not v)
... | nothing = nothing
eval env (f ∧ g) with eval env f | eval env g
... | just v1 | just v2 = just (v1 ∧b v2)
... | _       | _       = nothing
eval env (f ∨ g) with eval env f | eval env g
... | just v1 | just v2 = just (v1 ∨b v2)
... | _       | _       = nothing

{- -----------------------------------------------------------------------------
    Problem 6:
    Define an evaluation function eval-nnf ∶ Assignment → NNF → Maybe Bool
    assigning to each assignment of variables and negation normal from formula 
    its truth value.
----------------------------------------------------------------------------- -}
eval-nnf : Assignment → NNF → Maybe Bool
eval-nnf env (lit (pos x)) = env ‼ x
eval-nnf env (lit (neg x)) with env ‼ x
... | just v  = just (not v)
... | nothing = nothing
eval-nnf env (f ∧* g) with eval-nnf env f | eval-nnf env g
... | just v1 | just v2 = just (v1 ∧b v2)
... | _       | _       = nothing
eval-nnf env (f ∨* g) with eval-nnf env f | eval-nnf env g
... | just v1 | just v2 = just (v1 ∨b v2)
... | _       | _       = nothing

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
-- literal ze imamo

data Disjunct : Set where
  lit-d  : Literal → Disjunct
  _∨-d_  : Literal → Disjunct → Disjunct

data CNF : Set where
  dis    : Disjunct → CNF
  _∧-c_  : Disjunct → CNF → CNF

{- -----------------------------------------------------------------------------
    Problem 8:
    Define an evaluation function eval-cnf ∶ Assignment → CNF → Maybe Bool
    assigning to each assignment of variables and conjunction normal from 
    formula its truth value.
----------------------------------------------------------------------------- -}

eval-disjunct : Assignment → Disjunct → Maybe Bool
eval-disjunct env (lit-d (pos x)) = env ‼ x
eval-disjunct env (lit-d (neg x)) with env ‼ x
... | just v  = just (not v)
... | nothing = nothing
eval-disjunct env ((pos x) ∨-d d) with env ‼ x | eval-disjunct env d
... | just v1 | just v2 = just (v1 ∨b v2)
... | _       | _       = nothing
eval-disjunct env ((neg x) ∨-d d) with env ‼ x | eval-disjunct env d
... | just true  | just v2 = just (false ∨b v2)
... | just false | just v2 = just (true  ∨b v2)
... | _          | _       = nothing

eval-cnf : Assignment → CNF → Maybe Bool
eval-cnf env (dis d)    = eval-disjunct env d
eval-cnf env (d ∧-c c) with eval-disjunct env d | eval-cnf env c
... | just v1 | just v2 = just (v1 ∧b v2)
... | _       | _       = nothing
