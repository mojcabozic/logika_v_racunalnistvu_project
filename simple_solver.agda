module simple_solver where

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _⊔_; _≤?_)

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
    ~_  : Formula → Formula
    _∧∧_ : Formula → Formula → Formula
    _∨∨_ : Formula → Formula → Formula

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
    De Morgan's laws:
    ¬(A ∧ B) ≡ (¬A ∨ ¬B), ¬(A ∨ B) ≡ (¬A ∧ ¬B), ¬¬A ≡ A
-}

to-nnf : Formula → NNF
to-nnf (Var x)     = lit (pos x)
to-nnf (~ Var x)   = lit (neg x)
to-nnf (~ (~ f))   = to-nnf f
to-nnf (~ (f ∧∧ g)) = to-nnf (~ f) ∨* to-nnf (~ g)
to-nnf (~ (f ∨∨ g)) = to-nnf (~ f) ∧* to-nnf (~ g)
to-nnf (f ∧∧ g)    = to-nnf f ∧* to-nnf g
to-nnf (f ∨∨ g)    = to-nnf f ∨* to-nnf g
    
{- -----------------------------------------------------------------------------
    Problem 4:
    Copy the Assoc module from week 9 exercises and complete it to a fully
    working implementation of an associative structure you want (associative
    list, dictionary, etc.)
----------------------------------------------------------------------------- -}

open import Data.List using (List; []; _∷_; _++_; map; filter)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to Maybe-map)
open import Data.List.Relation.Unary.Any using (Any; any?; here; there)
open import Data.List.Relation.Unary.All using (All; all?)
open import Relation.Binary using (Decidable; DecidableEquality)
open import Relation.Nullary using (Dec; yes; no; ¬_; ¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym)
open import Function using (_∘_; case_of_)

record DecType : Set₁ where
  field
    carr   : Set
    test-≡ : (x y : carr) → Dec (x ≡ y)

open DecType

-- Membership predicate (no duplicates version)
-- NoDup ensures that keys are unique in the associative list.
module NoDupList where

  infix 4 _∈ₗ_

  data _∈ₗ_ {A : Set} : A → List A → Set where
    ∈-here  : {x : A} {xs : List A} → x ∈ₗ (x ∷ xs)
    ∈-there : {x y : A} {xs : List A} → x ∈ₗ xs → x ∈ₗ (y ∷ xs)

  data NoDup {A : Set} : List A → Set where
    []-nodup : NoDup []
    ∷-nodup  : {x : A} {xs : List A} → NoDup xs → ¬ (x ∈ₗ xs) → NoDup (x ∷ xs)

open NoDupList

-- Tiny helper: lift a Dec across an isomorphism
map-dec : {A B : Set} → (A → B) → (B → A) → Dec A → Dec B
map-dec f g (yes a) = yes (f a)
map-dec f g (no ¬a) = no  (¬a ∘ g)


module AssocList (K : DecType) (V : Set) where

  -- The underlying key equality
  _≟_ : DecidableEquality (carr K)
  _≟_ = test-≡ K

  -- Association list: list of key-value pairs with no duplicate keys
  -- We store it as a plain list; NoDupKeys enforces the invariant on keys
  Assoc : Set
  Assoc = List (carr K × V)

  -- Keys of an Assoc
  keys : Assoc → List (carr K)
  keys [] = []
  keys ((k , _) ∷ kvs) = k ∷ keys kvs

  -- No-duplicate-keys invariant
  NoDupKeys : Assoc → Set
  NoDupKeys kvs = NoDup (keys kvs)

  -- Elementhood: k appears as a key in kvs
  infix 4 _∈_

  _∈_ : carr K → Assoc → Set
  k ∈ kvs = Any (λ { (k' , _) → k ≡ k' }) kvs

  -- Safe lookup given a proof of membership
  lookup : {k : carr K} {kvs : Assoc} → k ∈ kvs → V
  lookup (here  {x = (_ , v)} refl) = v
  lookup (there p) = lookup p

  -- Decidable membership check
  _∈?_ : (k : carr K) → (kvs : Assoc) → Dec (k ∈ kvs)
  k ∈? kvs = any? (λ { (k' , _) → k ≟ k' }) kvs

  -- Lookup returning Maybe
  _‼_ : (kvs : Assoc) → (k : carr K) → Maybe V
  kvs ‼ k with k ∈? kvs
  ... | yes p = just (lookup p)
  ... | no  _ = nothing

  -- Update / insert:
  --   * if k is already present, replace its value
  --   * if k is absent, prepend the new pair
  _[_]≔_ : Assoc → carr K → V → Assoc
  []             [ k ]≔ v = (k , v) ∷ []
  ((k' , v') ∷ kvs) [ k ]≔ v with k ≟ k'
  ... | yes refl = (k' , v)  ∷ kvs   -- found the key: overwrite value
  ... | no  _    = (k' , v') ∷ (kvs [ k ]≔ v)  -- not this key: recurse

  -- Empty association list
  empty : Assoc
  empty = []

  -- Proof that empty has no duplicate keys
  empty-nodup : NoDupKeys empty
  empty-nodup = []-nodup

-- We use K = ℕ, V = Bool for use as variable assignments in CNF evaluation

module _ where

  open import Data.Bool using (Bool)

  -- Decidable equality for ℕ
  ℕ-dec : DecidableEquality ℕ
  ℕ-dec zero    zero    = yes refl
  ℕ-dec zero    (suc _) = no λ ()
  ℕ-dec (suc _) zero    = no λ ()
  ℕ-dec (suc m) (suc n) = map-dec (cong suc) (λ { refl → refl }) (ℕ-dec m n)

  𝒩 : DecType
  𝒩 .carr    = ℕ
  𝒩 .test-≡  = ℕ-dec


  open AssocList 𝒩 Bool public
    using ()
    renaming (Assoc to Assignment;
              _∈_   to _∈ᴬ_;
              lookup to lookupᴬ;
              _∈?_  to _∈?ᴬ_;
              _‼_   to _‼ᴬ_;
              _[_]≔_ to _[_]≔ᴬ_;
              empty  to emptyᴬ)



{- -----------------------------------------------------------------------------
    Problem 5:
    Define an evaluation function eval ∶ Assignment → Formula → Maybe Bool
    assigning to each assignment of variables and formula its truth value.
    
----------------------------------------------------------------------------- -}

open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)

open AssocList 𝒩 Bool

eval : Assignment → Formula → Maybe Bool
eval assn (Var x)  = assn ‼ᴬ x                      -- Var x looks up x in the assignment, returning nothing if not found
eval assn (~ f)    with eval assn f                 -- ~ f evaluates f and negates the result, propagating nothing if f is undefined
... | just b  = just (not b)
... | nothing = nothing
eval assn (f ∧∧ g)  with eval assn f | eval assn g   -- f ∧ g and f ∨ g evaluate both sides and apply the boolean operation, 
... | just b₁ | just b₂ = just (b₁ ∧ b₂)            -- returning nothing if either side is undefined
... | _        | _       = nothing
eval assn (f ∨∨ g)  with eval assn f | eval assn g
... | just b₁ | just b₂ = just (b₁ ∨ b₂)
... | _        | _       = nothing

{- -----------------------------------------------------------------------------
    Problem 6:
    Define an evaluation function eval-nnf ∶ Assignment → NNF → Maybe Bool
    assigning to each assignment of variables and negation normal from formula 
    its truth value.
----------------------------------------------------------------------------- -}

eval-nnf : Assignment → NNF → Maybe Bool
eval-nnf assn (lit (pos x)) = assn ‼ᴬ x
eval-nnf assn (lit (neg x)) with assn ‼ᴬ x
... | just b  = just (not b)
... | nothing = nothing
eval-nnf assn (f ∧* g) with eval-nnf assn f | eval-nnf assn g
... | just b₁ | just b₂ = just (b₁ ∧ b₂)
... | _        | _       = nothing
eval-nnf assn (f ∨* g) with eval-nnf assn f | eval-nnf assn g
... | just b₁ | just b₂ = just (b₁ ∨ b₂)
... | _        | _       = nothing

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

-- We already have Literal type from Problem 2

data Disjunct : Set where
  lit-d  : Literal → Disjunct               --a single literal
  _∨d_   : Literal → Disjunct → Disjunct    -- a literal joined to another disjunct

data CNF : Set where
  dis    : Disjunct → CNF           -- a single disjunct
  _∧c_   : Disjunct → CNF → CNF     -- a disjunct conjoined with another CNF

{- -----------------------------------------------------------------------------
    Problem 8:
    Define an evaluation function eval-cnf ∶ Assignment → CNF → Maybe Bool
    assigning to each assignment of variables and conjunction normal from 
    formula its truth value.
----------------------------------------------------------------------------- -}

-- base case: evaluates a literal
eval-literal : Assignment → Literal → Maybe Bool
eval-literal assn (pos x) = assn ‼ᴬ x
eval-literal assn (neg x) with assn ‼ᴬ x
... | just b  = just (not b)
... | nothing = nothing

-- disjunction of literals
eval-disjunct : Assignment → Disjunct → Maybe Bool
eval-disjunct assn (lit-d l)  = eval-literal assn l
eval-disjunct assn (l ∨d d)   with eval-literal assn l | eval-disjunct assn d
... | just b₁ | just b₂ = just (b₁ ∨ b₂)
... | _        | _       = nothing

-- evaluates the full CNF formula
eval-cnf : Assignment → CNF → Maybe Bool
eval-cnf assn (dis d)    = eval-disjunct assn d
eval-cnf assn (d ∧c cnf) with eval-disjunct assn d | eval-cnf assn cnf
... | just b₁ | just b₂ = just (b₁ ∧ b₂)
... | _        | _       = nothing



{- -----------------------------------------------------------------------------
    Problem 9: 
    Write an SAT solver for CNF formulas.
----------------------------------------------------------------------------- -}

-- Collect all variable indices from a CNF formula (with duplicates)
vars-lit : Literal → List ℕ
vars-lit (pos x) = x ∷ []
vars-lit (neg x) = x ∷ []

vars-disjunct : Disjunct → List ℕ
vars-disjunct (lit-d l)  = vars-lit l
vars-disjunct (l ∨d d)   = vars-lit l ++ vars-disjunct d

vars-cnf : CNF → List ℕ
vars-cnf (dis d)    = vars-disjunct d
vars-cnf (d ∧c cnf) = vars-disjunct d ++ vars-cnf cnf

-- Remove duplicates from a list
_∈ₙ?_ : ℕ → List ℕ → Bool
n ∈ₙ? []       = false
n ∈ₙ? (m ∷ ms) with ℕ-dec n m
... | yes _ = true
... | no  _ = n ∈ₙ? ms

remove-dup : List ℕ → List ℕ
remove-dup []       = []
remove-dup (x ∷ xs) with x ∈ₙ? xs
... | true  = remove-dup xs
... | false = x ∷ remove-dup xs

-- iterate over remaining variables, try true then false for each
solver : List ℕ → Assignment → CNF → Maybe Assignment
solver [] ρ φ with eval-cnf ρ φ
... | just true = just ρ
... | _         = nothing
solver (n ∷ ns) ρ φ with solver ns (ρ [ n ]≔ᴬ true) φ
... | just ρ'  = just ρ'
... | nothing  = solver ns (ρ [ n ]≔ᴬ false) φ

sat : CNF → Maybe Assignment
sat φ = solver (remove-dup (vars-cnf φ)) emptyᴬ φ


{- -----------------------------------------------------------------------------
    Problem 10: Show that the SAT solver you implemented is correct.
    
----------------------------------------------------------------------------- -}

-- Soundness: if sat phi returns just rho, then rho satisfies phi

solver-sound : (ns : List ℕ) (ρ : Assignment) (φ : CNF)
           → (ρ' : Assignment)
           → solver ns ρ φ ≡ just ρ'
           → eval-cnf ρ' φ ≡ just true

solver-sound [] ρ φ ρ' p with eval-cnf ρ φ in eq | p        -- base case
... | just true  | refl = eq
... | just false | ()
... | nothing    | ()

solver-sound (n ∷ ns) ρ φ ρ' p with solver ns (ρ [ n ]≔ᴬ true) φ in eq      -- inductive case
... | just _   = solver-sound ns (ρ [ n ]≔ᴬ true)  φ ρ' (trans eq p)
... | nothing  = solver-sound ns (ρ [ n ]≔ᴬ false) φ ρ' p

sat-sound : (φ : CNF) (ρ : Assignment)
          → sat φ ≡ just ρ
          → eval-cnf ρ φ ≡ just true
sat-sound φ ρ p = solver-sound (remove-dup (vars-cnf φ)) emptyᴬ φ ρ p



-- =====================
-- UNSATISFIABLE cases
-- =====================

-- x₀ ∧ ¬x₀  (direct contradiction)
_ : sat (lit-d (pos 0) ∧c dis (lit-d (neg 0))) ≡ nothing
_ = refl

-- (x₀ ∨ x₁) ∧ ¬x₀ ∧ ¬x₁
_ : sat ((pos 0 ∨d lit-d (pos 1)) ∧c (lit-d (neg 0) ∧c dis (lit-d (neg 1)))) ≡ nothing
_ = refl

-- =====================
-- SATISFIABLE cases
-- =====================

-- x₀
_ : sat (dis (lit-d (pos 0))) ≡ just ((0 , true) ∷ [])
_ = refl

-- ¬x₀
_ : sat (dis (lit-d (neg 0))) ≡ just ((0 , false) ∷ [])
_ = refl

-- x₀ ∨ x₁
_ : sat (dis (pos 0 ∨d lit-d (pos 1))) ≡ just ((0 , true) ∷ (1 , true) ∷ [])
_ = refl

-- x₀ ∧ x₁
_ : sat (lit-d (pos 0) ∧c dis (lit-d (pos 1))) ≡ just ((0 , true) ∷ (1 , true) ∷ [])
_ = refl

-- x₀ ∧ ¬x₁
_ : sat (lit-d (pos 0) ∧c dis (lit-d (neg 1))) ≡ just ((0 , true) ∷ (1 , false) ∷ [])
_ = refl

-- (x₀ ∨ ¬x₁) ∧ (¬x₀ ∨ x₁)
_ : sat ((pos 0 ∨d lit-d (neg 1)) ∧c dis (neg 0 ∨d lit-d (pos 1))) ≡ just ((0 , true) ∷ (1 , true) ∷ [])
_ = refl

-- =====================
-- Soundness spot-checks
-- =====================

_ : eval-cnf ((0 , true) ∷ (1 , true) ∷ []) (dis (pos 0 ∨d lit-d (pos 1))) ≡ just true
_ = refl

_ : eval-cnf ((0 , true) ∷ (1 , false) ∷ []) (lit-d (pos 0) ∧c dis (lit-d (neg 1))) ≡ just true
_ = refl