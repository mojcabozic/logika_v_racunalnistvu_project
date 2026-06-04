module project-v2 where

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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
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
    Write an SAT solver for CNFformulas.
----------------------------------------------------------------------------- -}

-- We implement DPLL.

open import Data.List using (List; []; _∷_; filter; map; concatMap; null)
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_; if_then_else_)
open import Data.Maybe using (Maybe; just; nothing; maybe)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

-- Helper functions on literals:

-- Get the variable index from a literal
lit-var : Literal → ℕ
lit-var (pos x) = x
lit-var (neg x) = x

-- Get the truth value: true = positive, false = negative
lit-pol : Literal → Bool
lit-pol (pos _) = true
lit-pol (neg _) = false

-- Negate a literal
neg-lit : Literal → Literal
neg-lit (pos x) = neg x
neg-lit (neg x) = pos x

-- Check if two literals are equal
lit-eq : Literal → Literal → Bool
lit-eq (pos x) (pos y) with ℕ-dec x y
... | yes _ = true
... | no  _ = false
lit-eq (neg x) (neg y) with ℕ-dec x y
... | yes _ = true
... | no  _ = false
lit-eq _ _ = false

-- A "working" CNF representation as List (List Literal) (easier to work with)

WorkingCNF : Set
WorkingCNF = List (List Literal)

-- Convert inductive CNF to WorkingCNF 
disjunct-to-list : Disjunct → List Literal
disjunct-to-list (lit-d l)  = l ∷ []
disjunct-to-list (l ∨d d)   = l ∷ disjunct-to-list d

cnf-to-working : CNF → WorkingCNF
cnf-to-working (dis d)    = disjunct-to-list d ∷ []
cnf-to-working (d ∧c cnf) = disjunct-to-list d ∷ cnf-to-working cnf

-- Core DPLL operations:

-- Check if a literal appears in a clause
lit-in-clause : Literal → List Literal → Bool
lit-in-clause _ []       = false
lit-in-clause l (l' ∷ ls) with lit-eq l l'
... | true  = true
... | false = lit-in-clause l ls

-- Assign a literal: 
--   * remove all clauses containing the literal (they are satisfied)
--   * remove the negation of the literal from remaining clauses
assign : Literal → WorkingCNF → WorkingCNF
assign l = filter-clauses ∘ map remove-neg
  where
    -- remove clauses that are already satisfied by l
    filter-clauses : WorkingCNF → WorkingCNF
    filter-clauses []       = []
    filter-clauses (c ∷ cs) with lit-in-clause l c
    ... | true  = filter-clauses cs        -- clause satisfied, drop it
    ... | false = c ∷ filter-clauses cs    -- keep clause

    -- remove ¬l from a clause
    remove-neg : List Literal → List Literal
    remove-neg []        = []
    remove-neg (l' ∷ ls) with lit-eq (neg-lit l) l'
    ... | true  = remove-neg ls            -- this is ¬l, remove it
    ... | false = l' ∷ remove-neg ls       -- keep it

-- Unit propagation: find a unit clause and return it
find-unit : WorkingCNF → Maybe Literal
find-unit []              = nothing
find-unit ((l ∷ []) ∷ _) = just l     -- found a unit clause
find-unit (_ ∷ cs)        = find-unit cs

-- Pure literal elimination:
-- A literal is pure if its negation never appears in any clause.
-- Collect all literals appearing in the formula
all-literals : WorkingCNF → List Literal
all-literals []       = []
all-literals (c ∷ cs) = c ++ all-literals cs

-- Check if a literal's negation appears anywhere
neg-appears : Literal → WorkingCNF → Bool
neg-appears l cnf = lit-in-clause (neg-lit l) (all-literals cnf)

-- Find a pure literal (one whose negation does not appear)
find-pure : WorkingCNF → Maybe Literal
find-pure cnf = go (all-literals cnf)
  where
    go : List Literal → Maybe Literal
    go []       = nothing
    go (l ∷ ls) with neg-appears l cnf
    ... | false = just l     -- l is pure
    ... | true  = go ls

-- Check if any clause is empty (formula is unsatisfiable at this point)
has-empty-clause : WorkingCNF → Bool
has-empty-clause []        = false
has-empty-clause ([] ∷ _)  = true
has-empty-clause (_ ∷ cs)  = has-empty-clause cs

-- Pick the first literal from the first clause (branching)
pick-literal : WorkingCNF → Maybe Literal
pick-literal []          = nothing
pick-literal ([] ∷ cs)   = pick-literal cs
pick-literal ((l ∷ _) ∷ _) = just l

-- Add a step counter to convince Agda the function terminates (it should not reach max steps for reasonable inputs)

dpll : ℕ → WorkingCNF → Assignment → Maybe Assignment
dpll zero    _   _    = nothing   -- out of fuel
dpll (suc n) cnf assn

  -- Base case 1: no clauses left → all satisfied → return assignment
  with null cnf
... | true  = just assn

  -- Base case 2: some clause is empty → contradiction → backtrack
... | false with has-empty-clause cnf
... | true  = nothing

  -- Unit propagation: if there is a unit clause, we MUST assign that literal
... | false with find-unit cnf
... | just l  = dpll n (assign l cnf) (assn [ lit-var l ]≔ᴬ lit-pol l)

  -- Pure literal elimination: assign pure literals for free (no branching)
... | nothing with find-pure cnf
... | just l  = dpll n (assign l cnf) (assn [ lit-var l ]≔ᴬ lit-pol l)

  -- Branching: pick a literal, try true first, then false if it fails
... | nothing with pick-literal cnf
... | nothing = just assn    -- no literals left, all satisfied
... | just l  with dpll n (assign l cnf) (assn [ lit-var l ]≔ᴬ lit-pol l)
...   | just assn' = just assn'   -- branch succeeded
...   | nothing    =              -- try the other polarity
        dpll n (assign (neg-lit l) cnf) (assn [ lit-var l ]≔ᴬ not (lit-pol l))

-- SAT solver:

max-steps : WorkingCNF → ℕ
max-steps cnf = Data.List.length (all-literals cnf) * 100 -- change if needed

sat : CNF → Maybe Assignment
sat cnf =
  let wcnf = cnf-to-working cnf
  in  dpll (max-steps wcnf) wcnf emptyᴬ


-- -------------------------------------------------------------------------
-- Test cases for the SAT solver
-- -------------------------------------------------------------------------

-- Helper: a single positive literal clause
pos-clause : ℕ → Disjunct
pos-clause x = lit-d (pos x)

-- Helper: a single negative literal clause
neg-clause : ℕ → Disjunct
neg-clause x = lit-d (neg x)

-- -------------------------------------------------------------------------
-- Test 1: trivially satisfiable — just (x₀)
-- Formula: x₀
-- Expected: just (assignment with x₀ = true)
-- -------------------------------------------------------------------------
test1 : Maybe Assignment
test1 = sat (dis (pos-clause 0))
_ = {!test1!}

-- -------------------------------------------------------------------------
-- Test 2: trivially unsatisfiable — (x₀) ∧ (¬x₀)
-- Formula: x₀ ∧ ¬x₀
-- Expected: nothing
-- -------------------------------------------------------------------------
test2 : Maybe Assignment
test2 = sat (pos-clause 0 ∧c dis (neg-clause 0))
_ = {!test2!}

-- -------------------------------------------------------------------------
-- Test 3: unit propagation — (x₀) ∧ (x₀ ∨ x₁)
-- x₀ is a unit clause so x₀ = true, second clause is satisfied
-- Expected: just (assignment with x₀ = true)
-- -------------------------------------------------------------------------
test3 : Maybe Assignment
test3 = sat (pos-clause 0 ∧c dis (pos 0 ∨d lit-d (pos 1)))
_ = {!test3!}

-- -------------------------------------------------------------------------
-- Test 4: requires branching — (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₁) ∧ (x₀ ∨ ¬x₁)
-- Expected: just some satisfying assignment
-- -------------------------------------------------------------------------
test4 : Maybe Assignment
test4 = sat
  (  (pos 0 ∨d lit-d (pos 1))
  ∧c ((neg 0 ∨d lit-d (pos 1))
  ∧c dis (pos 0 ∨d lit-d (neg 1)))
  )
_ = {!test4!}

-- -------------------------------------------------------------------------
-- Test 5: classic UNSAT — (x₀ ∨ x₁) ∧ (¬x₀ ∨ x₁) ∧ (x₀ ∨ ¬x₁) ∧ (¬x₀ ∨ ¬x₁)
-- All four combinations of x₀, x₁ are ruled out
-- Expected: nothing
-- -------------------------------------------------------------------------
test5 : Maybe Assignment
test5 = sat
  (  (pos 0 ∨d lit-d (pos 1))
  ∧c ((neg 0 ∨d lit-d (pos 1))
  ∧c ((pos 0 ∨d lit-d (neg 1))
  ∧c dis (neg 0 ∨d lit-d (neg 1))))
  )
_ = {!test5!}

{- -----------------------------------------------------------------------------
    Problem 10: 
    Show that the SAT solver you implemented is correct.
----------------------------------------------------------------------------- -}

-- first prove soundness: If sat cnf returns just assn, then assn is a satisfying assignment for cnf

sat-sound : ∀ (cnf : CNF) (assn : Assignment)
  → sat cnf ≡ just assn
  → eval-cnf assn cnf ≡ just true

{- -----------------------------------------------------------------------------
    Problem 11: 
    Write a function that converts an NNF formula to an equisatisfiable
    CNFformula using the Tseytin transformation.
----------------------------------------------------------------------------- -}

-- Tseytin transformation:
-- For each subformula you introduce a fresh variable t and add clauses encoding:
-- t ↔ (a ∧ b):
--      t → (a ∧ b): (¬t ∨ a)∧(¬t ∨ b)
--      (a ∧ b) → t: (¬a ∨ ¬b ∨ t)
-- t ↔ (a ∨ b):
--      t → (a ∨b ): (¬t ∨ a ∨ b)
--      (a ∨ b) → t: (¬a ∨ t)∧(¬b ∨ t)

-- We thread a "fresh variable counter" through the computation.
-- Each subformula gets a fresh variable. Emit clauses encoding the equivalence between that variable and the subformula.

-- We represent the output as a list of clauses (List (List Literal))
-- together with the "root" literal for the subformula.

-- State: next fresh variable index
-- We assume NNF variables are Var 0 .. Var (n-1);
-- fresh variables start at some offset we pass in.

-- Find the highest variable index used in an NNF formula
max-var-nnf : NNF → ℕ
max-var-nnf (lit (pos x)) = x
max-var-nnf (lit (neg x)) = x
max-var-nnf (f ∧* g) = (max-var-nnf f) ⊔ (max-var-nnf g) -- _⊔_ gives max of both
max-var-nnf (f ∨* g) = (max-var-nnf f) ⊔ (max-var-nnf g)

-- The Tseytin pass returns:
--   * the literal representing this subformula
--   * the clauses generated so far
--   * the next fresh variable index

tseytin : NNF → ℕ → (Literal × List (List Literal) × ℕ)
tseytin (lit l) fresh = (l , [] , fresh)   -- literals need no fresh var
tseytin (f ∧* g) fresh =
  let (lf , cf , fresh₁) = tseytin f fresh
      (lg , cg , fresh₂) = tseytin g fresh₁
      t                  = pos fresh₂
      -- t ↔ (lf ∧ lg):
      clauses = (neg fresh₂ ∷ lf ∷ [])          -- ¬t ∨ lf
              ∷ (neg fresh₂ ∷ lg ∷ [])          -- ¬t ∨ lg  
              ∷ (t ∷ neg-lit lf ∷ neg-lit lg ∷ []) -- t ∨ ¬lf ∨ ¬lg
              ∷ []
  in  (t , cf ++ cg ++ clauses , suc fresh₂)
tseytin (f ∨* g) fresh = 
  let (lf , cf , fresh₁) = tseytin f fresh
      (lg , cg , fresh₂) = tseytin g fresh₁
      t                  = pos fresh₂
      -- t ↔ (lf ∨ lg):
      clauses = (neg fresh₂ ∷ lf ∷ lg ∷ [])    -- ¬t ∨ lf ∨ lg
              ∷ (t ∷ neg-lit lf ∷ [])           -- t ∨ ¬lf
              ∷ (t ∷ neg-lit lg ∷ [])           -- t ∨ ¬lg
              ∷ []
  in  (t , cf ++ cg ++ clauses , suc fresh₂)

-- Top-level conversion
nnf-to-cnf-tseytin : NNF → List (List Literal)
nnf-to-cnf-tseytin f =
  let fresh₀         = suc (max-var-nnf f)   -- fresh vars start after all existing ones
      (root , cls , _) = tseytin f fresh₀
  in  (root ∷ []) ∷ cls                       -- assert the root is true

{- -----------------------------------------------------------------------------
    Problem 12:
    SAT solver for arbitrary Formula, via NNF and Tseytin transformation.
----------------------------------------------------------------------------- -}

-- The pipeline: 
-- to-nnf (push negations inward) -> nnf-to-cnf-tseytin (Tseytin transformation to WorkingCNF) -> sat (DPLL solver)
sat-formula : Formula → Maybe Assignment
sat-formula f =
  let nnf  = to-nnf f
      wcnf = nnf-to-cnf-tseytin nnf
  in  dpll (max-steps wcnf) wcnf emptyᴬ

-- Filter out Tseytin variables, keep only original ones
filter-original : ℕ → Assignment → Assignment
filter-original max-v assn = filter (λ { (k , _) → k ≤? max-v }) assn


-- returns only the original variable assignment
sat-formula-clean : Formula → Maybe Assignment
sat-formula-clean f =
  let nnf = to-nnf f
      max-v = max-var-nnf nnf
  in Data.Maybe.map (filter-original max-v) (sat-formula f)


-- ---------TESTS -------------------------------------------------------------------
-- Formula: ¬(x₀ ∧ x₁) ∧ (x₀ ∨ x₁)
-- exactly one of x₀, x₁ is true
-- Expected: satisfiable (either x₀=true,x₁=false or x₀=false,x₁=true)
test-formula : Maybe Assignment
test-formula = sat-formula-clean ((~ (Var 0 ∧∧ Var 1)) ∧∧ (Var 0 ∨∨ Var 1))

-- Formula: x₀ ∧ ¬x₀
-- Expected: nothing
test-formula-unsat : Maybe Assignment
test-formula-unsat = sat-formula-clean (Var 0 ∧∧ (~ Var 0))