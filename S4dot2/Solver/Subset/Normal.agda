{-# OPTIONS --safe #-}

module S4dot2.Solver.Subset.Normal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_; _++_; map)
open import Cubical.Data.Bool using (Bool; true; false; not; _and_; if_then_else_)
open import Cubical.Data.Empty as Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Relation.Nullary using (Discrete; yes; no; Dec)

open import S4dot2.ListExt using (_∈_; here; there; _⊆_; mem-++-l; mem-++-r)
open import S4dot2.Solver.Subset.Core

private
  variable
    ℓ : Level

-- Normal form module, parameterized by element type
module NormalForm {A : Type ℓ} (_≟_ : Discrete A) where

  open SubsetSolver _≟_ public

  -- An atom represents either:
  -- 1. A list variable with a list of element indices to remove
  -- 2. A singleton element variable (index) with list of element indices to remove
  data Atom : Type ℓ where
    list-atom : ℕ → List ℕ → Atom
    elem-atom : ℕ → List ℕ → Atom

  -- Normal form is a list of atoms
  NormalForm : Type ℓ
  NormalForm = List Atom

  -- Apply a removal (index) to an atom
  addRemoval : ℕ → Atom → Atom
  addRemoval k (list-atom i rs) = list-atom i (k ∷ rs)
  addRemoval k (elem-atom j rs) = elem-atom j (k ∷ rs)

  -- Apply removal to all atoms in normal form
  applyRemoval : ℕ → NormalForm → NormalForm
  applyRemoval k nf = map (addRemoval k) nf

  -- Flatten expression to normal form
  flatten : Expr → NormalForm
  flatten (var i) = list-atom i [] ∷ []
  flatten []ₑ = []
  flatten (elm i) = elem-atom i [] ∷ []
  flatten (e₁ ++ₑ e₂) = flatten e₁ ++ flatten e₂
  flatten (rem e k) = applyRemoval k (flatten e)

  -- Apply a single removal (given by index)
  evalRem : ℕ → List A → List A → List A
  evalRem k xs ρe with lookupElem ρe k
  ... | nothing = xs
  ... | just v  = removeAll v xs

  -- Bridging lemmas for evalRem (to handle with-abstraction)
  private
    nothing≢just : ∀ {X : Type ℓ} {x : X} → nothing ≡ just x → ⊥
    nothing≢just p = subst (λ { nothing → Unit* ; (just _) → ⊥ }) p tt*
      where
        open import Cubical.Data.Unit using (Unit*; tt*)

    just-inj : ∀ {X : Type ℓ} {x y : X} → _≡_ {A = Maybe X} (just x) (just y) → x ≡ y
    just-inj {x = x} p = subst (λ m → x ≡ fromJust m x) p refl
      where
        fromJust : ∀ {X : Type ℓ} → Maybe X → X → X
        fromJust (just a) _ = a
        fromJust nothing def = def

  evalRem-nothing : ∀ (k : ℕ) (xs : List A) (ρe : List A)
                  → lookupElem ρe k ≡ nothing
                  → evalRem k xs ρe ≡ xs
  evalRem-nothing k xs ρe eq with lookupElem ρe k
  ... | nothing = refl
  ... | just v = ⊥-rec (nothing≢just (sym eq))

  evalRem-just : ∀ (k : ℕ) (xs : List A) (ρe : List A) (v : A)
               → lookupElem ρe k ≡ just v
               → evalRem k xs ρe ≡ removeAll v xs
  evalRem-just k xs ρe v eq with lookupElem ρe k
  ... | nothing = ⊥-rec (nothing≢just eq)
  ... | just v' = cong (λ w → removeAll w xs) (just-inj eq)

  -- Bridging lemmas for ⟦_⟧ on rem expressions
  ⟦rem⟧-nothing : ∀ (e : Expr) (k : ℕ) (ρl : List (List A)) (ρe : List A)
                → lookupElem ρe k ≡ nothing
                → ⟦ rem e k ⟧ (ρl , ρe) ≡ ⟦ e ⟧ (ρl , ρe)
  ⟦rem⟧-nothing e k ρl ρe eq with lookupElem ρe k
  ... | nothing = refl
  ... | just v = ⊥-rec (nothing≢just (sym eq))

  ⟦rem⟧-just : ∀ (e : Expr) (k : ℕ) (ρl : List (List A)) (ρe : List A) (v : A)
             → lookupElem ρe k ≡ just v
             → ⟦ rem e k ⟧ (ρl , ρe) ≡ removeAll v (⟦ e ⟧ (ρl , ρe))
  ⟦rem⟧-just e k ρl ρe v eq with lookupElem ρe k
  ... | nothing = ⊥-rec (nothing≢just eq)
  ... | just v' = cong (λ w → removeAll w (⟦ e ⟧ (ρl , ρe))) (just-inj eq)

  -- Apply a list of removals (indices)
  removeIndices : List ℕ → List A → List A → List A
  removeIndices [] xs ρe = xs
  removeIndices (k ∷ ks) xs ρe = removeIndices ks (evalRem k xs ρe) ρe

  -- Semantics of an atom
  ⟦_⟧atom : Atom → Env → List A
  ⟦ list-atom i rs ⟧atom (ρl , ρe) = removeIndices rs (lookupList ρl i) ρe
  ⟦ elem-atom i rs ⟧atom (ρl , ρe) with lookupElem ρe i
  ... | nothing = []
  ... | just v  = removeIndices rs (v ∷ []) ρe

  -- Semantics of normal form
  ⟦_⟧nf : NormalForm → Env → List A
  ⟦ [] ⟧nf ρ = []
  ⟦ a ∷ as ⟧nf ρ = ⟦ a ⟧atom ρ ++ ⟦ as ⟧nf ρ

  -- === Proofs ===

  private
    -- removeAll commutativity from previous version
    removeAll-yes : ∀ (x z : A) (zs : List A)
                  → x ≡ z → removeAll x (z ∷ zs) ≡ removeAll x zs
    removeAll-yes x z zs eq with x ≟ z
    ... | yes _ = refl
    ... | no neq = ⊥-rec (neq eq)

    removeAll-no : ∀ (x z : A) (zs : List A)
                 → (x ≡ z → ⊥) → removeAll x (z ∷ zs) ≡ z ∷ removeAll x zs
    removeAll-no x z zs neq with x ≟ z
    ... | yes eq = ⊥-rec (neq eq)
    ... | no _ = refl

    removeAll-comm-aux : ∀ (x y : A) (z : A) (zs : List A)
                       → removeAll x (removeAll y zs) ≡ removeAll y (removeAll x zs)
                       → Dec (y ≡ z) → Dec (x ≡ z)
                       → removeAll x (removeAll y (z ∷ zs)) ≡ removeAll y (removeAll x (z ∷ zs))
    removeAll-comm-aux x y z zs ih (yes yeq) (yes xeq) =
      cong (removeAll x) (removeAll-yes y z zs yeq) ∙ ih ∙ sym (cong (removeAll y) (removeAll-yes x z zs xeq))
    removeAll-comm-aux x y z zs ih (yes yeq) (no xneq) =
      cong (removeAll x) (removeAll-yes y z zs yeq) ∙ ih ∙ sym (removeAll-yes y z (removeAll x zs) yeq) ∙ sym (cong (removeAll y) (removeAll-no x z zs xneq))
    removeAll-comm-aux x y z zs ih (no yneq) (yes xeq) =
      cong (removeAll x) (removeAll-no y z zs yneq) ∙ removeAll-yes x z (removeAll y zs) xeq ∙ ih ∙ sym (cong (removeAll y) (removeAll-yes x z zs xeq))
    removeAll-comm-aux x y z zs ih (no yneq) (no xneq) =
      cong (removeAll x) (removeAll-no y z zs yneq) ∙ removeAll-no x z (removeAll y zs) xneq ∙ cong (z ∷_) ih ∙ sym (removeAll-no y z (removeAll x zs) yneq) ∙ sym (cong (removeAll y) (removeAll-no x z zs xneq))

  removeAll-comm : ∀ (x y : A) (zs : List A)
                 → removeAll x (removeAll y zs) ≡ removeAll y (removeAll x zs)
  removeAll-comm x y [] = refl
  removeAll-comm x y (z ∷ zs) = removeAll-comm-aux x y z zs (removeAll-comm x y zs) (y ≟ z) (x ≟ z)

  -- evalRem commutativity
  evalRem-comm : ∀ (k j : ℕ) (xs : List A) (ρe : List A)
               → evalRem k (evalRem j xs ρe) ρe ≡ evalRem j (evalRem k xs ρe) ρe
  evalRem-comm k j xs ρe with lookupElem ρe k | lookupElem ρe j
  ... | nothing | nothing = refl
  ... | nothing | just y = refl
  ... | just x | nothing = refl
  ... | just x | just y = removeAll-comm x y xs

  -- removeIndices commutes with evalRem
  removeIndices-evalRem : ∀ (rs : List ℕ) (k : ℕ) (xs : List A) (ρe : List A)
                        → removeIndices rs (evalRem k xs ρe) ρe ≡ evalRem k (removeIndices rs xs ρe) ρe
  removeIndices-evalRem [] k xs ρe = refl
  removeIndices-evalRem (r ∷ rs) k xs ρe =
    removeIndices rs (evalRem r (evalRem k xs ρe) ρe) ρe
      ≡⟨ cong (λ z → removeIndices rs z ρe) (evalRem-comm r k xs ρe) ⟩
    removeIndices rs (evalRem k (evalRem r xs ρe) ρe) ρe
      ≡⟨ removeIndices-evalRem rs k (evalRem r xs ρe) ρe ⟩
    evalRem k (removeIndices rs (evalRem r xs ρe) ρe) ρe
      ∎

  -- Correctness of evalRem on empty list
  evalRem-empty : ∀ (k : ℕ) (ρe : List A) → evalRem k [] ρe ≡ []
  evalRem-empty k ρe with lookupElem ρe k
  ... | nothing = refl
  ... | just v = refl

  -- Correctness of removeIndices on empty list
  removeIndices-empty : ∀ (rs : List ℕ) (ρe : List A) → removeIndices rs [] ρe ≡ []
  removeIndices-empty [] ρe = refl
  removeIndices-empty (r ∷ rs) ρe =
    -- removeIndices rs (evalRem r [] ρe)
    cong (λ z → removeIndices rs z ρe) (evalRem-empty r ρe) ∙ removeIndices-empty rs ρe

  -- addRemoval correctness
  addRemoval-correct : ∀ (k : ℕ) (a : Atom) (ρ : Env)
                     → ⟦ addRemoval k a ⟧atom ρ ≡ evalRem k (⟦ a ⟧atom ρ) (snd ρ)
  addRemoval-correct k (list-atom i rs) (ρl , ρe) =
    -- LHS: removeIndices (k ∷ rs) (lookupList ρl i) ρe
    --      = removeIndices rs (evalRem k (lookupList ρl i) ρe) ρe
    -- RHS: evalRem k (removeIndices rs (lookupList ρl i) ρe) ρe
    removeIndices-evalRem rs k (lookupList ρl i) ρe
  addRemoval-correct k (elem-atom i rs) (ρl , ρe) with lookupElem ρe i
  ... | nothing = sym (evalRem-empty k ρe)
  ... | just v = removeIndices-evalRem rs k (v ∷ []) ρe

  -- applyRemoval correctness (map)
  applyRemoval-correct : ∀ (x : ℕ) (nf : NormalForm) (ρ : Env)
                       → ⟦ applyRemoval x nf ⟧nf ρ ≡ evalRem x (⟦ nf ⟧nf ρ) (snd ρ)
  applyRemoval-correct x [] (ρl , ρe) with lookupElem ρe x
  ... | nothing = refl
  ... | just v = refl
  applyRemoval-correct x (a ∷ as) (ρl , ρe) =
    ⟦ addRemoval x a ⟧atom (ρl , ρe) ++ ⟦ applyRemoval x as ⟧nf (ρl , ρe)
      ≡⟨ cong₂ _++_ (addRemoval-correct x a (ρl , ρe)) (applyRemoval-correct x as (ρl , ρe)) ⟩
    evalRem x (⟦ a ⟧atom (ρl , ρe)) ρe ++ evalRem x (⟦ as ⟧nf (ρl , ρe)) ρe
      ≡⟨ sym (lemma-dist x (⟦ a ⟧atom (ρl , ρe)) (⟦ as ⟧nf (ρl , ρe)) ρe) ⟩
    evalRem x (⟦ a ⟧atom (ρl , ρe) ++ ⟦ as ⟧nf (ρl , ρe)) ρe
    ∎
    where
       lemma-dist : ∀ (k : ℕ) (ys zs : List A) (ρe : List A)
                  → evalRem k (ys ++ zs) ρe ≡ evalRem k ys ρe ++ evalRem k zs ρe
       lemma-dist k ys zs ρe with lookupElem ρe k
       ... | nothing = refl
       ... | just v = removeAll-++ v ys zs

  -- flatten correctness
  flatten-correct : ∀ (e : Expr) (ρ : Env) → ⟦ flatten e ⟧nf ρ ≡ ⟦ e ⟧ ρ
  flatten-correct (var i) (ρl , ρe) = ++-unit-r (lookupList ρl i)
    where
      ++-unit-r : ∀ (xs : List A) → xs ++ [] ≡ xs
      ++-unit-r [] = refl
      ++-unit-r (x ∷ xs) = cong (x ∷_) (++-unit-r xs)
  flatten-correct []ₑ ρ = refl
  flatten-correct (elm i) (ρl , ρe) with lookupElem ρe i
  ... | nothing = refl
  ... | just v = ++-unit-r (v ∷ [])
    where
      ++-unit-r : ∀ (xs : List A) → xs ++ [] ≡ xs
      ++-unit-r [] = refl
      ++-unit-r (x ∷ xs) = cong (x ∷_) (++-unit-r xs)
  flatten-correct (e₁ ++ₑ e₂) ρ =
    ⟦ flatten e₁ ++ flatten e₂ ⟧nf ρ
      ≡⟨ ++-nf (flatten e₁) (flatten e₂) ρ ⟩
    ⟦ flatten e₁ ⟧nf ρ ++ ⟦ flatten e₂ ⟧nf ρ
      ≡⟨ cong₂ _++_ (flatten-correct e₁ ρ) (flatten-correct e₂ ρ) ⟩
    ⟦ e₁ ⟧ ρ ++ ⟦ e₂ ⟧ ρ
    ∎
    where
       ++-nf : ∀ (nf1 nf2 : NormalForm) (ρ : Env)
             → ⟦ nf1 ++ nf2 ⟧nf ρ ≡ ⟦ nf1 ⟧nf ρ ++ ⟦ nf2 ⟧nf ρ
       ++-nf [] nf2 ρ = refl
       ++-nf (a ∷ as) nf2 ρ =
         ⟦ a ⟧atom ρ ++ ⟦ as ++ nf2 ⟧nf ρ
           ≡⟨ cong (⟦ a ⟧atom ρ ++_) (++-nf as nf2 ρ) ⟩
         ⟦ a ⟧atom ρ ++ (⟦ as ⟧nf ρ ++ ⟦ nf2 ⟧nf ρ)
           ≡⟨ sym (++-assoc (⟦ a ⟧atom ρ) (⟦ as ⟧nf ρ) (⟦ nf2 ⟧nf ρ)) ⟩
         (⟦ a ⟧atom ρ ++ ⟦ as ⟧nf ρ) ++ ⟦ nf2 ⟧nf ρ
         ∎
         where
           ++-assoc : ∀ (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
           ++-assoc [] ys zs = refl
           ++-assoc (x ∷ xs) ys zs = cong (x ∷_) (++-assoc xs ys zs)
  flatten-correct (rem e k) (ρl , ρe) = helper (lookupElem ρe k) refl
    where
      -- Use helper to avoid "with ... in eq" which needs REFL builtin
      helper : (m : Maybe A) → lookupElem ρe k ≡ m
             → ⟦ applyRemoval k (flatten e) ⟧nf (ρl , ρe) ≡ ⟦ rem e k ⟧ (ρl , ρe)
      helper nothing eq =
        ⟦ applyRemoval k (flatten e) ⟧nf (ρl , ρe)
          ≡⟨ applyRemoval-correct k (flatten e) (ρl , ρe) ⟩
        evalRem k (⟦ flatten e ⟧nf (ρl , ρe)) ρe
          ≡⟨ evalRem-nothing k (⟦ flatten e ⟧nf (ρl , ρe)) ρe eq ⟩
        ⟦ flatten e ⟧nf (ρl , ρe)
          ≡⟨ flatten-correct e (ρl , ρe) ⟩
        ⟦ e ⟧ (ρl , ρe)
          ≡⟨ sym (⟦rem⟧-nothing e k ρl ρe eq) ⟩
        ⟦ rem e k ⟧ (ρl , ρe)
        ∎
      helper (just v) eq =
        ⟦ applyRemoval k (flatten e) ⟧nf (ρl , ρe)
          ≡⟨ applyRemoval-correct k (flatten e) (ρl , ρe) ⟩
        evalRem k (⟦ flatten e ⟧nf (ρl , ρe)) ρe
          ≡⟨ evalRem-just k (⟦ flatten e ⟧nf (ρl , ρe)) ρe v eq ⟩
        removeAll v (⟦ flatten e ⟧nf (ρl , ρe))
          ≡⟨ cong (removeAll v) (flatten-correct e (ρl , ρe)) ⟩
        removeAll v (⟦ e ⟧ (ρl , ρe))
          ≡⟨ sym (⟦rem⟧-just e k ρl ρe v eq) ⟩
        ⟦ rem e k ⟧ (ρl , ρe)
        ∎
