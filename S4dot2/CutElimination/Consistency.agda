{-# OPTIONS --cubical --safe #-}

-- Consistency for S4.2
-- Reference: 2sequents.tex, Corollary (Consistency)
--
-- E_S4.2 is consistent, namely there is no proof of the empty sequent ⊢

module S4dot2.CutElimination.Consistency where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl; sym; cong; subst)
open import Cubical.Data.Nat using (ℕ; zero; suc; max)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤0→≡0)
open import Cubical.Data.Nat.Properties using (snotz)
open import Cubical.Data.Sigma using (Σ; _,_; fst; snd)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Unit using (Unit; tt)

open import S4dot2.Syntax hiding (_⊢_)
open import S4dot2.System
open import S4dot2.CutElimination.Defs
open import S4dot2.CutElimination.CutElimination

-- =============================================================================
-- Consistency: No Proof of the Empty Sequent
-- =============================================================================

-- The key observation: In a cut-free proof, the last rule determines
-- the structure of the conclusion. All rules require at least one formula
-- in either the antecedent or succedent.

-- First, let's show that a cut-free proof of [] ⊢ [] is impossible
-- by case analysis on the last rule.

-- Helper: no cut-free proof of the empty sequent
noCutFreeProofOfEmpty : (Π : [] ⊢ []) → isCutFree Π → ⊥
-- Case analysis on the proof structure:
-- Each rule requires some formula to be present

-- Ax requires [A^s] ⊢ [A^s], not [] ⊢ []
-- But Ax has type [A^s] ⊢ [A^s], so the pattern can't match [] ⊢ []
-- Actually, we need to show that no constructor can produce [] ⊢ []

-- Let's analyze each possible last rule:
-- - Ax: conclusion is [A^s] ⊢ [A^s] ≠ [] ⊢ []
-- - Cut: not cut-free
-- - W⊢: conclusion has at least [A^s] on the left
-- - ⊢W: conclusion has at least [A^s] on the right
-- - C⊢: conclusion has at least [A^s] on the left
-- - ⊢C: conclusion has at least [A^s] on the right
-- - Exc⊢: conclusion has at least [B^t],[A^s] on the left
-- - ⊢Exc: conclusion has at least [B^t],[A^s] on the right
-- - ¬⊢: conclusion has at least [¬A^s] on the left
-- - ⊢¬: conclusion has at least [¬A^s] on the right
-- - All logical rules: conclusion has at least the principal formula

-- The proof uses that [] cannot be unified with lists containing elements

-- Since Agda cannot directly pattern match on the empty case for all rules,
-- we need to show that each constructor's conclusion type doesn't unify with [] ⊢ []

-- suc n ≤ 0 is impossible
private
  suc-not-≤-zero : {n : ℕ} → suc n ≤ 0 → ⊥
  suc-not-≤-zero {n} sn≤0 = snotz (≤0→≡0 sn≤0)

  -- Helper: suc n ≤ max (suc n) m
  suc-≤-max : (n m : ℕ) → suc n ≤ max (suc n) m
  suc-≤-max n zero = ≤-refl
  suc-≤-max n (suc m) = leq-max-1 (suc n) (suc m) (max (suc n) (suc m)) ≤-refl

  -- max (suc n) m ≥ 1, so it cannot equal 0
  max-suc-neq-zero : {n m : ℕ} → max (suc n) m ≡ 0 → ⊥
  max-suc-neq-zero {n} {m} eq = suc-not-≤-zero (subst (λ x → suc n ≤ x) eq (suc-≤-max n m))

-- Key insight: any proof of [] ⊢ [] must use Cut (indirectly or directly),
-- and Cut proofs are never cut-free.
-- Actually, we prove: if Π : [] ⊢ [], then δ Π > 0
-- This is because:
-- - Ax has type [A^s] ⊢ [A^s], so it can't prove [] ⊢ []
-- - All logical and structural rules preserve "has at least one formula"
-- - Only Cut can eliminate all formulas

-- However, the cut-freeness condition (δ = 0) rules out Cut.
-- So a cut-free proof of [] ⊢ [] is impossible.

-- The proof is by case analysis on the proof structure.
-- Key insight: Any proof Π : [] ⊢ [] must use Cut somewhere,
-- and any proof with a Cut has δ > 0, contradicting isCutFree.

-- Helper: x ∷ xs ≠ [] (using subst for Cubical Agda)
∷≠[] : {A : Type} {x : A} {xs : List A} → x ∷ xs ≡ [] → ⊥
∷≠[] eq = subst (λ { [] → ⊥ ; (_ ∷ _) → Unit }) eq tt

-- Helper: If xs ++ ys = [], then xs = [] and ys = []
++-conicalˡ : {A : Type} (xs ys : List A) → xs ++ ys ≡ [] → xs ≡ []
++-conicalˡ [] ys p = refl
++-conicalˡ (x ∷ xs) ys p = ⊥-rec (∷≠[] p)

++-conicalʳ : {A : Type} (xs ys : List A) → xs ++ ys ≡ [] → ys ≡ []
++-conicalʳ [] ys p = p
++-conicalʳ (x ∷ xs) ys p = ⊥-rec (∷≠[] p)

-- Helper for nested concatenations: xs ++ (ys ++ zs) = [] implies zs = []
++-conical-nested : {A : Type} (xs ys zs : List A) → xs ++ (ys ++ zs) ≡ [] → zs ≡ []
++-conical-nested xs ys zs eq = ++-conicalʳ ys zs (++-conicalʳ xs (ys ++ zs) eq)

-- Helper for deeply nested: ((xs ++ ys) ++ zs) ++ ws = [] implies ys = []
-- Structure: ((Δ₁ ,, [B^t]) ,, [A^s]) ,, Δ₂ = [] ⟹ [B^t] = []
++-conical-deep-2 : {A : Type} (xs ys zs ws : List A) → ((xs ++ ys) ++ zs) ++ ws ≡ [] → ys ≡ []
++-conical-deep-2 xs ys zs ws eq =
  let step1 = ++-conicalˡ ((xs ++ ys) ++ zs) ws eq  -- (xs ++ ys) ++ zs = []
      step2 = ++-conicalˡ (xs ++ ys) zs step1       -- xs ++ ys = []
  in ++-conicalʳ xs ys step2                         -- ys = []

-- Helper: ((xs ++ ys) ++ zs) ++ ws = [] implies zs = []
++-conical-deep-3 : {A : Type} (xs ys zs ws : List A) → ((xs ++ ys) ++ zs) ++ ws ≡ [] → zs ≡ []
++-conical-deep-3 xs ys zs ws eq =
  let step1 = ++-conicalˡ ((xs ++ ys) ++ zs) ws eq  -- (xs ++ ys) ++ zs = []
  in ++-conicalʳ (xs ++ ys) zs step1                 -- zs = []

-- Now we can prove that any proof of [] ⊢ [] has δ > 0
-- by showing that only Cut can produce it, and Cut has δ > 0
noCutFreeProofOfEmpty Π cf = helper Π refl refl cf
  where
    -- We explicitly track that the context equals []
    helper : {Γ Δ : Ctx} → (Π : Γ ⊢ Δ) → Γ ≡ [] → Δ ≡ [] → δ Π ≡ 0 → ⊥
    -- Cut case: δ (Cut p₁ p₂) = max (suc (degree A)) ... ≥ 1
    helper (Cut {A = A} p₁ p₂) Γ≡[] Δ≡[] δ≡0 =
      max-suc-neq-zero {n = degree A} {m = max (δ p₁) (δ p₂)} δ≡0
    -- Ax case: requires [A^s] ⊢ [A^s], not [] ⊢ []
    helper Ax Γ≡[] Δ≡[] δ≡0 = ∷≠[] Γ≡[]
    -- Structural rules: all require formulas in conclusion
    helper (W⊢ {Γ} {Δ} {A} {s} p) Γ≡[] Δ≡[] δ≡0 = ∷≠[] (++-conicalʳ Γ [ A ^ s ] Γ≡[])
    helper (⊢W {Γ} {Δ} {A} {s} p) Γ≡[] Δ≡[] δ≡0 = ∷≠[] (++-conicalˡ [ A ^ s ] Δ Δ≡[])
    helper (C⊢ p) Γ≡[] Δ≡[] δ≡0 = ∷≠[] (++-conicalʳ _ _ Γ≡[])
    helper (⊢C p) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Δ≡[]
    -- Exc⊢: conclusion antecedent is ((Γ₁ ,, [B^t]) ,, [A^s]) ,, Γ₂
    helper (Exc⊢ {Γ₁} {A} {s} {B} {t} {Γ₂} {Δ} p) Γ≡[] Δ≡[] δ≡0 =
      ∷≠[] (++-conical-deep-2 Γ₁ [ B ^ t ] [ A ^ s ] Γ₂ Γ≡[])
    -- ⊢Exc: conclusion succedent is ((Δ₁ ,, [B^t]) ,, [A^s]) ,, Δ₂
    helper (⊢Exc {Γ} {Δ₁} {A} {s} {B} {t} {Δ₂} p) Γ≡[] Δ≡[] δ≡0 =
      ∷≠[] (++-conical-deep-2 Δ₁ [ B ^ t ] [ A ^ s ] Δ₂ Δ≡[])
    -- Logical rules: all have principal formulas in conclusion
    helper (¬⊢ p) Γ≡[] Δ≡[] δ≡0 = ∷≠[] (++-conicalʳ _ _ Γ≡[])
    helper (⊢¬ p) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Δ≡[]
    helper (∧₁⊢ p) Γ≡[] Δ≡[] δ≡0 = ∷≠[] (++-conicalʳ _ _ Γ≡[])
    helper (∧₂⊢ p) Γ≡[] Δ≡[] δ≡0 = ∷≠[] (++-conicalʳ _ _ Γ≡[])
    helper (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} p₁ p₂) Γ≡[] Δ≡[] δ≡0 =
      ∷≠[] (++-conicalˡ [ (A ∧ B) ^ s ] (Δ₁ ++ Δ₂) Δ≡[])
    helper (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} p₁ p₂) Γ≡[] Δ≡[] δ≡0 =
      ∷≠[] (++-conical-nested Γ₁ Γ₂ [ (A ∨ B) ^ s ] Γ≡[])
    helper (⊢∨₁ p) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Δ≡[]
    helper (⊢∨₂ p) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Δ≡[]
    helper (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} p₁ p₂) Γ≡[] Δ≡[] δ≡0 =
      ∷≠[] (++-conical-nested Γ₁ Γ₂ [ (A ⇒ B) ^ s ] Γ≡[])
    helper (⊢⇒ p) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Δ≡[]
    -- Modal rules
    helper (□⊢ p) Γ≡[] Δ≡[] δ≡0 = ∷≠[] (++-conicalʳ _ _ Γ≡[])
    helper (⊢□ _ _ _ p) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Δ≡[]
    helper (♢⊢ _ _ _ p) Γ≡[] Δ≡[] δ≡0 = ∷≠[] (++-conicalʳ _ _ Γ≡[])
    helper (⊢♢ p) Γ≡[] Δ≡[] δ≡0 = ∷≠[] Δ≡[]

-- =============================================================================
-- Main Consistency Theorem
-- =============================================================================

-- Consistency: there is no E_S4.2 proof of the empty sequent
Consistency : ([] ⊢ []) → ⊥
Consistency Π =
  let (Π* , cf*) = CutElimination Π
  in noCutFreeProofOfEmpty Π* cf*

-- =============================================================================
-- Corollary: S4.2 is consistent
-- =============================================================================

-- This means we cannot derive a contradiction in the system.
-- In particular, for any formula A, we cannot have both a proof of A and ¬A
-- from empty contexts (otherwise we could cut them to get [] ⊢ []).
