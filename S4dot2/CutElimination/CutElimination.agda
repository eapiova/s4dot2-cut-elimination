{-# OPTIONS --cubical --safe #-}

-- Cut Elimination Theorem for S4.2
-- Reference: 2sequents.tex, Theorem (Cut elimination for E_K, E_K4)

module S4dot2.CutElimination.CutElimination where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl; sym; cong; subst; transport)
open import Cubical.Data.Nat using (ℕ; zero; suc; max; _+_)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-trans; zero-≤; suc-≤-suc; pred-≤-pred; _<_; ≤0→≡0; ≤-suc; ¬-<-zero; <-weaken)
open import Cubical.Data.Sigma using (Σ; _,_; fst; snd)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Induction.WellFounded using (Acc; acc; WellFounded)

open import S4dot2.Syntax hiding (_⊢_)
open import S4dot2.System
open import S4dot2.CutElimination.Base hiding (<-wf)
open import S4dot2.CutElimination.MixNew using (mix)
open import S4dot2.ListExt using (_∈_; _⊆_; mem-++-l; mem-++-r)

-- Use removeAll subset lemma from Base (which re-exports from solver)
private
  mem-removeAll-subset' = S4dot2.CutElimination.Base.mem-removeAll-subset

-- =============================================================================
-- Well-Founded Recursion on Natural Numbers
-- =============================================================================

-- Prove: all numbers ≤ n are accessible under _<_
-- By structural induction on both n and m
private
  acc≤ : (n : ℕ) → (m : ℕ) → m ≤ n → Acc _<_ m
  acc≤ n zero _ = acc λ k k<0 → ⊥-rec (¬-<-zero k<0)
  acc≤ zero (suc m) sm≤0 = ⊥-rec (¬-<-zero sm≤0)
  acc≤ (suc n) (suc m) sm≤sn = acc helper
    where
      helper : (k : ℕ) → k < suc m → Acc _<_ k
      helper k k<sm = acc≤ n k (≤-trans (pred-≤-pred k<sm) (pred-≤-pred sm≤sn))

-- Well-foundedness of _<_ on ℕ
<-wf : (n : ℕ) → Acc _<_ n
<-wf n = acc λ m m<n → acc≤ n m (<-weaken m<n)

-- =============================================================================
-- Helper Lemmas for Structural Rules
-- =============================================================================

open import Cubical.Data.Sum using (_⊎_; inl; inr)

-- removeAll produces a subset
removeAll-⊆ : {A : PFormula} {Γ : Ctx} → (Γ - A) ⊆ Γ
removeAll-⊆ y yIn = mem-removeAll-subset' yIn

-- Subset lemmas for combining with removeAll
subset-remove-left : (Γ₁ Γ₂ : Ctx) (A : PFormula) → (Γ₁ ,, (Γ₂ - A)) ⊆ (Γ₁ ,, Γ₂)
subset-remove-left Γ₁ Γ₂ A y yIn with mem-++-split {xs = Γ₁} yIn
... | inl yInΓ₁ = mem-++-l yInΓ₁
... | inr yInΓ₂-A = mem-++-r Γ₁ (removeAll-⊆ y yInΓ₂-A)

subset-remove-right : (Δ₁ Δ₂ : Ctx) (A : PFormula) → ((Δ₁ - A) ,, Δ₂) ⊆ (Δ₁ ,, Δ₂)
subset-remove-right Δ₁ Δ₂ A y yIn with mem-++-split {xs = Δ₁ - A} yIn
... | inl yInΔ₁-A =
  let
    yInΔ₁ : y ∈ Δ₁
    yInΔ₁ = removeAll-⊆ {A = A} {Γ = Δ₁} y yInΔ₁-A
  in mem-++-l {xs = Δ₁} {ys = Δ₂} yInΔ₁
... | inr yInΔ₂ = mem-++-r Δ₁ yInΔ₂

-- Helper for the left context in Cut: (Γ₁ ,, ((Γ₂ ,, [ A ^ s ]) - (A ^ s))) ⊆ (Γ₁ ,, Γ₂)
cut-sub-left : (Γ₁ Γ₂ : Ctx) (A : Formula) (s : Position)
             → (Γ₁ ,, ((Γ₂ ,, [ A ^ s ]) - (A ^ s))) ⊆ (Γ₁ ,, Γ₂)
cut-sub-left Γ₁ Γ₂ A s y yIn with mem-++-split {xs = Γ₁} yIn
... | inl yInΓ₁ = mem-++-l yInΓ₁
... | inr yInRem = mem-++-r Γ₁ (helper2 (mem-removeAll-subset' yInRem))
  where
    -- From (Γ₂ ,, [A^s]) - A^s ⊆ Γ₂ ,, [A^s] and y came from removeAll, so y ∈ Γ₂ ,, [A^s]
    -- Since y ∈ removeAll, y ≠ A^s, so y must be in Γ₂
    helper2 : y ∈ (Γ₂ ,, [ A ^ s ]) → y ∈ Γ₂
    helper2 yInΓ₂' with mem-++-split {xs = Γ₂} yInΓ₂'
    ... | inl yInΓ₂ = yInΓ₂
    ... | inr here = ⊥-rec (not-in-removeAll' y ((Γ₂ ,, [ A ^ s ])) yInRem)
      where
        not-in-removeAll' = S4dot2.CutElimination.Base.not-in-removeAll

-- Helper for the right context in Cut: ((([ A ^ s ] ,, Δ₁) - (A ^ s)) ,, Δ₂) ⊆ (Δ₁ ,, Δ₂)
cut-sub-right : (Δ₁ Δ₂ : Ctx) (A : Formula) (s : Position)
              → ((([ A ^ s ] ,, Δ₁) - (A ^ s)) ,, Δ₂) ⊆ (Δ₁ ,, Δ₂)
cut-sub-right Δ₁ Δ₂ A s y yIn with mem-++-split {xs = ([ A ^ s ] ,, Δ₁) - (A ^ s)} yIn
... | inr yInΔ₂ = mem-++-r Δ₁ yInΔ₂
... | inl yInRem =
  let
    yInHeadΔ₁ : y ∈ ([ A ^ s ] ,, Δ₁)
    yInHeadΔ₁ = mem-removeAll-subset' {x = A ^ s} {xs = [ A ^ s ] ,, Δ₁} {y = y} yInRem
  in mem-++-l {xs = Δ₁} {ys = Δ₂} (helper2 yInHeadΔ₁)
  where
    -- If y ∈ [A^s] ,, Δ₁ and y came from (... - A^s), then y ≠ A^s, so y ∈ Δ₁
    helper2 : y ∈ ([ A ^ s ] ,, Δ₁) → y ∈ Δ₁
    helper2 yIn' with mem-++-split {xs = [ A ^ s ]} yIn'
    ... | inr yInΔ₁ = yInΔ₁
    ... | inl here = ⊥-rec (not-in-removeAll' y ([ A ^ s ] ,, Δ₁) yInRem)
      where
        not-in-removeAll' = S4dot2.CutElimination.Base.not-in-removeAll

-- =============================================================================
-- Cut Elimination Theorem
-- =============================================================================

-- The main theorem: every proof can be converted to a cut-free proof
--
-- Proof strategy (following the reference):
-- By induction on (δ Π, height Π).
--
-- Case 1: δ Π = 0. Then Π is already cut-free.
-- Case 2: δ Π > 0. There is at least one Cut in Π.
--   - If the last rule is not Cut: apply IH to premises
--   - If the last rule is Cut: apply IH to premises, then use MixLemma

-- Helper: A proof with δ = 0 is cut-free
δ-zero-is-cutfree : {Γ Δ : Ctx} → (p : Γ ⊢ Δ) → δ p ≡ 0 → isCutFree p
δ-zero-is-cutfree p eq = eq

-- Helper: max of two zeros is zero
max-zero : {a b : ℕ} → a ≡ 0 → b ≡ 0 → max a b ≡ 0
max-zero {a} {b} p q = subst (λ x → max x b ≡ 0) (sym p) (subst (λ y → max 0 y ≡ 0) (sym q) refl)

-- The cut elimination theorem
-- Given any proof Π : Γ ⊢ Δ, there exists a cut-free proof of the same sequent
CutElimination : {Γ Δ : Ctx} → (Π : Γ ⊢ Δ) → Σ (Γ ⊢ Δ) isCutFree
CutElimination Π = cutElim Π (δ Π) ≤-refl (<-wf (δ Π))
  where
    -- Helper: n < suc n
    n<sn : ∀ {n} → n < suc n
    n<sn {n} = suc-≤-suc ≤-refl

    -- Main recursive function: eliminate cuts from proofs with δ ≤ n
    -- By well-founded induction on n combined with structural induction on Π
    -- The termination argument:
    -- - For non-Cut rules: we recurse on subproofs (structurally smaller)
    -- - For Cut: we first recurse on premises (structurally smaller),
    --   then apply MixLemma (gives δ ≤ degA), then recurse with smaller n
    cutElim : {Γ Δ : Ctx} → (Π : Γ ⊢ Δ) → (n : ℕ) → δ Π ≤ n → Acc _<_ n → Σ (Γ ⊢ Δ) isCutFree

    -- Base case: n = 0 means δ Π = 0, so Π is already cut-free
    cutElim Π zero δ≤0 _ = Π , ≤0→≡0 δ≤0

    -- Inductive case: n = suc m
    -- Process the proof structure
    cutElim Ax (suc n) _ _ = Ax , refl

    cutElim (Cut {Γ₁} {A} {s} {Δ₁} {Γ₂} {Δ₂} Π₁ Π₂) (suc n) δ≤sn (acc recAcc) =
      let
        -- Extract bounds for premises
        degA = degree A
        δΠ₁ = δ Π₁
        δΠ₂ = δ Π₂

        -- δ (Cut Π₁ Π₂) = max (suc degA) (max δΠ₁ δΠ₂) ≤ suc n
        -- So: suc degA ≤ suc n, meaning degA ≤ n
        -- And: δΠ₁ ≤ suc n, δΠ₂ ≤ suc n

        degA≤n : degA ≤ n
        degA≤n = pred-≤-pred (leq-max-1 (suc degA) (max δΠ₁ δΠ₂) (suc n) δ≤sn)

        δΠ₁≤sn : δΠ₁ ≤ suc n
        δΠ₁≤sn = leq-max-2-1 (suc degA) δΠ₁ δΠ₂ (suc n) δ≤sn

        δΠ₂≤sn : δΠ₂ ≤ suc n
        δΠ₂≤sn = leq-max-2-2 (suc degA) δΠ₁ δΠ₂ (suc n) δ≤sn

        -- First, get cut-free versions of the premises (recurse with suc n)
        -- Π₁ and Π₂ are structurally smaller than Cut Π₁ Π₂
        (Π₁* , cf₁) = cutElim Π₁ (suc n) δΠ₁≤sn (acc recAcc)
        (Π₂* , cf₂) = cutElim Π₂ (suc n) δΠ₂≤sn (acc recAcc)

        -- Now Π₁* and Π₂* are cut-free (δ = 0)
        -- Use MixLemma to combine them
        -- MixLemma needs: δ Π₁* ≤ degA and δ Π₂* ≤ degA
        -- Since δ Πᵢ* = 0, this is satisfied (0 ≤ degA)

        δΠ₁*≤degA : δ Π₁* ≤ degA
        δΠ₁*≤degA = subst (λ x → x ≤ degA) (sym cf₁) zero-≤

        δΠ₂*≤degA : δ Π₂* ≤ degA
        δΠ₂*≤degA = subst (λ x → x ≤ degA) (sym cf₂) zero-≤

        -- Apply mix wrapper (uses well-founded recursion internally)
        (Π₀ , δΠ₀≤degA) = mix {A = A} {s = s} refl Π₁* Π₂* δΠ₁*≤degA δΠ₂*≤degA
        -- Π₀ : Γ₁ ,, (Γ₂ - (A ^ s)) ⊢ (Δ₁ - (A ^ s)) ,, Δ₂
        -- with δ Π₀ ≤ degA

        -- Now we need to recurse on Π₀ since δ Π₀ ≤ degA ≤ n
        -- This is where well-founded recursion kicks in: n < suc n
        δΠ₀≤n : δ Π₀ ≤ n
        δΠ₀≤n = ≤-trans δΠ₀≤degA degA≤n

        (Π* , cf*) = cutElim Π₀ n δΠ₀≤n (recAcc n n<sn)

        -- Π₀ has type: Γ₁ ,, ((Γ₂ ,, [A^s]) - (A ^ s)) ⊢ (([A^s] ,, Δ₁) - (A ^ s)) ,, Δ₂
        -- We need: Γ₁ ,, Γ₂ ⊢ Δ₁ ,, Δ₂
        -- Use the module-level helpers cut-sub-left and cut-sub-right
        Π** : Γ₁ ,, Γ₂ ⊢ Δ₁ ,, Δ₂
        Π** = structural (cut-sub-left Γ₁ Γ₂ A s) (cut-sub-right Δ₁ Δ₂ A s) Π*

        cf** : isCutFree Π**
        cf** = trans (structural-preserves-δ _ _ Π*) cf*

      in (Π** , cf**)

    -- Non-cut rules: just recurse on premises (structurally smaller Π, same n)
    cutElim (W⊢ Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (W⊢ Π* , cf*)

    cutElim (⊢W Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (⊢W Π* , cf*)

    cutElim (C⊢ Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (C⊢ Π* , cf*)

    cutElim (⊢C Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (⊢C Π* , cf*)

    cutElim (Exc⊢ {Γ₁ = Γ₁} {A = A} {s = s} {B = B} {t = t} {Γ₂ = Γ₂} {Δ = Δ} Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (Exc⊢ {Γ₁ = Γ₁} {A = A} {s = s} {B = B} {t = t} {Γ₂ = Γ₂} {Δ = Δ} Π* , cf*)

    cutElim (⊢Exc {Γ = Γ} {Δ₁ = Δ₁} {A = A} {s = s} {B = B} {t = t} {Δ₂ = Δ₂} Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (⊢Exc {Γ = Γ} {Δ₁ = Δ₁} {A = A} {s = s} {B = B} {t = t} {Δ₂ = Δ₂} Π* , cf*)

    cutElim (¬⊢ Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (¬⊢ Π* , cf*)

    cutElim (⊢¬ Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (⊢¬ Π* , cf*)

    cutElim (∧₁⊢ Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (∧₁⊢ Π* , cf*)

    cutElim (∧₂⊢ Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (∧₂⊢ Π* , cf*)

    cutElim (⊢∧ Π₁ Π₂) (suc n) δ≤sn wf =
      let
        δΠ₁≤sn = leq-max-1 (δ Π₁) (δ Π₂) (suc n) δ≤sn
        δΠ₂≤sn = leq-max-2 (δ Π₁) (δ Π₂) (suc n) δ≤sn
        (Π₁* , cf₁*) = cutElim Π₁ (suc n) δΠ₁≤sn wf
        (Π₂* , cf₂*) = cutElim Π₂ (suc n) δΠ₂≤sn wf
      in (⊢∧ Π₁* Π₂* , max-zero cf₁* cf₂*)

    cutElim (∨⊢ Π₁ Π₂) (suc n) δ≤sn wf =
      let
        δΠ₁≤sn = leq-max-1 (δ Π₁) (δ Π₂) (suc n) δ≤sn
        δΠ₂≤sn = leq-max-2 (δ Π₁) (δ Π₂) (suc n) δ≤sn
        (Π₁* , cf₁*) = cutElim Π₁ (suc n) δΠ₁≤sn wf
        (Π₂* , cf₂*) = cutElim Π₂ (suc n) δΠ₂≤sn wf
      in (∨⊢ Π₁* Π₂* , max-zero cf₁* cf₂*)

    cutElim (⊢∨₁ Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (⊢∨₁ Π* , cf*)

    cutElim (⊢∨₂ Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (⊢∨₂ Π* , cf*)

    cutElim (⇒⊢ Π₁ Π₂) (suc n) δ≤sn wf =
      let
        δΠ₁≤sn = leq-max-1 (δ Π₁) (δ Π₂) (suc n) δ≤sn
        δΠ₂≤sn = leq-max-2 (δ Π₁) (δ Π₂) (suc n) δ≤sn
        (Π₁* , cf₁*) = cutElim Π₁ (suc n) δΠ₁≤sn wf
        (Π₂* , cf₂*) = cutElim Π₂ (suc n) δΠ₂≤sn wf
      in (⇒⊢ Π₁* Π₂* , max-zero cf₁* cf₂*)

    cutElim (⊢⇒ Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (⊢⇒ Π* , cf*)

    cutElim (□⊢ Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (□⊢ Π* , cf*)

    cutElim (⊢□ ext freshΓ freshΔ Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (⊢□ ext freshΓ freshΔ Π* , cf*)

    cutElim (♢⊢ ext freshΓ freshΔ Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (♢⊢ ext freshΓ freshΔ Π* , cf*)

    cutElim (⊢♢ Π) (suc n) δ≤sn wf =
      let (Π* , cf*) = cutElim Π (suc n) δ≤sn wf
      in (⊢♢ Π* , cf*)

-- =============================================================================
-- Corollaries
-- =============================================================================

-- Alternative formulation: extract just the cut-free proof
cutFreeProof : {Γ Δ : Ctx} → (Π : Γ ⊢ Δ) → Γ ⊢ Δ
cutFreeProof Π = fst (CutElimination Π)

-- The extracted proof is indeed cut-free
cutFreeProof-isCutFree : {Γ Δ : Ctx} → (Π : Γ ⊢ Δ) → isCutFree (cutFreeProof Π)
cutFreeProof-isCutFree Π = snd (CutElimination Π)
