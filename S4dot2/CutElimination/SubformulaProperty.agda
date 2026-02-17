{-# OPTIONS --safe #-}

-- Subformula Property for S4.2
-- Reference: 2sequents.tex, Corollary (Subformula Property)
--
-- Each formula occurring in a cut-free proof Π is a subformula of
-- some formula occurring in the conclusion of Π.

module S4dot2.CutElimination.SubformulaProperty where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl; sym; cong; cong₂; subst; transport; _∙_)
open import Cubical.Data.Nat using (ℕ; zero; suc; max; _+_)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-trans; ≤0→≡0; left-≤-max; right-≤-max)
open import Cubical.Data.Nat.Properties using (snotz)
open import Cubical.Data.Sigma using (Σ; _,_; fst; snd; _×_)
open import Cubical.Data.List using (List; []; _∷_; _++_; map)
open import Cubical.Data.List.Properties using (++-assoc)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)

open import S4dot2.Syntax hiding (_⊢_) renaming (_∧_ to _and'_; _∨_ to _or'_)
open import S4dot2.System
open import S4dot2.CutElimination.Defs
open import S4dot2.ListExt using (_∈_; mem-++-l; mem-++-r)
open import S4dot2.SchutteCompleteness.Subformula using (sequentSubformulas; contextSubformulas; positionedSubformulas; allSubformulas; allSubformulas-fuel; formulaDepth)

-- =============================================================================
-- Faithful Subformula Relation (matching paper's Definition 3.1)
-- =============================================================================

-- The paper's definition of subformula for positioned formulas:
--   Sub(p^s) = {p^s}
--   Sub((¬A)^s) = {(¬A)^s} ∪ Sub(A^s)
--   Sub((A#B)^s) = {(A#B)^s} ∪ Sub(A^s) ∪ Sub(B^s)  for # ∈ {∧,∨,→}
--   Sub((□A)^s) = {(□A)^s} ∪ ⋃{Sub(A^(s∘t)) : t ∈ P}
--   Sub((♢A)^s) = {(♢A)^s} ∪ ⋃{Sub(A^(s∘t)) : t ∈ P}
--
-- Key insight: For modal formulas, subformulas include ALL position extensions!

data _isSubformulaOf_ : PFormula → PFormula → Type where
  -- Reflexivity
  refl-sub : ∀ {A s} → (A ^ s) isSubformulaOf (A ^ s)

  -- Negation: subformulas of A^s are subformulas of (¬A)^s
  ¬-sub : ∀ {A s pf} → pf isSubformulaOf (A ^ s) → pf isSubformulaOf ((¬ A) ^ s)

  -- Conjunction: subformulas of A^s or B^s are subformulas of (A∧B)^s
  ∧₁-sub : ∀ {A B s pf} → pf isSubformulaOf (A ^ s) → pf isSubformulaOf ((A and' B) ^ s)
  ∧₂-sub : ∀ {A B s pf} → pf isSubformulaOf (B ^ s) → pf isSubformulaOf ((A and' B) ^ s)

  -- Disjunction: subformulas of A^s or B^s are subformulas of (A∨B)^s
  ∨₁-sub : ∀ {A B s pf} → pf isSubformulaOf (A ^ s) → pf isSubformulaOf ((A or' B) ^ s)
  ∨₂-sub : ∀ {A B s pf} → pf isSubformulaOf (B ^ s) → pf isSubformulaOf ((A or' B) ^ s)

  -- Implication: subformulas of A^s or B^s are subformulas of (A⇒B)^s
  ⇒₁-sub : ∀ {A B s pf} → pf isSubformulaOf (A ^ s) → pf isSubformulaOf ((A ⇒ B) ^ s)
  ⇒₂-sub : ∀ {A B s pf} → pf isSubformulaOf (B ^ s) → pf isSubformulaOf ((A ⇒ B) ^ s)

  -- Box: subformulas of A^t where s ⊑ t are subformulas of (□A)^s
  -- For S4.2, we use the subset relation (⊑) to match the system's modal rules
  □-sub : ∀ {A s t pf} → (s ⊑ t) → pf isSubformulaOf (A ^ t) → pf isSubformulaOf ((□ A) ^ s)

  -- Diamond: subformulas of A^t where s ⊑ t are subformulas of (♢A)^s
  ♢-sub : ∀ {A s t pf} → (s ⊑ t) → pf isSubformulaOf (A ^ t) → pf isSubformulaOf ((♢ A) ^ s)

-- Subformula of a context: pf is a subformula of some formula in Γ
_isSubformulaOfCtx_ : PFormula → Ctx → Type
pf isSubformulaOfCtx Γ = Σ PFormula λ qf → (qf ∈ Γ) × (pf isSubformulaOf qf)

-- Subformula of a sequent: pf is a subformula of some formula in Γ or Δ
isSubformulaOfSeq : PFormula → Ctx → Ctx → Type
isSubformulaOfSeq pf Γ Δ = (pf isSubformulaOfCtx Γ) ⊎ (pf isSubformulaOfCtx Δ)

-- =============================================================================
-- All formulas in a proof (including ALL sequents)
-- =============================================================================

-- Collects all formulas from all sequents in the proof tree
allFormulasInProof : {Γ Δ : Ctx} → Γ ⊢ Δ → List PFormula
allFormulasInProof {Γ} {Δ} Ax = Γ ++ Δ
allFormulasInProof {Γ} {Δ} (Cut Π₁ Π₂) = (Γ ++ Δ) ++ allFormulasInProof Π₁ ++ allFormulasInProof Π₂
allFormulasInProof {Γ} {Δ} (W⊢ Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (⊢W Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (C⊢ Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (⊢C Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (Exc⊢ Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (⊢Exc Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (¬⊢ Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (⊢¬ Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (∧₁⊢ Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (∧₂⊢ Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (⊢∧ Π₁ Π₂) = (Γ ++ Δ) ++ allFormulasInProof Π₁ ++ allFormulasInProof Π₂
allFormulasInProof {Γ} {Δ} (∨⊢ Π₁ Π₂) = (Γ ++ Δ) ++ allFormulasInProof Π₁ ++ allFormulasInProof Π₂
allFormulasInProof {Γ} {Δ} (⊢∨₁ Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (⊢∨₂ Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (⇒⊢ Π₁ Π₂) = (Γ ++ Δ) ++ allFormulasInProof Π₁ ++ allFormulasInProof Π₂
allFormulasInProof {Γ} {Δ} (⊢⇒ Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (□⊢ Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (⊢□ _ _ _ Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (♢⊢ _ _ _ Π) = (Γ ++ Δ) ++ allFormulasInProof Π
allFormulasInProof {Γ} {Δ} (⊢♢ Π) = (Γ ++ Δ) ++ allFormulasInProof Π

-- =============================================================================
-- Formulas occurring in a proof
-- =============================================================================

-- All positioned formulas occurring in a proof tree
-- This includes all formulas in all sequents (both premises and conclusion)
formulasInProof : {Γ Δ : Ctx} → Γ ⊢ Δ → List PFormula
formulasInProof Ax = []  -- Just [A^s] ⊢ [A^s], formulas are in the conclusion
formulasInProof (Cut {Γ₁} {A} {s} {Δ₁} {Γ₂} {Δ₂} Π₁ Π₂) =
  [ A ^ s ] ++ formulasInProof Π₁ ++ formulasInProof Π₂
formulasInProof (W⊢ Π) = formulasInProof Π
formulasInProof (⊢W Π) = formulasInProof Π
formulasInProof (C⊢ Π) = formulasInProof Π
formulasInProof (⊢C Π) = formulasInProof Π
formulasInProof (Exc⊢ Π) = formulasInProof Π
formulasInProof (⊢Exc Π) = formulasInProof Π
formulasInProof (¬⊢ Π) = formulasInProof Π
formulasInProof (⊢¬ Π) = formulasInProof Π
formulasInProof (∧₁⊢ Π) = formulasInProof Π
formulasInProof (∧₂⊢ Π) = formulasInProof Π
formulasInProof (⊢∧ Π₁ Π₂) = formulasInProof Π₁ ++ formulasInProof Π₂
formulasInProof (∨⊢ Π₁ Π₂) = formulasInProof Π₁ ++ formulasInProof Π₂
formulasInProof (⊢∨₁ Π) = formulasInProof Π
formulasInProof (⊢∨₂ Π) = formulasInProof Π
formulasInProof (⇒⊢ Π₁ Π₂) = formulasInProof Π₁ ++ formulasInProof Π₂
formulasInProof (⊢⇒ Π) = formulasInProof Π
formulasInProof (□⊢ Π) = formulasInProof Π
formulasInProof (⊢□ _ _ _ Π) = formulasInProof Π
formulasInProof (♢⊢ _ _ _ Π) = formulasInProof Π
formulasInProof (⊢♢ Π) = formulasInProof Π

-- =============================================================================
-- Key observation for cut-free proofs
-- =============================================================================

-- In a cut-free proof (δ = 0), there are no Cut constructors.
-- Since Cut is the only rule that introduces formulas not in the conclusion
-- (the cut formula A^s), all formulas must come from breaking down the conclusion.

-- For most rules, the formulas in premises are subformulas of the conclusion.
-- The exception is Cut, which introduces a new formula.

-- Membership in empty list is absurd
∈-[]→⊥ : {A : Type} {x : A} → x ∈ [] → ⊥
∈-[]→⊥ ()

-- For cut-free proofs, formulasInProof is empty
-- This is because only Cut adds formulas, and cut-free proofs have no Cut
formulasInProof-cutfree : {Γ Δ : Ctx} (Π : Γ ⊢ Δ) → isCutFree Π → formulasInProof Π ≡ []
formulasInProof-cutfree Ax cf = refl
formulasInProof-cutfree (Cut {A = A} Π₁ Π₂) cf = ⊥-rec (snotz (≤0→≡0 helper))
  where
    -- δ (Cut ...) = max (suc (degree A)) (max (δ Π₁) (δ Π₂)) ≥ suc (degree A) ≥ 1
    -- If cf : δ (Cut ...) ≡ 0, this is absurd
    helper : suc (degree A) ≤ 0
    helper = subst (suc (degree A) ≤_) cf (left-≤-max {m = suc (degree A)} {n = max (δ Π₁) (δ Π₂)})
formulasInProof-cutfree (W⊢ Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (⊢W Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (C⊢ Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (⊢C Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (Exc⊢ Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (⊢Exc Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (¬⊢ Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (⊢¬ Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (∧₁⊢ Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (∧₂⊢ Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (⊢∧ Π₁ Π₂) cf = cong₂ _++_
  (formulasInProof-cutfree Π₁ (≤0→≡0 (subst (δ Π₁ ≤_) cf (left-≤-max {m = δ Π₁} {n = δ Π₂}))))
  (formulasInProof-cutfree Π₂ (≤0→≡0 (subst (δ Π₂ ≤_) cf (right-≤-max {n = δ Π₂} {m = δ Π₁}))))
formulasInProof-cutfree (∨⊢ Π₁ Π₂) cf = cong₂ _++_
  (formulasInProof-cutfree Π₁ (≤0→≡0 (subst (δ Π₁ ≤_) cf (left-≤-max {m = δ Π₁} {n = δ Π₂}))))
  (formulasInProof-cutfree Π₂ (≤0→≡0 (subst (δ Π₂ ≤_) cf (right-≤-max {n = δ Π₂} {m = δ Π₁}))))
formulasInProof-cutfree (⊢∨₁ Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (⊢∨₂ Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (⇒⊢ Π₁ Π₂) cf = cong₂ _++_
  (formulasInProof-cutfree Π₁ (≤0→≡0 (subst (δ Π₁ ≤_) cf (left-≤-max {m = δ Π₁} {n = δ Π₂}))))
  (formulasInProof-cutfree Π₂ (≤0→≡0 (subst (δ Π₂ ≤_) cf (right-≤-max {n = δ Π₂} {m = δ Π₁}))))
formulasInProof-cutfree (⊢⇒ Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (□⊢ Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (⊢□ _ _ _ Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (♢⊢ _ _ _ Π) cf = formulasInProof-cutfree Π cf
formulasInProof-cutfree (⊢♢ Π) cf = formulasInProof-cutfree Π cf

-- =============================================================================
-- Helper lemmas for monotonicity
-- =============================================================================

-- contextSubformulas distributes over ++
ctx-sub-++ : (Γ₁ Γ₂ : Ctx) → contextSubformulas (Γ₁ ++ Γ₂) ≡ contextSubformulas Γ₁ ++ contextSubformulas Γ₂
ctx-sub-++ [] Γ₂ = refl
ctx-sub-++ (pf ∷ Γ₁) Γ₂ = cong (positionedSubformulas pf ++_) (ctx-sub-++ Γ₁ Γ₂)
                        ∙ sym (++-assoc (positionedSubformulas pf) (contextSubformulas Γ₁) (contextSubformulas Γ₂))
  where
    open import Cubical.Data.List.Properties using (++-assoc)

-- Membership is preserved when adding to the left of context subformulas
ctx-sub-mono-l : {Γ Γ' : Ctx} {pf : PFormula}
               → pf ∈ contextSubformulas Γ → pf ∈ contextSubformulas (Γ' ++ Γ)
ctx-sub-mono-l {Γ} {Γ'} {pf} pfIn = subst (pf ∈_) (sym (ctx-sub-++ Γ' Γ)) (mem-++-r (contextSubformulas Γ') pfIn)

-- Membership is preserved when adding to the right of context subformulas
ctx-sub-mono-r : {Γ Γ' : Ctx} {pf : PFormula}
               → pf ∈ contextSubformulas Γ → pf ∈ contextSubformulas (Γ ++ Γ')
ctx-sub-mono-r {Γ} {Γ'} {pf} pfIn = subst (pf ∈_) (sym (ctx-sub-++ Γ Γ')) (mem-++-l pfIn)

-- Sequent subformulas monotonicity: adding to left context
seq-sub-mono-Γ-l : {Γ Γ' Δ : Ctx} {pf : PFormula}
                 → pf ∈ sequentSubformulas Γ Δ → pf ∈ sequentSubformulas (Γ' ++ Γ) Δ
seq-sub-mono-Γ-l {Γ} {Γ'} {Δ} {pf} pfIn with mem-++-split {xs = contextSubformulas Γ} pfIn
... | inl pfInΓ = mem-++-l (ctx-sub-mono-l {Γ} {Γ'} pfInΓ)
... | inr pfInΔ = mem-++-r (contextSubformulas (Γ' ++ Γ)) pfInΔ

-- Sequent subformulas monotonicity: adding to right context
seq-sub-mono-Γ-r : {Γ Γ' Δ : Ctx} {pf : PFormula}
                 → pf ∈ sequentSubformulas Γ Δ → pf ∈ sequentSubformulas (Γ ++ Γ') Δ
seq-sub-mono-Γ-r {Γ} {Γ'} {Δ} {pf} pfIn with mem-++-split {xs = contextSubformulas Γ} pfIn
... | inl pfInΓ = mem-++-l (ctx-sub-mono-r {Γ} {Γ'} pfInΓ)
... | inr pfInΔ = mem-++-r (contextSubformulas (Γ ++ Γ')) pfInΔ

-- Sequent subformulas monotonicity: adding to left of succedent
seq-sub-mono-Δ-l : {Γ Δ Δ' : Ctx} {pf : PFormula}
                 → pf ∈ sequentSubformulas Γ Δ → pf ∈ sequentSubformulas Γ (Δ' ++ Δ)
seq-sub-mono-Δ-l {Γ} {Δ} {Δ'} {pf} pfIn with mem-++-split {xs = contextSubformulas Γ} pfIn
... | inl pfInΓ = mem-++-l pfInΓ
... | inr pfInΔ = mem-++-r (contextSubformulas Γ) (ctx-sub-mono-l {Δ} {Δ'} pfInΔ)

-- Sequent subformulas monotonicity: adding to right of succedent
seq-sub-mono-Δ-r : {Γ Δ Δ' : Ctx} {pf : PFormula}
                 → pf ∈ sequentSubformulas Γ Δ → pf ∈ sequentSubformulas Γ (Δ ++ Δ')
seq-sub-mono-Δ-r {Γ} {Δ} {Δ'} {pf} pfIn with mem-++-split {xs = contextSubformulas Γ} pfIn
... | inl pfInΓ = mem-++-l pfInΓ
... | inr pfInΔ = mem-++-r (contextSubformulas Γ) (ctx-sub-mono-r {Δ} {Δ'} pfInΔ)

-- Helper: membership in duplicate list implies membership in single
-- xs ++ ys ++ ys contains pf ⟹ xs ++ ys contains pf
mem-++-dup : {A : Type} {x : A} (xs ys : List A) → x ∈ (xs ++ ys) ++ ys → x ∈ xs ++ ys
mem-++-dup {_} {x} xs ys xIn with mem-++-split {xs = xs ++ ys} xIn
... | inl xInXsYs = xInXsYs
... | inr xInYs = mem-++-r xs xInYs

-- Single element context subformulas
ctx-sub-single : (P : PFormula) → contextSubformulas [ P ] ≡ positionedSubformulas P ++ []
ctx-sub-single P = refl

-- Context subformulas contraction: duplicate formula doesn't add new subformulas
ctx-sub-contract : {Γ : Ctx} {P : PFormula} {pf : PFormula}
                 → pf ∈ contextSubformulas ((Γ ++ [ P ]) ++ [ P ])
                 → pf ∈ contextSubformulas (Γ ++ [ P ])
ctx-sub-contract {Γ} {P} {pf} pfIn =
  subst (pf ∈_) (sym (ctx-sub-++ Γ [ P ]))
    (mem-++-dup' (contextSubformulas Γ) (positionedSubformulas P)
      (subst (pf ∈_) step2
        (subst (pf ∈_) step1 pfIn)))
  where
    open import Cubical.Data.List.Properties using (++-assoc; ++-unit-r)
    -- xs ++ (ys ++ []) membership implies xs ++ ys membership
    mem-++-dup' : {A : Type} {x : A} (xs ys : List A) → x ∈ (xs ++ (ys ++ [])) ++ (ys ++ []) → x ∈ xs ++ (ys ++ [])
    mem-++-dup' xs ys xIn with mem-++-split {xs = xs ++ (ys ++ [])} xIn
    ... | inl xInXsYs = xInXsYs
    ... | inr xInYs = mem-++-r xs xInYs
    -- Step 1: ((Γ ++ [P]) ++ [P]) unfolds
    step1 : contextSubformulas ((Γ ++ [ P ]) ++ [ P ]) ≡ contextSubformulas (Γ ++ [ P ]) ++ (positionedSubformulas P ++ [])
    step1 = ctx-sub-++ (Γ ++ [ P ]) [ P ]
    -- Step 2: contextSubformulas (Γ ++ [P]) unfolds
    step2 : contextSubformulas (Γ ++ [ P ]) ++ (positionedSubformulas P ++ []) ≡ (contextSubformulas Γ ++ (positionedSubformulas P ++ [])) ++ (positionedSubformulas P ++ [])
    step2 = cong (_++ (positionedSubformulas P ++ [])) (ctx-sub-++ Γ [ P ])

-- Sequent subformulas contraction for antecedent
seq-sub-contract-Γ : {Γ Δ : Ctx} {P : PFormula} {pf : PFormula}
                   → pf ∈ sequentSubformulas ((Γ ++ [ P ]) ++ [ P ]) Δ
                   → pf ∈ sequentSubformulas (Γ ++ [ P ]) Δ
seq-sub-contract-Γ {Γ} {Δ} {P} {pf} pfIn with mem-++-split {xs = contextSubformulas ((Γ ++ [ P ]) ++ [ P ])} pfIn
... | inl pfInΓ = mem-++-l (ctx-sub-contract {Γ} {P} pfInΓ)
... | inr pfInΔ = mem-++-r (contextSubformulas (Γ ++ [ P ])) pfInΔ

-- Sequent subformulas contraction for succedent
seq-sub-contract-Δ : {Γ Δ : Ctx} {P : PFormula} {pf : PFormula}
                   → pf ∈ sequentSubformulas Γ (([ P ] ++ [ P ]) ++ Δ)
                   → pf ∈ sequentSubformulas Γ ([ P ] ++ Δ)
seq-sub-contract-Δ {Γ} {Δ} {P} {pf} pfIn with mem-++-split {xs = contextSubformulas Γ} pfIn
... | inl pfInΓ = mem-++-l pfInΓ
... | inr pfInΔ = mem-++-r (contextSubformulas Γ) (helper pfInΔ)
  where
    -- Work with (ys ++ []) instead of ys to match contextSubformulas computation
    ys = positionedSubformulas P
    helper : pf ∈ contextSubformulas (([ P ] ++ [ P ]) ++ Δ) → pf ∈ contextSubformulas ([ P ] ++ Δ)
    helper pfIn' =
      subst (pf ∈_) (sym (ctx-sub-++ [ P ] Δ))
        (mem-++-dup' (ys ++ []) (contextSubformulas Δ)
          (subst (pf ∈_) step2
            (subst (pf ∈_) step1 pfIn')))
      where
        -- (xs ++ []) ++ (xs ++ []) ++ zs membership implies (xs ++ []) ++ zs
        mem-++-dup' : {A : Type} {x : A} (xs zs : List A) → x ∈ (xs ++ xs) ++ zs → x ∈ xs ++ zs
        mem-++-dup' xs zs xIn with mem-++-split {xs = xs ++ xs} xIn
        ... | inl xInXsXs with mem-++-split {xs = xs} xInXsXs
        ...   | inl xInXs = mem-++-l xInXs
        ...   | inr xInXs = mem-++-l xInXs
        mem-++-dup' xs zs xIn | inr xInZs = mem-++-r xs xInZs
        -- Unfold the premise
        step1 : contextSubformulas (([ P ] ++ [ P ]) ++ Δ) ≡ contextSubformulas ([ P ] ++ [ P ]) ++ contextSubformulas Δ
        step1 = ctx-sub-++ ([ P ] ++ [ P ]) Δ
        step2 : contextSubformulas ([ P ] ++ [ P ]) ++ contextSubformulas Δ ≡ ((ys ++ []) ++ (ys ++ [])) ++ contextSubformulas Δ
        step2 = cong (_++ contextSubformulas Δ) (ctx-sub-++ [ P ] [ P ])

-- Exchange lemmas: swapping two elements preserves membership
-- Helper: membership in xs ++ ys implies membership in ys ++ xs
mem-++-swap : {A : Type} {x : A} (xs ys : List A) → x ∈ xs ++ ys → x ∈ ys ++ xs
mem-++-swap xs ys xIn with mem-++-split {xs = xs} xIn
... | inl xInXs = mem-++-r ys xInXs
... | inr xInYs = mem-++-l xInYs

-- Context subformulas exchange: swapping two formulas preserves membership
-- Exchange for (Γ₁ ,, [A]) ,, [B]) ,, Γ₂ ↔ ((Γ₁ ,, [B]) ,, [A]) ,, Γ₂
-- Key insight: both contexts have the same formulas, just reordered
ctx-sub-exchange : {Γ₁ Γ₂ : Ctx} {P Q : PFormula} {pf : PFormula}
                 → pf ∈ contextSubformulas (((Γ₁ ++ [ P ]) ++ [ Q ]) ++ Γ₂)
                 → pf ∈ contextSubformulas (((Γ₁ ++ [ Q ]) ++ [ P ]) ++ Γ₂)
ctx-sub-exchange {Γ₁} {Γ₂} {P} {Q} {pf} pfIn =
  subst (pf ∈_) (sym step-out) (helper (subst (pf ∈_) step-in pfIn))
  where
    open import Cubical.Data.List.Properties using (++-assoc)
    pP = positionedSubformulas P ++ []  -- Keeping the ++ [] to match contextSubformulas [P]
    pQ = positionedSubformulas Q ++ []
    -- Unfold input using ctx-sub-++ repeatedly
    step-in : contextSubformulas (((Γ₁ ++ [ P ]) ++ [ Q ]) ++ Γ₂) ≡
              ((contextSubformulas Γ₁ ++ pP) ++ pQ) ++ contextSubformulas Γ₂
    step-in = ctx-sub-++ ((Γ₁ ++ [ P ]) ++ [ Q ]) Γ₂
            ∙ cong (_++ contextSubformulas Γ₂) (ctx-sub-++ (Γ₁ ++ [ P ]) [ Q ]
                                                ∙ cong (_++ pQ) (ctx-sub-++ Γ₁ [ P ]))
    -- Fold output
    step-out : contextSubformulas (((Γ₁ ++ [ Q ]) ++ [ P ]) ++ Γ₂) ≡
               ((contextSubformulas Γ₁ ++ pQ) ++ pP) ++ contextSubformulas Γ₂
    step-out = ctx-sub-++ ((Γ₁ ++ [ Q ]) ++ [ P ]) Γ₂
             ∙ cong (_++ contextSubformulas Γ₂) (ctx-sub-++ (Γ₁ ++ [ Q ]) [ P ]
                                                 ∙ cong (_++ pP) (ctx-sub-++ Γ₁ [ Q ]))
    -- Swap pP and pQ in the flattened form
    -- Input:  ((Γ₁-sub ++ pP) ++ pQ) ++ Γ₂-sub
    -- Output: ((Γ₁-sub ++ pQ) ++ pP) ++ Γ₂-sub
    helper : pf ∈ ((contextSubformulas Γ₁ ++ pP) ++ pQ) ++ contextSubformulas Γ₂
           → pf ∈ ((contextSubformulas Γ₁ ++ pQ) ++ pP) ++ contextSubformulas Γ₂
    helper pfIn' with mem-++-split {xs = (contextSubformulas Γ₁ ++ pP) ++ pQ} pfIn'
    ... | inr pfInΓ₂ = mem-++-r ((contextSubformulas Γ₁ ++ pQ) ++ pP) pfInΓ₂
    ... | inl pfInΓ₁PQ with mem-++-split {xs = contextSubformulas Γ₁ ++ pP} pfInΓ₁PQ
    ...   | inr pfInQ = mem-++-l (mem-++-l (mem-++-r (contextSubformulas Γ₁) pfInQ))
    ...   | inl pfInΓ₁P with mem-++-split {xs = contextSubformulas Γ₁} pfInΓ₁P
    ...     | inl pfInΓ₁ = mem-++-l (mem-++-l (mem-++-l pfInΓ₁))
    ...     | inr pfInP = mem-++-l (mem-++-r (contextSubformulas Γ₁ ++ pQ) pfInP)

-- Sequent subformulas exchange for antecedent
seq-sub-exchange-Γ : {Γ₁ Γ₂ Δ : Ctx} {P Q : PFormula} {pf : PFormula}
                   → pf ∈ sequentSubformulas (((Γ₁ ++ [ P ]) ++ [ Q ]) ++ Γ₂) Δ
                   → pf ∈ sequentSubformulas (((Γ₁ ++ [ Q ]) ++ [ P ]) ++ Γ₂) Δ
seq-sub-exchange-Γ {Γ₁} {Γ₂} {Δ} {P} {Q} {pf} pfIn with mem-++-split {xs = contextSubformulas (((Γ₁ ++ [ P ]) ++ [ Q ]) ++ Γ₂)} pfIn
... | inl pfInΓ = mem-++-l (ctx-sub-exchange {Γ₁} {Γ₂} {P} {Q} pfInΓ)
... | inr pfInΔ = mem-++-r (contextSubformulas (((Γ₁ ++ [ Q ]) ++ [ P ]) ++ Γ₂)) pfInΔ

-- Sequent subformulas exchange for succedent
seq-sub-exchange-Δ : {Γ Δ₁ Δ₂ : Ctx} {P Q : PFormula} {pf : PFormula}
                   → pf ∈ sequentSubformulas Γ (((Δ₁ ++ [ P ]) ++ [ Q ]) ++ Δ₂)
                   → pf ∈ sequentSubformulas Γ (((Δ₁ ++ [ Q ]) ++ [ P ]) ++ Δ₂)
seq-sub-exchange-Δ {Γ} {Δ₁} {Δ₂} {P} {Q} {pf} pfIn with mem-++-split {xs = contextSubformulas Γ} pfIn
... | inl pfInΓ = mem-++-l pfInΓ
... | inr pfInΔ = mem-++-r (contextSubformulas Γ) (ctx-sub-exchange {Δ₁} {Δ₂} {P} {Q} pfInΔ)

-- Combine sequent subformulas from two sequents
seq-sub-combine : {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {pf : PFormula}
                → (pf ∈ sequentSubformulas Γ₁ Δ₁) ⊎ (pf ∈ sequentSubformulas Γ₂ Δ₂)
                → pf ∈ sequentSubformulas (Γ₁ ++ Γ₂) (Δ₁ ++ Δ₂)
seq-sub-combine {Γ₁} {Γ₂} {Δ₁} {Δ₂} {pf} (inl pfIn₁) =
  seq-sub-mono-Γ-r {Γ₁} {Γ₂} {Δ₁ ++ Δ₂} {pf} (seq-sub-mono-Δ-r {Γ₁} {Δ₁} {Δ₂} {pf} pfIn₁)
seq-sub-combine {Γ₁} {Γ₂} {Δ₁} {Δ₂} {pf} (inr pfIn₂) =
  seq-sub-mono-Γ-l {Γ₂} {Γ₁} {Δ₁ ++ Δ₂} {pf} (seq-sub-mono-Δ-l {Γ₂} {Δ₂} {Δ₁} {pf} pfIn₂)

-- =============================================================================
-- Subformula Inclusion Lemmas
-- =============================================================================

-- Subformulas of A are subformulas of ¬A, A∧B, A∨B, A⇒B, □A, ♢A
-- For positioned formulas: positionedSubformulas (A ^ s) ⊆ positionedSubformulas ((¬ A) ^ s), etc.

-- Helper: membership in empty list is absurd
¬mem-[] : {A : Type} {x : A} → x ∈ [] → ⊥
¬mem-[] ()

-- Helper: if x ∈ xs, then x ∈ y ∷ xs (there constructor)
mem-there : {A : Type} {x y : A} {xs : List A} → x ∈ xs → x ∈ (y ∷ xs)
mem-there = there

-- =============================================================================
-- Fuel Stability for allSubformulas
-- =============================================================================

-- When fuel is sufficient, allSubformulas-fuel gives the same result as allSubformulas
-- We prove this by showing the fuel-based version equals the standard one

-- First, a simpler lemma: membership is preserved when increasing fuel
-- Using the fact that formulaDepth A ≤ n implies allSubformulas-fuel n A ≡ allSubformulas A

open import Cubical.Data.Nat.Order using (≤SumLeft; ≤SumRight; pred-≤-pred)

-- Helper: dA ≤ dA + dB
depth-≤-sum₁ : (A B : Formula) → formulaDepth A ≤ formulaDepth A + formulaDepth B
depth-≤-sum₁ A B = ≤SumLeft {formulaDepth A} {formulaDepth B}

-- Helper: dB ≤ dA + dB
depth-≤-sum₂ : (A B : Formula) → formulaDepth B ≤ formulaDepth A + formulaDepth B
depth-≤-sum₂ A B = ≤SumRight {formulaDepth B} {formulaDepth A}

-- Helper: suc n ≤ 0 is impossible
suc-≤-zero-absurd : {n : ℕ} → suc n ≤ zero → ⊥
suc-≤-zero-absurd {n} p = snotz (≤0→≡0 p)

-- Key lemma: allSubformulas-fuel with sufficient fuel equals allSubformulas
allSubformulas-fuel-eq : (A : Formula) (n : ℕ) → formulaDepth A ≤ n
                       → allSubformulas-fuel n A ≡ allSubformulas A
allSubformulas-fuel-eq (Atom k) zero p = refl
allSubformulas-fuel-eq (Atom k) (suc n) p = refl
allSubformulas-fuel-eq (A and' B) zero p = ⊥-rec (suc-≤-zero-absurd p)
allSubformulas-fuel-eq (A or' B) zero p = ⊥-rec (suc-≤-zero-absurd p)
allSubformulas-fuel-eq (A ⇒ B) zero p = ⊥-rec (suc-≤-zero-absurd p)
allSubformulas-fuel-eq (¬ A) zero p = ⊥-rec (suc-≤-zero-absurd p)
allSubformulas-fuel-eq (□ A) zero p = ⊥-rec (suc-≤-zero-absurd p)
allSubformulas-fuel-eq (♢ A) zero p = ⊥-rec (suc-≤-zero-absurd p)
allSubformulas-fuel-eq (A and' B) (suc n) p =
  cong ((A and' B) ∷_)
    (cong₂ _++_
      (allSubformulas-fuel-eq A n (≤-trans (depth-≤-sum₁ A B) (pred-≤-pred p))
       ∙ sym (allSubformulas-fuel-eq A (formulaDepth A + formulaDepth B) (depth-≤-sum₁ A B)))
      (allSubformulas-fuel-eq B n (≤-trans (depth-≤-sum₂ A B) (pred-≤-pred p))
       ∙ sym (allSubformulas-fuel-eq B (formulaDepth A + formulaDepth B) (depth-≤-sum₂ A B))))
allSubformulas-fuel-eq (A or' B) (suc n) p =
  cong ((A or' B) ∷_)
    (cong₂ _++_
      (allSubformulas-fuel-eq A n (≤-trans (depth-≤-sum₁ A B) (pred-≤-pred p))
       ∙ sym (allSubformulas-fuel-eq A (formulaDepth A + formulaDepth B) (depth-≤-sum₁ A B)))
      (allSubformulas-fuel-eq B n (≤-trans (depth-≤-sum₂ A B) (pred-≤-pred p))
       ∙ sym (allSubformulas-fuel-eq B (formulaDepth A + formulaDepth B) (depth-≤-sum₂ A B))))
allSubformulas-fuel-eq (A ⇒ B) (suc n) p =
  cong ((A ⇒ B) ∷_)
    (cong₂ _++_
      (allSubformulas-fuel-eq A n (≤-trans (depth-≤-sum₁ A B) (pred-≤-pred p))
       ∙ sym (allSubformulas-fuel-eq A (formulaDepth A + formulaDepth B) (depth-≤-sum₁ A B)))
      (allSubformulas-fuel-eq B n (≤-trans (depth-≤-sum₂ A B) (pred-≤-pred p))
       ∙ sym (allSubformulas-fuel-eq B (formulaDepth A + formulaDepth B) (depth-≤-sum₂ A B))))
allSubformulas-fuel-eq (¬ A) (suc n) p =
  cong ((¬ A) ∷_) (allSubformulas-fuel-eq A n (pred-≤-pred p))
allSubformulas-fuel-eq (□ A) (suc n) p =
  cong ((□ A) ∷_) (allSubformulas-fuel-eq A n (pred-≤-pred p))
allSubformulas-fuel-eq (♢ A) (suc n) p =
  cong ((♢ A) ∷_) (allSubformulas-fuel-eq A n (pred-≤-pred p))

-- Positioned subformulas with different fuel
positionedSubformulas-fuel : PFormula → ℕ → List PFormula
positionedSubformulas-fuel (A ^ s) n = map (_^ s) (allSubformulas-fuel n A)

positionedSubformulas-fuel-eq : (P : PFormula) (n : ℕ) → formulaDepth (PFormula.form P) ≤ n
                              → positionedSubformulas-fuel P n ≡ positionedSubformulas P
positionedSubformulas-fuel-eq (A ^ s) n p = cong (map (_^ s)) (allSubformulas-fuel-eq A n p)

-- =============================================================================
-- Subformula Inclusion via Fuel Stability
-- =============================================================================

-- Subformulas of A at position s are subformulas of (¬ A) at position s
sub-¬ : {A : Formula} {s : Position} {pf : PFormula}
      → pf ∈ positionedSubformulas (A ^ s) → pf ∈ positionedSubformulas ((¬ A) ^ s)
sub-¬ {A} {s} {pf} pfIn = mem-there pfIn

-- Helper: membership preserved through map and concatenation
-- This avoids needing the map++ equality path which causes type unification issues
mem-map-++-l : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {x : B} {xs ys : List A}
             → x ∈ map f xs → x ∈ map f (xs ++ ys)
mem-map-++-l {xs = []} ()
mem-map-++-l {xs = z ∷ zs} here = here
mem-map-++-l {xs = z ∷ zs} (there p) = there (mem-map-++-l p)

mem-map-++-r : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {x : B} (xs : List A) {ys : List A}
             → x ∈ map f ys → x ∈ map f (xs ++ ys)
mem-map-++-r [] p = p
mem-map-++-r (z ∷ zs) p = there (mem-map-++-r zs p)

-- Subformulas of A at position s are subformulas of (A ∧ B) at position s
sub-∧₁ : {A B : Formula} {s : Position} {pf : PFormula}
       → pf ∈ positionedSubformulas (A ^ s) → pf ∈ positionedSubformulas ((A and' B) ^ s)
sub-∧₁ {A} {B} {s} {pf} pfIn = mem-there combined
  where
    fuel = formulaDepth A + formulaDepth B
    sfA = allSubformulas-fuel fuel A
    sfB = allSubformulas-fuel fuel B
    -- Transport pfIn to use the right fuel level
    eq : positionedSubformulas (A ^ s) ≡ map (_^ s) sfA
    eq = cong (map (_^ s)) (sym (allSubformulas-fuel-eq A fuel (depth-≤-sum₁ A B)))
    pfIn' : pf ∈ map (_^ s) sfA
    pfIn' = subst (pf ∈_) eq pfIn
    -- Use direct membership lemma to avoid map++ path issues
    combined : pf ∈ map (_^ s) (sfA ++ sfB)
    combined = mem-map-++-l {ys = sfB} pfIn'

-- Subformulas of B at position s are subformulas of (A ∧ B) at position s
sub-∧₂ : {A B : Formula} {s : Position} {pf : PFormula}
       → pf ∈ positionedSubformulas (B ^ s) → pf ∈ positionedSubformulas ((A and' B) ^ s)
sub-∧₂ {A} {B} {s} {pf} pfIn = mem-there combined
  where
    fuel = formulaDepth A + formulaDepth B
    sfA = allSubformulas-fuel fuel A
    sfB = allSubformulas-fuel fuel B
    eq : positionedSubformulas (B ^ s) ≡ map (_^ s) sfB
    eq = cong (map (_^ s)) (sym (allSubformulas-fuel-eq B fuel (depth-≤-sum₂ A B)))
    pfIn' : pf ∈ map (_^ s) sfB
    pfIn' = subst (pf ∈_) eq pfIn
    -- Use direct membership lemma to avoid map++ path issues
    combined : pf ∈ map (_^ s) (sfA ++ sfB)
    combined = mem-map-++-r sfA pfIn'

-- Subformulas of A at position s are subformulas of (A ∨ B) at position s
sub-∨₁ : {A B : Formula} {s : Position} {pf : PFormula}
       → pf ∈ positionedSubformulas (A ^ s) → pf ∈ positionedSubformulas ((A or' B) ^ s)
sub-∨₁ {A} {B} {s} {pf} pfIn = mem-there combined
  where
    fuel = formulaDepth A + formulaDepth B
    sfA = allSubformulas-fuel fuel A
    sfB = allSubformulas-fuel fuel B
    eq : positionedSubformulas (A ^ s) ≡ map (_^ s) sfA
    eq = cong (map (_^ s)) (sym (allSubformulas-fuel-eq A fuel (depth-≤-sum₁ A B)))
    pfIn' : pf ∈ map (_^ s) sfA
    pfIn' = subst (pf ∈_) eq pfIn
    combined : pf ∈ map (_^ s) (sfA ++ sfB)
    combined = mem-map-++-l {ys = sfB} pfIn'

-- Subformulas of B at position s are subformulas of (A ∨ B) at position s
sub-∨₂ : {A B : Formula} {s : Position} {pf : PFormula}
       → pf ∈ positionedSubformulas (B ^ s) → pf ∈ positionedSubformulas ((A or' B) ^ s)
sub-∨₂ {A} {B} {s} {pf} pfIn = mem-there combined
  where
    fuel = formulaDepth A + formulaDepth B
    sfA = allSubformulas-fuel fuel A
    sfB = allSubformulas-fuel fuel B
    eq : positionedSubformulas (B ^ s) ≡ map (_^ s) sfB
    eq = cong (map (_^ s)) (sym (allSubformulas-fuel-eq B fuel (depth-≤-sum₂ A B)))
    pfIn' : pf ∈ map (_^ s) sfB
    pfIn' = subst (pf ∈_) eq pfIn
    combined : pf ∈ map (_^ s) (sfA ++ sfB)
    combined = mem-map-++-r sfA pfIn'

-- Subformulas of A at position s are subformulas of (A ⇒ B) at position s
sub-⇒₁ : {A B : Formula} {s : Position} {pf : PFormula}
       → pf ∈ positionedSubformulas (A ^ s) → pf ∈ positionedSubformulas ((A ⇒ B) ^ s)
sub-⇒₁ {A} {B} {s} {pf} pfIn = mem-there combined
  where
    fuel = formulaDepth A + formulaDepth B
    sfA = allSubformulas-fuel fuel A
    sfB = allSubformulas-fuel fuel B
    eq : positionedSubformulas (A ^ s) ≡ map (_^ s) sfA
    eq = cong (map (_^ s)) (sym (allSubformulas-fuel-eq A fuel (depth-≤-sum₁ A B)))
    pfIn' : pf ∈ map (_^ s) sfA
    pfIn' = subst (pf ∈_) eq pfIn
    combined : pf ∈ map (_^ s) (sfA ++ sfB)
    combined = mem-map-++-l {ys = sfB} pfIn'

-- Subformulas of B at position s are subformulas of (A ⇒ B) at position s
sub-⇒₂ : {A B : Formula} {s : Position} {pf : PFormula}
       → pf ∈ positionedSubformulas (B ^ s) → pf ∈ positionedSubformulas ((A ⇒ B) ^ s)
sub-⇒₂ {A} {B} {s} {pf} pfIn = mem-there combined
  where
    fuel = formulaDepth A + formulaDepth B
    sfA = allSubformulas-fuel fuel A
    sfB = allSubformulas-fuel fuel B
    eq : positionedSubformulas (B ^ s) ≡ map (_^ s) sfB
    eq = cong (map (_^ s)) (sym (allSubformulas-fuel-eq B fuel (depth-≤-sum₂ A B)))
    pfIn' : pf ∈ map (_^ s) sfB
    pfIn' = subst (pf ∈_) eq pfIn
    combined : pf ∈ map (_^ s) (sfA ++ sfB)
    combined = mem-map-++-r sfA pfIn'

-- Note: Modal rules (□⊢, ⊢□, ♢⊢, ⊢♢) change positions, so subformulas at one
-- position are NOT generally subformulas at another position. However, this is
-- not a problem because for cut-free proofs, formulasInProof is always empty
-- (only Cut adds formulas), so the SubformulaProperty follows vacuously.

-- =============================================================================
-- Sequent Subformula Inclusion for Logical Rules
-- =============================================================================

-- ¬⊢: From Γ ⊢ [A^s] ++ Δ to Γ ++ [¬A^s] ⊢ Δ
seq-sub-¬⊢ : {Γ Δ : Ctx} {A : Formula} {s : Position} {pf : PFormula}
           → pf ∈ sequentSubformulas Γ ([ A ^ s ] ++ Δ)
           → pf ∈ sequentSubformulas (Γ ++ [ (¬ A) ^ s ]) Δ
seq-sub-¬⊢ {Γ} {Δ} {A} {s} {pf} pfIn with mem-++-split {xs = contextSubformulas Γ} pfIn
... | inl pfInΓ = mem-++-l (ctx-sub-mono-r {Γ} {[ (¬ A) ^ s ]} pfInΓ)
... | inr pfInΔ' with mem-++-split {xs = positionedSubformulas (A ^ s)} pfInΔ'
...   | inr pfInΔ = mem-++-r (contextSubformulas (Γ ++ [ (¬ A) ^ s ])) pfInΔ
...   | inl pfInAsub = mem-++-l (ctx-sub-mono-l {[ (¬ A) ^ s ]} {Γ}
                         (subst (pf ∈_) (sym (ctx-sub-single ((¬ A) ^ s)))
                           (mem-++-l (sub-¬ pfInAsub))))

-- ⊢¬: From Γ ++ [A^s] ⊢ Δ to Γ ⊢ [¬A^s] ++ Δ
seq-sub-⊢¬ : {Γ Δ : Ctx} {A : Formula} {s : Position} {pf : PFormula}
           → pf ∈ sequentSubformulas (Γ ++ [ A ^ s ]) Δ
           → pf ∈ sequentSubformulas Γ ([ (¬ A) ^ s ] ++ Δ)
seq-sub-⊢¬ {Γ} {Δ} {A} {s} {pf} pfIn with mem-++-split {xs = contextSubformulas (Γ ++ [ A ^ s ])} pfIn
... | inr pfInΔ = mem-++-r (contextSubformulas Γ) (ctx-sub-mono-l {Δ} {[ (¬ A) ^ s ]} pfInΔ)
... | inl pfInΓA = helper (subst (pf ∈_) (ctx-sub-++ Γ [ A ^ s ]) pfInΓA)
  where
    helper : pf ∈ contextSubformulas Γ ++ (positionedSubformulas (A ^ s) ++ [])
           → pf ∈ sequentSubformulas Γ ([ (¬ A) ^ s ] ++ Δ)
    helper pfIn' with mem-++-split {xs = contextSubformulas Γ} pfIn'
    ... | inl pfInΓ = mem-++-l pfInΓ
    ... | inr pfInA' with mem-++-split {xs = positionedSubformulas (A ^ s)} pfInA'
    ...   | inr pfIn[] = ⊥-rec (¬mem-[] pfIn[])
    ...   | inl pfInAsub = mem-++-r (contextSubformulas Γ)
                             (subst (pf ∈_) (sym (ctx-sub-++ [ (¬ A) ^ s ] Δ))
                               (mem-++-l (subst (pf ∈_) (sym (ctx-sub-single ((¬ A) ^ s)))
                                 (mem-++-l (sub-¬ pfInAsub)))))

-- ∧₁⊢: From Γ ++ [A^s] ⊢ Δ to Γ ++ [(A∧B)^s] ⊢ Δ
seq-sub-∧₁⊢ : {Γ Δ : Ctx} {A B : Formula} {s : Position} {pf : PFormula}
            → pf ∈ sequentSubformulas (Γ ++ [ A ^ s ]) Δ
            → pf ∈ sequentSubformulas (Γ ++ [ (A and' B) ^ s ]) Δ
seq-sub-∧₁⊢ {Γ} {Δ} {A} {B} {s} {pf} pfIn with mem-++-split {xs = contextSubformulas (Γ ++ [ A ^ s ])} pfIn
... | inr pfInΔ = mem-++-r (contextSubformulas (Γ ++ [ (A and' B) ^ s ])) pfInΔ
... | inl pfInΓA = helper (subst (pf ∈_) (ctx-sub-++ Γ [ A ^ s ]) pfInΓA)
  where
    helper : pf ∈ contextSubformulas Γ ++ (positionedSubformulas (A ^ s) ++ [])
           → pf ∈ sequentSubformulas (Γ ++ [ (A and' B) ^ s ]) Δ
    helper pfIn' with mem-++-split {xs = contextSubformulas Γ} pfIn'
    ... | inl pfInΓ = mem-++-l (ctx-sub-mono-r {Γ} {[ (A and' B) ^ s ]} pfInΓ)
    ... | inr pfInA' with mem-++-split {xs = positionedSubformulas (A ^ s)} pfInA'
    ...   | inr pfIn[] = ⊥-rec (¬mem-[] pfIn[])
    ...   | inl pfInAsub = mem-++-l (ctx-sub-mono-l {[ (A and' B) ^ s ]} {Γ}
                             (subst (pf ∈_) (sym (ctx-sub-single ((A and' B) ^ s)))
                               (mem-++-l (sub-∧₁ pfInAsub))))

-- ∧₂⊢: From Γ ++ [B^s] ⊢ Δ to Γ ++ [(A∧B)^s] ⊢ Δ
seq-sub-∧₂⊢ : {Γ Δ : Ctx} {A B : Formula} {s : Position} {pf : PFormula}
            → pf ∈ sequentSubformulas (Γ ++ [ B ^ s ]) Δ
            → pf ∈ sequentSubformulas (Γ ++ [ (A and' B) ^ s ]) Δ
seq-sub-∧₂⊢ {Γ} {Δ} {A} {B} {s} {pf} pfIn with mem-++-split {xs = contextSubformulas (Γ ++ [ B ^ s ])} pfIn
... | inr pfInΔ = mem-++-r (contextSubformulas (Γ ++ [ (A and' B) ^ s ])) pfInΔ
... | inl pfInΓB = helper (subst (pf ∈_) (ctx-sub-++ Γ [ B ^ s ]) pfInΓB)
  where
    helper : pf ∈ contextSubformulas Γ ++ (positionedSubformulas (B ^ s) ++ [])
           → pf ∈ sequentSubformulas (Γ ++ [ (A and' B) ^ s ]) Δ
    helper pfIn' with mem-++-split {xs = contextSubformulas Γ} pfIn'
    ... | inl pfInΓ = mem-++-l (ctx-sub-mono-r {Γ} {[ (A and' B) ^ s ]} pfInΓ)
    ... | inr pfInB' with mem-++-split {xs = positionedSubformulas (B ^ s)} pfInB'
    ...   | inr pfIn[] = ⊥-rec (¬mem-[] pfIn[])
    ...   | inl pfInBsub = mem-++-l (ctx-sub-mono-l {[ (A and' B) ^ s ]} {Γ}
                             (subst (pf ∈_) (sym (ctx-sub-single ((A and' B) ^ s)))
                               (mem-++-l (sub-∧₂ {A} pfInBsub))))

-- ⊢∧: From Γ₁ ⊢ [A^s] ++ Δ₁ and Γ₂ ⊢ [B^s] ++ Δ₂ to Γ₁ ++ Γ₂ ⊢ [(A∧B)^s] ++ Δ₁ ++ Δ₂
seq-sub-⊢∧ : {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {A B : Formula} {s : Position} {pf : PFormula}
           → (pf ∈ sequentSubformulas Γ₁ ([ A ^ s ] ++ Δ₁)) ⊎ (pf ∈ sequentSubformulas Γ₂ ([ B ^ s ] ++ Δ₂))
           → pf ∈ sequentSubformulas (Γ₁ ++ Γ₂) ([ (A and' B) ^ s ] ++ Δ₁ ++ Δ₂)
seq-sub-⊢∧ {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {s} {pf} (inl pfIn₁) =
  helper (SubformulaProperty-helper₁ pfIn₁)
  where
    -- Helper: analyze membership from first premise
    SubformulaProperty-helper₁ : pf ∈ sequentSubformulas Γ₁ ([ A ^ s ] ++ Δ₁)
                               → (pf ∈ contextSubformulas Γ₁) ⊎ ((pf ∈ positionedSubformulas (A ^ s)) ⊎ (pf ∈ contextSubformulas Δ₁))
    SubformulaProperty-helper₁ pfIn' with mem-++-split {xs = contextSubformulas Γ₁} pfIn'
    ... | inl pfInΓ₁ = inl pfInΓ₁
    ... | inr pfInAΔ₁ with mem-++-split {xs = positionedSubformulas (A ^ s)} pfInAΔ₁
    ...   | inr pfInΔ₁ = inr (inr pfInΔ₁)
    ...   | inl pfInAsub = inr (inl pfInAsub)
    helper : (pf ∈ contextSubformulas Γ₁) ⊎ ((pf ∈ positionedSubformulas (A ^ s)) ⊎ (pf ∈ contextSubformulas Δ₁))
           → pf ∈ sequentSubformulas (Γ₁ ++ Γ₂) ([ (A and' B) ^ s ] ++ Δ₁ ++ Δ₂)
    helper (inl pfInΓ₁) = mem-++-l (ctx-sub-mono-r {Γ₁} {Γ₂} pfInΓ₁)
    helper (inr (inl pfInA)) = mem-++-r (contextSubformulas (Γ₁ ++ Γ₂))
                                 (subst (pf ∈_) (sym (ctx-sub-++ [ (A and' B) ^ s ] (Δ₁ ++ Δ₂)))
                                   (mem-++-l (subst (pf ∈_) (sym (ctx-sub-single ((A and' B) ^ s)))
                                     (mem-++-l (sub-∧₁ pfInA)))))
    helper (inr (inr pfInΔ₁)) = mem-++-r (contextSubformulas (Γ₁ ++ Γ₂))
                                  (subst (pf ∈_) (sym (ctx-sub-++ [ (A and' B) ^ s ] (Δ₁ ++ Δ₂)))
                                    (mem-++-r (positionedSubformulas ((A and' B) ^ s) ++ [])
                                      (ctx-sub-mono-r {Δ₁} {Δ₂} pfInΔ₁)))
seq-sub-⊢∧ {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {s} {pf} (inr pfIn₂) =
  helper (SubformulaProperty-helper₂ pfIn₂)
  where
    -- Helper: analyze membership from second premise
    SubformulaProperty-helper₂ : pf ∈ sequentSubformulas Γ₂ ([ B ^ s ] ++ Δ₂)
                               → (pf ∈ contextSubformulas Γ₂) ⊎ ((pf ∈ positionedSubformulas (B ^ s)) ⊎ (pf ∈ contextSubformulas Δ₂))
    SubformulaProperty-helper₂ pfIn' with mem-++-split {xs = contextSubformulas Γ₂} pfIn'
    ... | inl pfInΓ₂ = inl pfInΓ₂
    ... | inr pfInBΔ₂ with mem-++-split {xs = positionedSubformulas (B ^ s)} pfInBΔ₂
    ...   | inr pfInΔ₂ = inr (inr pfInΔ₂)
    ...   | inl pfInBsub = inr (inl pfInBsub)
    helper : (pf ∈ contextSubformulas Γ₂) ⊎ ((pf ∈ positionedSubformulas (B ^ s)) ⊎ (pf ∈ contextSubformulas Δ₂))
           → pf ∈ sequentSubformulas (Γ₁ ++ Γ₂) ([ (A and' B) ^ s ] ++ Δ₁ ++ Δ₂)
    helper (inl pfInΓ₂) = mem-++-l (ctx-sub-mono-l {Γ₂} {Γ₁} pfInΓ₂)
    helper (inr (inl pfInB)) = mem-++-r (contextSubformulas (Γ₁ ++ Γ₂))
                                 (subst (pf ∈_) (sym (ctx-sub-++ [ (A and' B) ^ s ] (Δ₁ ++ Δ₂)))
                                   (mem-++-l (subst (pf ∈_) (sym (ctx-sub-single ((A and' B) ^ s)))
                                     (mem-++-l (sub-∧₂ {A} pfInB)))))
    helper (inr (inr pfInΔ₂)) = mem-++-r (contextSubformulas (Γ₁ ++ Γ₂))
                                  (subst (pf ∈_) (sym (ctx-sub-++ [ (A and' B) ^ s ] (Δ₁ ++ Δ₂)))
                                    (mem-++-r (positionedSubformulas ((A and' B) ^ s) ++ [])
                                      (ctx-sub-mono-l {Δ₂} {Δ₁} pfInΔ₂)))

-- ∨⊢: From Γ₁ ++ [A^s] ⊢ Δ₁ and Γ₂ ++ [B^s] ⊢ Δ₂ to Γ₁ ++ Γ₂ ++ [(A∨B)^s] ⊢ Δ₁ ++ Δ₂
seq-sub-∨⊢ : {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {A B : Formula} {s : Position} {pf : PFormula}
           → (pf ∈ sequentSubformulas (Γ₁ ++ [ A ^ s ]) Δ₁) ⊎ (pf ∈ sequentSubformulas (Γ₂ ++ [ B ^ s ]) Δ₂)
           → pf ∈ sequentSubformulas ((Γ₁ ++ Γ₂) ++ [ (A or' B) ^ s ]) (Δ₁ ++ Δ₂)
seq-sub-∨⊢ {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {s} {pf} (inl pfIn₁) =
  helper (SubformulaProperty-helper₁ pfIn₁)
  where
    SubformulaProperty-helper₁ : pf ∈ sequentSubformulas (Γ₁ ++ [ A ^ s ]) Δ₁
                               → (pf ∈ contextSubformulas Γ₁) ⊎ ((pf ∈ positionedSubformulas (A ^ s)) ⊎ (pf ∈ contextSubformulas Δ₁))
    SubformulaProperty-helper₁ pfIn' with mem-++-split {xs = contextSubformulas (Γ₁ ++ [ A ^ s ])} pfIn'
    ... | inr pfInΔ₁ = inr (inr pfInΔ₁)
    ... | inl pfInΓ₁A with mem-++-split {xs = contextSubformulas Γ₁} (subst (pf ∈_) (ctx-sub-++ Γ₁ [ A ^ s ]) pfInΓ₁A)
    ...   | inl pfInΓ₁ = inl pfInΓ₁
    ...   | inr pfInA with mem-++-split {xs = positionedSubformulas (A ^ s)} pfInA
    ...     | inr pfIn[] = ⊥-rec (¬mem-[] pfIn[])
    ...     | inl pfInAsub = inr (inl pfInAsub)
    helper : (pf ∈ contextSubformulas Γ₁) ⊎ ((pf ∈ positionedSubformulas (A ^ s)) ⊎ (pf ∈ contextSubformulas Δ₁))
           → pf ∈ sequentSubformulas ((Γ₁ ++ Γ₂) ++ [ (A or' B) ^ s ]) (Δ₁ ++ Δ₂)
    helper (inl pfInΓ₁) = mem-++-l (ctx-sub-mono-r {Γ₁ ++ Γ₂} {[ (A or' B) ^ s ]}
                            (ctx-sub-mono-r {Γ₁} {Γ₂} pfInΓ₁))
    helper (inr (inl pfInA)) = mem-++-l (ctx-sub-mono-l {[ (A or' B) ^ s ]} {Γ₁ ++ Γ₂}
                                 (subst (pf ∈_) (sym (ctx-sub-single ((A or' B) ^ s)))
                                   (mem-++-l (sub-∨₁ pfInA))))
    helper (inr (inr pfInΔ₁)) = mem-++-r (contextSubformulas ((Γ₁ ++ Γ₂) ++ [ (A or' B) ^ s ]))
                                  (ctx-sub-mono-r {Δ₁} {Δ₂} pfInΔ₁)
seq-sub-∨⊢ {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {s} {pf} (inr pfIn₂) =
  helper (SubformulaProperty-helper₂ pfIn₂)
  where
    SubformulaProperty-helper₂ : pf ∈ sequentSubformulas (Γ₂ ++ [ B ^ s ]) Δ₂
                               → (pf ∈ contextSubformulas Γ₂) ⊎ ((pf ∈ positionedSubformulas (B ^ s)) ⊎ (pf ∈ contextSubformulas Δ₂))
    SubformulaProperty-helper₂ pfIn' with mem-++-split {xs = contextSubformulas (Γ₂ ++ [ B ^ s ])} pfIn'
    ... | inr pfInΔ₂ = inr (inr pfInΔ₂)
    ... | inl pfInΓ₂B with mem-++-split {xs = contextSubformulas Γ₂} (subst (pf ∈_) (ctx-sub-++ Γ₂ [ B ^ s ]) pfInΓ₂B)
    ...   | inl pfInΓ₂ = inl pfInΓ₂
    ...   | inr pfInB with mem-++-split {xs = positionedSubformulas (B ^ s)} pfInB
    ...     | inr pfIn[] = ⊥-rec (¬mem-[] pfIn[])
    ...     | inl pfInBsub = inr (inl pfInBsub)
    helper : (pf ∈ contextSubformulas Γ₂) ⊎ ((pf ∈ positionedSubformulas (B ^ s)) ⊎ (pf ∈ contextSubformulas Δ₂))
           → pf ∈ sequentSubformulas ((Γ₁ ++ Γ₂) ++ [ (A or' B) ^ s ]) (Δ₁ ++ Δ₂)
    helper (inl pfInΓ₂) = mem-++-l (ctx-sub-mono-r {Γ₁ ++ Γ₂} {[ (A or' B) ^ s ]}
                            (ctx-sub-mono-l {Γ₂} {Γ₁} pfInΓ₂))
    helper (inr (inl pfInB)) = mem-++-l (ctx-sub-mono-l {[ (A or' B) ^ s ]} {Γ₁ ++ Γ₂}
                                 (subst (pf ∈_) (sym (ctx-sub-single ((A or' B) ^ s)))
                                   (mem-++-l (sub-∨₂ {A} pfInB))))
    helper (inr (inr pfInΔ₂)) = mem-++-r (contextSubformulas ((Γ₁ ++ Γ₂) ++ [ (A or' B) ^ s ]))
                                  (ctx-sub-mono-l {Δ₂} {Δ₁} pfInΔ₂)

-- ⊢∨₁: From Γ ⊢ [A^s] ++ Δ to Γ ⊢ [(A∨B)^s] ++ Δ
seq-sub-⊢∨₁ : {Γ Δ : Ctx} {A B : Formula} {s : Position} {pf : PFormula}
            → pf ∈ sequentSubformulas Γ ([ A ^ s ] ++ Δ)
            → pf ∈ sequentSubformulas Γ ([ (A or' B) ^ s ] ++ Δ)
seq-sub-⊢∨₁ {Γ} {Δ} {A} {B} {s} {pf} pfIn with mem-++-split {xs = contextSubformulas Γ} pfIn
... | inl pfInΓ = mem-++-l pfInΓ
... | inr pfInAΔ with mem-++-split {xs = positionedSubformulas (A ^ s)} pfInAΔ
...   | inr pfInΔ = mem-++-r (contextSubformulas Γ)
                      (subst (pf ∈_) (sym (ctx-sub-++ [ (A or' B) ^ s ] Δ))
                        (mem-++-r (positionedSubformulas ((A or' B) ^ s) ++ []) pfInΔ))
...   | inl pfInAsub = mem-++-r (contextSubformulas Γ)
                         (subst (pf ∈_) (sym (ctx-sub-++ [ (A or' B) ^ s ] Δ))
                           (mem-++-l (subst (pf ∈_) (sym (ctx-sub-single ((A or' B) ^ s)))
                             (mem-++-l (sub-∨₁ pfInAsub)))))

-- ⊢∨₂: From Γ ⊢ [B^s] ++ Δ to Γ ⊢ [(A∨B)^s] ++ Δ
seq-sub-⊢∨₂ : {Γ Δ : Ctx} {A B : Formula} {s : Position} {pf : PFormula}
            → pf ∈ sequentSubformulas Γ ([ B ^ s ] ++ Δ)
            → pf ∈ sequentSubformulas Γ ([ (A or' B) ^ s ] ++ Δ)
seq-sub-⊢∨₂ {Γ} {Δ} {A} {B} {s} {pf} pfIn with mem-++-split {xs = contextSubformulas Γ} pfIn
... | inl pfInΓ = mem-++-l pfInΓ
... | inr pfInBΔ with mem-++-split {xs = positionedSubformulas (B ^ s)} pfInBΔ
...   | inr pfInΔ = mem-++-r (contextSubformulas Γ)
                      (subst (pf ∈_) (sym (ctx-sub-++ [ (A or' B) ^ s ] Δ))
                        (mem-++-r (positionedSubformulas ((A or' B) ^ s) ++ []) pfInΔ))
...   | inl pfInBsub = mem-++-r (contextSubformulas Γ)
                         (subst (pf ∈_) (sym (ctx-sub-++ [ (A or' B) ^ s ] Δ))
                           (mem-++-l (subst (pf ∈_) (sym (ctx-sub-single ((A or' B) ^ s)))
                             (mem-++-l (sub-∨₂ {A} pfInBsub)))))

-- ⇒⊢: From Γ₁ ++ [B^s] ⊢ Δ₁ and Γ₂ ⊢ [A^s] ++ Δ₂ to Γ₁ ++ Γ₂ ++ [(A⇒B)^s] ⊢ Δ₁ ++ Δ₂
seq-sub-⇒⊢ : {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {A B : Formula} {s : Position} {pf : PFormula}
           → (pf ∈ sequentSubformulas (Γ₁ ++ [ B ^ s ]) Δ₁) ⊎ (pf ∈ sequentSubformulas Γ₂ ([ A ^ s ] ++ Δ₂))
           → pf ∈ sequentSubformulas ((Γ₁ ++ Γ₂) ++ [ (A ⇒ B) ^ s ]) (Δ₁ ++ Δ₂)
seq-sub-⇒⊢ {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {s} {pf} (inl pfIn₁) =
  helper (SubformulaProperty-helper₁ pfIn₁)
  where
    SubformulaProperty-helper₁ : pf ∈ sequentSubformulas (Γ₁ ++ [ B ^ s ]) Δ₁
                               → (pf ∈ contextSubformulas Γ₁) ⊎ ((pf ∈ positionedSubformulas (B ^ s)) ⊎ (pf ∈ contextSubformulas Δ₁))
    SubformulaProperty-helper₁ pfIn' with mem-++-split {xs = contextSubformulas (Γ₁ ++ [ B ^ s ])} pfIn'
    ... | inr pfInΔ₁ = inr (inr pfInΔ₁)
    ... | inl pfInΓ₁B with mem-++-split {xs = contextSubformulas Γ₁} (subst (pf ∈_) (ctx-sub-++ Γ₁ [ B ^ s ]) pfInΓ₁B)
    ...   | inl pfInΓ₁ = inl pfInΓ₁
    ...   | inr pfInB with mem-++-split {xs = positionedSubformulas (B ^ s)} pfInB
    ...     | inr pfIn[] = ⊥-rec (¬mem-[] pfIn[])
    ...     | inl pfInBsub = inr (inl pfInBsub)
    helper : (pf ∈ contextSubformulas Γ₁) ⊎ ((pf ∈ positionedSubformulas (B ^ s)) ⊎ (pf ∈ contextSubformulas Δ₁))
           → pf ∈ sequentSubformulas ((Γ₁ ++ Γ₂) ++ [ (A ⇒ B) ^ s ]) (Δ₁ ++ Δ₂)
    helper (inl pfInΓ₁) = mem-++-l (ctx-sub-mono-r {Γ₁ ++ Γ₂} {[ (A ⇒ B) ^ s ]}
                            (ctx-sub-mono-r {Γ₁} {Γ₂} pfInΓ₁))
    helper (inr (inl pfInB)) = mem-++-l (ctx-sub-mono-l {[ (A ⇒ B) ^ s ]} {Γ₁ ++ Γ₂}
                                 (subst (pf ∈_) (sym (ctx-sub-single ((A ⇒ B) ^ s)))
                                   (mem-++-l (sub-⇒₂ pfInB))))
    helper (inr (inr pfInΔ₁)) = mem-++-r (contextSubformulas ((Γ₁ ++ Γ₂) ++ [ (A ⇒ B) ^ s ]))
                                  (ctx-sub-mono-r {Δ₁} {Δ₂} pfInΔ₁)
seq-sub-⇒⊢ {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {s} {pf} (inr pfIn₂) =
  helper (SubformulaProperty-helper₂ pfIn₂)
  where
    SubformulaProperty-helper₂ : pf ∈ sequentSubformulas Γ₂ ([ A ^ s ] ++ Δ₂)
                               → (pf ∈ contextSubformulas Γ₂) ⊎ ((pf ∈ positionedSubformulas (A ^ s)) ⊎ (pf ∈ contextSubformulas Δ₂))
    SubformulaProperty-helper₂ pfIn' with mem-++-split {xs = contextSubformulas Γ₂} pfIn'
    ... | inl pfInΓ₂ = inl pfInΓ₂
    ... | inr pfInAΔ₂ with mem-++-split {xs = positionedSubformulas (A ^ s)} pfInAΔ₂
    ...   | inr pfInΔ₂ = inr (inr pfInΔ₂)
    ...   | inl pfInAsub = inr (inl pfInAsub)
    helper : (pf ∈ contextSubformulas Γ₂) ⊎ ((pf ∈ positionedSubformulas (A ^ s)) ⊎ (pf ∈ contextSubformulas Δ₂))
           → pf ∈ sequentSubformulas ((Γ₁ ++ Γ₂) ++ [ (A ⇒ B) ^ s ]) (Δ₁ ++ Δ₂)
    helper (inl pfInΓ₂) = mem-++-l (ctx-sub-mono-r {Γ₁ ++ Γ₂} {[ (A ⇒ B) ^ s ]}
                            (ctx-sub-mono-l {Γ₂} {Γ₁} pfInΓ₂))
    helper (inr (inl pfInA)) = mem-++-l (ctx-sub-mono-l {[ (A ⇒ B) ^ s ]} {Γ₁ ++ Γ₂}
                                 (subst (pf ∈_) (sym (ctx-sub-single ((A ⇒ B) ^ s)))
                                   (mem-++-l (sub-⇒₁ pfInA))))
    helper (inr (inr pfInΔ₂)) = mem-++-r (contextSubformulas ((Γ₁ ++ Γ₂) ++ [ (A ⇒ B) ^ s ]))
                                  (ctx-sub-mono-l {Δ₂} {Δ₁} pfInΔ₂)

-- ⊢⇒: From Γ ++ [A^s] ⊢ [B^s] ++ Δ to Γ ⊢ [(A⇒B)^s] ++ Δ
seq-sub-⊢⇒ : {Γ Δ : Ctx} {A B : Formula} {s : Position} {pf : PFormula}
           → pf ∈ sequentSubformulas (Γ ++ [ A ^ s ]) ([ B ^ s ] ++ Δ)
           → pf ∈ sequentSubformulas Γ ([ (A ⇒ B) ^ s ] ++ Δ)
seq-sub-⊢⇒ {Γ} {Δ} {A} {B} {s} {pf} pfIn with mem-++-split {xs = contextSubformulas (Γ ++ [ A ^ s ])} pfIn
... | inr pfInBΔ with mem-++-split {xs = positionedSubformulas (B ^ s)} pfInBΔ
...   | inr pfInΔ = mem-++-r (contextSubformulas Γ)
                      (subst (pf ∈_) (sym (ctx-sub-++ [ (A ⇒ B) ^ s ] Δ))
                        (mem-++-r (positionedSubformulas ((A ⇒ B) ^ s) ++ []) pfInΔ))
...   | inl pfInBsub = mem-++-r (contextSubformulas Γ)
                         (subst (pf ∈_) (sym (ctx-sub-++ [ (A ⇒ B) ^ s ] Δ))
                           (mem-++-l (subst (pf ∈_) (sym (ctx-sub-single ((A ⇒ B) ^ s)))
                             (mem-++-l (sub-⇒₂ pfInBsub)))))
seq-sub-⊢⇒ {Γ} {Δ} {A} {B} {s} {pf} pfIn | inl pfInΓA with mem-++-split {xs = contextSubformulas Γ} (subst (pf ∈_) (ctx-sub-++ Γ [ A ^ s ]) pfInΓA)
... | inl pfInΓ = mem-++-l pfInΓ
... | inr pfInA with mem-++-split {xs = positionedSubformulas (A ^ s)} pfInA
...   | inr pfIn[] = ⊥-rec (¬mem-[] pfIn[])
...   | inl pfInAsub = mem-++-r (contextSubformulas Γ)
                         (subst (pf ∈_) (sym (ctx-sub-++ [ (A ⇒ B) ^ s ] Δ))
                           (mem-++-l (subst (pf ∈_) (sym (ctx-sub-single ((A ⇒ B) ^ s)))
                             (mem-++-l (sub-⇒₁ pfInAsub)))))

-- =============================================================================
-- Subformula Property Theorem
-- =============================================================================

-- The key insight: for a cut-free proof, formulasInProof only contains
-- formulas that are subformulas of the conclusion formulas.
--
-- Proof: By induction on the proof structure.
-- - Ax: No extra formulas
-- - Cut: Cannot occur (proof is cut-free)
-- - Logical rules: Subformulas of the principal formula are subformulas of conclusion
-- - Structural rules: Pass through (same formulas)
-- - Modal rules: Position-extended subformulas (handled by the subformula definition)

-- The Subformula Property:
-- Every formula in a cut-free proof is a subformula of the conclusion.
SubformulaProperty : {Γ Δ : Ctx} → (Π : Γ ⊢ Δ) → isCutFree Π
                   → (pf : PFormula) → pf ∈ formulasInProof Π
                   → pf ∈ sequentSubformulas Γ Δ
SubformulaProperty Ax _ pf ()
SubformulaProperty (Cut {A = A} Π₁ Π₂) cf pf pfIn = ⊥-rec (max-suc-neq-zero cf)
  where
    -- Helper: suc n ≤ max (suc n) m
    suc-≤-max : (n m : ℕ) → suc n ≤ max (suc n) m
    suc-≤-max n zero = ≤-refl
    suc-≤-max n (suc m) = leq-max-1 (suc n) (suc m) (max (suc n) (suc m)) ≤-refl

    -- suc n ≤ 0 is impossible (suc n ≤ 0 → suc n ≡ 0, contradiction)
    suc-not-≤-zero : {n : ℕ} → suc n ≤ 0 → ⊥
    suc-not-≤-zero {n} sn≤0 = snotz (≤0→≡0 sn≤0)

    -- max (suc n) m ≥ 1, so it cannot equal 0
    max-suc-neq-zero : max (suc (degree A)) (max (δ Π₁) (δ Π₂)) ≡ 0 → ⊥
    max-suc-neq-zero eq = suc-not-≤-zero (subst (λ x → suc (degree A) ≤ x) eq (suc-≤-max (degree A) (max (δ Π₁) (δ Π₂))))

SubformulaProperty (W⊢ {Γ} {Δ} {A} {s} Π) cf pf pfIn =
  seq-sub-mono-Γ-r {Γ} {[ A ^ s ]} {Δ} {pf} (SubformulaProperty Π cf pf pfIn)
SubformulaProperty (⊢W {Γ} {Δ} {A} {s} Π) cf pf pfIn =
  seq-sub-mono-Δ-l {Γ} {Δ} {[ A ^ s ]} (SubformulaProperty Π cf pf pfIn)
SubformulaProperty (C⊢ {Γ} {A} {s} {Δ} Π) cf pf pfIn =
  seq-sub-contract-Γ {Γ} {Δ} {A ^ s} (SubformulaProperty Π cf pf pfIn)
SubformulaProperty (⊢C {Γ} {A} {s} {Δ} Π) cf pf pfIn =
  seq-sub-contract-Δ {Γ} {Δ} {A ^ s} (SubformulaProperty Π cf pf pfIn)
SubformulaProperty (Exc⊢ {Γ₁} {A} {s} {B} {t} {Γ₂} {Δ} Π) cf pf pfIn =
  seq-sub-exchange-Γ {Γ₁} {Γ₂} {Δ} {A ^ s} {B ^ t} (SubformulaProperty Π cf pf pfIn)
SubformulaProperty (⊢Exc {Γ} {Δ₁} {A} {s} {B} {t} {Δ₂} Π) cf pf pfIn =
  seq-sub-exchange-Δ {Γ} {Δ₁} {Δ₂} {A ^ s} {B ^ t} (SubformulaProperty Π cf pf pfIn)
SubformulaProperty (¬⊢ {Γ} {A} {s} {Δ} Π) cf pf pfIn =
  seq-sub-¬⊢ {Γ} {Δ} {A} {s} (SubformulaProperty Π cf pf pfIn)
SubformulaProperty (⊢¬ {Γ} {A} {s} {Δ} Π) cf pf pfIn =
  seq-sub-⊢¬ {Γ} {Δ} {A} {s} (SubformulaProperty Π cf pf pfIn)
SubformulaProperty (∧₁⊢ {Γ} {A} {s} {Δ} {B} Π) cf pf pfIn =
  seq-sub-∧₁⊢ {Γ} {Δ} {A} {B} {s} (SubformulaProperty Π cf pf pfIn)
SubformulaProperty (∧₂⊢ {Γ} {B} {s} {Δ} {A} Π) cf pf pfIn =
  seq-sub-∧₂⊢ {Γ} {Δ} {A} {B} {s} (SubformulaProperty Π cf pf pfIn)
SubformulaProperty (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) cf pf pfIn =
  seq-sub-⊢∧ {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {s} (helper pfIn)
  where
    -- Extract cut-freeness for subproofs
    cf₁ : isCutFree Π₁
    cf₁ = ≤0→≡0 (subst (δ Π₁ ≤_) cf (left-≤-max {m = δ Π₁} {n = δ Π₂}))
    cf₂ : isCutFree Π₂
    cf₂ = ≤0→≡0 (subst (δ Π₂ ≤_) cf (right-≤-max {n = δ Π₂} {m = δ Π₁}))
    helper : pf ∈ formulasInProof Π₁ ++ formulasInProof Π₂
           → (pf ∈ sequentSubformulas Γ₁ ([ A ^ s ] ++ Δ₁)) ⊎ (pf ∈ sequentSubformulas Γ₂ ([ B ^ s ] ++ Δ₂))
    helper pfIn' with mem-++-split {xs = formulasInProof Π₁} pfIn'
    ... | inl pfIn₁ = inl (SubformulaProperty Π₁ cf₁ pf pfIn₁)
    ... | inr pfIn₂ = inr (SubformulaProperty Π₂ cf₂ pf pfIn₂)
SubformulaProperty (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) cf pf pfIn =
  subst (λ ctx → pf ∈ sequentSubformulas ctx (Δ₁ ++ Δ₂))
        (++-assoc Γ₁ Γ₂ [ (A or' B) ^ s ])
        (seq-sub-∨⊢ {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {s} (helper pfIn))
  where
    cf₁ : isCutFree Π₁
    cf₁ = ≤0→≡0 (subst (δ Π₁ ≤_) cf (left-≤-max {m = δ Π₁} {n = δ Π₂}))
    cf₂ : isCutFree Π₂
    cf₂ = ≤0→≡0 (subst (δ Π₂ ≤_) cf (right-≤-max {n = δ Π₂} {m = δ Π₁}))
    helper : pf ∈ formulasInProof Π₁ ++ formulasInProof Π₂
           → (pf ∈ sequentSubformulas (Γ₁ ++ [ A ^ s ]) Δ₁) ⊎ (pf ∈ sequentSubformulas (Γ₂ ++ [ B ^ s ]) Δ₂)
    helper pfIn' with mem-++-split {xs = formulasInProof Π₁} pfIn'
    ... | inl pfIn₁ = inl (SubformulaProperty Π₁ cf₁ pf pfIn₁)
    ... | inr pfIn₂ = inr (SubformulaProperty Π₂ cf₂ pf pfIn₂)
SubformulaProperty (⊢∨₁ {Γ} {A} {s} {Δ} {B} Π) cf pf pfIn =
  seq-sub-⊢∨₁ {Γ} {Δ} {A} {B} {s} (SubformulaProperty Π cf pf pfIn)
SubformulaProperty (⊢∨₂ {Γ} {B} {s} {Δ} {A} Π) cf pf pfIn =
  seq-sub-⊢∨₂ {Γ} {Δ} {A} {B} {s} (SubformulaProperty Π cf pf pfIn)
SubformulaProperty (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} Π₁ Π₂) cf pf pfIn =
  subst (λ ctx → pf ∈ sequentSubformulas ctx (Δ₁ ++ Δ₂))
        (++-assoc Γ₁ Γ₂ [ (A ⇒ B) ^ s ])
        (seq-sub-⇒⊢ {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {s} (helper pfIn))
  where
    cf₁ : isCutFree Π₁
    cf₁ = ≤0→≡0 (subst (δ Π₁ ≤_) cf (left-≤-max {m = δ Π₁} {n = δ Π₂}))
    cf₂ : isCutFree Π₂
    cf₂ = ≤0→≡0 (subst (δ Π₂ ≤_) cf (right-≤-max {n = δ Π₂} {m = δ Π₁}))
    helper : pf ∈ formulasInProof Π₁ ++ formulasInProof Π₂
           → (pf ∈ sequentSubformulas (Γ₁ ++ [ B ^ s ]) Δ₁) ⊎ (pf ∈ sequentSubformulas Γ₂ ([ A ^ s ] ++ Δ₂))
    helper pfIn' with mem-++-split {xs = formulasInProof Π₁} pfIn'
    ... | inl pfIn₁ = inl (SubformulaProperty Π₁ cf₁ pf pfIn₁)
    ... | inr pfIn₂ = inr (SubformulaProperty Π₂ cf₂ pf pfIn₂)
SubformulaProperty (⊢⇒ {Γ} {A} {s} {B} {Δ} Π) cf pf pfIn =
  seq-sub-⊢⇒ {Γ} {Δ} {A} {B} {s} (SubformulaProperty Π cf pf pfIn)
SubformulaProperty (□⊢ Π) cf pf pfIn =
  ⊥-rec (∈-[]→⊥ (subst (pf ∈_) (formulasInProof-cutfree Π cf) pfIn))
SubformulaProperty (⊢□ _ _ _ Π) cf pf pfIn =
  ⊥-rec (∈-[]→⊥ (subst (pf ∈_) (formulasInProof-cutfree Π cf) pfIn))
SubformulaProperty (♢⊢ _ _ _ Π) cf pf pfIn =
  ⊥-rec (∈-[]→⊥ (subst (pf ∈_) (formulasInProof-cutfree Π cf) pfIn))
SubformulaProperty (⊢♢ Π) cf pf pfIn =
  ⊥-rec (∈-[]→⊥ (subst (pf ∈_) (formulasInProof-cutfree Π cf) pfIn))

-- =============================================================================
-- Faithful Subformula Property using the relation
-- =============================================================================

-- Helper: every formula is a subformula of itself
refl-subformula : (pf : PFormula) → pf isSubformulaOf pf
refl-subformula (A ^ s) = refl-sub

-- Helper: membership in a list gives subformula of itself in context
mem-gives-ctx-sub : {pf : PFormula} {Γ : Ctx} → pf ∈ Γ → pf isSubformulaOfCtx Γ
mem-gives-ctx-sub {pf} pfIn = pf , pfIn , refl-subformula pf

-- Helper: membership in Γ gives subformula of sequent (left)
mem-gives-seq-sub-l : {pf : PFormula} {Γ Δ : Ctx} → pf ∈ Γ → isSubformulaOfSeq pf Γ Δ
mem-gives-seq-sub-l pfIn = inl (mem-gives-ctx-sub pfIn)

-- Helper: membership in Δ gives subformula of sequent (right)
mem-gives-seq-sub-r : {pf : PFormula} {Γ Δ : Ctx} → pf ∈ Δ → isSubformulaOfSeq pf Γ Δ
mem-gives-seq-sub-r pfIn = inr (mem-gives-ctx-sub pfIn)

-- Helper: membership in Γ ++ Δ gives subformula of sequent
mem-gives-seq-sub : {pf : PFormula} {Γ Δ : Ctx} → pf ∈ Γ ++ Δ → isSubformulaOfSeq pf Γ Δ
mem-gives-seq-sub {pf} {Γ} {Δ} pfIn with mem-++-split {xs = Γ} pfIn
... | inl pfInΓ = mem-gives-seq-sub-l pfInΓ
... | inr pfInΔ = mem-gives-seq-sub-r pfInΔ

-- =============================================================================
-- Structural Rule Helpers for SubformulaProperty'
-- =============================================================================

-- Weakening left: premise Γ ⊢ Δ, conclusion Γ ++ [A^s] ⊢ Δ
seq-sub'-W⊢ : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {s : Position}
            → isSubformulaOfSeq pf Γ Δ
            → isSubformulaOfSeq pf (Γ ++ [ A ^ s ]) Δ
seq-sub'-W⊢ {pf} {Γ} {Δ} {A} {s} (inl (qf , qfIn , sub)) =
  inl (qf , mem-++-l qfIn , sub)
seq-sub'-W⊢ (inr x) = inr x

-- Weakening right: premise Γ ⊢ Δ, conclusion Γ ⊢ [A^s] ++ Δ
seq-sub'-⊢W : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {s : Position}
            → isSubformulaOfSeq pf Γ Δ
            → isSubformulaOfSeq pf Γ ([ A ^ s ] ++ Δ)
seq-sub'-⊢W {pf} {Γ} {Δ} {A} {s} (inl x) = inl x
seq-sub'-⊢W (inr (qf , qfIn , sub)) = inr (qf , mem-there qfIn , sub)

-- Contraction left: premise (Γ ++ [A^s]) ++ [A^s] ⊢ Δ, conclusion Γ ++ [A^s] ⊢ Δ
-- Note: The system uses left-associated contexts
seq-sub'-C⊢ : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {s : Position}
            → isSubformulaOfSeq pf ((Γ ++ [ A ^ s ]) ++ [ A ^ s ]) Δ
            → isSubformulaOfSeq pf (Γ ++ [ A ^ s ]) Δ
seq-sub'-C⊢ {pf} {Γ} {Δ} {A} {s} (inl (qf , qfIn , sub)) = inl (qf , contract-mem qfIn , sub)
  where
    contract-mem : qf ∈ ((Γ ++ [ A ^ s ]) ++ [ A ^ s ]) → qf ∈ (Γ ++ [ A ^ s ])
    contract-mem qfIn' with mem-++-split {xs = Γ ++ [ A ^ s ]} qfIn'
    ... | inl qfInΓA = qfInΓA
    ... | inr qfInA2 with mem-++-split {xs = [ A ^ s ]} qfInA2
    ...   | inl here = mem-++-r Γ here
    ...   | inr ()
seq-sub'-C⊢ {pf} {Γ} {Δ} {A} {s} (inr x) = inr x

-- Contraction right: premise Γ ⊢ [A^s] ++ [A^s] ++ Δ, conclusion Γ ⊢ [A^s] ++ Δ
seq-sub'-⊢C : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {s : Position}
            → isSubformulaOfSeq pf Γ ([ A ^ s ] ++ [ A ^ s ] ++ Δ)
            → isSubformulaOfSeq pf Γ ([ A ^ s ] ++ Δ)
seq-sub'-⊢C {pf} {Γ} {Δ} {A} {s} (inl x) = inl x
seq-sub'-⊢C {pf} {Γ} {Δ} {A} {s} (inr (qf , qfIn , sub)) = inr (qf , contract-mem qfIn , sub)
  where
    contract-mem : qf ∈ ([ A ^ s ] ++ [ A ^ s ] ++ Δ) → qf ∈ ([ A ^ s ] ++ Δ)
    contract-mem here = here
    contract-mem (there qfIn') with mem-++-split {xs = [ A ^ s ]} qfIn'
    ... | inl here = here
    ... | inr qfInΔ = there qfInΔ

-- Exchange left: premise ((Γ₁ ++ [A^s]) ++ [B^t]) ++ Γ₂ ⊢ Δ, conclusion ((Γ₁ ++ [B^t]) ++ [A^s]) ++ Γ₂ ⊢ Δ
-- Note: The system uses left-associated contexts
seq-sub'-Exc⊢ : {pf : PFormula} {Γ₁ Γ₂ Δ : Ctx} {A B : Formula} {s t : Position}
              → isSubformulaOfSeq pf (((Γ₁ ++ [ A ^ s ]) ++ [ B ^ t ]) ++ Γ₂) Δ
              → isSubformulaOfSeq pf (((Γ₁ ++ [ B ^ t ]) ++ [ A ^ s ]) ++ Γ₂) Δ
seq-sub'-Exc⊢ {pf} {Γ₁} {Γ₂} {Δ} {A} {B} {s} {t} (inl (qf , qfIn , sub)) =
  inl (qf , exchange-mem qfIn , sub)
  where
    exchange-mem : qf ∈ (((Γ₁ ++ [ A ^ s ]) ++ [ B ^ t ]) ++ Γ₂) → qf ∈ (((Γ₁ ++ [ B ^ t ]) ++ [ A ^ s ]) ++ Γ₂)
    exchange-mem qfIn' with mem-++-split {xs = (Γ₁ ++ [ A ^ s ]) ++ [ B ^ t ]} qfIn'
    ... | inr qfInΓ₂ = mem-++-r ((Γ₁ ++ [ B ^ t ]) ++ [ A ^ s ]) qfInΓ₂
    ... | inl qfInΓ₁AB with mem-++-split {xs = Γ₁ ++ [ A ^ s ]} qfInΓ₁AB
    ...   | inr here = mem-++-l (mem-++-l (mem-++-r Γ₁ here))  -- B is in Γ₁ ++ [B^t] part
    ...   | inl qfInΓ₁A with mem-++-split {xs = Γ₁} qfInΓ₁A
    ...     | inl qfInΓ₁ = mem-++-l (mem-++-l (mem-++-l qfInΓ₁))
    ...     | inr here = mem-++-l (mem-++-r (Γ₁ ++ [ B ^ t ]) here)  -- A is in [A^s] part
    ...     | inr (there ())
seq-sub'-Exc⊢ {pf} {Γ₁} {Γ₂} {Δ} {A} {B} {s} {t} (inr x) = inr x

-- Exchange right: premise Γ ⊢ ((Δ₁ ++ [A^s]) ++ [B^t]) ++ Δ₂, conclusion Γ ⊢ ((Δ₁ ++ [B^t]) ++ [A^s]) ++ Δ₂
-- Note: The system uses left-associated contexts
seq-sub'-⊢Exc : {pf : PFormula} {Γ Δ₁ Δ₂ : Ctx} {A B : Formula} {s t : Position}
              → isSubformulaOfSeq pf Γ (((Δ₁ ++ [ A ^ s ]) ++ [ B ^ t ]) ++ Δ₂)
              → isSubformulaOfSeq pf Γ (((Δ₁ ++ [ B ^ t ]) ++ [ A ^ s ]) ++ Δ₂)
seq-sub'-⊢Exc {pf} {Γ} {Δ₁} {Δ₂} {A} {B} {s} {t} (inl x) = inl x
seq-sub'-⊢Exc {pf} {Γ} {Δ₁} {Δ₂} {A} {B} {s} {t} (inr (qf , qfIn , sub)) = inr (qf , exchange-mem qfIn , sub)
  where
    exchange-mem : qf ∈ (((Δ₁ ++ [ A ^ s ]) ++ [ B ^ t ]) ++ Δ₂) → qf ∈ (((Δ₁ ++ [ B ^ t ]) ++ [ A ^ s ]) ++ Δ₂)
    exchange-mem qfIn' with mem-++-split {xs = (Δ₁ ++ [ A ^ s ]) ++ [ B ^ t ]} qfIn'
    ... | inr qfInΔ₂ = mem-++-r ((Δ₁ ++ [ B ^ t ]) ++ [ A ^ s ]) qfInΔ₂
    ... | inl qfInΔ₁AB with mem-++-split {xs = Δ₁ ++ [ A ^ s ]} qfInΔ₁AB
    ...   | inr here = mem-++-l (mem-++-l (mem-++-r Δ₁ here))  -- B is in Δ₁ ++ [B^t] part
    ...   | inl qfInΔ₁A with mem-++-split {xs = Δ₁} qfInΔ₁A
    ...     | inl qfInΔ₁ = mem-++-l (mem-++-l (mem-++-l qfInΔ₁))
    ...     | inr here = mem-++-l (mem-++-r (Δ₁ ++ [ B ^ t ]) here)  -- A is in [A^s] part
    ...     | inr (there ())

-- =============================================================================
-- Propositional Rule Helpers for SubformulaProperty'
-- =============================================================================

-- Helper: subformula relation is transitive-like for negation
sub'-¬⊢ : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {s : Position}
        → isSubformulaOfSeq pf Γ ([ A ^ s ] ++ Δ)
        → isSubformulaOfSeq pf (Γ ++ [ (¬ A) ^ s ]) Δ
sub'-¬⊢ {pf} {Γ} {Δ} {A} {s} (inl (qf , qfIn , sub)) = inl (qf , mem-++-l qfIn , sub)
sub'-¬⊢ (inr (qf , qfIn , sub)) with mem-++-split {xs = [ _ ]} qfIn
... | inr qfInΔ = inr (qf , qfInΔ , sub)
... | inl here = inl ((¬ _) ^ _ , mem-++-r _ here , ¬-sub sub)

sub'-⊢¬ : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {s : Position}
        → isSubformulaOfSeq pf (Γ ++ [ A ^ s ]) Δ
        → isSubformulaOfSeq pf Γ ([ (¬ A) ^ s ] ++ Δ)
sub'-⊢¬ {pf} {Γ} {Δ} {A} {s} (inr (qf , qfIn , sub)) = inr (qf , there qfIn , sub)
sub'-⊢¬ {pf} {Γ} {Δ} {A} {s} (inl (qf , qfIn , sub)) with mem-++-split {xs = Γ} qfIn
... | inl qfInΓ = inl (qf , qfInΓ , sub)
... | inr here = inr ((¬ _) ^ _ , here , ¬-sub sub)
... | inr (there ())

-- Conjunction rules
sub'-∧₁⊢ : {pf : PFormula} {Γ Δ : Ctx} {A B : Formula} {s : Position}
         → isSubformulaOfSeq pf (Γ ++ [ A ^ s ]) Δ
         → isSubformulaOfSeq pf (Γ ++ [ (A and' B) ^ s ]) Δ
sub'-∧₁⊢ {pf} {Γ} {Δ} {A} {B} {s} (inr x) = inr x
sub'-∧₁⊢ {pf} {Γ} {Δ} {A} {B} {s} (inl (qf , qfIn , sub)) with mem-++-split {xs = Γ} qfIn
... | inl qfInΓ = inl (qf , mem-++-l qfInΓ , sub)
... | inr here = inl ((_ and' _) ^ _ , mem-++-r _ here , ∧₁-sub sub)
... | inr (there ())

sub'-∧₂⊢ : {pf : PFormula} {Γ Δ : Ctx} {A B : Formula} {s : Position}
         → isSubformulaOfSeq pf (Γ ++ [ B ^ s ]) Δ
         → isSubformulaOfSeq pf (Γ ++ [ (A and' B) ^ s ]) Δ
sub'-∧₂⊢ {pf} {Γ} {Δ} {A} {B} {s} (inr x) = inr x
sub'-∧₂⊢ {pf} {Γ} {Δ} {A} {B} {s} (inl (qf , qfIn , sub)) with mem-++-split {xs = Γ} qfIn
... | inl qfInΓ = inl (qf , mem-++-l qfInΓ , sub)
... | inr here = inl ((_ and' _) ^ _ , mem-++-r _ here , ∧₂-sub sub)
... | inr (there ())

sub'-⊢∧ : {pf : PFormula} {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {A B : Formula} {s : Position}
        → isSubformulaOfSeq pf Γ₁ ([ A ^ s ] ++ Δ₁) ⊎ isSubformulaOfSeq pf Γ₂ ([ B ^ s ] ++ Δ₂)
        → isSubformulaOfSeq pf (Γ₁ ++ Γ₂) ([ (A and' B) ^ s ] ++ Δ₁ ++ Δ₂)
sub'-⊢∧ {pf} {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {s} (inl (inl (qf , qfIn , sub))) =
  inl (qf , mem-++-l qfIn , sub)
sub'-⊢∧ (inl (inr (qf , qfIn , sub))) with mem-++-split {xs = [ _ ]} qfIn
... | inr qfInΔ₁ = inr (qf , there (mem-++-l qfInΔ₁) , sub)
... | inl here = inr ((_ and' _) ^ _ , here , ∧₁-sub sub)
sub'-⊢∧ {Γ₁ = Γ₁} (inr (inl (qf , qfIn , sub))) = inl (qf , mem-++-r Γ₁ qfIn , sub)
sub'-⊢∧ {Δ₁ = Δ₁} (inr (inr (qf , qfIn , sub))) with mem-++-split {xs = [ _ ]} qfIn
... | inr qfInΔ₂ = inr (qf , there (mem-++-r Δ₁ qfInΔ₂) , sub)
... | inl here = inr ((_ and' _) ^ _ , here , ∧₂-sub sub)

-- Disjunction rules (note: uses right-associated antecedent Γ₁ ++ (Γ₂ ++ [_]))
sub'-∨⊢ : {pf : PFormula} {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {A B : Formula} {s : Position}
        → isSubformulaOfSeq pf (Γ₁ ++ [ A ^ s ]) Δ₁ ⊎ isSubformulaOfSeq pf (Γ₂ ++ [ B ^ s ]) Δ₂
        → isSubformulaOfSeq pf (Γ₁ ++ (Γ₂ ++ [ (A or' B) ^ s ])) (Δ₁ ++ Δ₂)
sub'-∨⊢ {pf} {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {s} (inl (inl (qf , qfIn , sub))) with mem-++-split {xs = Γ₁} qfIn
... | inl qfInΓ₁ = inl (qf , mem-++-l qfInΓ₁ , sub)
... | inr here = inl ((_ or' _) ^ _ , mem-++-r Γ₁ (mem-++-r Γ₂ here) , ∨₁-sub sub)
... | inr (there ())
sub'-∨⊢ {Δ₁ = Δ₁} (inl (inr (qf , qfIn , sub))) = inr (qf , mem-++-l qfIn , sub)
sub'-∨⊢ {Γ₁ = Γ₁} {Γ₂ = Γ₂'} (inr (inl (qf , qfIn , sub))) with mem-++-split {xs = Γ₂'} qfIn
... | inl qfInΓ₂ = inl (qf , mem-++-r Γ₁ (mem-++-l qfInΓ₂) , sub)
... | inr here = inl ((_ or' _) ^ _ , mem-++-r Γ₁ (mem-++-r Γ₂' here) , ∨₂-sub sub)
... | inr (there ())
sub'-∨⊢ {Δ₁ = Δ₁} (inr (inr (qf , qfIn , sub))) = inr (qf , mem-++-r Δ₁ qfIn , sub)

sub'-⊢∨₁ : {pf : PFormula} {Γ Δ : Ctx} {A B : Formula} {s : Position}
         → isSubformulaOfSeq pf Γ ([ A ^ s ] ++ Δ)
         → isSubformulaOfSeq pf Γ ([ (A or' B) ^ s ] ++ Δ)
sub'-⊢∨₁ {pf} {Γ} {Δ} {A} {B} {s} (inl x) = inl x
sub'-⊢∨₁ (inr (qf , qfIn , sub)) with mem-++-split {xs = [ _ ]} qfIn
... | inr qfInΔ = inr (qf , there qfInΔ , sub)
... | inl here = inr ((_ or' _) ^ _ , here , ∨₁-sub sub)

sub'-⊢∨₂ : {pf : PFormula} {Γ Δ : Ctx} {A B : Formula} {s : Position}
         → isSubformulaOfSeq pf Γ ([ B ^ s ] ++ Δ)
         → isSubformulaOfSeq pf Γ ([ (A or' B) ^ s ] ++ Δ)
sub'-⊢∨₂ {pf} {Γ} {Δ} {A} {B} {s} (inl x) = inl x
sub'-⊢∨₂ (inr (qf , qfIn , sub)) with mem-++-split {xs = [ _ ]} qfIn
... | inr qfInΔ = inr (qf , there qfInΔ , sub)
... | inl here = inr ((_ or' _) ^ _ , here , ∨₂-sub sub)

-- Implication rules (note: uses right-associated antecedent Γ₁ ++ (Γ₂ ++ [_]))
sub'-⇒⊢ : {pf : PFormula} {Γ₁ Γ₂ Δ₁ Δ₂ : Ctx} {A B : Formula} {s : Position}
        → isSubformulaOfSeq pf (Γ₁ ++ [ B ^ s ]) Δ₁ ⊎ isSubformulaOfSeq pf Γ₂ ([ A ^ s ] ++ Δ₂)
        → isSubformulaOfSeq pf (Γ₁ ++ (Γ₂ ++ [ (A ⇒ B) ^ s ])) (Δ₁ ++ Δ₂)
sub'-⇒⊢ {pf} {Γ₁} {Γ₂} {Δ₁} {Δ₂} {A} {B} {s} (inl (inl (qf , qfIn , sub))) with mem-++-split {xs = Γ₁} qfIn
... | inl qfInΓ₁ = inl (qf , mem-++-l qfInΓ₁ , sub)
... | inr here = inl ((_ ⇒ _) ^ _ , mem-++-r Γ₁ (mem-++-r Γ₂ here) , ⇒₂-sub sub)
... | inr (there ())
sub'-⇒⊢ {Δ₁ = Δ₁} (inl (inr (qf , qfIn , sub))) = inr (qf , mem-++-l qfIn , sub)
sub'-⇒⊢ {Γ₁ = Γ₁} (inr (inl (qf , qfIn , sub))) = inl (qf , mem-++-r Γ₁ (mem-++-l qfIn) , sub)
sub'-⇒⊢ {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Δ₁ = Δ₁} (inr (inr (qf , qfIn , sub))) with mem-++-split {xs = [ _ ]} qfIn
... | inr qfInΔ₂ = inr (qf , mem-++-r Δ₁ qfInΔ₂ , sub)
... | inl here = inl ((_ ⇒ _) ^ _ , mem-++-r Γ₁ (mem-++-r Γ₂ here) , ⇒₁-sub sub)

sub'-⊢⇒ : {pf : PFormula} {Γ Δ : Ctx} {A B : Formula} {s : Position}
        → isSubformulaOfSeq pf (Γ ++ [ A ^ s ]) ([ B ^ s ] ++ Δ)
        → isSubformulaOfSeq pf Γ ([ (A ⇒ B) ^ s ] ++ Δ)
sub'-⊢⇒ {pf} {Γ} {Δ} {A} {B} {s} (inl (qf , qfIn , sub)) with mem-++-split {xs = Γ} qfIn
... | inl qfInΓ = inl (qf , qfInΓ , sub)
... | inr here = inr ((_ ⇒ _) ^ _ , here , ⇒₁-sub sub)
... | inr (there ())
sub'-⊢⇒ (inr (qf , qfIn , sub)) with mem-++-split {xs = [ _ ]} qfIn
... | inr qfInΔ = inr (qf , there qfInΔ , sub)
... | inl here = inr ((_ ⇒ _) ^ _ , here , ⇒₂-sub sub)

-- =============================================================================
-- Modal Rule Helpers for SubformulaProperty'
-- =============================================================================

-- For S4.2, the subformula relation uses ⊑ (subset) to match the system's modal rules.
-- SortedPosition._⊑_ is the subset relation for positions: s ⊑ t means all tokens in s are in t.

-- Helper: s ⊑ insertToken x s (inserting a token preserves existing elements)
⊑-insertToken-base : ∀ s x → s ⊑ insertToken x s
⊑-insertToken-base s x t t∈s = insertToken-∈Pos x t s (inr t∈s)

sub'-□⊢ : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {s t : Position}
        → (ext : s ⊑ t)  -- s is a subset of t
        → isSubformulaOfSeq pf (Γ ++ [ A ^ t ]) Δ
        → isSubformulaOfSeq pf (Γ ++ [ (□ A) ^ s ]) Δ
sub'-□⊢ {pf} {Γ} {Δ} {A} {s} {t} ext (inr x) = inr x
sub'-□⊢ {pf} {Γ} {Δ} {A} {s} {t} ext (inl (qf , qfIn , sub)) with mem-++-split {xs = Γ} qfIn
... | inl qfInΓ = inl (qf , mem-++-l qfInΓ , sub)
... | inr here = inl ((□ A) ^ s , mem-++-r Γ here , □-sub ext sub)
... | inr (there ())

sub'-⊢□ : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {s t : Position}
        → (ext : s ⊑ t)  -- s is a subset of t
        → isSubformulaOfSeq pf Γ ([ A ^ t ] ++ Δ)
        → isSubformulaOfSeq pf Γ ([ (□ A) ^ s ] ++ Δ)
sub'-⊢□ {pf} {Γ} {Δ} {A} {s} {t} ext (inl x) = inl x
sub'-⊢□ {pf} {Γ} {Δ} {A} {s} {t} ext (inr (qf , qfIn , sub)) with mem-++-split {xs = [ A ^ t ]} qfIn
... | inr qfInΔ = inr (qf , there qfInΔ , sub)
... | inl here = inr ((□ A) ^ s , here , □-sub ext sub)

sub'-♢⊢ : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {s t : Position}
        → (ext : s ⊑ t)  -- s is a subset of t
        → isSubformulaOfSeq pf (Γ ++ [ A ^ t ]) Δ
        → isSubformulaOfSeq pf (Γ ++ [ (♢ A) ^ s ]) Δ
sub'-♢⊢ {pf} {Γ} {Δ} {A} {s} {t} ext (inr x) = inr x
sub'-♢⊢ {pf} {Γ} {Δ} {A} {s} {t} ext (inl (qf , qfIn , sub)) with mem-++-split {xs = Γ} qfIn
... | inl qfInΓ = inl (qf , mem-++-l qfInΓ , sub)
... | inr here = inl ((♢ A) ^ s , mem-++-r Γ here , ♢-sub ext sub)
... | inr (there ())

sub'-⊢♢ : {pf : PFormula} {Γ Δ : Ctx} {A : Formula} {s t : Position}
        → (ext : s ⊑ t)  -- s is a subset of t
        → isSubformulaOfSeq pf Γ ([ A ^ t ] ++ Δ)
        → isSubformulaOfSeq pf Γ ([ (♢ A) ^ s ] ++ Δ)
sub'-⊢♢ {pf} {Γ} {Δ} {A} {s} {t} ext (inl x) = inl x
sub'-⊢♢ {pf} {Γ} {Δ} {A} {s} {t} ext (inr (qf , qfIn , sub)) with mem-++-split {xs = [ A ^ t ]} qfIn
... | inr qfInΔ = inr (qf , there qfInΔ , sub)
... | inl here = inr ((♢ A) ^ s , here , ♢-sub ext sub)

-- =============================================================================
-- The Faithful Subformula Property
-- =============================================================================

-- This theorem proves that every formula occurring in a cut-free proof
-- is a subformula of some formula in the conclusion.
--
-- The subformula relation uses ⊑ (subset) for modal formulas, matching
-- the S4.2 system's modal rules.

SubformulaProperty' : {Γ Δ : Ctx} → (Π : Γ ⊢ Δ) → isCutFree Π
                    → (pf : PFormula) → pf ∈ allFormulasInProof Π
                    → isSubformulaOfSeq pf Γ Δ
SubformulaProperty' {Γ} {Δ} Ax cf pf pfIn = mem-gives-seq-sub pfIn
SubformulaProperty' (Cut Π₁ Π₂) cf pf pfIn = ⊥-rec (snotz (≤0→≡0 helper))
  where
    helper : suc (degree _) ≤ 0
    helper = subst (suc (degree _) ≤_) cf (left-≤-max {m = suc (degree _)} {n = max (δ Π₁) (δ Π₂)})
SubformulaProperty' (W⊢ {Γ} {Δ} {A} {s} Π) cf pf pfIn with mem-++-split {xs = (Γ ++ [ A ^ s ]) ++ Δ} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc  -- conclusion already has weakened context
... | inr pfInSub = seq-sub'-W⊢ (SubformulaProperty' Π cf pf pfInSub)
SubformulaProperty' (⊢W {Γ} {Δ} {A} {s} Π) cf pf pfIn with mem-++-split {xs = Γ ++ ([ A ^ s ] ++ Δ)} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc  -- conclusion already has weakened context
... | inr pfInSub = seq-sub'-⊢W (SubformulaProperty' Π cf pf pfInSub)
SubformulaProperty' (C⊢ {Γ} {A} {s} {Δ} Π) cf pf pfIn with mem-++-split {xs = (Γ ++ [ A ^ s ]) ++ Δ} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub'-C⊢ (SubformulaProperty' Π cf pf pfInSub)
SubformulaProperty' (⊢C {Γ} {A} {s} {Δ} Π) cf pf pfIn with mem-++-split {xs = Γ ++ ([ A ^ s ] ++ Δ)} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub'-⊢C (SubformulaProperty' Π cf pf pfInSub)
SubformulaProperty' (Exc⊢ {Γ₁} {A} {s} {B} {t} {Γ₂} {Δ} Π) cf pf pfIn
  with mem-++-split {xs = (((Γ₁ ++ [ B ^ t ]) ++ [ A ^ s ]) ++ Γ₂) ++ Δ} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub'-Exc⊢ {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Δ = Δ} {A = A} {B = B} {s = s} {t = t} (SubformulaProperty' Π cf pf pfInSub)
SubformulaProperty' (⊢Exc {Γ} {Δ₁} {A} {s} {B} {t} {Δ₂} Π) cf pf pfIn
  with mem-++-split {xs = Γ ++ (((Δ₁ ++ [ B ^ t ]) ++ [ A ^ s ]) ++ Δ₂)} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = seq-sub'-⊢Exc {Γ = Γ} {Δ₁ = Δ₁} {Δ₂ = Δ₂} {A = A} {B = B} {s = s} {t = t} (SubformulaProperty' Π cf pf pfInSub)
SubformulaProperty' (¬⊢ {Γ} {A} {s} {Δ} Π) cf pf pfIn with mem-++-split {xs = (Γ ++ [ (¬ A) ^ s ]) ++ Δ} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = sub'-¬⊢ (SubformulaProperty' Π cf pf pfInSub)
SubformulaProperty' (⊢¬ {Γ} {A} {s} {Δ} Π) cf pf pfIn with mem-++-split {xs = Γ ++ ([ (¬ A) ^ s ] ++ Δ)} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = sub'-⊢¬ (SubformulaProperty' Π cf pf pfInSub)
SubformulaProperty' (∧₁⊢ {Γ} {A} {s} {Δ} {B} Π) cf pf pfIn with mem-++-split {xs = (Γ ++ [ (A and' B) ^ s ]) ++ Δ} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = sub'-∧₁⊢ (SubformulaProperty' Π cf pf pfInSub)
SubformulaProperty' (∧₂⊢ {Γ} {B} {s} {Δ} {A} Π) cf pf pfIn with mem-++-split {xs = (Γ ++ [ (A and' B) ^ s ]) ++ Δ} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = sub'-∧₂⊢ (SubformulaProperty' Π cf pf pfInSub)
SubformulaProperty' (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) cf pf pfIn
  with mem-++-split {xs = (Γ₁ ++ Γ₂) ++ ([ (A and' B) ^ s ] ++ Δ₁ ++ Δ₂)} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub with mem-++-split {xs = allFormulasInProof Π₁} pfInSub
...   | inl pfIn₁ = sub'-⊢∧ (inl (SubformulaProperty' Π₁ cf₁ pf pfIn₁))
        where cf₁ = ≤0→≡0 (subst (δ Π₁ ≤_) cf (left-≤-max {m = δ Π₁}))
...   | inr pfIn₂ = sub'-⊢∧ {Γ₁ = Γ₁} (inr (SubformulaProperty' Π₂ cf₂ pf pfIn₂))
        where cf₂ = ≤0→≡0 (leq-max-2 (δ Π₁) (δ Π₂) 0 (subst (_≤ 0) (sym cf) ≤-refl))
SubformulaProperty' (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) cf pf pfIn
  with mem-++-split {xs = (Γ₁ ++ (Γ₂ ++ [ (A or' B) ^ s ])) ++ (Δ₁ ++ Δ₂)} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub with mem-++-split {xs = allFormulasInProof Π₁} pfInSub
...   | inl pfIn₁ = sub'-∨⊢ (inl (SubformulaProperty' Π₁ cf₁ pf pfIn₁))
        where cf₁ = ≤0→≡0 (subst (δ Π₁ ≤_) cf (left-≤-max {m = δ Π₁}))
...   | inr pfIn₂ = sub'-∨⊢ {Γ₁ = Γ₁} (inr (SubformulaProperty' Π₂ cf₂ pf pfIn₂))
        where cf₂ = ≤0→≡0 (leq-max-2 (δ Π₁) (δ Π₂) 0 (subst (_≤ 0) (sym cf) ≤-refl))
SubformulaProperty' (⊢∨₁ {Γ} {A} {s} {Δ} {B} Π) cf pf pfIn with mem-++-split {xs = Γ ++ ([ (A or' B) ^ s ] ++ Δ)} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = sub'-⊢∨₁ (SubformulaProperty' Π cf pf pfInSub)
SubformulaProperty' (⊢∨₂ {Γ} {B} {s} {Δ} {A} Π) cf pf pfIn with mem-++-split {xs = Γ ++ ([ (A or' B) ^ s ] ++ Δ)} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = sub'-⊢∨₂ (SubformulaProperty' Π cf pf pfInSub)
SubformulaProperty' (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} Π₁ Π₂) cf pf pfIn
  with mem-++-split {xs = (Γ₁ ++ (Γ₂ ++ [ (A ⇒ B) ^ s ])) ++ (Δ₁ ++ Δ₂)} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub with mem-++-split {xs = allFormulasInProof Π₁} pfInSub
...   | inl pfIn₁ = sub'-⇒⊢ (inl (SubformulaProperty' Π₁ cf₁ pf pfIn₁))
        where cf₁ = ≤0→≡0 (subst (δ Π₁ ≤_) cf (left-≤-max {m = δ Π₁}))
...   | inr pfIn₂ = sub'-⇒⊢ {Γ₁ = Γ₁} (inr (SubformulaProperty' Π₂ cf₂ pf pfIn₂))
        where cf₂ = ≤0→≡0 (leq-max-2 (δ Π₁) (δ Π₂) 0 (subst (_≤ 0) (sym cf) ≤-refl))
SubformulaProperty' (⊢⇒ {Γ} {A} {s} {B} {Δ} Π) cf pf pfIn with mem-++-split {xs = Γ ++ ([ (A ⇒ B) ^ s ] ++ Δ)} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = sub'-⊢⇒ (SubformulaProperty' Π cf pf pfInSub)
-- Modal rules: □⊢ and ⊢♢ use merge (s ∘ t), so s ⊑ (s ∘ t) by ⊑-merge-l
-- ⊢□ and ♢⊢ use insertToken x s, and IsSingleTokenExt provides s ⊑ t
SubformulaProperty' (□⊢ {Γ = Γ} {A = A} {s = s} {t = t} {Δ = Δ} Π) cf pf pfIn
  with mem-++-split {xs = (Γ ++ [ (□ A) ^ s ]) ++ Δ} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = sub'-□⊢ (⊑-merge-l s t) (SubformulaProperty' Π cf pf pfInSub)
-- ⊢□: uses insertToken x s, we derive s ⊑ (insertToken x s) via ⊑-insertToken-base
SubformulaProperty' {Γ} {Δ'} (⊢□ {x} {s} _ _ _ Π) cf pf pfIn
  with mem-++-split {xs = Γ ++ Δ'} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = sub'-⊢□ (⊑-insertToken-base s x) (SubformulaProperty' Π cf pf pfInSub)
-- ♢⊢: uses insertToken x s, we derive s ⊑ (insertToken x s) via ⊑-insertToken-base
SubformulaProperty' {Γ'} {Δ} (♢⊢ {x} {s} _ _ _ Π) cf pf pfIn
  with mem-++-split {xs = Γ' ++ Δ} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = sub'-♢⊢ (⊑-insertToken-base s x) (SubformulaProperty' Π cf pf pfInSub)
-- ⊢♢: uses merge (s ∘ t), so s ⊑ (s ∘ t) by ⊑-merge-l
SubformulaProperty' (⊢♢ {Γ = Γ} {A = A} {s = s} {t = t} {Δ = Δ} Π) cf pf pfIn
  with mem-++-split {xs = Γ ++ ([ (♢ A) ^ s ] ++ Δ)} pfIn
... | inl pfInConc = mem-gives-seq-sub pfInConc
... | inr pfInSub = sub'-⊢♢ (⊑-merge-l s t) (SubformulaProperty' Π cf pf pfInSub)

-- =============================================================================
-- Corollary: Combined with Cut Elimination
-- =============================================================================

-- For any proof (not necessarily cut-free), its formulas are all subformulas
-- of the conclusion after applying cut elimination.
-- This follows immediately from CutElimination + SubformulaProperty
