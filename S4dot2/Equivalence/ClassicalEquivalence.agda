{-# OPTIONS --cubical --safe #-}

-- Classical equivalences for S4.2
-- Derives Hilbert ↔ Sequent equivalence (at ∅), Hilbert finite soundness,
-- and the Finite Model Property from two classical assumptions
-- (segerberg-FMP + decidable-⊢S4dot2).

module S4dot2.Equivalence.ClassicalEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (true; false; false≢true)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)

open import S4dot2.Syntax hiding (_⊢_; ¬_)
open import S4dot2.System hiding (Ctx)
open import S4dot2.Equivalence.FiniteModel
open import S4dot2.Equivalence.FiniteSoundness using (finiteSoundness)
open import S4dot2.Equivalence.HilbertCompleteness using (completeness)

module Classical
  (segerberg-FMP : ∀ A → ¬ (⊢S4dot2 A)
    → Σ FiniteModel λ M → eval M (m M) A ≡ false)
  (decidable-⊢S4dot2 : ∀ A → Dec (⊢S4dot2 A))
  where

  -- =============================================================================
  -- Finite Model Property (Harrop 1958, Section 4)
  -- =============================================================================
  -- "We shall say that a calculus P has the finite model property if there
  -- is a finite model counter-example to each non-provable formula of P"

  Valid : FiniteModel → Formula → Type
  Valid M A = ∀ (w : World M) → eval M w A ≡ true

  HasFMP : Type₁
  HasFMP = ∀ A → ¬ (⊢S4dot2 A) → Σ FiniteModel λ M → ¬ (Valid M A)

  -- =============================================================================
  -- Classical assumptions
  -- =============================================================================

  -- Segerberg (1971), Chapter I, Theorem 7.4 + 7.6(iv):
  -- FMP for S4.2 via Lemmon filtration of the canonical model.
  --
  -- Step 1 (standard FMP): Given ¬⊢A, Kripke completeness yields an S4.2
  -- model M and a world w₀ falsifying A.  Lemmon filtration through Sub(A):
  --   Thm 7.4:     filtration preserves truth of subformulas;
  --   Thm 7.6(iv): Lemmon filtration preserves convergence (K4.2 case);
  --   reflexivity and transitivity are preserved by the K4 base case.
  -- Result: a *finite* S4.2 Kripke model with w₀ falsifying A.
  --
  -- Step 2 (strengthening to minimum): restrict to the upset
  -- {w' : w' ≥ w₀}. This is a finite semilattice with minimum w₀,
  -- giving a FiniteModel with eval M (m M) A ≡ false.

  -- Harrop (1958), Lemma 4.1: FMP implies decidability.
  -- "If P satisfies the finite model property then it is decidable."
  -- Applies since S4.2 has FMP by segerberg-FMP above.

  -- =============================================================================
  -- Derived: FMP for S4.2
  -- =============================================================================

  fmp-S4dot2 : HasFMP
  fmp-S4dot2 A ¬⊢A =
    let (M , p) = segerberg-FMP A ¬⊢A
    in M , λ valid → false≢true (sym p ∙ valid (m M))

  -- =============================================================================
  -- Derived: hilbert-FMP (was postulate, now theorem)
  -- =============================================================================

  hilbert-FMP : ∀ {A}
      → (∀ (M : FiniteModel) (ms : ModalSemantics M) → eval M (m M) A ≡ true)
      → ⊢S4dot2 A
  hilbert-FMP {A} hyp with decidable-⊢S4dot2 A
  ... | yes ⊢A = ⊢A
  ... | no ¬⊢A =
    let (M , p) = segerberg-FMP A ¬⊢A
    in ⊥-rec (false≢true (sym p ∙ hyp M (defaultModalSemantics M)))

  -- =============================================================================
  -- Derived theorems
  -- =============================================================================

  -- Sequent provability at ∅ implies Hilbert provability.
  -- Proof: finiteSoundness gives A true at m M for every finite model,
  -- then hilbert-FMP gives ⊢S4dot2 A.
  seq→hilbert : ∀ {A} → [] ⊢ [ A ^ ∅ ] → ⊢S4dot2 A
  seq→hilbert {A} d = hilbert-FMP λ M ms →
    extract M (finiteSoundness d M ms (λ _ → m M) (λ _ ()))
    where
      extract : ∀ M → M , (λ _ → m M) ⊩Succᶠ [ A ^ ∅ ] → eval M (m M) A ≡ true
      extract M (_ , here , sat) = sat

  -- Hilbert provability ↔ sequent provability at ∅.
  hilbert-sequent-equiv : ∀ {A} → (⊢S4dot2 A → [] ⊢ [ A ^ ∅ ]) × ([] ⊢ [ A ^ ∅ ] → ⊢S4dot2 A)
  hilbert-sequent-equiv = completeness , seq→hilbert

  -- Hilbert provability implies finite model soundness.
  hilbert-finite-soundness : ∀ {A} → ⊢S4dot2 A
    → (M : FiniteModel) → (ms : ModalSemantics M) → (ρ : FiniteInterpretation M)
    → M , ρ ⊩Succᶠ [ A ^ ∅ ]
  hilbert-finite-soundness h M ms ρ = finiteSoundness (completeness h) M ms ρ (λ _ ())
