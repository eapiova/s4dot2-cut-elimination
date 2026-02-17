{-# OPTIONS --cubical #-}

-- Classical equivalences for S4.2
-- Derives Hilbert ↔ Sequent equivalence (at ε) and Hilbert finite soundness
-- using one classical postulate (hilbert-FMP).

module S4dot2.Equivalence.ClassicalEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (true)

open import S4dot2.Syntax hiding (_⊢_)
open import S4dot2.System hiding (Ctx)
open import S4dot2.Equivalence.FiniteModel
open import S4dot2.Equivalence.FiniteSoundness using (finiteSoundness)
open import S4dot2.Equivalence.HilbertCompleteness using (completeness)

-- =============================================================================
-- Classical postulate: Finite Model Property for Hilbert S4.2
-- =============================================================================
-- Justification: Segerberg (1971) FMP + upward closure.
-- For any finite semilattice model and world w₀, the upset {w : w ≥ w₀}
-- is a finite semilattice with minimum w₀. So A true at every minimum
-- → A true at every world → ⊢H A by standard Hilbert FMP.

postulate
  hilbert-FMP : ∀ {A}
    → (∀ (M : FiniteModel) (ms : ModalSemantics M) → eval M (m M) A ≡ true)
    → ⊢S4dot2 A

-- =============================================================================
-- Derived theorems
-- =============================================================================

-- Sequent provability at ε implies Hilbert provability.
-- Proof: finiteSoundness gives A true at m M for every finite model,
-- then hilbert-FMP gives ⊢S4dot2 A.
seq→hilbert : ∀ {A} → [] ⊢ [ A ^ ε ] → ⊢S4dot2 A
seq→hilbert {A} d = hilbert-FMP λ M ms →
  extract M (finiteSoundness d M ms (λ _ → m M) (λ _ ()))
  where
    extract : ∀ M → M , (λ _ → m M) ⊩Succᶠ [ A ^ ε ] → eval M (m M) A ≡ true
    extract M (_ , here , sat) = sat

-- Hilbert provability ↔ sequent provability at ε.
hilbert-sequent-equiv : ∀ {A} → (⊢S4dot2 A → [] ⊢ [ A ^ ε ]) × ([] ⊢ [ A ^ ε ] → ⊢S4dot2 A)
hilbert-sequent-equiv = completeness , seq→hilbert

-- Hilbert provability implies finite model soundness.
hilbert-finite-soundness : ∀ {A} → ⊢S4dot2 A
  → (M : FiniteModel) → (ms : ModalSemantics M) → (ρ : FiniteInterpretation M)
  → M , ρ ⊩Succᶠ [ A ^ ε ]
hilbert-finite-soundness h M ms ρ = finiteSoundness (completeness h) M ms ρ (λ _ ())
