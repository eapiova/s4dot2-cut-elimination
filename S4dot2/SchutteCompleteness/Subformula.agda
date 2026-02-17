{-# OPTIONS --safe #-}

-- Subformula Closure and Finiteness Properties
-- For completeness via reduction trees, we need the subformula property

module S4dot2.SchutteCompleteness.Subformula where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Nat.Order using (_≤_) renaming (≤-refl to ≤ℕ-refl)

open import S4dot2.Syntax hiding (_⊢_) renaming (_∧_ to _and'_; _∨_ to _or'_)

-- =============================================================================
-- Subformula Enumeration
-- =============================================================================

-- Immediate subformulas of a formula
immediateSubformulas : Formula → List Formula
immediateSubformulas (Atom _) = []
immediateSubformulas (A and' B) = A ∷ B ∷ []
immediateSubformulas (A or' B) = A ∷ B ∷ []
immediateSubformulas (A ⇒ B) = A ∷ B ∷ []
immediateSubformulas (¬ A) = A ∷ []
immediateSubformulas (□ A) = A ∷ []
immediateSubformulas (♢ A) = A ∷ []

-- Formula complexity (depth)
formulaDepth : Formula → ℕ
formulaDepth (Atom _) = zero
formulaDepth (A and' B) = suc (formulaDepth A + formulaDepth B)
formulaDepth (A or' B) = suc (formulaDepth A + formulaDepth B)
formulaDepth (A ⇒ B) = suc (formulaDepth A + formulaDepth B)
formulaDepth (¬ A) = suc (formulaDepth A)
formulaDepth (□ A) = suc (formulaDepth A)
formulaDepth (♢ A) = suc (formulaDepth A)

-- All subformulas (including the formula itself)
-- Uses fuel to ensure termination
allSubformulas-fuel : ℕ → Formula → List Formula
allSubformulas-fuel zero A = A ∷ []
allSubformulas-fuel (suc n) (Atom k) = Atom k ∷ []
allSubformulas-fuel (suc n) (A and' B) = 
  (A and' B) ∷ allSubformulas-fuel n A ++ allSubformulas-fuel n B
allSubformulas-fuel (suc n) (A or' B) = 
  (A or' B) ∷ allSubformulas-fuel n A ++ allSubformulas-fuel n B
allSubformulas-fuel (suc n) (A ⇒ B) = 
  (A ⇒ B) ∷ allSubformulas-fuel n A ++ allSubformulas-fuel n B
allSubformulas-fuel (suc n) (¬ A) = 
  (¬ A) ∷ allSubformulas-fuel n A
allSubformulas-fuel (suc n) (□ A) = 
  (□ A) ∷ allSubformulas-fuel n A
allSubformulas-fuel (suc n) (♢ A) = 
  (♢ A) ∷ allSubformulas-fuel n A

allSubformulas : Formula → List Formula
allSubformulas A = allSubformulas-fuel (formulaDepth A) A

-- =============================================================================
-- Positioned Subformulas
-- =============================================================================

-- For a positioned formula A^s, the subformulas are also at position s
-- Modal rules may introduce extended positions

-- Subformulas at the same position
positionedSubformulas : PFormula → List PFormula
positionedSubformulas (A ^ s) = map (_^ s) (allSubformulas A)

-- =============================================================================
-- Context Subformula Closure
-- =============================================================================

-- All subformulas occurring in a context
contextSubformulas : List PFormula → List PFormula
contextSubformulas [] = []
contextSubformulas (pf ∷ Γ) = positionedSubformulas pf ++ contextSubformulas Γ

-- Subformula closure for a sequent
sequentSubformulas : List PFormula → List PFormula → List PFormula
sequentSubformulas Γ Δ = contextSubformulas Γ ++ contextSubformulas Δ

-- =============================================================================
-- Finiteness Properties
-- =============================================================================

-- Length bound: subformulas of A has length ≤ some bound
-- (trivially, the length itself is a bound)
subformulasBounded : (A : Formula) → Σ ℕ λ bound → length (allSubformulas A) ≤ bound
subformulasBounded A = length (allSubformulas A) , ≤ℕ-refl

-- Note: For completeness, we need:
-- 1. Every formula in a reduction tree is a subformula of the original sequent
-- 2. The set of positions is bounded (by prefix closure of initial positions)
-- 3. Therefore the search space is finite

-- =============================================================================
-- Formula Membership
-- =============================================================================

-- Check if a formula is a subformula of another
isSubformulaOf : Formula → Formula → Type
isSubformulaOf sub A = sub ∈ allSubformulas A

-- Positioned formula membership in subformula closure
inSubClosure : PFormula → List PFormula → Type
inSubClosure pf Γ = pf ∈ contextSubformulas Γ

-- =============================================================================
-- Modal Subformulas
-- =============================================================================

isModal : Formula → Bool
isModal (□ _) = true
isModal (♢ _) = true
isModal (Atom _) = false
isModal (_ and' _) = false
isModal (_ or' _) = false
isModal (_ ⇒ _) = false
isModal (¬ _) = false

-- All modal subformulas of a single formula
modalSubformulas : Formula → List Formula
modalSubformulas A = filterModal (allSubformulas A)
  where
    filterModal : List Formula → List Formula
    filterModal [] = []
    filterModal (f ∷ fs) with isModal f
    ... | true = f ∷ filterModal fs
    ... | false = filterModal fs

-- All (unpositioned) subformulas from a context
allSubformulasCtx : List PFormula → List Formula
allSubformulasCtx [] = []
allSubformulasCtx ((A ^ _) ∷ pfs) = allSubformulas A ++ allSubformulasCtx pfs

-- All modal subformulas occurring in a context (unpositioned)
modalSubformulasOfCtx : List PFormula → List Formula
modalSubformulasOfCtx [] = []
modalSubformulasOfCtx ((A ^ _) ∷ pfs) = modalSubformulas A ++ modalSubformulasOfCtx pfs
