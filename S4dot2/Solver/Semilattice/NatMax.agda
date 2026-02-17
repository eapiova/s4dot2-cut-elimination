{-# OPTIONS --safe #-}

module S4dot2.Solver.Semilattice.NatMax where

open import Cubical.Foundations.Prelude

open import Cubical.Data.Bool using (true)
open import Cubical.Data.FinData using (Fin)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order renaming (_≤_ to _≤ℕ_)
open import Cubical.Data.Vec using (Vec)

open import Cubical.Algebra.Semilattice
open import Cubical.Algebra.Semilattice.Instances.NatMax

open import S4dot2.Solver.Semilattice.Expression
open import S4dot2.Solver.Semilattice.Solver

-- NatMax solver: solves max/≤ goals on natural numbers
module NatMaxSolver where

  private
    L : Semilattice ℓ-zero
    L = (ℕ , maxSemilatticeStr)

  open SemilatticeSolve L public

  -- Solve inequality in standard ℕ order (not semilattice order)
  solve≤ℕ : {n : ℕ}
          → (e₁ e₂ : Expr n)
          → (ρ : Vec ℕ n)
          → {pf : flatten e₁ ⊆? flatten e₂ ≡ true}
          → ⟦ e₁ ⟧ ρ ≤ℕ ⟦ e₂ ⟧ ρ
  solve≤ℕ e₁ e₂ ρ {pf} = ≤max→≤ℕ _ _ (solve≤ e₁ e₂ ρ {pf})
