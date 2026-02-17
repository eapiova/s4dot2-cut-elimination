{-# OPTIONS --safe #-}

module S4dot2.Solver.Semilattice.Expression where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Vec using (Vec; lookup)

open import Cubical.Algebra.Semilattice

private
  variable
    ℓ : Level

infixl 7 _∨ₑ_

-- Expression in a semilattice with n variables
data Expr (n : ℕ) : Type where
  ∣_   : Fin n → Expr n          -- Variable
  ε∨   : Expr n                   -- Identity
  _∨ₑ_ : Expr n → Expr n → Expr n -- Join

module Eval (L : Semilattice ℓ) where
  open SemilatticeStr (snd L) renaming (_·_ to _∨l_; ε to 0l)

  Env : ℕ → Type ℓ
  Env n = Vec ⟨ L ⟩ n

  ⟦_⟧ : {n : ℕ} → Expr n → Env n → ⟨ L ⟩
  ⟦ ∣ i ⟧ ρ       = lookup i ρ
  ⟦ ε∨ ⟧ ρ        = 0l
  ⟦ e₁ ∨ₑ e₂ ⟧ ρ = ⟦ e₁ ⟧ ρ ∨l ⟦ e₂ ⟧ ρ
