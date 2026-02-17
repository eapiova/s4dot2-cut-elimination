{-# OPTIONS --safe #-}

-- Shared boolean reflection lemmas.
-- Consolidates duplicated definitions from FiniteSoundness, FiniteModel,
-- FairSoundness, and Solver/Subset/Routing.

module S4dot2.BoolReflect where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool; true; false; _and_; _or_; false≢true)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Sum using (_⊎_; inl; inr)

and-true-l : {a b : Bool} → a and b ≡ true → a ≡ true
and-true-l {true} _ = refl
and-true-l {false} p = ⊥-rec (false≢true p)

and-true-r : {a b : Bool} → a and b ≡ true → b ≡ true
and-true-r {true} {true} _ = refl
and-true-r {true} {false} p = ⊥-rec (false≢true p)
and-true-r {false} p = ⊥-rec (false≢true p)

and-intro : {a b : Bool} → a ≡ true → b ≡ true → a and b ≡ true
and-intro p q = cong₂ _and_ p q

or-true-intro-l : {a b : Bool} → a ≡ true → a or b ≡ true
or-true-intro-l {true} _ = refl
or-true-intro-l {false} p = ⊥-rec (false≢true p)

or-true-intro-r : {a b : Bool} → b ≡ true → a or b ≡ true
or-true-intro-r {a = true} _ = refl
or-true-intro-r {a = false} {true} _ = refl
or-true-intro-r {a = false} {false} p = ⊥-rec (false≢true p)

or-true-cases : {a b : Bool} → a or b ≡ true → (a ≡ true) ⊎ (b ≡ true)
or-true-cases {true} _ = inl refl
or-true-cases {false} p = inr p

decide-no-means-false : {b : Bool} → (b ≡ true → ⊥) → b ≡ false
decide-no-means-false {true} p = ⊥-rec (p refl)
decide-no-means-false {false} _ = refl
