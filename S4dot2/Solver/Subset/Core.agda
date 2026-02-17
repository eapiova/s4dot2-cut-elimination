{-# OPTIONS --safe #-}

module S4dot2.Solver.Subset.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_; _++_; map)
open import Cubical.Data.Bool using (Bool; true; false; not; if_then_else_)
open import Cubical.Data.Empty as Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma using (_×_; _,_)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Relation.Nullary using (Discrete; yes; no; Dec)

open import S4dot2.ListExt using (_∈_; here; there; _⊆_; mem-++-l; mem-++-r)

private
  variable
    ℓ : Level

-- Inequality
_≢_ : ∀ {ℓ'} {A : Type ℓ'} → A → A → Type ℓ'
x ≢ y = x ≡ y → ⊥

-- filter for lists (defined here to avoid circular imports)
filter : {A : Type ℓ} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) = if p x then x ∷ filter p xs else filter p xs

-- Core solver module parameterized by element type with decidable equality
module SubsetSolver {A : Type ℓ} (_≟_ : Discrete A) where

  -- Extract Bool from Dec (reduces definitionally!)
  ⌊_⌋ : {P : Type ℓ} → Dec P → Bool
  ⌊ yes _ ⌋ = true
  ⌊ no  _ ⌋ = false

  -- removeAll using recursive Dec pattern matching
  -- Key insight: pattern matching on Dec directly means the decision
  -- will unify with with-variables when we case split on the same decision
  removeAll : A → List A → List A
  removeAll x [] = []
  removeAll x (y ∷ ys) with x ≟ y
  ... | yes _ = removeAll x ys
  ... | no  _ = y ∷ removeAll x ys

  -- Simple expression language
  -- Uses de Bruijn indices for list variables
  -- Element variables are concrete elements (simpler for now)
  data Expr : Type ℓ where
    var   : ℕ → Expr                    -- List variable
    []ₑ   : Expr                         -- Empty list
    elm   : ℕ → Expr                     -- Element variable (index)
    _++ₑ_ : Expr → Expr → Expr           -- Concatenation
    rem   : Expr → ℕ → Expr              -- removeAll by index

  infixr 5 _++ₑ_
  infixl 6 rem

  -- Environment: list of lists AND list of elements
  Env : Type ℓ
  Env = List (List A) × List A

  -- Safe lookup for lists
  lookupList : List (List A) → ℕ → List A
  lookupList [] _ = []
  lookupList (x ∷ _) zero = x
  lookupList (_ ∷ xs) (suc n) = lookupList xs n

  -- Safe lookup for elements (defaulting to something? A is not inhabited necessarily)
  -- But we need a complete function.
  -- We can require A to be pointed? Or just return a dummy if we could used Maybe?
  -- But ⟦_⟧ must return List A.
  -- For removeAll, we need a value.
  -- If index out of bounds, what to do?
  -- We can pass a default value in Env? Or just say Env is safe?
  -- Better: lookupElem returns A. But we don't have an A.
  
  -- Alternative: Expr interpretation returns List A.
  -- `elm k` -> `[ lookupElem k ]`.
  -- `rem e k` -> `removeAll (lookupElem k) (interp e)`.
  
  -- To make safe lookup possible without an A, we need `Env` to perhaps provide a default?
  -- Or simpler: use `Maybe A` in lookup, and if nothing, act as if it's a special value?
  -- But `removeAll` needs an A.
  
  -- Let's check how `lookupDef` was implemented.
  -- `lookupDef [] _ = []`.
  -- It returned `List A`. `[]` is a valid `List A`.
  
  -- For `A`, we don't have a default.
  -- UNLESS we assume A has some structure or we require Env to be infinite?
  -- Or just use a dummy element if we can? No.
  
  -- We can stick to `Maybe A` for `lookupElement`.
  -- `elm k` -> if `nothing` then `[]` else `[x]`.
  -- `rem e k` -> if `nothing` then `interp e` (remove nothing) else `removeAll x ...`.
  
  lookupElem : List A → ℕ → Maybe A
  lookupElem [] _ = nothing
  lookupElem (x ∷ _) zero = just x
  lookupElem (_ ∷ xs) (suc n) = lookupElem xs n

  -- Semantics of expressions
  ⟦_⟧ : Expr → Env → List A
  ⟦ var i ⟧ (ρl , _)     = lookupList ρl i
  ⟦ []ₑ ⟧ _              = []
  ⟦ elm i ⟧ (_ , ρe)     with lookupElem ρe i
  ... | nothing = []
  ... | just x  = x ∷ []
  ⟦ e₁ ++ₑ e₂ ⟧ ρ        = ⟦ e₁ ⟧ ρ ++ ⟦ e₂ ⟧ ρ
  ⟦ rem e i ⟧ (ρl , ρe)  with lookupElem ρe i
  ... | nothing = ⟦ e ⟧ (ρl , ρe)
  ... | just x  = removeAll x (⟦ e ⟧ (ρl , ρe))

  -- Shorthand constructors
  v : ℕ → Expr
  v = var

  -- Elements in removeAll were in original list
  mem-removeAll-subset : ∀ {x : A} {xs : List A} {y : A}
                       → y ∈ removeAll x xs → y ∈ xs
  mem-removeAll-subset {x} {[]} ()
  mem-removeAll-subset {x} {z ∷ xs} yIn with x ≟ z
  ... | yes _ = there (mem-removeAll-subset yIn)
  mem-removeAll-subset {x} {z ∷ xs} here | no _ = here
  mem-removeAll-subset {x} {z ∷ xs} (there yIn) | no _ = there (mem-removeAll-subset yIn)

  -- Elements different from x pass through removeAll
  mem-removeAll-neq : ∀ {x y : A} {xs : List A}
                    → y ∈ xs → x ≢ y → y ∈ removeAll x xs
  mem-removeAll-neq {x} {y} {[]} () neq
  mem-removeAll-neq {x} {y} {z ∷ xs} here neq with x ≟ z
  ... | yes p = ⊥-rec (neq p)
  ... | no _ = here
  mem-removeAll-neq {x} {y} {z ∷ xs} (there yIn) neq with x ≟ z
  ... | yes _ = mem-removeAll-neq yIn neq
  ... | no _ = there (mem-removeAll-neq yIn neq)

  -- x is not in removeAll x xs
  not-in-removeAll : ∀ (x : A) (xs : List A) → x ∈ removeAll x xs → ⊥
  not-in-removeAll x [] ()
  not-in-removeAll x (z ∷ xs) xIn with x ≟ z
  ... | yes _ = not-in-removeAll x xs xIn
  not-in-removeAll x (z ∷ xs) here | no neq = neq refl
  not-in-removeAll x (z ∷ xs) (there xIn) | no _ = not-in-removeAll x xs xIn

  -- removeAll distributes over ++
  removeAll-++ : ∀ (x : A) (xs ys : List A)
               → removeAll x (xs ++ ys) ≡ removeAll x xs ++ removeAll x ys
  removeAll-++ x [] ys = refl
  removeAll-++ x (z ∷ xs) ys with x ≟ z
  ... | yes _ = removeAll-++ x xs ys
  ... | no _ = cong (z ∷_) (removeAll-++ x xs ys)

  -- subset is preserved by removeAll
  subset-removeAll-mono : ∀ {xs ys : List A} (x : A)
                        → xs ⊆ ys → removeAll x xs ⊆ removeAll x ys
  subset-removeAll-mono {xs} {ys} x sub y yIn =
    let yInXs = mem-removeAll-subset yIn
        yInYs = sub y yInXs
    in mem-removeAll-preserve yInYs yIn
    where
      mem-removeAll-preserve : y ∈ ys → y ∈ removeAll x xs → y ∈ removeAll x ys
      mem-removeAll-preserve yInYs yInRemXs with x ≟ y
      ... | yes p = ⊥-rec (not-in-removeAll x xs (subst (λ z → z ∈ removeAll x xs) (sym p) yInRemXs))
      ... | no neq = mem-removeAll-neq yInYs neq
