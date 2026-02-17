{-# OPTIONS --safe #-}

module S4dot2.ListExt where

open import Cubical.Core.Primitives using (Level)
open import Cubical.Foundations.Prelude using (Level; Type; _≡_; refl; sym; cong; subst; _∙_)
open import Cubical.Data.List using (List; _∷_; []; _++_; map)
open import Cubical.Data.List.Properties using (++-assoc; ++-unit-r)
open import Cubical.Data.Sigma using (Σ; _,_; _×_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥; elim; rec)
open import Cubical.Relation.Nullary using (Dec; yes; no) renaming (¬_ to Neg)

-- List membership
data _∈_ {ℓ} {A : Type ℓ} (x : A) : List A → Type ℓ where
  here : ∀ {xs} → x ∈ (x ∷ xs)
  there : ∀ {y xs} → x ∈ xs → x ∈ (y ∷ xs)

-- Prefix relation
_⊑_ : ∀ {ℓ} {A : Type ℓ} → List A → List A → Type ℓ
_⊑_ {A = A} u s = Σ (List A) λ v → u ++ v ≡ s

infix 4 _∈_ _⊑_

-- Membership preservation under map
mem-map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (x : A) (l : List A) → x ∈ l → f x ∈ map f l
mem-map f x ._ (here {xs}) = here
mem-map f x ._ (there {y} {xs} p) = there (mem-map f x xs p)

-- List membership lemmas
mem-++-l : ∀ {ℓ} {A : Type ℓ} {x : A} {xs ys : List A} → x ∈ xs → x ∈ xs ++ ys
mem-++-l here = here
mem-++-l (there p) = there (mem-++-l p)

mem-++-r : ∀ {ℓ} {A : Type ℓ} {x : A} (xs : List A) {ys : List A} → x ∈ ys → x ∈ xs ++ ys
mem-++-r [] p = p
mem-++-r (y ∷ xs) p = there (mem-++-r xs p)

-- Case analysis on membership in concatenated list
mem-++-case : ∀ {ℓ} {A : Type ℓ} {x : A} (xs ys : List A) → x ∈ (xs ++ ys) → (x ∈ xs) ⊎ (x ∈ ys)
mem-++-case [] ys p = inr p
mem-++-case (z ∷ xs) ys here = inl here
mem-++-case (z ∷ xs) ys (there p) with mem-++-case xs ys p
... | inl q = inl (there q)
... | inr q = inr q

-- Remove first occurrence
remove-first : ∀ {ℓ} {A : Type ℓ} (x : A) (l : List A) → x ∈ l → List A
remove-first x ._ (here {xs}) = xs
remove-first x ._ (there {y} {xs} p) = y ∷ remove-first x xs p

remove-first-++-l : ∀ {ℓ} {A : Type ℓ} (x : A) (xs ys : List A) (p : x ∈ xs)
                  → remove-first x (xs ++ ys) (mem-++-l p) ≡ (remove-first x xs p) ++ ys
remove-first-++-l x ._ ys (here {xs}) = refl
remove-first-++-l x ._ ys (there {y} {xs} p) = cong (λ l → y ∷ l) (remove-first-++-l x xs ys p)

remove-first-++-r : ∀ {ℓ} {A : Type ℓ} (x : A) (xs ys : List A) (p : x ∈ ys)
                  → remove-first x (xs ++ ys) (mem-++-r xs p) ≡ xs ++ (remove-first x ys p)
remove-first-++-r x [] ys p = refl
remove-first-++-r x (y ∷ xs) ys p = cong (λ l → y ∷ l) (remove-first-++-r x xs ys p)

-- Transitivity of prefix
prefix-trans : ∀ {ℓ} {A : Type ℓ} {a b c : List A} → a ⊑ b → b ⊑ c → a ⊑ c
prefix-trans {a = a} {b} {c} (v1 , p1) (v2 , p2) = (v1 ++ v2) , (sym (++-assoc a v1 v2) ∙ cong (λ x → x ++ v2) p1 ∙ p2)

-- Prefix is reflexive
prefix-refl : ∀ {ℓ} {A : Type ℓ} {a : List A} → a ⊑ a
prefix-refl {a = a} = [] , ++-unit-r a

-- Prefix subset lemma
prefix-subset-l : ∀ {ℓ} {A : Type ℓ} (u v : List A) → u ⊑ u ++ v
prefix-subset-l u v = v , refl

-- Subset relation for lists
_⊆_ : ∀ {ℓ} {A : Type ℓ} → List A → List A → Type ℓ
l1 ⊆ l2 = ∀ x → x ∈ l1 → x ∈ l2

-- Lemma: membership in remove-first
mem-remove-first : ∀ {ℓ} {A : Type ℓ} (x : A) (l : List A) (p : x ∈ l) (y : A)
                 → y ∈ l → Neg (x ≡ y) → y ∈ remove-first x l p
mem-remove-first x ._ (here {xs}) y yIn neq = help-here yIn neq
  where
    help-here : y ∈ (x ∷ xs) → Neg (x ≡ y) → y ∈ xs
    help-here here neq = elim (neq refl)
    help-here (there p) neq = p
mem-remove-first x ._ (there {y = z} {xs} p) y yIn neq = help-there yIn neq
  where
    help-there : y ∈ (z ∷ xs) → Neg (x ≡ y) → y ∈ z ∷ remove-first x xs p
    help-there here neq = here
    help-there (there yIn') neq = there (mem-remove-first x xs p y yIn' neq)

-- Prefix properties
prefix-⊑-++ : ∀ {ℓ} {A : Type ℓ} (w : List A) {u v : List A} → u ⊑ v → (w ++ u) ⊑ (w ++ v)
prefix-⊑-++ w {u} {v} (s , p) = s , (assoc w u s ∙ cong (λ z → w ++ z) p)
  where
    assoc : ∀ {ℓ} {A : Type ℓ} (xs ys zs : List A) → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
    assoc [] ys zs = refl
    assoc (x ∷ xs) ys zs = cong (x ∷_) (assoc xs ys zs)

stripPrefix-⊑-cancel : ∀ {ℓ} {A : Type ℓ} (w : List A) {u v : List A} → (w ++ u) ⊑ (w ++ v) → u ⊑ v
stripPrefix-⊑-cancel w {u} {v} (s , p) = s , (++-cancel-l w (u ++ s) v (sym (++-assoc w u s) ∙ p))
  where
    cons-inj : ∀ {ℓ} {A : Type ℓ} {x : A} {xs ys : List A} → x ∷ xs ≡ x ∷ ys → xs ≡ ys
    cons-inj {x = x} p = cong (tail) p
      where
        tail : List _ → List _
        tail [] = []
        tail (x ∷ xs) = xs

    ++-cancel-l : ∀ {ℓ} {A : Type ℓ} (xs ys zs : List A) → xs ++ ys ≡ xs ++ zs → ys ≡ zs
    ++-cancel-l [] ys zs p = p
    ++-cancel-l (x ∷ xs) ys zs p = ++-cancel-l xs ys zs (cons-inj p)

mem-map-inv : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (y : B) (l : List A)
            → y ∈ map f l → Σ A λ x → (x ∈ l) × (f x ≡ y)
mem-map-inv f y (x ∷ xs) here = x , here , refl
mem-map-inv f y (x ∷ xs) (there p) =
  let (x' , xIn , eq) = mem-map-inv f y xs p
  in x' , there xIn , eq

-- List monoid transport combinators
-- These wrap common subst+path patterns for list associativity and right-unit.

subst-++-assoc : ∀ {ℓ ℓ'} {A : Type ℓ} {P : List A → Type ℓ'} {xs ys zs : List A}
  → P ((xs ++ ys) ++ zs) → P (xs ++ (ys ++ zs))
subst-++-assoc {P = P} {xs = xs} {ys} {zs} = subst P (++-assoc xs ys zs)

subst-++-assoc⁻ : ∀ {ℓ ℓ'} {A : Type ℓ} {P : List A → Type ℓ'} {xs ys zs : List A}
  → P (xs ++ (ys ++ zs)) → P ((xs ++ ys) ++ zs)
subst-++-assoc⁻ {P = P} {xs = xs} {ys} {zs} = subst P (sym (++-assoc xs ys zs))

subst-++-unit-r : ∀ {ℓ ℓ'} {A : Type ℓ} {P : List A → Type ℓ'} {xs : List A}
  → P (xs ++ []) → P xs
subst-++-unit-r {P = P} {xs = xs} = subst P (++-unit-r xs)

subst-++-unit-r⁻ : ∀ {ℓ ℓ'} {A : Type ℓ} {P : List A → Type ℓ'} {xs : List A}
  → P xs → P (xs ++ [])
subst-++-unit-r⁻ {P = P} {xs = xs} = subst P (sym (++-unit-r xs))

