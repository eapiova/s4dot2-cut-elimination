{-# OPTIONS --cubical --safe #-}

-- Sorted positions for S4.2 modal logic
-- Uses Cubical's DescendingList.Strict instantiated with ℕ and _>_

module S4dot2.SortedPosition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Nat using (ℕ; zero; suc; discreteℕ)
open import Cubical.Data.Nat.Order using (_<_; _>_; Trichotomy; _≟_; <-trans; ¬m<m; <→≢)
open import Cubical.Data.Nat.Order using (isProp≤)
open import Cubical.Relation.Nullary using (Dec; yes; no; Discrete) renaming (¬_ to Type¬)
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.List using (List; _∷_; [])

-- For proving Position equalities via LFSet
open import Cubical.HITs.ListedFiniteSet as LFSet using (LFSet; _++_; [])
open import Cubical.HITs.ListedFiniteSet.Properties using (comm-++; comm-++-[])

-- Token is ℕ
Token : Type₀
Token = ℕ

-- The ordering relation for strictly descending lists
_>ℕ_ : ℕ → ℕ → Type₀
_>ℕ_ = _>_

-- Import the SDL module instantiated with ℕ and _>_
open import Cubical.Data.DescendingList.Strict ℕ _>ℕ_ public
  renaming (SDL to Position; [] to ε; cons to pos-cons)

-- Import properties module
import Cubical.Data.DescendingList.Strict.Properties as SDLPropsModule
module SDLProps = SDLPropsModule ℕ _>ℕ_

-- Import base Properties for _++ᴰᴸ_ (works for SDL since SDL = DL with >)
import Cubical.Data.DescendingList.Properties ℕ _>ℕ_ as DLProps

-- Required properties
>-isProp : ∀ {m n} → isProp (m >ℕ n)
>-isProp = isProp≤

>-trans : ∀ {x y z} → x >ℕ y → y >ℕ z → x >ℕ z
>-trans x>y y>z = <-trans y>z x>y

>-irreflexive : ∀ {x} → Type¬ (x >ℕ x)
>-irreflexive {x} x>x = ¬m<m x>x

-- Trichotomy (export these for use in other modules)
open SDLProps using (Tri; tri-<; tri-≡; tri->) public

triℕ : ∀ x y → Tri (y >ℕ x) (x ≡ y) (x >ℕ y)
triℕ x y with x ≟ y
triℕ x y | Trichotomy.lt x<y = tri-< x<y (<→≢ x<y) λ y<x → ¬m<m (<-trans x<y y<x)
triℕ x y | Trichotomy.eq x≡y = tri-≡ (λ y>x → <→≢ y>x x≡y) x≡y (λ y<x → <→≢ y<x (sym x≡y))
triℕ x y | Trichotomy.gt y<x = tri-> (λ x<y → ¬m<m (<-trans y<x x<y)) (<→≢ y<x ∘ sym) y<x

-- Re-export from library
unsortTokens : Position → LFSet ℕ
unsortTokens = SDLProps.unsort

open SDLProps.IsoToLFSet discreteℕ >-isProp triℕ >-trans >-irreflexive public
  renaming (
    insert to insertToken;
    insert-swap to insertToken-swap;
    insert-dup to insertToken-dup;
    unsort-inj to position-inj;
    SDL-isSet to Position-isSet
  )

-- Singleton position
[_] : Token → Position
[ x ] = pos-cons x ε >ᴴ[]

-- Direct membership
_∈Pos_ : Token → Position → Type₀
x ∈Pos ε = ⊥.⊥
x ∈Pos (pos-cons y ys _) = (x ≡ y) ⊎ (x ∈Pos ys)

_∉Pos_ : Token → Position → Type₀
x ∉Pos s = Type¬ (x ∈Pos s)

-- Decidable membership
_∈Pos?_ : (x : Token) → (s : Position) → Dec (x ∈Pos s)
x ∈Pos? ε = no (λ ())
x ∈Pos? (pos-cons y ys _) with discreteℕ x y
... | yes x≡y = yes (inl x≡y)
... | no x≢y with x ∈Pos? ys
...   | yes x∈ys = yes (inr x∈ys)
...   | no x∉ys = no λ { (inl x≡y) → x≢y x≡y ; (inr x∈ys) → x∉ys x∈ys }

-- Merge (union) of two positions
-- Note: Semantically equivalent to DLProps._++ᴰᴸ_ but defined recursively
-- for computational behavior (pattern matching, decidability)
merge : Position → Position → Position
merge ε t = t
merge (pos-cons x xs x>xs) t = insertToken x (merge xs t)

-- Helper: unsortTokens (merge s t) ≡ unsortTokens s ++ unsortTokens t
unsort-merge : ∀ s t → unsortTokens (merge s t) ≡ unsortTokens s LFSet.++ unsortTokens t
unsort-merge ε t = refl
unsort-merge (pos-cons x xs x>xs) t =
  insert-correct x (merge xs t) ∙ cong (x LFSet.∷_) (unsort-merge xs t)

-- merge is commutative (via LFSet)
merge-comm : ∀ s t → merge s t ≡ merge t s
merge-comm s t = position-inj (merge s t) (merge t s)
  (unsort-merge s t ∙ comm-++ (unsortTokens s) (unsortTokens t) ∙ sym (unsort-merge t s))

-- Remove a single token
remove : Token → Position → Position
remove x ε = ε
remove x (pos-cons y ys y>ys) with discreteℕ x y
... | yes _ = ys
... | no _ = insertToken y (remove x ys)

-- Token substitution
substTokenPos : Token → Position → Position → Position
substTokenPos x t s = merge (remove x s) t

-- Helper: unsortTokens (remove x s) ≡ unsortTokens s when x ∉Pos s
-- (removing a non-existent element is identity for LFSet semantics)
unsort-remove-not-in : ∀ x s → x ∉Pos s → unsortTokens (remove x s) ≡ unsortTokens s
unsort-remove-not-in x ε x∉s = refl
unsort-remove-not-in x (pos-cons y ys y>ys) x∉s with discreteℕ x y
... | yes x≡y = ⊥.rec (x∉s (inl x≡y))
... | no x≢y =
  insert-correct y (remove x ys) ∙
  cong (y LFSet.∷_) (unsort-remove-not-in x ys (λ x∈ys → x∉s (inr x∈ys)))

-- Helper: x ∉Pos s → remove x (insertToken x s) ≡ s
remove-insertToken : ∀ x s → x ∉Pos s → remove x (insertToken x s) ≡ s
remove-insertToken x s x∉s = position-inj (remove x (insertToken x s)) s goal
  where
  goal : unsortTokens (remove x (insertToken x s)) ≡ unsortTokens s
  goal = aux s x∉s
    where
    aux : ∀ r → x ∉Pos r → unsortTokens (remove x (insertToken x r)) ≡ unsortTokens r
    aux ε _ with discreteℕ x x
    ... | yes _ = refl
    ... | no x≢x = ⊥.rec (x≢x refl)

    aux (pos-cons z zs z>zs) x∉r with triℕ x z
    ... | tri-≡ _ x≡z _ = ⊥.rec (x∉r (inl x≡z))
    aux (pos-cons z zs z>zs) x∉r | tri-< z>x _ _ with discreteℕ x z
    ...   | yes x≡z = ⊥.rec (x∉r (inl x≡z))
    ...   | no x≢z =
      insert-correct z (remove x (insertToken x zs)) ∙
      cong (z LFSet.∷_) (aux zs (λ x∈zs → x∉r (inr x∈zs)))
    aux (pos-cons z zs z>zs) x∉r | tri-> _ _ x>z with discreteℕ x x
    ...   | yes _ = refl
    ...   | no x≢x = ⊥.rec (x≢x refl)

-- Key lemma for mix
substTokenPos-insert : ∀ x s t → x ∉Pos s → substTokenPos x t (insertToken x s) ≡ merge s t
substTokenPos-insert x s t x∉s =
  cong (λ r → merge r t) (remove-insertToken x s x∉s)

-- =============================================================================
-- InsertToken membership lemmas (needed before remove lemmas)
-- =============================================================================

-- Helper: membership in insertToken
-- When z > x (tri-<): insert x into tail, result is (z ∷ insert x zs), so mem type is (y ≡ z) ⊎ (y ∈Pos (insert x zs))
-- When x ≡ z (tri-≡): duplicate, result is (z ∷ zs), so mem type is (y ≡ z) ⊎ (y ∈Pos zs)
-- When x > z (tri->): x goes at head, result is (x ∷ z ∷ zs), so mem type is (y ≡ x) ⊎ ((y ≡ z) ⊎ (y ∈Pos zs))
∈Pos-insertToken : ∀ x y s → y ∈Pos (insertToken x s) → (y ≡ x) ⊎ (y ∈Pos s)
∈Pos-insertToken x y ε mem with triℕ x x
... | tri-≡ _ _ _ with mem
...   | inl y≡x = inl y≡x
∈Pos-insertToken x y ε mem | tri-< x>x _ _ = ⊥.rec {A = (y ≡ x) ⊎ (y ∈Pos ε)} (>-irreflexive x>x)
∈Pos-insertToken x y ε mem | tri-> _ _ x>x = ⊥.rec {A = (y ≡ x) ⊎ (y ∈Pos ε)} (>-irreflexive x>x)
∈Pos-insertToken x y (pos-cons z zs z>zs) mem with triℕ x z
-- Case tri-< z>x: z > x, so result is pos-cons z (insertToken x zs), mem : (y ≡ z) ⊎ (y ∈Pos (insertToken x zs))
∈Pos-insertToken x y (pos-cons z zs z>zs) mem | tri-< z>x _ _ with mem
...   | inl y≡z = inr (inl y≡z)
...   | inr y∈insert with ∈Pos-insertToken x y zs y∈insert
...     | inl y≡x = inl y≡x
...     | inr y∈zs = inr (inr y∈zs)
-- Case tri-≡: x ≡ z, duplicate removed, result is pos-cons z zs, mem : (y ≡ z) ⊎ (y ∈Pos zs)
∈Pos-insertToken x y (pos-cons z zs z>zs) mem | tri-≡ _ x≡z _ with mem
...   | inl y≡z = inl (y≡z ∙ sym x≡z)
...   | inr y∈zs = inr (inr y∈zs)
-- Case tri-> x>z: x > z, x at head, result is pos-cons x (pos-cons z zs), mem : (y ≡ x) ⊎ ((y ≡ z) ⊎ (y ∈Pos zs))
∈Pos-insertToken x y (pos-cons z zs z>zs) mem | tri-> _ _ x>z with mem
...   | inl y≡x = inl y≡x
...   | inr (inl y≡z) = inr (inl y≡z)
...   | inr (inr y∈zs) = inr (inr y∈zs)

-- Helper: membership into insertToken
insertToken-∈Pos : ∀ x y s → (y ≡ x) ⊎ (y ∈Pos s) → y ∈Pos (insertToken x s)
insertToken-∈Pos x y ε (inl y≡x) with triℕ x x
... | tri-≡ _ _ _ = inl y≡x
... | tri-< x>x _ _ = ⊥.rec {A = y ∈Pos (insertToken x ε)} (>-irreflexive x>x)
... | tri-> _ _ x>x = ⊥.rec {A = y ∈Pos (insertToken x ε)} (>-irreflexive x>x)
insertToken-∈Pos x y ε (inr ())
insertToken-∈Pos x y (pos-cons z zs z>zs) choice with triℕ x z
-- Case tri-< z>x: z > x, result is pos-cons z (insertToken x zs)
insertToken-∈Pos x y (pos-cons z zs z>zs) (inl y≡x) | tri-< z>x _ _ = inr (insertToken-∈Pos x y zs (inl y≡x))
insertToken-∈Pos x y (pos-cons z zs z>zs) (inr (inl y≡z)) | tri-< z>x _ _ = inl y≡z
insertToken-∈Pos x y (pos-cons z zs z>zs) (inr (inr y∈zs)) | tri-< z>x _ _ = inr (insertToken-∈Pos x y zs (inr y∈zs))
-- Case tri-≡: x ≡ z, duplicate, result is pos-cons z zs
insertToken-∈Pos x y (pos-cons z zs z>zs) (inl y≡x) | tri-≡ _ x≡z _ = inl (y≡x ∙ x≡z)
insertToken-∈Pos x y (pos-cons z zs z>zs) (inr (inl y≡z)) | tri-≡ _ x≡z _ = inl y≡z
insertToken-∈Pos x y (pos-cons z zs z>zs) (inr (inr y∈zs)) | tri-≡ _ x≡z _ = inr y∈zs
-- Case tri-> x>z: x > z, result is pos-cons x (pos-cons z zs)
insertToken-∈Pos x y (pos-cons z zs z>zs) (inl y≡x) | tri-> _ _ x>z = inl y≡x
insertToken-∈Pos x y (pos-cons z zs z>zs) (inr (inl y≡z)) | tri-> _ _ x>z = inr (inl y≡z)
insertToken-∈Pos x y (pos-cons z zs z>zs) (inr (inr y∈zs)) | tri-> _ _ x>z = inr (inr y∈zs)

-- Non-membership in insertToken: y ∉Pos (insertToken x s) if y ≢ x and y ∉Pos s
∉Pos-insertToken : ∀ x y s → y ∉Pos s → (y ≡ x → ⊥.⊥) → y ∉Pos (insertToken x s)
∉Pos-insertToken x y s y∉s y≢x y∈insert with ∈Pos-insertToken x y s y∈insert
... | inl y≡x = y≢x y≡x
... | inr y∈s = y∉s y∈s

-- =============================================================================
-- Remove membership lemmas
-- =============================================================================

-- Helper: the head of an SDL is not in the tail (follows from strict ordering)
head-∉Pos-tail : ∀ y ys → (y>ys : y >ᴴ ys) → y ∉Pos ys
head-∉Pos-tail y ε _ ()
head-∉Pos-tail y (pos-cons z zs z>zs) (>ᴴcons y>z) (inl y≡z) =
  >-irreflexive (subst (y >ℕ_) (sym y≡z) y>z)
head-∉Pos-tail y (pos-cons z zs z>zs) (>ᴴcons y>z) (inr y∈zs) =
  head-∉Pos-tail y zs (>ᴴ-trans y z zs y>z z>zs) y∈zs

-- If t ∈ remove x s, then t ∈ s
remove-∈Pos : ∀ x t s → t ∈Pos (remove x s) → t ∈Pos s
remove-∈Pos x t ε ()
remove-∈Pos x t (pos-cons y ys y>ys) t∈rem with discreteℕ x y
... | yes x≡y = inr t∈rem  -- remove x (y∷ys) = ys when x≡y, so t∈ys
... | no x≢y with ∈Pos-insertToken y t (remove x ys) t∈rem
...   | inl t≡y = inl t≡y
...   | inr t∈remys = inr (remove-∈Pos x t ys t∈remys)

-- If t ∈ remove x s, then x ≢ t
remove-∈Pos-neq : ∀ x t s → t ∈Pos (remove x s) → (x ≡ t → ⊥.⊥)
remove-∈Pos-neq x t ε () _
remove-∈Pos-neq x t (pos-cons y ys y>ys) t∈rem x≡t with discreteℕ x y
remove-∈Pos-neq x t (pos-cons y ys y>ys) t∈rem x≡t | yes x≡y =
  -- remove x (y∷ys) = ys, and t ∈ ys
  -- x≡y and x≡t means t≡y, so y ∈ ys, which contradicts SDL (head not in tail)
  let t∈ys = t∈rem
      t≡y = sym x≡t ∙ x≡y
  in head-∉Pos-tail y ys y>ys (subst (_∈Pos ys) t≡y t∈ys)
remove-∈Pos-neq x t (pos-cons y ys y>ys) t∈rem x≡t | no x≢y
  with ∈Pos-insertToken y t (remove x ys) t∈rem
...   | inl t≡y = x≢y (x≡t ∙ t≡y)
...   | inr t∈remys = remove-∈Pos-neq x t ys t∈remys x≡t

-- If t ∈ s and x ≢ t, then t ∈ remove x s
∈Pos-remove : ∀ x t s → t ∈Pos s → (x ≡ t → ⊥.⊥) → t ∈Pos (remove x s)
∈Pos-remove x t ε () _
∈Pos-remove x t (pos-cons y ys y>ys) (inl t≡y) x≢t with discreteℕ x y
... | yes x≡y = ⊥.rec (x≢t (x≡y ∙ sym t≡y))  -- x≡y and t≡y means x≡t, contradiction
... | no x≢y = insertToken-∈Pos y t (remove x ys) (inl t≡y)
∈Pos-remove x t (pos-cons y ys y>ys) (inr t∈ys) x≢t with discreteℕ x y
... | yes x≡y = t∈ys  -- remove x (y∷ys) = ys
... | no x≢y = insertToken-∈Pos y t (remove x ys) (inr (∈Pos-remove x t ys t∈ys x≢t))

-- When x ∉Pos s: remove x s ≡ s
remove-∉Pos-id : ∀ x s → x ∉Pos s → remove x s ≡ s
remove-∉Pos-id x s x∉s = position-inj (remove x s) s (unsort-remove-not-in x s x∉s)

-- =============================================================================
-- Subset relation for positions
-- =============================================================================

-- Position subset relation (s ⊆ t means all tokens in s are in t)
_⊑_ : Position → Position → Type₀
s ⊑ t = ∀ y → y ∈Pos s → y ∈Pos t

-- Decidable subset
_⊑?_ : (s t : Position) → Dec (s ⊑ t)
ε ⊑? t = yes (λ _ ())
pos-cons x xs x>xs ⊑? t with x ∈Pos? t
... | no x∉t = no (λ sub → x∉t (sub x (inl refl)))
... | yes x∈t with xs ⊑? t
...   | yes rest = yes λ { y (inl y≡x) → subst (_∈Pos t) (sym y≡x) x∈t
                         ; y (inr y∈xs) → rest y y∈xs }
...   | no ¬rest = no (λ sub → ¬rest (λ y y∈xs → sub y (inr y∈xs)))

-- =============================================================================
-- Merge properties
-- =============================================================================

-- merge with ε is identity (left)
merge-ε-l : ∀ s → merge ε s ≡ s
merge-ε-l s = refl

-- Membership in merge
∈Pos-merge : ∀ x s t → x ∈Pos (merge s t) → (x ∈Pos s) ⊎ (x ∈Pos t)
∈Pos-merge x ε t mem = inr mem
∈Pos-merge x (pos-cons y ys y>ys) t mem with ∈Pos-insertToken y x (merge ys t) mem
... | inl x≡y = inl (inl x≡y)
... | inr x∈merge with ∈Pos-merge x ys t x∈merge
...   | inl x∈ys = inl (inr x∈ys)
...   | inr x∈t = inr x∈t

-- Membership into merge (left)
merge-∈Pos-l : ∀ x s t → x ∈Pos s → x ∈Pos (merge s t)
merge-∈Pos-l x (pos-cons y ys y>ys) t (inl x≡y) =
  insertToken-∈Pos y x (merge ys t) (inl x≡y)
merge-∈Pos-l x (pos-cons y ys y>ys) t (inr x∈ys) =
  insertToken-∈Pos y x (merge ys t) (inr (merge-∈Pos-l x ys t x∈ys))

-- Membership into merge (right)
merge-∈Pos-r : ∀ x s t → x ∈Pos t → x ∈Pos (merge s t)
merge-∈Pos-r x ε t mem = mem
merge-∈Pos-r x (pos-cons y ys y>ys) t mem =
  insertToken-∈Pos y x (merge ys t) (inr (merge-∈Pos-r x ys t mem))

-- merge with ε is identity (right) - via LFSet
merge-ε-r : ∀ s → merge s ε ≡ s
merge-ε-r ε = refl
merge-ε-r (pos-cons x xs x>xs) = position-inj (merge (pos-cons x xs x>xs) ε) (pos-cons x xs x>xs)
  (unsort-merge (pos-cons x xs x>xs) ε ∙ comm-++-[] (unsortTokens (pos-cons x xs x>xs)))

-- merge is associative (via LFSet)
merge-assoc : ∀ s t r → merge (merge s t) r ≡ merge s (merge t r)
merge-assoc s t r = position-inj (merge (merge s t) r) (merge s (merge t r))
  (unsort-merge (merge s t) r ∙
   cong (LFSet._++ unsortTokens r) (unsort-merge s t) ∙
   sym (LFSet.assoc-++ (unsortTokens s) (unsortTokens t) (unsortTokens r)) ∙
   cong (unsortTokens s LFSet.++_) (sym (unsort-merge t r)) ∙
   sym (unsort-merge s (merge t r)))

-- Merge with singleton equals insertToken: s ∘ [ x ] ≡ insertToken x s
merge-singleton : ∀ s x → merge s [ x ] ≡ insertToken x s
merge-singleton s x = position-inj (merge s [ x ]) (insertToken x s)
  (unsort-merge s [ x ] ∙
   cong (unsortTokens s LFSet.++_) (insert-correct x ε) ∙
   comm-++ (unsortTokens s) (x LFSet.∷ LFSet.[]) ∙
   sym (insert-correct x s))

-- =============================================================================
-- Subset preservation by merge
-- =============================================================================

-- s is a subset of merge s t
⊑-merge-l : ∀ s t → s ⊑ (merge s t)
⊑-merge-l s t y y∈s = merge-∈Pos-l y s t y∈s

-- t is a subset of merge s t
⊑-merge-r : ∀ s t → t ⊑ (merge s t)
⊑-merge-r s t y y∈t = merge-∈Pos-r y s t y∈t

-- Merge is monotonic with respect to subset
merge-⊑-mono : ∀ {s s' t t'} → s ⊑ s' → t ⊑ t' → (merge s t) ⊑ (merge s' t')
merge-⊑-mono {s} {s'} {t} {t'} s⊑s' t⊑t' y y∈merge with ∈Pos-merge y s t y∈merge
... | inl y∈s = merge-∈Pos-l y s' t' (s⊑s' y y∈s)
... | inr y∈t = merge-∈Pos-r y s' t' (t⊑t' y y∈t)

-- Non-membership is preserved by merge
∉Pos-merge : ∀ {x s t} → x ∉Pos s → x ∉Pos t → x ∉Pos (merge s t)
∉Pos-merge {x} {s} {t} x∉s x∉t x∈merge with ∈Pos-merge x s t x∈merge
... | inl x∈s = x∉s x∈s
... | inr x∈t = x∉t x∈t

-- =============================================================================
-- Conversion utilities
-- =============================================================================

-- Convert Position to List (forgetting sorted property)
toList : Position → List Token
toList ε = []
toList (pos-cons x xs _) = x ∷ toList xs

-- Build Position from unsorted list by repeated insertion
fromTokenList : List Token → Position
fromTokenList [] = ε
fromTokenList (x ∷ xs) = insertToken x (fromTokenList xs)

-- Membership in List
data _∈List_ {ℓ} {A : Type ℓ} (x : A) : List A → Type ℓ where
  here : ∀ {xs} → x ∈List (x ∷ xs)
  there : ∀ {y xs} → x ∈List xs → x ∈List (y ∷ xs)

-- fromTokenList preserves membership
fromTokenList-∈ : ∀ x xs → x ∈List xs → x ∈Pos (fromTokenList xs)
fromTokenList-∈ x (y ∷ xs) here = insertToken-∈Pos y x (fromTokenList xs) (inl refl)
fromTokenList-∈ x (y ∷ xs) (there mem) = insertToken-∈Pos y x (fromTokenList xs) (inr (fromTokenList-∈ x xs mem))

-- toList preserves membership (Position → List)
toList-∈ : ∀ x s → x ∈Pos s → x ∈List (toList s)
toList-∈ x (pos-cons y ys _) (inl x≡y) = subst (λ z → z ∈List (y ∷ toList ys)) (sym x≡y) here
toList-∈ x (pos-cons y ys _) (inr x∈ys) = there (toList-∈ x ys x∈ys)

-- =============================================================================
-- Eigentoken preservation lemmas (for proof substitution)
-- =============================================================================

-- Non-membership is preserved by remove (removing elements can't add new ones)
∉Pos-remove : ∀ {x} z s → x ∉Pos s → x ∉Pos (remove z s)
∉Pos-remove z ε x∉s ()
∉Pos-remove {x} z (pos-cons y ys y>ys) x∉s x∈rem with discreteℕ z y
... | yes z≡y = x∉s (inr x∈rem)  -- remove z (y∷ys) = ys when z≡y
... | no z≢y with ∈Pos-insertToken y x (remove z ys) x∈rem
...   | inl x≡y = x∉s (inl x≡y)
...   | inr x∈remys = ∉Pos-remove z ys (λ x∈ys → x∉s (inr x∈ys)) x∈remys

-- Non-membership is preserved by substTokenPos
-- substTokenPos z t s = merge (remove z s) t
-- If x ∉ s and x ∉ t, then x ∉ (remove z s) and x ∉ t, so x ∉ merge (remove z s) t
∉Pos-substTokenPos : ∀ {x} z t s → x ∉Pos s → x ∉Pos t → x ∉Pos (substTokenPos z t s)
∉Pos-substTokenPos z t s x∉s x∉t = ∉Pos-merge (∉Pos-remove z s x∉s) x∉t

-- When z ≢ x: remove z (insertToken x s) ≡ insertToken x (remove z s)
-- (removing z from s∪{x} equals {x} ∪ (removing z from s) when z≠x)
remove-insertToken-neq : ∀ z x s → (z ≡ x → ⊥.⊥) → remove z (insertToken x s) ≡ insertToken x (remove z s)
remove-insertToken-neq z x ε z≢x with triℕ x x
... | tri-≡ _ _ _ with discreteℕ z x
...   | yes z≡x = ⊥.rec (z≢x z≡x)
...   | no _ = refl
remove-insertToken-neq z x ε z≢x | tri-< x>x _ _ = ⊥.rec (>-irreflexive x>x)
remove-insertToken-neq z x ε z≢x | tri-> _ _ x>x = ⊥.rec (>-irreflexive x>x)
remove-insertToken-neq z x (pos-cons y ys y>ys) z≢x with triℕ x y
-- Case y > x: insertToken x (y∷ys) = y ∷ (insertToken x ys)
remove-insertToken-neq z x (pos-cons y ys y>ys) z≢x | tri-< y>x _ _ with discreteℕ z y
-- Subcase z ≡ y: both sides equal insertToken x ys
...   | yes z≡y = refl
-- Subcase z ≢ y: use IH and insertToken-swap
...   | no z≢y =
  cong (insertToken y) (remove-insertToken-neq z x ys z≢x) ∙ insertToken-swap y x (remove z ys)
-- Case x ≡ y: insertToken x (y∷ys) = y∷ys (duplicate)
remove-insertToken-neq z x (pos-cons y ys y>ys) z≢x | tri-≡ _ x≡y _ with discreteℕ z y
-- Subcase z ≡ y: contradiction since z ≢ x and x ≡ y means z ≢ y
...   | yes z≡y = ⊥.rec (z≢x (z≡y ∙ sym x≡y))
-- Subcase z ≢ y: LHS = insertToken y (remove z ys), RHS uses dup
-- Path: insertToken y r ≡ insertToken y (insertToken y r) ≡ insertToken x (insertToken y r)
...   | no z≢y =
  sym (insertToken-dup y (remove z ys)) ∙ cong (λ w → insertToken w (insertToken y (remove z ys))) (sym x≡y)
-- Case x > y: insertToken x (y∷ys) = x ∷ y∷ys
remove-insertToken-neq z x (pos-cons y ys y>ys) z≢x | tri-> _ _ x>y with discreteℕ z x
-- Subcase z ≡ x: contradiction
...   | yes z≡x = ⊥.rec (z≢x z≡x)
-- Subcase z ≢ x: LHS = insertToken x (remove z (y∷ys)) = RHS
...   | no _ = refl

-- merge (insertToken x s) t ≡ insertToken x (merge s t)
-- This is (s∪{x})∪t = {x}∪(s∪t), which holds unconditionally for sets
merge-insertToken-l : ∀ x s t → merge (insertToken x s) t ≡ insertToken x (merge s t)
merge-insertToken-l x ε t = refl  -- insertToken x ε = [x], merge [x] t = insertToken x t
merge-insertToken-l x (pos-cons y ys y>ys) t with triℕ x y
-- Case y > x: insertToken x (y∷ys) = y ∷ (insertToken x ys)
-- LHS: merge (y ∷ insertToken x ys) t = insertToken y (merge (insertToken x ys) t)
-- RHS: insertToken x (insertToken y (merge ys t))
-- By IH and insertToken-swap
... | tri-< y>x _ _ =
  cong (insertToken y) (merge-insertToken-l x ys t) ∙ insertToken-swap y x (merge ys t)
-- Case x ≡ y: insertToken x (y∷ys) = y∷ys (duplicate removed)
-- LHS: merge (y∷ys) t = insertToken y (merge ys t)
-- RHS: insertToken x (insertToken y (merge ys t)) = insertToken y (merge ys t) by dup
-- Path: insertToken y r ≡ insertToken y (insertToken y r) ≡ insertToken x (insertToken y r)
... | tri-≡ _ x≡y _ =
  sym (insertToken-dup y (merge ys t)) ∙ cong (λ z → insertToken z (insertToken y (merge ys t))) (sym x≡y)
-- Case x > y: insertToken x (y∷ys) = x ∷ y∷ys
-- LHS: merge (x ∷ y∷ys) t = insertToken x (merge (y∷ys) t)
-- RHS: insertToken x (merge (y∷ys) t)
... | tri-> _ _ x>y = refl

-- =============================================================================
-- Remove distributes over merge
-- =============================================================================

-- Helper: insertToken z zs ≡ pos-cons z zs z>zs (inserting at head)
-- If we have a proof that z > everything in zs, then insertToken z zs = pos-cons z zs (...)
insertToken-cons : ∀ z zs (z>zs : z >ᴴ zs) → insertToken z zs ≡ pos-cons z zs z>zs
insertToken-cons z zs z>zs = position-inj (insertToken z zs) (pos-cons z zs z>zs)
  (insert-correct z zs)

-- Inserting an element that's already present is identity (via position-inj)
-- When x ∈Pos s, the LFSet representations are equal: x ∷ unsort s ≡ unsort s
insertToken-∈Pos-id : ∀ x s → x ∈Pos s → insertToken x s ≡ s
insertToken-∈Pos-id x s x∈s = position-inj (insertToken x s) s
  (insert-correct x s ∙ ∈→dup x s x∈s)
  where
    -- unsort (pos-cons y ys _) ≡ y ∷ unsort ys via insertToken-cons
    unsort-cons : ∀ y ys y>ys → unsortTokens (pos-cons y ys y>ys) ≡ y LFSet.∷ unsortTokens ys
    unsort-cons y ys y>ys = cong unsortTokens (sym (insertToken-cons y ys y>ys)) ∙ insert-correct y ys

    -- Key lemma: if x ∈ s, then x ∷ unsort s ≡ unsort s (via LFSet dup path)
    ∈→dup : ∀ x t → x ∈Pos t → x LFSet.∷ unsortTokens t ≡ unsortTokens t
    ∈→dup x ε ()
    ∈→dup x (pos-cons y ys y>ys) (inl x≡y) =
      -- x ≡ y, so x ∷ (y ∷ unsort ys) ≡ y ∷ unsort ys
      -- By LFSet.dup: y ∷ y ∷ xs ≡ y ∷ xs
      x LFSet.∷ unsortTokens (pos-cons y ys y>ys)
        ≡⟨ cong (x LFSet.∷_) (unsort-cons y ys y>ys) ⟩
      x LFSet.∷ (y LFSet.∷ unsortTokens ys)
        ≡⟨ cong (λ z → z LFSet.∷ (y LFSet.∷ unsortTokens ys)) x≡y ⟩
      y LFSet.∷ (y LFSet.∷ unsortTokens ys)
        ≡⟨ LFSet.dup y (unsortTokens ys) ⟩
      y LFSet.∷ unsortTokens ys
        ≡⟨ sym (unsort-cons y ys y>ys) ⟩
      unsortTokens (pos-cons y ys y>ys) ∎
    ∈→dup x (pos-cons y ys y>ys) (inr x∈ys) =
      -- x ∈ ys, so by IH: x ∷ unsort ys ≡ unsort ys
      -- We need: x ∷ (y ∷ unsort ys) ≡ y ∷ unsort ys
      -- Use comm: x ∷ y ∷ xs ≡ y ∷ x ∷ xs, then apply IH
      x LFSet.∷ unsortTokens (pos-cons y ys y>ys)
        ≡⟨ cong (x LFSet.∷_) (unsort-cons y ys y>ys) ⟩
      x LFSet.∷ (y LFSet.∷ unsortTokens ys)
        ≡⟨ LFSet.comm x y (unsortTokens ys) ⟩
      y LFSet.∷ (x LFSet.∷ unsortTokens ys)
        ≡⟨ cong (y LFSet.∷_) (∈→dup x ys x∈ys) ⟩
      y LFSet.∷ unsortTokens ys
        ≡⟨ sym (unsort-cons y ys y>ys) ⟩
      unsortTokens (pos-cons y ys y>ys) ∎

-- Helper: remove y (insertToken y r) ≡ remove y r
-- Whether y is in r or not, inserting and then removing y is the same as just removing y
remove-insertToken-same : ∀ y r → remove y (insertToken y r) ≡ remove y r
remove-insertToken-same y ε with triℕ y y
... | tri-≡ _ _ _ with discreteℕ y y
...   | yes _ = refl
...   | no y≢y = ⊥.rec (y≢y refl)
remove-insertToken-same y ε | tri-< y>y _ _ = ⊥.rec (>-irreflexive y>y)
remove-insertToken-same y ε | tri-> _ _ y>y = ⊥.rec (>-irreflexive y>y)
remove-insertToken-same y (pos-cons z zs z>zs) with triℕ y z
-- Case z > y: insertToken y (z∷zs) = z ∷ (insertToken y zs)
remove-insertToken-same y (pos-cons z zs z>zs) | tri-< z>y _ _ with discreteℕ y z
...   | yes y≡z = ⊥.rec (>-irreflexive (subst (z >ℕ_) y≡z z>y))
...   | no y≢z = cong (insertToken z) (remove-insertToken-same y zs)
-- Case y ≡ z: insertToken y (z∷zs) = z∷zs (duplicate)
-- remove y (z∷zs) = zs (since y ≡ z)
remove-insertToken-same y (pos-cons z zs z>zs) | tri-≡ _ y≡z _ = refl
-- Case y > z: insertToken y (z∷zs) = y ∷ z∷zs
-- remove y (y ∷ z∷zs) = z∷zs
-- remove y (z∷zs) = insertToken z (remove y zs) (since y > z means y ≢ z)
remove-insertToken-same y (pos-cons z zs z>zs) | tri-> _ y≢z y>z with discreteℕ y y
...   | yes _ with discreteℕ y z
...     | yes y≡z = ⊥.rec (y≢z y≡z)
...     | no _ =
  -- LHS: z ∷ zs
  -- RHS: insertToken z (remove y zs)
  -- Need: z ∷ zs ≡ insertToken z (remove y zs)
  -- Since y > z, y can't be in zs (zs has elements < z < y), so remove y zs = zs
  -- Then insertToken z zs = z ∷ zs by z>zs
  let y∉zs : y ∉Pos zs
      y∉zs y∈zs = head-∉Pos-tail y zs (>ᴴ-trans y z zs y>z z>zs) y∈zs
  in sym (cong (insertToken z) (remove-∉Pos-id y zs y∉zs) ∙ insertToken-cons z zs z>zs)
remove-insertToken-same y (pos-cons z zs z>zs) | tri-> _ _ y>z | no y≢y = ⊥.rec (y≢y refl)

-- Remove distributes over merge: (s ∪ t) \ {x} = (s \ {x}) ∪ (t \ {x})
remove-merge-distrib : ∀ x s t → remove x (merge s t) ≡ merge (remove x s) (remove x t)
remove-merge-distrib x ε t = refl
remove-merge-distrib x (pos-cons y ys y>ys) t with discreteℕ x y
-- Case x ≡ y: remove from head
-- LHS: remove x (insertToken y (merge ys t))
-- RHS: merge (remove x (y∷ys)) (remove x t) = merge ys (remove x t)
--      (since x≡y means remove x (y∷ys) = ys by definition)
-- Using x≡y: LHS = remove y (insertToken y (merge ys t)) = remove y (merge ys t)
--                = merge (remove y ys) (remove y t) = merge ys (remove y t)
--      and RHS = merge ys (remove y t)
... | yes x≡y =
  subst (λ w → remove w (insertToken y (merge ys t)) ≡ merge ys (remove w t)) (sym x≡y)
    (remove-insertToken-same y (merge ys t) ∙
     remove-merge-distrib y ys t ∙
     cong (λ r → merge r (remove y t)) (remove-∉Pos-id y ys (head-∉Pos-tail y ys y>ys)))
-- Case x ≢ y: use remove-insertToken-neq and merge-insertToken-l
-- LHS: remove x (insertToken y (merge ys t)) = insertToken y (remove x (merge ys t))
--    = insertToken y (merge (remove x ys) (remove x t)) by IH
-- RHS: merge (insertToken y (remove x ys)) (remove x t)
-- By merge-insertToken-l
... | no x≢y =
  remove-insertToken-neq x y (merge ys t) x≢y ∙
  cong (insertToken y) (remove-merge-distrib x ys t) ∙
  sym (merge-insertToken-l y (remove x ys) (remove x t))

-- =============================================================================

-- Key lemma: substTokenPos preserves insertToken when eigentoken is different
-- When z ≢ y:
-- substTokenPos z t (insertToken y s) ≡ insertToken y (substTokenPos z t s)
--
-- This is the formal version of "eigenposition is preserved under substitution"
-- from Lemma 4.8 (Sequents Prefix Replacement) in the paper.
substTokenPos-insertToken-neq : ∀ z y s t
  → (z ≡ y → ⊥.⊥)
  → substTokenPos z t (insertToken y s) ≡ insertToken y (substTokenPos z t s)
substTokenPos-insertToken-neq z y s t z≢y =
  cong (λ r → merge r t) (remove-insertToken-neq z y s z≢y) ∙ merge-insertToken-l y (remove z s) t

-- Idempotence of merge (since positions are sets, s ∪ s ≡ s)
merge-idem : ∀ s → merge s s ≡ s
merge-idem s = position-inj (merge s s) s (unsort-merge s s ∙ LFSet.idem-++ (unsortTokens s))

-- =============================================================================
-- Position antisymmetry: mutual subset implies equality
-- =============================================================================

-- Helper: if s ⊑ t, then merge s t ≡ t (s adds nothing new)
merge-absorb-⊑ : ∀ s t → s ⊑ t → merge s t ≡ t
merge-absorb-⊑ ε t _ = refl
merge-absorb-⊑ (pos-cons x xs x>xs) t s⊑t =
  -- merge (x∷xs) t = insertToken x (merge xs t)
  -- Since x ∈ t (from s⊑t), and xs ⊑ t (from s⊑t), we have merge xs t ≡ t by IH
  -- Then insertToken x t ≡ t since x is already in t
  cong (insertToken x) (merge-absorb-⊑ xs t (λ y y∈xs → s⊑t y (inr y∈xs))) ∙
  insertToken-∈Pos-id x t (s⊑t x (inl refl))

-- Antisymmetry of position subset: s ⊑ t → t ⊑ s → s ≡ t
⊑-antisym : ∀ s t → s ⊑ t → t ⊑ s → s ≡ t
⊑-antisym s t s⊑t t⊑s =
  -- s ≡ merge t s (since t ⊑ s)
  -- ≡ merge s t (commutativity)
  -- ≡ t (since s ⊑ t)
  sym (merge-absorb-⊑ t s t⊑s) ∙ merge-comm t s ∙ merge-absorb-⊑ s t s⊑t
