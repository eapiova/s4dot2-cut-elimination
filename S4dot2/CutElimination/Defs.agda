{-# OPTIONS --cubical --safe #-}

-- Lightweight definitions for cut elimination: degree, height, δ, isCutFree, etc.
-- Split from Base.agda to avoid pulling in S4dot2.Solver.Subset transitively.

module S4dot2.CutElimination.Defs where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl; sym; cong; subst; J; substRefl; _∙_)
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Cubical.Data.Empty renaming (rec to emptyRec) using (⊥)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.List using (List; _∷_; []; _++_)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Sigma using (_×_; _,_; Σ)
open import Cubical.Relation.Nullary using (Dec; yes; no) renaming (¬_ to Neg)
open import Cubical.Data.Nat using (ℕ; max; _+_; suc; snotz; zero; predℕ)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; ≤-trans; left-≤-max; right-≤-max; ≤0→≡0; _<_; suc-≤-suc; pred-≤-pred)
open import Cubical.Data.Nat.Properties using (+-zero; +-suc; suc-predℕ)
open import Cubical.Data.Unit using (Unit; tt)

open import S4dot2.Syntax hiding (_⊢_; _≢_)
open import S4dot2.System hiding (discretePFormula)


case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = f x

false-neq-true : false ≡ true → ⊥
false-neq-true p = emptyRec (subst (λ b → if b then Unit else ⊥) (sym p) tt)


-- Definition 3.1: Degree of a formula
degree : Formula → ℕ
degree (Atom _) = 0
degree (A ∧ B)  = suc (max (degree A) (degree B))
degree (A ∨ B)  = suc (max (degree A) (degree B))
degree (A ⇒ B) = suc (max (degree A) (degree B))
degree (¬ A)    = suc (degree A)
degree (□ A)    = suc (degree A)
degree (♢ A)    = suc (degree A)

-- Definition 3.2: Height of a derivation
height : ∀ {Γ Δ} → (Γ ⊢ Δ) → ℕ
height (Ax)        = 0
height (Cut p1 p2) = max (height p1) (height p2) + 1
height (W⊢ p)      = height p + 1
height (⊢W p)      = height p + 1
height (C⊢ p)      = height p + 1
height (⊢C p)      = height p + 1
height (Exc⊢ p)    = height p + 1
height (⊢Exc p)    = height p + 1
height (¬⊢ p)      = height p + 1
height (⊢¬ p)      = height p + 1
height (∧₁⊢ p)     = height p + 1
height (∧₂⊢ p)     = height p + 1
height (⊢∧ p1 p2)  = max (height p1) (height p2) + 1
height (∨⊢ p1 p2)  = max (height p1) (height p2) + 1
height (⊢∨₁ p)     = height p + 1
height (⊢∨₂ p)     = height p + 1
height (⇒⊢ p1 p2) = max (height p1) (height p2) + 1
height (⊢⇒ p)     = height p + 1
height (□⊢ p)    = height p + 1
height (⊢□ _ _ _ p)    = height p + 1
height (♢⊢ _ _ _ p)    = height p + 1
height (⊢♢ p) = height p + 1

-- Lemma: subst preserves height
-- When we transport a proof along a path, its height doesn't change
height-subst : ∀ {A : Type} {P : A → Ctx} {Q : A → Ctx} {x y : A}
               (eq : x ≡ y) (Π : P x ⊢ Q x)
             → height (subst (λ a → P a ⊢ Q a) eq Π) ≡ height Π
height-subst {A} {P} {Q} {x} {y} eq Π =
  J (λ y' eq' → height (subst (λ a → P a ⊢ Q a) eq' Π) ≡ height Π)
    (cong height (substRefl {B = λ a → P a ⊢ Q a} Π))
    eq

-- Specialized version for antecedent-only substitution
height-subst-Γ : ∀ {A : Type} {P : A → Ctx} {Δ : Ctx} {x y : A}
                 (eq : x ≡ y) (Π : P x ⊢ Δ)
               → height (subst (λ a → P a ⊢ Δ) eq Π) ≡ height Π
height-subst-Γ {A} {P} {Δ} {x} {y} eq Π =
  J (λ y' eq' → height (subst (λ a → P a ⊢ Δ) eq' Π) ≡ height Π)
    (cong height (substRefl {B = λ a → P a ⊢ Δ} Π))
    eq

-- Specialized version for succedent-only substitution
height-subst-Δ : ∀ {A : Type} {Γ : Ctx} {Q : A → Ctx} {x y : A}
                 (eq : x ≡ y) (Π : Γ ⊢ Q x)
               → height (subst (λ a → Γ ⊢ Q a) eq Π) ≡ height Π
height-subst-Δ {A} {Γ} {Q} {x} {y} eq Π =
  J (λ y' eq' → height (subst (λ a → Γ ⊢ Q a) eq' Π) ≡ height Π)
    (cong height (substRefl {B = λ a → Γ ⊢ Q a} Π))
    eq

-- Definition: Degree of a proof (max degree of cut formulas)
δ : Γ ⊢ Δ → ℕ
δ (Ax)        = 0
δ (Cut {A = A} p1 p2) = max (suc (degree A)) (max (δ p1) (δ p2))
δ (W⊢ p)      = δ p
δ (⊢W p)      = δ p
δ (C⊢ p)      = δ p
δ (⊢C p)      = δ p
δ (Exc⊢ p)    = δ p
δ (⊢Exc p)    = δ p
δ (¬⊢ p)      = δ p
δ (⊢¬ p)      = δ p
δ (∧₁⊢ p)     = δ p
δ (∧₂⊢ p)     = δ p
δ (⊢∧ p1 p2)  = max (δ p1) (δ p2)
δ (∨⊢ p1 p2)  = max (δ p1) (δ p2)
δ (⊢∨₁ p)     = δ p
δ (⊢∨₂ p)     = δ p
δ (⇒⊢ p1 p2) = max (δ p1) (δ p2)
δ (⊢⇒ p)     = δ p
δ (□⊢ p)    = δ p
δ (⊢□ _ _ _ p)    = δ p
δ (♢⊢ _ _ _ p)    = δ p
δ (⊢♢ p)    = δ p

-- Definition: A proof is cut-free when its degree is 0
isCutFree : {Γ Δ : Ctx} → Γ ⊢ Δ → Type
isCutFree p = δ p ≡ 0

-- Lemmas for max
leq-max-1 : ∀ m n k → max m n ≤ k → m ≤ k
leq-max-1 m n k p = ≤-trans left-≤-max p

leq-max-2 : ∀ m n k → max m n ≤ k → n ≤ k
leq-max-2 m n k p = ≤-trans (right-≤-max {n} {m}) p

leq-max-2-1 : ∀ m n k l → max m (max n k) ≤ l → n ≤ l
leq-max-2-1 m n k l p = leq-max-1 n k l (leq-max-2 m (max n k) l p)

leq-max-2-2 : ∀ m n k l → max m (max n k) ≤ l → k ≤ l
leq-max-2-2 m n k l p = leq-max-2 n k l (leq-max-2 m (max n k) l p)

-- Convert equality to ≤
≤-reflexive : ∀ {m n} → m ≡ n → m ≤ n
≤-reflexive {m} eq = subst (m ≤_) eq ≤-refl

_≢_ : ∀ {ℓ} {A : Type ℓ} → A → A → Type ℓ
x ≢ y = Neg (x ≡ y)

trans : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p q = p ∙ q

¬m<m : ∀ {m} → Neg (m < m)
¬m<m {zero} lt = snotz (≤0→≡0 lt)
¬m<m {suc m} lt = ¬m<m (pred-≤-pred lt)

<→≢ : ∀ {m n} → m < n → m ≢ n
<→≢ {m} {n} lt eq = ¬m<m (subst (λ k → k < n) eq lt)

z≤ : ∀ {n} → zero ≤ n
z≤ {n} = n , +-zero n

s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n
s≤s {m} {n} (k , p) = k , (+-suc k m ∙ cong suc p)

inv-s≤s : ∀ {m n} → suc m ≤ suc n → m ≤ n
inv-s≤s {m} {n} (k , p) = k , (cong predℕ (sym (+-suc k m) ∙ p))

-- In cubical v0.9, max is structural so this is refl.
-- In later versions, max uses _<ᵇ_ and this is a lemma in Nat.Properties.
maxSuc : ∀ {n m : ℕ} → max (suc n) (suc m) ≡ suc (max n m)
maxSuc = refl

max-least : ∀ {m n k} → m ≤ k → n ≤ k → max m n ≤ k
max-least {zero} {n} {k} mk nk = nk
max-least {suc m} {zero} {k} mk nk = mk
max-least {suc m} {suc n} {zero} mk nk = emptyRec (snotz (≤0→≡0 mk))
max-least {suc m} {suc n} {suc k} mk nk = subst (λ z → z ≤ suc k) (sym (maxSuc {m} {n})) (s≤s (max-least (inv-s≤s mk) (inv-s≤s nk)))

-- Inspect for pattern matching with equality
data Inspect {ℓ} {A : Type ℓ} (x : A) : Type ℓ where
  it : (y : A) → x ≡ y → Inspect x

inspect : ∀ {ℓ} {A : Type ℓ} (x : A) → Inspect x
inspect x = it x refl

-- List membership splitting
mem-++-split : ∀ {ℓ} {A : Type ℓ} {x : A} {xs ys : List A} → x ∈ xs ++ ys → (x ∈ xs) ⊎ (x ∈ ys)
mem-++-split {xs = []} p = inr p
mem-++-split {xs = y ∷ xs} here = inl here
mem-++-split {xs = y ∷ xs} (there p) with mem-++-split p
... | inl p' = inl (there p')
... | inr p' = inr p'
