{-# OPTIONS --cubical --safe #-}

-- Finite decidable models for S4.2
-- These models have finitely many worlds with decidable satisfaction
-- enabling constructive soundness proofs
--
-- This version uses module parameters instead of record projections to avoid
-- Cubical Agda metavariable fragmentation issues.

module S4dot2.Equivalence.FiniteModel where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Foundations.Function using (_$_)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _·_; predℕ; snotz; znots)
open import Cubical.Data.Nat.Order using (zero-≤; suc-≤-suc; pred-≤-pred; <-weaken) renaming (_≤_ to _≤ℕ_; _<_ to _<ℕ_)
open import Cubical.Data.Fin using (Fin; fzero; fsuc; toℕ)
open import Cubical.Data.Fin.Properties using (isSetFin; discreteFin; Fin-fst-≡)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Bool using (Bool; true; false; Bool→Type; _and_; _or_; not; false≢true)
open import Cubical.Relation.Nullary

open import S4dot2.BoolReflect

-- Inspect idiom for capturing equalities in with-expressions
record Reveal_·_is_ {A B : Type} (f : A → B) (x : A) (y : B) : Type where
  constructor [_]ᵢ
  field eq : f x ≡ y
open Reveal_·_is_ public

inspect : {A B : Type} (f : A → B) (x : A) → Reveal f · x is (f x)
inspect f x = [ refl ]ᵢ

open import S4dot2.Syntax hiding (_⊢_) renaming (_∧_ to _and'_; _∨_ to _or'_)

-- =============================================================================
-- Natural Number Decidability Helper
-- =============================================================================

_≤?ℕ_ : ℕ → ℕ → Bool
zero ≤?ℕ _ = true
suc m ≤?ℕ zero = false
suc m ≤?ℕ suc n = m ≤?ℕ n

_<?ℕ_ : ℕ → ℕ → Bool
m <?ℕ n = suc m ≤?ℕ n

-- =============================================================================
-- Finite Semilattice Models - Module Parameterized Approach
-- =============================================================================

-- Core module with all model parameters fixed
-- This avoids metavariable fragmentation by making operations parameters, not projections
module FiniteModelCore
  (n : ℕ)
  (n≥1 : 1 ≤ℕ n)
  (_⊔_ : Fin n → Fin n → Fin n)
  (m : Fin n)
  (_≤?_ : Fin n → Fin n → Bool)
  (V : Fin n → ℕ → Bool)
  (⊔-comm : ∀ w₁ w₂ → (w₁ ⊔ w₂) ≡ (w₂ ⊔ w₁))
  (⊔-assoc : ∀ w₁ w₂ w₃ → ((w₁ ⊔ w₂) ⊔ w₃) ≡ (w₁ ⊔ (w₂ ⊔ w₃)))
  (⊔-idem : ∀ w → (w ⊔ w) ≡ w)
  (m-unit : ∀ w → (m ⊔ w) ≡ w)
  (≤?-refl : ∀ w → (w ≤? w) ≡ true)
  (≤?-⊔ : ∀ w₁ w₂ → (w₁ ≤? w₂) ≡ true → (w₁ ⊔ w₂) ≡ w₂)
  (⊔-≤? : ∀ w₁ w₂ → (w₁ ⊔ w₂) ≡ w₂ → (w₁ ≤? w₂) ≡ true)
  where

  World : Type
  World = Fin n

  _≤_ : World → World → Type
  w₁ ≤ w₂ = (w₁ ≤? w₂) ≡ true

  ≤-dec : ∀ w₁ w₂ → Dec (w₁ ≤ w₂)
  ≤-dec w₁ w₂ = decBool (w₁ ≤? w₂)
    where
      decBool : (b : Bool) → Dec (b ≡ true)
      decBool true = yes refl
      decBool false = no false≢true

  ⊔-upper-l : ∀ w₁ w₂ → w₁ ≤ (w₁ ⊔ w₂)
  ⊔-upper-l w₁ w₂ = ⊔-≤? w₁ (w₁ ⊔ w₂) (sym (⊔-assoc w₁ w₁ w₂) ∙ cong (_⊔ w₂) (⊔-idem w₁))

  ⊔-upper-r : ∀ w₁ w₂ → w₂ ≤ (w₁ ⊔ w₂)
  ⊔-upper-r w₁ w₂ = subst (λ x → w₂ ≤ x) (⊔-comm w₂ w₁) (⊔-upper-l w₂ w₁)

  m-min : ∀ w → m ≤ w
  m-min w = ⊔-≤? m w (m-unit w)

  -- Bound on toℕ for elements of Fin n
  -- In Cubical, Fin n = Σ[ k ∈ ℕ ] k < n, and toℕ is fst
  toℕ<n : (x : World) → toℕ x <ℕ n
  toℕ<n (k , k<n) = k<n

  -- Constructor for Fin n from ℕ with proof
  fromℕ≤ : (k : ℕ) → k <ℕ n → World
  fromℕ≤ k k<n = k , k<n

  -- Interpretation and position evaluation
  Interpretation : Type
  Interpretation = Token → World

  ρ-pos : Interpretation → Position → World
  ρ-pos ρ ε = m
  ρ-pos ρ (pos-cons x s _) = (ρ x) ⊔ (ρ-pos ρ s)

  _[_/_] : Interpretation → Token → World → Interpretation
  (ρ [ x / val ]) y with discreteToken x y
  ... | yes _ = val
  ... | no _ = ρ y

  update-same : (ρ : Interpretation) (x : Token) (v : World)
              → (ρ [ x / v ]) x ≡ v
  update-same ρ x v with discreteToken x x
  ... | yes _ = refl
  ... | no x≢x = ⊥-rec (x≢x refl)

  update-different : (ρ : Interpretation) (x y : Token) (v : World)
                   → (x ≡ y → ⊥) → (ρ [ x / v ]) y ≡ ρ y
  update-different ρ x y v neq with discreteToken x y
  ... | yes p = ⊥-rec (neq p)
  ... | no _ = refl

  -- Key lemma: now _⊔_ is a fixed parameter, not a projection
  ρ-pos-update-not-in : (ρ : Interpretation) (x : Token) (v : World) (s : Position)
                      → x ∉Pos s → ρ-pos (ρ [ x / v ]) s ≡ ρ-pos ρ s
  ρ-pos-update-not-in ρ x v ε _ = refl
  ρ-pos-update-not-in ρ x v (pos-cons y s pf) x∉ys =
    cong₂ _⊔_
          (update-different ρ x y v (λ eq → x∉ys (inl eq)))
          (ρ-pos-update-not-in ρ x v s (λ mem → x∉ys (inr mem)))

  -- Satisfaction relations
  _→Bool_ : Bool → Bool → Bool
  false →Bool _ = true
  true →Bool b = b

  eval : World → Formula → Bool
  -- Helper: iterate over worlds 0..k-1, checking □ semantics
  -- eval-all□-bounded w A k pf checks worlds with index < k (where k ≤ n)
  eval-all□-bounded : World → Formula → (k : ℕ) → k ≤ℕ n → Bool
  -- Helper: iterate over worlds 0..k-1, checking ♢ semantics
  eval-any♢-bounded : World → Formula → (k : ℕ) → k ≤ℕ n → Bool

  eval w (Atom p) = V w p
  eval w (A and' B) = eval w A and eval w B
  eval w (A or' B) = eval w A or eval w B
  eval w (A ⇒ B) = not (eval w A) or eval w B
  eval w (¬_ A) = not (eval w A)
  eval w (□ A) = eval-all□-bounded w A n ≤-refl
    where
      ≤-refl : n ≤ℕ n
      ≤-refl = zero , refl
  eval w (♢ A) = eval-any♢-bounded w A n ≤-refl
    where
      ≤-refl : n ≤ℕ n
      ≤-refl = zero , refl

  -- □A holds at w iff A holds at all w' ≥ w
  -- Check worlds 0, 1, ..., k-1 for accessibility from w
  eval-all□-bounded w A zero _ = true  -- no more worlds to check
  eval-all□-bounded w A (suc k) sk≤n =
    let k<n : k <ℕ n
        k<n = sk≤n  -- suc k ≤ n is exactly k < n
        w' : World
        w' = fromℕ≤ k k<n
        -- If w ≤ w', check that A holds at w'; otherwise skip this world
        checkThis : Bool
        checkThis = (w ≤? w') →Bool eval w' A
        k≤n : k ≤ℕ n
        k≤n = <-weaken k<n
    in checkThis and eval-all□-bounded w A k k≤n

  -- ♢A holds at w iff A holds at some w' ≥ w
  -- Check worlds 0, 1, ..., k-1 for accessibility from w
  eval-any♢-bounded w A zero _ = false  -- no more worlds to check
  eval-any♢-bounded w A (suc k) sk≤n =
    let k<n : k <ℕ n
        k<n = sk≤n
        w' : World
        w' = fromℕ≤ k k<n
        -- If w ≤ w' and A holds at w', then ♢A holds
        checkThis : Bool
        checkThis = (w ≤? w') and eval w' A
        k≤n : k ≤ℕ n
        k≤n = <-weaken k<n
    in checkThis or eval-any♢-bounded w A k k≤n

  _⊨_ : World → Formula → Type
  w ⊨ A = eval w A ≡ true

  _⊩_ : Interpretation → PFormula → Type
  ρ ⊩ (A ^ s) = (ρ-pos ρ s) ⊨ A

  _⊩Ctx_ : Interpretation → List PFormula → Type
  ρ ⊩Ctx Γ = ∀ pf → pf ∈ Γ → ρ ⊩ pf

  _⊩Succ_ : Interpretation → List PFormula → Type
  ρ ⊩Succ Δ = Σ PFormula λ pf → (pf ∈ Δ) × (ρ ⊩ pf)

  -- Decidability
  decide-⊨ : (w : World) → (A : Formula) → Dec (w ⊨ A)
  decide-⊨ w A = decBool (eval w A)
    where
      decBool : (b : Bool) → Dec (b ≡ true)
      decBool true = yes refl
      decBool false = no false≢true

  decide-⊩ : (ρ : Interpretation) → (pf : PFormula) → Dec (ρ ⊩ pf)
  decide-⊩ ρ (A ^ s) = decide-⊨ (ρ-pos ρ s) A

  findSatisfied : (ρ : Interpretation) → (Δ : List PFormula) → Dec (ρ ⊩Succ Δ)
  findSatisfied ρ [] = no (λ { (_ , () , _) })
  findSatisfied ρ (pf ∷ Δ) with decide-⊩ ρ pf
  ... | yes sat = yes (pf , here , sat)
  ... | no ¬sat with findSatisfied ρ Δ
  ...   | yes (pf' , mem , sat') = yes (pf' , there mem , sat')
  ...   | no ¬rest = no helper
    where
      helper : ρ ⊩Succ (pf ∷ Δ) → ⊥
      helper (pf' , here , sat') = ¬sat sat'
      helper (pf' , there mem , sat') = ¬rest (pf' , mem , sat')

  -- Transitivity and LUB
  ≤-trans : (w₁ w₂ w₃ : World)
          → w₁ ≤? w₂ ≡ true → w₂ ≤? w₃ ≡ true → w₁ ≤? w₃ ≡ true
  ≤-trans w₁ w₂ w₃ le12 le23 = ⊔-≤? w₁ w₃ goal
    where
      eq12 : w₁ ⊔ w₂ ≡ w₂
      eq12 = ≤?-⊔ w₁ w₂ le12
      eq23 : w₂ ⊔ w₃ ≡ w₃
      eq23 = ≤?-⊔ w₂ w₃ le23
      goal : w₁ ⊔ w₃ ≡ w₃
      goal = cong (λ z → w₁ ⊔ z) (sym eq23)
           ∙ sym (⊔-assoc w₁ w₂ w₃)
           ∙ cong (λ z → z ⊔ w₃) eq12
           ∙ eq23

  ≤-lub : (a b c : World)
        → a ≤? c ≡ true → b ≤? c ≡ true → (a ⊔ b) ≤? c ≡ true
  ≤-lub a b c leac lebc = ⊔-≤? (a ⊔ b) c goal
    where
      eqac : a ⊔ c ≡ c
      eqac = ≤?-⊔ a c leac
      eqbc : b ⊔ c ≡ c
      eqbc = ≤?-⊔ b c lebc
      goal : (a ⊔ b) ⊔ c ≡ c
      goal = ⊔-assoc a b c ∙ cong (λ z → a ⊔ z) eqbc ∙ eqac

  ∈Pos→≤-pos : (ρ : Interpretation) (x : Token) (t : Position)
             → x ∈Pos t → (ρ x) ≤? (ρ-pos ρ t) ≡ true
  ∈Pos→≤-pos ρ x (pos-cons y s y>s) (inl x≡y) =
    subst (λ z → (ρ z) ≤? (ρ-pos ρ (pos-cons y s y>s)) ≡ true) (sym x≡y)
          (⊔-upper-l (ρ y) (ρ-pos ρ s))
  ∈Pos→≤-pos ρ x (pos-cons y s pf) (inr mem) =
    ≤-trans (ρ x) (ρ-pos ρ s) (ρ-pos ρ (pos-cons y s pf))
            (∈Pos→≤-pos ρ x s mem) (⊔-upper-r (ρ y) (ρ-pos ρ s))

  subset-to-≤ : (ρ : Interpretation) (s t : Position) → s ⊑ t
              → (ρ-pos ρ s) ≤? (ρ-pos ρ t) ≡ true
  subset-to-≤ ρ ε t sub = m-min (ρ-pos ρ t)
  subset-to-≤ ρ (pos-cons x s pf) t sub =
    ≤-lub (ρ x) (ρ-pos ρ s) (ρ-pos ρ t)
          (∈Pos→≤-pos ρ x t (sub x (inl refl)))
          (subset-to-≤ ρ s t (λ y mem → sub y (inr mem)))

  -- Update corollaries
  ⊩-update-not-in : (ρ : Interpretation) (x : Token) (v : World)
                  → (pf : PFormula) → x ∉Pos (PFormula.pos pf)
                  → (ρ [ x / v ]) ⊩ pf → ρ ⊩ pf
  ⊩-update-not-in ρ x v pf notIn sat =
    let A = PFormula.form pf
        s = PFormula.pos pf
        path : ρ-pos (ρ [ x / v ]) s ≡ ρ-pos ρ s
        path = ρ-pos-update-not-in ρ x v s notIn
    in subst (λ w → eval w A ≡ true) path sat

  ⊩-update-not-in-rev : (ρ : Interpretation) (x : Token) (v : World)
                      → (pf : PFormula) → x ∉Pos (PFormula.pos pf)
                      → ρ ⊩ pf → (ρ [ x / v ]) ⊩ pf
  ⊩-update-not-in-rev ρ x v pf notIn sat =
    let A = PFormula.form pf
        s = PFormula.pos pf
        path : ρ-pos (ρ [ x / v ]) s ≡ ρ-pos ρ s
        path = ρ-pos-update-not-in ρ x v s notIn
    in subst (λ w → eval w A ≡ true) (sym path) sat

  -- Insert token lemma
  ρ-pos-insertToken : (ρ : Interpretation) (t : Token) (s : Position)
                    → t ∉Pos s
                    → ρ-pos ρ (insertToken t s) ≡ (ρ t) ⊔ (ρ-pos ρ s)
  ρ-pos-insertToken ρ t ε _ with triℕ t t
  ... | tri-≡ _ _ _ = refl
  ... | tri-< t>t _ _ = ⊥-rec (>-irreflexive t>t)
  ... | tri-> _ _ t>t = ⊥-rec (>-irreflexive t>t)
  ρ-pos-insertToken ρ t (pos-cons y ys y>ys) t∉yys with triℕ t y
  ... | tri-< y>t _ _ =
    let t∉ys : t ∉Pos ys
        t∉ys mem = t∉yys (inr mem)
        ih : ρ-pos ρ (insertToken t ys) ≡ (ρ t) ⊔ (ρ-pos ρ ys)
        ih = ρ-pos-insertToken ρ t ys t∉ys
    in cong (λ z → (ρ y) ⊔ z) ih
     ∙ sym (⊔-assoc (ρ y) (ρ t) (ρ-pos ρ ys))
     ∙ cong (λ z → z ⊔ (ρ-pos ρ ys)) (⊔-comm (ρ y) (ρ t))
     ∙ ⊔-assoc (ρ t) (ρ y) (ρ-pos ρ ys)
  ... | tri-≡ _ t≡y _ = ⊥-rec (t∉yys (inl t≡y))
  ... | tri-> _ _ t>y = refl

  -- =============================================================================
  -- Modal Semantic Lemmas
  -- =============================================================================

  -- Helper for boolean implications
  →Bool-true : (a b : Bool) → (a →Bool b) ≡ true → a ≡ true → b ≡ true
  →Bool-true false b _ a≡t = ⊥-rec (false≢true a≡t)
  →Bool-true true b impl refl = impl


  →Bool-intro : (a b : Bool) → (a ≡ true → b ≡ true) → (a →Bool b) ≡ true
  →Bool-intro false _ _ = refl
  →Bool-intro true b f = f refl

  -- Lemma: fromℕ≤ gives the index back
  -- Since fromℕ≤ k k<n = (k , k<n) and toℕ (k , _) = k, this is definitional
  toℕ-fromℕ≤ : (k : ℕ) (k<n : k <ℕ n) → toℕ (fromℕ≤ k k<n) ≡ k
  toℕ-fromℕ≤ k k<n = refl

  -- When w ≤ w' and w' = fromℕ≤ k, we get the check contribution
  box-sem-step : (w : World) (A : Formula) (k : ℕ) (k≤n : k ≤ℕ n)
               → eval-all□-bounded w A k k≤n ≡ true
               → (w' : World) → toℕ w' <ℕ k → (w ≤? w') ≡ true
               → eval w' A ≡ true
  box-sem-step w A zero _ _ w' (m , p) _ = ⊥-rec (snotz (+-suc m (toℕ w') ∙ p))  -- k = 0, but w' < 0 is impossible
    where
      +-suc : (a b : ℕ) → suc (a + b) ≡ a + suc b
      +-suc zero b = refl
      +-suc (suc a) b = cong suc (+-suc a b)
  box-sem-step w A (suc k) sk≤n all□ w' w'<sk w≤w' with toℕ w' ≟ k
    where
      _≟_ : (m n : ℕ) → Dec (m ≡ n)
      zero ≟ zero = yes refl
      zero ≟ suc n = no znots
      suc m ≟ zero = no snotz
      suc m ≟ suc n with m ≟ n
      ... | yes p = yes (cong suc p)
      ... | no ¬p = no (λ p → ¬p (cong predℕ p))
  box-sem-step w A (suc k) sk≤n all□ w' w'<sk w≤w' | yes w'≡k =
    -- w' has index k, so we check the current step
    let k<n = sk≤n
        checkThis = (w ≤? fromℕ≤ k k<n) →Bool eval (fromℕ≤ k k<n) A
        andEq = all□
        checkTrue = and-true-l andEq
        -- w' ≡ fromℕ≤ k k<n since toℕ w' ≡ k and toℕ (fromℕ≤ k k<n) ≡ k definitionally
        w'≡fk : w' ≡ fromℕ≤ k k<n
        w'≡fk = Fin-fst-≡ w'≡k
    in subst (λ v → eval v A ≡ true) (sym w'≡fk)
         (→Bool-true (w ≤? fromℕ≤ k k<n) (eval (fromℕ≤ k k<n) A) checkTrue
           (subst (λ v → (w ≤? v) ≡ true) w'≡fk w≤w'))
  box-sem-step w A (suc k) sk≤n all□ w' w'<sk w≤w' | no w'≢k =
    -- w' has index < k, recurse
    let ih = and-true-r all□
    in box-sem-step w A k (<-weaken sk≤n) ih w' (weaken-< w'<sk) w≤w'
    where
      -- weaken toℕ w' < suc k to toℕ w' < k (since w' ≢ k)
      weaken-< : toℕ w' <ℕ suc k → toℕ w' <ℕ k
      weaken-< (zero , p) = ⊥-rec (w'≢k (cong predℕ p))  -- suc (toℕ w') ≡ suc k implies toℕ w' ≡ k
      weaken-< (suc m' , p) = m' , cong predℕ p  -- suc m' + suc (toℕ w') ≡ suc k implies m' + suc (toℕ w') ≡ k

  -- Main box semantics: if □A at w, then A at all w' ≥ w
  box-semantics : (w w' : World) (A : Formula)
                → eval w (□ A) ≡ true
                → (w ≤? w') ≡ true
                → eval w' A ≡ true
  box-semantics w w' A □A w≤w' =
    let w'<n : toℕ w' <ℕ n
        w'<n = toℕ<n w'
    in box-sem-step w A n (zero , refl) □A w' (toℕ<n w') w≤w'

  -- Diamond witness extraction: if ♢A at w, find v ≥ w with A
  diamond-step : (w : World) (A : Formula) (k : ℕ) (k≤n : k ≤ℕ n)
               → eval-any♢-bounded w A k k≤n ≡ true
               → Σ World λ v → ((w ≤? v) ≡ true) × (eval v A ≡ true)
  diamond-step w A zero _ f≡t = ⊥-rec (false≢true f≡t)  -- base: false ≡ true is absurd
  diamond-step w A (suc k) sk≤n any♢ = helper check refl
    where
      w' = fromℕ≤ k sk≤n
      check = (w ≤? w') and eval w' A
      helper : (b : Bool) → b ≡ check → Σ World λ v → ((w ≤? v) ≡ true) × (eval v A ≡ true)
      helper true eq =
        let w≤w' = and-true-l (sym eq)
            Aw' = and-true-r (sym eq)
        in (w' , w≤w' , Aw')
      helper false eq =
        -- This step didn't contribute, recurse
        let rest = subst (λ b → (b or eval-any♢-bounded w A k (<-weaken sk≤n)) ≡ true)
                         (sym eq) any♢
        in diamond-step w A k (<-weaken sk≤n) rest

  diamond-semantics : (w : World) (A : Formula)
                    → eval w (♢ A) ≡ true
                    → Σ World λ v → ((w ≤? v) ≡ true) × (eval v A ≡ true)
  diamond-semantics w A ♢A = diamond-step w A n (zero , refl) ♢A

  -- Box eigen: if A holds at all v ≥ w, then □A holds at w
  box-eigen-step : (w : World) (A : Formula) (k : ℕ) (k≤n : k ≤ℕ n)
                 → ((v : World) → toℕ v <ℕ k → (w ≤? v) ≡ true → eval v A ≡ true)
                 → eval-all□-bounded w A k k≤n ≡ true
  box-eigen-step w A zero _ _ = refl
  box-eigen-step w A (suc k) sk≤n all = and-intro
    (→Bool-intro (w ≤? fromℕ≤ k sk≤n) (eval (fromℕ≤ k sk≤n) A)
      (λ w≤fk → all (fromℕ≤ k sk≤n) (subst (λ x → suc x ≤ℕ suc k) (sym (toℕ-fromℕ≤ k sk≤n)) (suc-≤-suc (zero , refl))) w≤fk))
    (box-eigen-step w A k (<-weaken sk≤n) (λ v v<k w≤v → all v (<-trans v<k (suc-≤-suc (zero , refl))) w≤v))
    where
      -- Transitivity of < for naturals
      -- a < b and b < c implies a < c
      -- Using the definition: a <ℕ b = suc a ≤ℕ b = Σ k. k + suc a ≡ b
      <-trans : {a b c : ℕ} → a <ℕ b → b <ℕ c → a <ℕ c
      <-trans {a} {b} {c} (m , p) (n , q) = (suc (m + n)) , goal
        where
          -- p : m + suc a ≡ b, so suc (m + a) ≡ b
          -- q : n + suc b ≡ c, so suc (n + b) ≡ c
          -- Goal: suc (m + n) + suc a ≡ c
          -- i.e., suc (suc (m + n) + a) ≡ c
          -- i.e., suc (suc (m + n + a)) ≡ c
          +-suc : (x y : ℕ) → x + suc y ≡ suc (x + y)
          +-suc zero y = refl
          +-suc (suc x) y = cong suc (+-suc x y)

          +-assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
          +-assoc zero y z = refl
          +-assoc (suc x) y z = cong suc (+-assoc x y z)

          +-comm : (x y : ℕ) → x + y ≡ y + x
          +-comm zero zero = refl
          +-comm zero (suc y) = cong suc (+-comm zero y)
          +-comm (suc x) zero = cong suc (+-comm x zero)
          +-comm (suc x) (suc y) = cong suc (+-suc x y ∙ cong suc (+-comm x y) ∙ sym (+-suc y x))

          -- Work through the chain:
          -- suc (m + n) + suc a = suc (suc (m + n) + a) = suc (suc (m + n + a))
          -- From p: b = m + suc a = suc (m + a)
          -- From q: c = n + suc b = n + suc (suc (m + a)) = suc (n + suc (m + a)) = suc (suc (n + m + a))
          step1 : suc (m + n) + suc a ≡ suc (suc (m + n + a))
          step1 = +-suc (suc (m + n)) a ∙ cong suc (cong suc refl)

          step2 : n + suc (suc (m + a)) ≡ c
          step2 = cong (λ x → n + suc x) (sym (+-suc m a) ∙ p) ∙ q

          step3 : suc (suc (n + (m + a))) ≡ c
          step3 = cong suc (sym (+-suc n (m + a))) ∙ sym (+-suc n (suc (m + a))) ∙ step2

          step4 : suc (suc (m + n + a)) ≡ suc (suc (n + (m + a)))
          step4 = cong (λ x → suc (suc x))
            (+-assoc m n a ∙ +-comm m (n + a) ∙ +-assoc n a m ∙ cong (n +_) (+-comm a m))

          goal : suc (m + n) + suc a ≡ c
          goal = step1 ∙ step4 ∙ step3

  box-eigen-semantics : (w : World) (A : Formula)
                      → ((v : World) → (w ≤? v) ≡ true → eval v A ≡ true)
                      → eval w (□ A) ≡ true
  box-eigen-semantics w A all = box-eigen-step w A n (zero , refl)
    (λ v v<n w≤v → all v w≤v)

  -- Diamond introduction: if A holds at v ≥ w, then ♢A holds at w
  diamond-intro-step : (w v : World) (A : Formula) (k : ℕ) (k≤n : k ≤ℕ n)
                     → toℕ v <ℕ k
                     → (w ≤? v) ≡ true → eval v A ≡ true
                     → eval-any♢-bounded w A k k≤n ≡ true
  diamond-intro-step w v A zero _ (m , p) _ _ = ⊥-rec (snotz (sym (+-suc m (toℕ v)) ∙ p))
    where
      +-suc : (a b : ℕ) → a + suc b ≡ suc (a + b)
      +-suc zero b = refl
      +-suc (suc a) b = cong suc (+-suc a b)
  diamond-intro-step w v A (suc k) sk≤n v<sk w≤v Av with toℕ v ≟ k
    where
      _≟_ : (m n : ℕ) → Dec (m ≡ n)
      zero ≟ zero = yes refl
      zero ≟ suc n = no znots
      suc m ≟ zero = no snotz
      suc m ≟ suc n with m ≟ n
      ... | yes p = yes (cong suc p)
      ... | no ¬p = no (λ p → ¬p (cong predℕ p))
  ... | yes v≡k =
    -- v has index k, contribute here
    let v≡fk : v ≡ fromℕ≤ k sk≤n
        v≡fk = Fin-fst-≡ v≡k
        checkTrue = and-intro
                      (subst (λ x → (w ≤? x) ≡ true) v≡fk w≤v)
                      (subst (λ x → eval x A ≡ true) v≡fk Av)
    in or-true-intro-l checkTrue
  ... | no v≢k =
    -- v has index < k, recurse
    or-true-intro-r (diamond-intro-step w v A k (<-weaken sk≤n) (weaken-< v<sk) w≤v Av)
    where
      -- weaken toℕ v < suc k to toℕ v < k (since v ≢ k)
      weaken-< : toℕ v <ℕ suc k → toℕ v <ℕ k
      weaken-< (zero , p) = ⊥-rec (v≢k (cong predℕ p))  -- suc (toℕ v) ≡ suc k implies toℕ v ≡ k
      weaken-< (suc m' , p) = m' , cong predℕ p  -- suc m' + suc (toℕ v) ≡ suc k implies m' + suc (toℕ v) ≡ k

  diamond-intro-semantics : (w v : World) (A : Formula)
                          → (w ≤? v) ≡ true → eval v A ≡ true
                          → eval w (♢ A) ≡ true
  diamond-intro-semantics w v A w≤v Av =
    diamond-intro-step w v A n (zero , refl) (toℕ<n v) w≤v Av

-- =============================================================================
-- FiniteModel Record - Bundles parameters for external interface
-- =============================================================================

record FiniteModel : Type₁ where
  field
    n : ℕ
    n≥1 : 1 ≤ℕ n
    _⊔_ : Fin n → Fin n → Fin n
    m : Fin n
    _≤?_ : Fin n → Fin n → Bool
    V : Fin n → ℕ → Bool
    ⊔-comm : ∀ w₁ w₂ → (w₁ ⊔ w₂) ≡ (w₂ ⊔ w₁)
    ⊔-assoc : ∀ w₁ w₂ w₃ → ((w₁ ⊔ w₂) ⊔ w₃) ≡ (w₁ ⊔ (w₂ ⊔ w₃))
    ⊔-idem : ∀ w → (w ⊔ w) ≡ w
    m-unit : ∀ w → (m ⊔ w) ≡ w
    ≤?-refl : ∀ w → (w ≤? w) ≡ true
    ≤?-⊔ : ∀ w₁ w₂ → (w₁ ≤? w₂) ≡ true → (w₁ ⊔ w₂) ≡ w₂
    ⊔-≤? : ∀ w₁ w₂ → (w₁ ⊔ w₂) ≡ w₂ → (w₁ ≤? w₂) ≡ true

  World : Type
  World = Fin n

  _≤_ : World → World → Type
  w₁ ≤ w₂ = (w₁ ≤? w₂) ≡ true

  ≤-dec : ∀ w₁ w₂ → Dec (w₁ ≤ w₂)
  ≤-dec w₁ w₂ = FiniteModelCore.≤-dec n n≥1 _⊔_ m _≤?_ V ⊔-comm ⊔-assoc ⊔-idem m-unit ≤?-refl ≤?-⊔ ⊔-≤? w₁ w₂

  ⊔-upper-l : ∀ w₁ w₂ → w₁ ≤ (w₁ ⊔ w₂)
  ⊔-upper-l = FiniteModelCore.⊔-upper-l n n≥1 _⊔_ m _≤?_ V ⊔-comm ⊔-assoc ⊔-idem m-unit ≤?-refl ≤?-⊔ ⊔-≤?

  ⊔-upper-r : ∀ w₁ w₂ → w₂ ≤ (w₁ ⊔ w₂)
  ⊔-upper-r = FiniteModelCore.⊔-upper-r n n≥1 _⊔_ m _≤?_ V ⊔-comm ⊔-assoc ⊔-idem m-unit ≤?-refl ≤?-⊔ ⊔-≤?

  m-min : ∀ w → m ≤ w
  m-min = FiniteModelCore.m-min n n≥1 _⊔_ m _≤?_ V ⊔-comm ⊔-assoc ⊔-idem m-unit ≤?-refl ≤?-⊔ ⊔-≤?

open FiniteModel public

-- =============================================================================
-- External Interface - Functions taking FiniteModel
-- =============================================================================

-- Helper to open the core module with a FiniteModel's fields
private
  module M→Core (M : FiniteModel) = FiniteModelCore
    (n M) (n≥1 M) (_⊔_ M) (m M) (_≤?_ M) (V M)
    (⊔-comm M) (⊔-assoc M) (⊔-idem M) (m-unit M)
    (≤?-refl M) (≤?-⊔ M) (⊔-≤? M)

FiniteInterpretation : FiniteModel → Type
FiniteInterpretation M = M→Core.Interpretation M

ρ-pos-fin : (M : FiniteModel) → FiniteInterpretation M → Position → World M
ρ-pos-fin M = M→Core.ρ-pos M

_[_/_]ᶠ : ∀ {M : FiniteModel} → FiniteInterpretation M → Token → World M → FiniteInterpretation M
_[_/_]ᶠ {M} = M→Core._[_/_] M

update-same : ∀ (M : FiniteModel) (ρ : FiniteInterpretation M) (x : Token) (v : World M)
            → (_[_/_]ᶠ {M} ρ x v) x ≡ v
update-same M = M→Core.update-same M

update-different : ∀ (M : FiniteModel) (ρ : FiniteInterpretation M) (x y : Token) (v : World M)
                 → (x ≡ y → ⊥) → (_[_/_]ᶠ {M} ρ x v) y ≡ ρ y
update-different M = M→Core.update-different M

ρ-pos-update-not-in : ∀ (M : FiniteModel) (ρ : FiniteInterpretation M) (x : Token) (v : World M) (s : Position)
                    → x ∉Pos s → ρ-pos-fin M (_[_/_]ᶠ {M} ρ x v) s ≡ ρ-pos-fin M ρ s
ρ-pos-update-not-in M = M→Core.ρ-pos-update-not-in M

eval : (M : FiniteModel) → World M → Formula → Bool
eval M = M→Core.eval M

_⦦_⊨ᶠ_ : (M : FiniteModel) → World M → Formula → Type
M ⦦ w ⊨ᶠ A = M→Core._⊨_ M w A

_,_⊩ᶠ_ : (M : FiniteModel) → FiniteInterpretation M → PFormula → Type
M , ρ ⊩ᶠ pf = M→Core._⊩_ M ρ pf

_,_⊩Ctxᶠ_ : (M : FiniteModel) → FiniteInterpretation M → List PFormula → Type
M , ρ ⊩Ctxᶠ Γ = M→Core._⊩Ctx_ M ρ Γ

_,_⊩Succᶠ_ : (M : FiniteModel) → FiniteInterpretation M → List PFormula → Type
M , ρ ⊩Succᶠ Δ = M→Core._⊩Succ_ M ρ Δ

decide-⊨ᶠ : (M : FiniteModel) → (w : World M) → (A : Formula) → Dec (M ⦦ w ⊨ᶠ A)
decide-⊨ᶠ M = M→Core.decide-⊨ M

decide-⊩ᶠ : (M : FiniteModel) → (ρ : FiniteInterpretation M) → (pf : PFormula) → Dec (M , ρ ⊩ᶠ pf)
decide-⊩ᶠ M = M→Core.decide-⊩ M

findSatisfied : (M : FiniteModel) → (ρ : FiniteInterpretation M) → (Δ : List PFormula) → Dec (M , ρ ⊩Succᶠ Δ)
findSatisfied M = M→Core.findSatisfied M

_⊨finseq_ : List PFormula → List PFormula → Type₁
Γ ⊨finseq Δ = (M : FiniteModel) → (ρ : FiniteInterpretation M)
            → M , ρ ⊩Ctxᶠ Γ → M , ρ ⊩Succᶠ Δ

≤-trans : (M : FiniteModel) → (w₁ w₂ w₃ : World M)
        → _≤?_ M w₁ w₂ ≡ true → _≤?_ M w₂ w₃ ≡ true → _≤?_ M w₁ w₃ ≡ true
≤-trans M = M→Core.≤-trans M

≤-lub : (M : FiniteModel) → (a b c : World M)
      → _≤?_ M a c ≡ true → _≤?_ M b c ≡ true → _≤?_ M (_⊔_ M a b) c ≡ true
≤-lub M = M→Core.≤-lub M

∈Pos→≤-pos : (M : FiniteModel) (ρ : FiniteInterpretation M) (x : Token) (t : Position)
           → x ∈Pos t → _≤?_ M (ρ x) (ρ-pos-fin M ρ t) ≡ true
∈Pos→≤-pos M = M→Core.∈Pos→≤-pos M

subset-to-≤ : (M : FiniteModel) → (ρ : FiniteInterpretation M)
            → (s t : Position) → s ⊑ t
            → _≤?_ M (ρ-pos-fin M ρ s) (ρ-pos-fin M ρ t) ≡ true
subset-to-≤ M = M→Core.subset-to-≤ M

⊩ᶠ-update-not-in : ∀ (M : FiniteModel) (ρ : FiniteInterpretation M) (x : Token) (v : World M)
                 → (pf : PFormula) → x ∉Pos (PFormula.pos pf)
                 → M , (_[_/_]ᶠ {M} ρ x v) ⊩ᶠ pf → M , ρ ⊩ᶠ pf
⊩ᶠ-update-not-in M = M→Core.⊩-update-not-in M

⊩ᶠ-update-not-in-rev : ∀ (M : FiniteModel) (ρ : FiniteInterpretation M) (x : Token) (v : World M)
                     → (pf : PFormula) → x ∉Pos (PFormula.pos pf)
                     → M , ρ ⊩ᶠ pf → M , (_[_/_]ᶠ {M} ρ x v) ⊩ᶠ pf
⊩ᶠ-update-not-in-rev M = M→Core.⊩-update-not-in-rev M

ρ-pos-fin-insertToken : ∀ (M : FiniteModel) (ρ : FiniteInterpretation M) (t : Token) (s : Position)
                      → t ∉Pos s
                      → ρ-pos-fin M ρ (insertToken t s) ≡ _⊔_ M (ρ t) (ρ-pos-fin M ρ s)
ρ-pos-fin-insertToken M = M→Core.ρ-pos-insertToken M

-- =============================================================================
-- Modal Semantic Lemmas - External Interface
-- =============================================================================

-- Box semantics: □A at w and w ≤ w' implies A at w'
box-semantics : (M : FiniteModel) → (w w' : World M) → (A : Formula)
              → eval M w (□ A) ≡ true
              → _≤?_ M w w' ≡ true
              → eval M w' A ≡ true
box-semantics M = M→Core.box-semantics M

-- Diamond semantics: ♢A at w implies witness v ≥ w with A
diamond-semantics : (M : FiniteModel) → (w : World M) → (A : Formula)
                  → eval M w (♢ A) ≡ true
                  → Σ (World M) λ v → (_≤?_ M w v ≡ true) × (eval M v A ≡ true)
diamond-semantics M = M→Core.diamond-semantics M

-- Box eigen: A at all v ≥ w implies □A at w
box-eigen-semantics : (M : FiniteModel) → (w : World M) → (A : Formula)
                    → ((v : World M) → _≤?_ M w v ≡ true → eval M v A ≡ true)
                    → eval M w (□ A) ≡ true
box-eigen-semantics M = M→Core.box-eigen-semantics M

-- Diamond intro: A at v and w ≤ v implies ♢A at w
diamond-intro-semantics : (M : FiniteModel) → (w v : World M) → (A : Formula)
                        → _≤?_ M w v ≡ true → eval M v A ≡ true
                        → eval M w (♢ A) ≡ true
diamond-intro-semantics M = M→Core.diamond-intro-semantics M

-- =============================================================================
-- Modal Semantics Record
-- =============================================================================

record ModalSemantics (M : FiniteModel) : Type where
  field
    box-sem : (A : Formula) → (w w' : World M)
            → eval M w (□ A) ≡ true
            → _≤?_ M w w' ≡ true
            → eval M w' A ≡ true

    diamond-sem : (A : Formula) → (w w' : World M)
                → eval M w' A ≡ true
                → _≤?_ M w w' ≡ true
                → eval M w (♢ A) ≡ true

    box-eigen-sem : (A : Formula) → (w : World M)
                  → ((v : World M) → _≤?_ M w v ≡ true → eval M v A ≡ true)
                  → eval M w (□ A) ≡ true

    diamond-eigen-sem : (A : Formula) → (w : World M)
                      → eval M w (♢ A) ≡ true
                      → Σ (World M) λ v → (_≤?_ M w v ≡ true) × (eval M v A ≡ true)

open ModalSemantics public

box-accessible : (M : FiniteModel) → ModalSemantics M → {A : Formula} → {w w' : World M}
               → eval M w (□ A) ≡ true
               → _≤?_ M w w' ≡ true
               → eval M w' A ≡ true
box-accessible M ms {A} {w} {w'} = box-sem ms A w w'

diamond-accessible : (M : FiniteModel) → ModalSemantics M → {A : Formula} → {w w' : World M}
                   → eval M w' A ≡ true
                   → _≤?_ M w w' ≡ true
                   → eval M w (♢ A) ≡ true
diamond-accessible M ms {A} {w} {w'} = diamond-sem ms A w w'

-- =============================================================================
-- Default Modal Semantics - Uses the semantic lemmas automatically
-- =============================================================================

-- Any FiniteModel automatically has correct modal semantics
-- since eval now properly implements □ and ♢ via world iteration
defaultModalSemantics : (M : FiniteModel) → ModalSemantics M
defaultModalSemantics M = record
  { box-sem = λ A w w' □A w≤w' → box-semantics M w w' A □A w≤w'
  ; diamond-sem = λ A w w' Aw' w≤w' → diamond-intro-semantics M w w' A w≤w' Aw'
  ; box-eigen-sem = λ A w allAcc → box-eigen-semantics M w A allAcc
  ; diamond-eigen-sem = λ A w ♢A → diamond-semantics M w A ♢A
  }
