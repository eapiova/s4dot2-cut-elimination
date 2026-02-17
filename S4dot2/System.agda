{-# OPTIONS --cubical --safe #-}

module S4dot2.System where

open import Cubical.Core.Primitives using ()
import Cubical.Foundations.Prelude as P
open P using (Type; _≡_; refl; sym; cong; cong₂; subst; transport; _∙_; funExt; isProp→PathP)
open import Cubical.Data.List using (List; _∷_; []; _++_; map)
open import Cubical.Data.List.Properties
open import Cubical.Data.Nat using (ℕ; discreteℕ)
open import Cubical.Data.Bool using (Bool; true; false) renaming (not to ¬B)
open import Cubical.Data.Sigma using (Σ; _,_; fst; snd; _×_)
open import Cubical.Data.Empty using (⊥; elim; rec)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Relation.Nullary using (Dec; yes; no; Discrete) renaming (¬_ to Neg)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Maybe using (Maybe; just; nothing)

-- For proving Position equalities via LFSet
open import Cubical.HITs.ListedFiniteSet as LFSet using (LFSet)

open import S4dot2.Syntax hiding (_⊢_)

-- Context definition
Ctx = List PFormula

_,,_ = _++_
infixr 5 _,,_


variable
  Γ Δ Γ₁ Γ₂ Δ₁ Δ₂ : Ctx
  s t : Position
  x : Token


-- Proof System for S4.2
-- Indexed by Left Context (Γ) and Right Context (Δ)
-- Reference: Figure 1 (Rules for System ES4)
infix 3 _⊢_

data _⊢_ : Ctx → Ctx → Type where
  -- Axiom: A^s ⊢ A^s
  -- Reference: Figure 1, Axiom
  Ax : [ A ^ s ] ⊢ [ A ^ s ]

  -- Cut Rule
  -- Reference: Figure 1, Cut
  Cut : (Γ₁ ⊢ [ A ^ s ] ,, Δ₁) → (Γ₂ ,, [ A ^ s ] ⊢ Δ₂)
        → (Γ₁ ,, Γ₂ ⊢ Δ₁ ,, Δ₂)

  -- Structural Rules
  -- Reference: Figure 1, Structural rules
  W⊢ : (Γ ⊢ Δ)
     → (Γ ,, [ A ^ s ] ⊢ Δ)

  ⊢W : (Γ ⊢ Δ)
     → (Γ ⊢ [ A ^ s ] ,, Δ)

  C⊢ : ((Γ ,, [ A ^ s ]) ,, [ A ^ s ]  ⊢ Δ) → (Γ ,, [ A ^ s ] ⊢ Δ)

  ⊢C : (Γ ⊢ ([ A ^ s ] ,, [ A ^ s ]) ,, Δ)
     → (Γ ⊢ [ A ^ s ] ,, Δ)

  Exc⊢ : (((Γ₁ ,, [ A ^ s ]) ,, [ B ^ t ]) ,, Γ₂ ⊢ Δ)
       → (((Γ₁ ,, [ B ^ t ]) ,, [ A ^ s ]) ,, Γ₂ ⊢ Δ)

  ⊢Exc : (Γ ⊢ ((Δ₁ ,, [ A ^ s ]) ,, [ B ^ t ]) ,, Δ₂)
       → (Γ ⊢ ((Δ₁ ,, [ B ^ t ]) ,, [ A ^ s ]) ,, Δ₂)

  ¬⊢ : (Γ ⊢ [ A ^ s ] ,, Δ)
       → (Γ ,, [ (¬ A) ^ s ] ⊢ Δ)

  ⊢¬ : (Γ ,, [ A ^ s ] ⊢ Δ)
       → (Γ ⊢ [ (¬ A) ^ s ] ,, Δ)

  ∧₁⊢ : (Γ ,, [ A ^ s ] ⊢ Δ)
        → (Γ ,, [ (A ∧ B) ^ s ] ⊢ Δ)

  ∧₂⊢ : (Γ ,, [ B ^ s ] ⊢ Δ)
        → (Γ ,, [ (A ∧ B) ^ s ] ⊢ Δ)

  ⊢∧ : (Γ₁ ⊢ [ A ^ s ] ,, Δ₁)
       → (Γ₂ ⊢ [ B ^ s ] ,, Δ₂)
       → (Γ₁ ,, Γ₂ ⊢ [ (A ∧ B) ^ s ] ,, Δ₁ ,, Δ₂)

  ∨⊢ : (Γ₁ ,, [ A ^ s ] ⊢ Δ₁)
      → (Γ₂ ,, [ B ^ s ] ⊢ Δ₂)
      → (Γ₁ ,, Γ₂ ,, [ (A ∨ B) ^ s ] ⊢ Δ₁ ,, Δ₂)

  ⊢∨₁ : (Γ ⊢ [ A ^ s ] ,, Δ)
       → (Γ ⊢ [ (A ∨ B) ^ s ] ,, Δ)

  ⊢∨₂ : (Γ ⊢ [ B ^ s ] ,, Δ)
       → (Γ ⊢ [ (A ∨ B) ^ s ] ,, Δ)

  ⇒⊢ : (Γ₁ ,, [ B ^ s ] ⊢ Δ₁)
       → (Γ₂ ⊢ [ A ^ s ] ,, Δ₂)
       → (Γ₁ ,, Γ₂ ,, [ (A ⇒ B) ^ s ] ⊢ Δ₁ ,, Δ₂)

  ⊢⇒ : (Γ ,, [ A ^ s ] ⊢ [ B ^ s ] ,, Δ)
       → (Γ ⊢ [ (A ⇒ B) ^ s ] ,, Δ)
  
  □⊢ : (Γ ,, [ A ^ (s ∘ t) ] ⊢ Δ)
        → (Γ ,, [ (□ A) ^ s ] ⊢ Δ)

  ⊢□ : x ∉Pos s
       → TokenFresh x Γ
       → TokenFresh x Δ
       → (Γ ⊢ [ A ^ insertToken x s ] ,, Δ)
       → (Γ ⊢ [ (□ A) ^ s ] ,, Δ)

  ♢⊢ : x ∉Pos s
       → TokenFresh x Γ
       → TokenFresh x Δ
       → (Γ ,, [ A ^ insertToken x s ] ⊢ Δ)
       → (Γ ,, [ (♢ A) ^ s ] ⊢ Δ)

  ⊢♢ : (Γ ⊢ [ A ^ (s ∘ t) ] ,, Δ)
       → (Γ ⊢ [ (♢ A) ^ s ] ,, Δ)

-- =============================================================================
-- Eigenposition Condition
-- =============================================================================
-- The eigenposition condition states that (s ∘ singleton-pos x) is NOT a subset
-- of any position in Γ or Δ. This is the semantic condition captured by the
-- _⊑_ subset relation on SDL positions (set containment).
-- NOTE: With SDL positions, we use subset (⊑) instead of prefix relationship.

IsEigenposition : Position → Token → Ctx → Ctx → Type
IsEigenposition s x Γ Δ = Neg (Σ PFormula (λ pf → (pf ∈ (Γ ,, Δ)) × ((s ∘ singleton-pos x) ⊑ PFormula.pos pf)))

-- =============================================================================
-- Generalized Weakening Implementation
-- =============================================================================

-- Decidable equality for Formula
discreteFormula : Discrete Formula
discreteFormula (Atom x) (Atom y) with discreteℕ x y
... | yes p = yes (cong Atom p)
... | no p = no (λ eq → p (cong (λ { (Atom z) → z ; _ → x }) eq))
discreteFormula (A ∧ B) (A' ∧ B') with discreteFormula A A' | discreteFormula B B'
... | yes p | yes q = yes (cong₂ _∧_ p q)
... | no p | _ = no (λ eq → p (cong (λ { (X ∧ Y) → X ; _ → A }) eq))
... | _ | no q = no (λ eq → q (cong (λ { (X ∧ Y) → Y ; _ → B }) eq))
discreteFormula (A ∨ B) (A' ∨ B') with discreteFormula A A' | discreteFormula B B'
... | yes p | yes q = yes (cong₂ _∨_ p q)
... | no p | _ = no (λ eq → p (cong (λ { (X ∨ Y) → X ; _ → A }) eq))
... | _ | no q = no (λ eq → q (cong (λ { (X ∨ Y) → Y ; _ → B }) eq))
discreteFormula (A ⇒ B) (A' ⇒ B') with discreteFormula A A' | discreteFormula B B'
... | yes p | yes q = yes (cong₂ _⇒_ p q)
... | no p | _ = no (λ eq → p (cong (λ { (X ⇒ Y) → X ; _ → A }) eq))
... | _ | no q = no (λ eq → q (cong (λ { (X ⇒ Y) → Y ; _ → B }) eq))
discreteFormula (¬ A) (¬ A') with discreteFormula A A'
... | yes p = yes (cong ¬_ p)
... | no p = no (λ eq → p (cong (λ { (¬ X) → X ; _ → A }) eq))
discreteFormula (□ A) (□ A') with discreteFormula A A'
... | yes p = yes (cong □ p)
... | no p = no (λ eq → p (cong (λ { (□ X) → X ; _ → A }) eq))
discreteFormula (♢ A) (♢ A') with discreteFormula A A'
... | yes p = yes (cong ♢ p)
... | no p = no (λ eq → p (cong (λ { (♢ X) → X ; _ → A }) eq))
discreteFormula (Atom _) (_ ∧ _) = no (λ eq → subst (λ { (Atom _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (Atom _) (_ ∨ _) = no (λ eq → subst (λ { (Atom _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (Atom _) (_ ⇒ _) = no (λ eq → subst (λ { (Atom _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (Atom _) (¬ _) = no (λ eq → subst (λ { (Atom _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (Atom _) (□ _) = no (λ eq → subst (λ { (Atom _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (Atom _) (♢ _) = no (λ eq → subst (λ { (Atom _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ∧ _) (Atom _) = no (λ eq → subst (λ { (_ ∧ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ∧ _) (_ ∨ _) = no (λ eq → subst (λ { (_ ∧ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ∧ _) (_ ⇒ _) = no (λ eq → subst (λ { (_ ∧ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ∧ _) (¬ _) = no (λ eq → subst (λ { (_ ∧ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ∧ _) (□ _) = no (λ eq → subst (λ { (_ ∧ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ∧ _) (♢ _) = no (λ eq → subst (λ { (_ ∧ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ∨ _) (Atom _) = no (λ eq → subst (λ { (_ ∨ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ∨ _) (_ ∧ _) = no (λ eq → subst (λ { (_ ∨ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ∨ _) (_ ⇒ _) = no (λ eq → subst (λ { (_ ∨ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ∨ _) (¬ _) = no (λ eq → subst (λ { (_ ∨ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ∨ _) (□ _) = no (λ eq → subst (λ { (_ ∨ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ∨ _) (♢ _) = no (λ eq → subst (λ { (_ ∨ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ⇒ _) (Atom _) = no (λ eq → subst (λ { (_ ⇒ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ⇒ _) (_ ∧ _) = no (λ eq → subst (λ { (_ ⇒ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ⇒ _) (_ ∨ _) = no (λ eq → subst (λ { (_ ⇒ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ⇒ _) (¬ _) = no (λ eq → subst (λ { (_ ⇒ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ⇒ _) (□ _) = no (λ eq → subst (λ { (_ ⇒ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (_ ⇒ _) (♢ _) = no (λ eq → subst (λ { (_ ⇒ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (¬ _) (Atom _) = no (λ eq → subst (λ { (¬ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (¬ _) (_ ∧ _) = no (λ eq → subst (λ { (¬ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (¬ _) (_ ∨ _) = no (λ eq → subst (λ { (¬ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (¬ _) (_ ⇒ _) = no (λ eq → subst (λ { (¬ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (¬ _) (□ _) = no (λ eq → subst (λ { (¬ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (¬ _) (♢ _) = no (λ eq → subst (λ { (¬ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (□ _) (Atom _) = no (λ eq → subst (λ { (□ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (□ _) (_ ∧ _) = no (λ eq → subst (λ { (□ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (□ _) (_ ∨ _) = no (λ eq → subst (λ { (□ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (□ _) (_ ⇒ _) = no (λ eq → subst (λ { (□ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (□ _) (¬ _) = no (λ eq → subst (λ { (□ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (□ _) (♢ _) = no (λ eq → subst (λ { (□ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (♢ _) (Atom _) = no (λ eq → subst (λ { (♢ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (♢ _) (_ ∧ _) = no (λ eq → subst (λ { (♢ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (♢ _) (_ ∨ _) = no (λ eq → subst (λ { (♢ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (♢ _) (_ ⇒ _) = no (λ eq → subst (λ { (♢ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (♢ _) (¬ _) = no (λ eq → subst (λ { (♢ _) → Unit ; _ → ⊥ }) eq tt)
discreteFormula (♢ _) (□ _) = no (λ eq → subst (λ { (♢ _) → Unit ; _ → ⊥ }) eq tt)

-- toList : Position → List Token is now imported from SortedPosition

-- Helper: Convert list to LFSet
fromList : List Token → LFSet ℕ
fromList [] = LFSet.[]
fromList (x ∷ xs) = x LFSet.∷ fromList xs

-- Lemma: unsortTokens factors through toList
unsort-factor : ∀ (u : Position) → unsortTokens u ≡ fromList (toList u)
unsort-factor ε = refl
unsort-factor (pos-cons x xs _) = cong (x LFSet.∷_) (unsort-factor xs)

-- Injectivity of toList via position-inj
toList-inj : ∀ {u v : Position} → toList u ≡ toList v → u ≡ v
toList-inj {u} {v} p = position-inj u v (
  unsort-factor u ∙
  cong fromList p ∙
  sym (unsort-factor v))

discretePosition : Discrete Position
discretePosition s t with discreteList discreteToken (toList s) (toList t)
... | yes p = yes (toList-inj p)
... | no p = no (λ eq → p (cong toList eq))

discretePFormula : Discrete PFormula
discretePFormula (A ^ s) (B ^ t) with discreteFormula A B | discretePosition s t
... | yes p | yes q = yes (cong₂ _^_ p q)
... | no p | _ = no (λ eq → p (cong (λ { (f ^ _) → f }) eq))
... | _ | no q = no (λ eq → q (cong (λ { (_ ^ p) → p }) eq))

-- Decidable membership
_∈?_ : (x : PFormula) (l : Ctx) → Dec (x ∈ l)
x ∈? [] = no (λ ())
x ∈? (y ∷ l) with discretePFormula x y
... | yes p = yes (subst (λ z → x ∈ z ∷ l) p here)
... | no p with x ∈? l
... | yes inTail = yes (there inTail)
... | no notInTail = no (λ { here → p refl ; (there inTail) → notInTail inTail })

-- Bring to front (Left)
bring-to-front-ctx : ∀ {Δ} (Γ₁ Γ₂ : Ctx) (x : PFormula) (p : x ∈ Γ₂)
                   → (Γ₁ ++ Γ₂ ⊢ Δ)
                   → (Γ₁ ++ x ∷ remove-first x Γ₂ p ⊢ Δ)
bring-to-front-ctx Γ₁ ._ x (here {xs = Γ₂}) d = d
bring-to-front-ctx {Δ} Γ₁ ._ x@(B ^ t) (there {y = y@(A ^ s)} {xs = Γ₂} p) d =
  let
    d' = subst (λ G → G ⊢ Δ) (sym (++-assoc Γ₁ [ y ] Γ₂)) d
    step1 = bring-to-front-ctx (Γ₁ ++ [ y ]) Γ₂ x p d'
    step1_ready = subst (λ G → G ⊢ Δ) (sym (++-assoc (Γ₁ ++ [ y ]) [ x ] (remove-first x Γ₂ p))) step1
    step2_raw = Exc⊢ {Γ₁ = Γ₁} {Γ₂ = remove-first x Γ₂ p} step1_ready
    eq = ++-assoc (Γ₁ ++ [ x ]) [ y ] (remove-first x Γ₂ p) ∙ ++-assoc Γ₁ [ x ] (y ∷ remove-first x Γ₂ p)
    step2 = subst (λ G → G ⊢ Δ) eq step2_raw
  in step2

bring-to-front : ∀ {Δ} (Γ : Ctx) (x : PFormula) (p : x ∈ Γ)
               → (Γ ⊢ Δ)
               → (x ∷ remove-first x Γ p ⊢ Δ)
bring-to-front Γ x p d = bring-to-front-ctx [] Γ x p d

-- Bring to front (Right)
bring-to-front-ctx-r : ∀ {Γ} (Δ₁ Δ₂ : Ctx) (x : PFormula) (p : x ∈ Δ₂)
                     → (Γ ⊢ Δ₁ ++ Δ₂)
                     → (Γ ⊢ Δ₁ ++ x ∷ remove-first x Δ₂ p)
bring-to-front-ctx-r Δ₁ ._ x (here {xs = Δ₂}) d = d
bring-to-front-ctx-r {Γ} Δ₁ ._ x@(B ^ t) (there {y = y@(A ^ s)} {xs = Δ₂} p) d =
  let
    d' = subst (λ D → Γ ⊢ D) (sym (++-assoc Δ₁ [ y ] Δ₂)) d
    step1 = bring-to-front-ctx-r (Δ₁ ++ [ y ]) Δ₂ x p d'
    step1_ready = subst (λ D → Γ ⊢ D) (sym (++-assoc (Δ₁ ++ [ y ]) [ x ] (remove-first x Δ₂ p))) step1
    step2_raw = ⊢Exc {Δ₁ = Δ₁} {Δ₂ = remove-first x Δ₂ p} step1_ready
    eq = ++-assoc (Δ₁ ++ [ x ]) [ y ] (remove-first x Δ₂ p) ∙ ++-assoc Δ₁ [ x ] (y ∷ remove-first x Δ₂ p)
    step2 = subst (λ D → Γ ⊢ D) eq step2_raw
  in step2

bring-to-front-r : ∀ {Γ} (Δ : Ctx) (x : PFormula) (p : x ∈ Δ)
                 → (Γ ⊢ Δ)
                 → (Γ ⊢ x ∷ remove-first x Δ p)
bring-to-front-r Δ x p d = bring-to-front-ctx-r [] Δ x p d

-- Weakening helpers
bring-last-to-front : ∀ {Δ} (Γ : Ctx) (x : PFormula)
                    → (Γ ++ [ x ] ⊢ Δ)
                    → (x ∷ Γ ⊢ Δ)
bring-last-to-front {Δ} Γ x d =
  let
    p : x ∈ (Γ ++ [ x ])
    p = mem-++-r Γ here
    
    step1 = bring-to-front (Γ ++ [ x ]) x p d
    
    lem : remove-first x (Γ ++ [ x ]) p ≡ Γ
    lem = remove-first-++-r x Γ [ x ] here ∙ ++-unit-r Γ
  in subst (λ G → x ∷ G ⊢ Δ) lem step1

weakening-left-1 : ∀ {Γ Δ} (A : PFormula) → (Γ ⊢ Δ) → (A ∷ Γ ⊢ Δ)
weakening-left-1 A d = bring-last-to-front _ A (W⊢ d)

weakening-insert-left : ∀ {Γ Δ} (Σ : Ctx) → (Γ ⊢ Δ) → (Σ ++ Γ ⊢ Δ)
weakening-insert-left [] d = d
weakening-insert-left (x ∷ Σ) d = weakening-left-1 x (weakening-insert-left Σ d)

bring-last-to-front-r : ∀ {Γ} (Δ : Ctx) (x : PFormula)
                      → (Γ ⊢ Δ ++ [ x ])
                      → (Γ ⊢ x ∷ Δ)
bring-last-to-front-r {Γ} Δ x d =
  let
    p : x ∈ (Δ ++ [ x ])
    p = mem-++-r Δ here
    
    step1 = bring-to-front-r (Δ ++ [ x ]) x p d
    
    lem : remove-first x (Δ ++ [ x ]) p ≡ Δ
    lem = remove-first-++-r x Δ [ x ] here ∙ ++-unit-r Δ
  in subst (λ D → Γ ⊢ x ∷ D) lem step1

weakening-right-1 : ∀ {Γ Δ} (A : PFormula) → (Γ ⊢ Δ) → (Γ ⊢ A ∷ Δ)
weakening-right-1 (A ^ s) d = ⊢W {A = A} {s = s} d

weakening-insert-right : ∀ {Γ Δ} (Σ : Ctx) → (Γ ⊢ Δ) → (Γ ⊢ Σ ++ Δ)
weakening-insert-right [] d = d
weakening-insert-right (x ∷ Σ) d = weakening-right-1 x (weakening-insert-right Σ d)

-- Subset Weakening Left
-- Helper: put back element (Left)
put_back_ctx : ∀ {Δ} (Γ₁ Γ₂ : Ctx) (x : PFormula) (p : x ∈ Γ₂)
             → (Γ₁ ++ x ∷ remove-first x Γ₂ p ⊢ Δ)
             → (Γ₁ ++ Γ₂ ⊢ Δ)
put_back_ctx Γ₁ ._ x (here {xs = Γ₂}) d = d
put_back_ctx {Δ} Γ₁ ._ x@(A ^ s) (there {y = y@(B ^ t)} {xs = Γ₂} p) d =
  let
    eq = sym (++-assoc Γ₁ [ x ] (y ∷ remove-first x Γ₂ p)) ∙ sym (++-assoc (Γ₁ ++ [ x ]) [ y ] (remove-first x Γ₂ p))
    d_ready = subst (λ G → G ⊢ Δ) eq d
    d' = Exc⊢ {Γ₁ = Γ₁} {Γ₂ = remove-first x Γ₂ p} d_ready
    d'_ready = subst (λ G → G ⊢ Δ) (++-assoc (Γ₁ ++ [ y ]) [ x ] (remove-first x Γ₂ p)) d'
    res = put_back_ctx (Γ₁ ++ [ y ]) Γ₂ x p d'_ready
  in subst (λ G → G ⊢ Δ) (++-assoc Γ₁ [ y ] Γ₂) res

put_back : ∀ {Δ} (Γ : Ctx) (x : PFormula) (p : x ∈ Γ)
         → (x ∷ remove-first x Γ p ⊢ Δ)
         → (Γ ⊢ Δ)
put_back Γ x p d = put_back_ctx [] Γ x p d

-- Helper: put back element (Right)
put_back_ctx-r : ∀ {Γ} (Δ₁ Δ₂ : Ctx) (x : PFormula) (p : x ∈ Δ₂)
               → (Γ ⊢ Δ₁ ++ x ∷ remove-first x Δ₂ p)
               → (Γ ⊢ Δ₁ ++ Δ₂)
put_back_ctx-r Δ₁ ._ x (here {xs = Δ₂}) d = d
put_back_ctx-r {Γ} Δ₁ ._ x@(A ^ s) (there {y = y@(B ^ t)} {xs = Δ₂} p) d =
  let
    eq = sym (++-assoc Δ₁ [ x ] (y ∷ remove-first x Δ₂ p)) ∙ sym (++-assoc (Δ₁ ++ [ x ]) [ y ] (remove-first x Δ₂ p))
    d_ready = subst (λ D → Γ ⊢ D) eq d
    d' = ⊢Exc {Δ₁ = Δ₁} {Δ₂ = remove-first x Δ₂ p} d_ready
    d'_ready = subst (λ D → Γ ⊢ D) (++-assoc (Δ₁ ++ [ y ]) [ x ] (remove-first x Δ₂ p)) d'
    res = put_back_ctx-r (Δ₁ ++ [ y ]) Δ₂ x p d'_ready
  in subst (λ D → Γ ⊢ D) (++-assoc Δ₁ [ y ] Δ₂) res

put_back_r : ∀ {Γ} (Δ : Ctx) (x : PFormula) (p : x ∈ Δ)
           → (Γ ⊢ x ∷ remove-first x Δ p)
           → (Γ ⊢ Δ)
put_back_r Δ x p d = put_back_ctx-r [] Δ x p d

-- Subset Weakening Left
contract-left : ∀ {Γ Δ} (x : PFormula) → (x ∷ x ∷ Γ ⊢ Δ) → (x ∷ Γ ⊢ Δ)
contract-left {Γ} {Δ} x d =
  let
    p : x ∈ (Γ ++ [ x ])
    p = mem-++-r Γ here
    
    lem : remove-first x (Γ ++ [ x ]) p ≡ Γ
    lem = remove-first-++-r x Γ [ x ] here ∙ ++-unit-r Γ
    
    d_casted : [ x ] ++ x ∷ remove-first x (Γ ++ [ x ]) p ⊢ Δ
    d_casted = subst (λ G → x ∷ x ∷ G ⊢ Δ) (sym lem) d
    
    d1 : [ x ] ++ (Γ ++ [ x ]) ⊢ Δ
    d1 = put_back_ctx [ x ] (Γ ++ [ x ]) x p d_casted
    
    p2 : x ∈ ((Γ ++ [ x ]) ++ [ x ])
    p2 = mem-++-r (Γ ++ [ x ]) here
    
    lem2 : remove-first x ((Γ ++ [ x ]) ++ [ x ]) p2 ≡ Γ ++ [ x ]
    lem2 = remove-first-++-r x (Γ ++ [ x ]) [ x ] here ∙ ++-unit-r (Γ ++ [ x ])
    
    d1_casted : x ∷ remove-first x ((Γ ++ [ x ]) ++ [ x ]) p2 ⊢ Δ
    d1_casted = subst (λ G → x ∷ G ⊢ Δ) (sym lem2) d1
    
    d2 : (Γ ++ [ x ]) ++ [ x ] ⊢ Δ
    d2 = put_back ((Γ ++ [ x ]) ++ [ x ]) x p2 d1_casted
    
    d3 : (Γ ++ [ x ]) ⊢ Δ
    d3 = C⊢ {Γ = Γ} {Δ = Δ} d2
    
    d4 : x ∷ Γ ⊢ Δ
    d4 = bring-last-to-front Γ x d3
  in d4

subset-weakening-left-gen : ∀ {Γ Γ' Σ Δ} → Γ ⊆ Γ' → (Γ ++ Σ ⊢ Δ) → (Γ' ++ Σ ⊢ Δ)
subset-weakening-left-gen {[]} {Γ'} {Σ} sub d = weakening-insert-left Γ' d
subset-weakening-left-gen {x ∷ Γ} {Γ'} {Σ} {Δ} sub d with x ∈? Γ
... | yes xInΓ =
       let
         d' : x ∷ x ∷ remove-first x (Γ ++ Σ) (mem-++-l xInΓ) ⊢ Δ
         d' = bring-to-front-ctx [ x ] (Γ ++ Σ) x (mem-++-l xInΓ) d
         
         d'' : x ∷ remove-first x (Γ ++ Σ) (mem-++-l xInΓ) ⊢ Δ
         d'' = contract-left x d'
         
         d_contracted = put_back (Γ ++ Σ) x (mem-++-l xInΓ) d''
         sub_gamma : Γ ⊆ Γ'
         sub_gamma y yIn = sub y (there yIn)
       in subset-weakening-left-gen sub_gamma d_contracted

... | no xNotInΓ =
       let
         xInGamma' : x ∈ Γ'
         xInGamma' = sub x here
         
         gammaSub : Γ ⊆ remove-first x Γ' xInGamma'
         gammaSub y yIn =
           let
             yInGamma' = sub y (there yIn)
             neq : Neg (x ≡ y)
             neq p = xNotInΓ (subst (λ z → z ∈ Γ) (sym p) yIn)
           in mem-remove-first x Γ' xInGamma' y yInGamma' neq

         lem_red : Γ ++ remove-first x (x ∷ Σ) here ≡ Γ ++ Σ
         lem_red = refl
         d_casted = subst (λ G → x ∷ G ⊢ Δ) (sym lem_red) d
         d_perm = put_back (Γ ++ x ∷ Σ) x (mem-++-r Γ here) (subst (λ G → x ∷ G ⊢ Δ) (sym (remove-first-++-r x Γ (x ∷ Σ) here)) d_casted)
         
         ih_res : (remove-first x Γ' xInGamma') ++ (x ∷ Σ) ⊢ Δ
         ih_res = subset-weakening-left-gen gammaSub d_perm
         
         d_final_perm_raw = bring-to-front ((remove-first x Γ' xInGamma') ++ x ∷ Σ) x (mem-++-r _ here) ih_res
         d_final_perm : x ∷ (remove-first x Γ' xInGamma') ++ Σ ⊢ Δ
         d_final_perm = subst (λ G → x ∷ G ⊢ Δ) (remove-first-++-r x (remove-first x Γ' xInGamma') (x ∷ Σ) here) d_final_perm_raw
         
         res : Γ' ++ Σ ⊢ Δ
         res = put_back (Γ' ++ Σ) x (mem-++-l xInGamma') (subst (λ G → x ∷ G ⊢ Δ) (sym (remove-first-++-l x Γ' Σ xInGamma')) d_final_perm)
       in res

-- Subset Weakening Right
subset-weakening-right-gen : ∀ {Δ Δ' Σ Γ} → Δ ⊆ Δ' → (Γ ⊢ Δ ++ Σ) → (Γ ⊢ Δ' ++ Σ)
subset-weakening-right-gen {[]} {Δ'} {Σ} sub d = weakening-insert-right Δ' d
subset-weakening-right-gen {x ∷ Δ} {Δ'} {Σ} {Γ} sub d with x ∈? Δ
... | yes xInΔ =
       let
         d' = bring-to-front-ctx-r [ x ] (Δ ++ Σ) x (mem-++-l xInΔ) d
         d'' = ⊢C {Γ = Γ} {Δ = remove-first x (Δ ++ Σ) (mem-++-l xInΔ)} d'
         d_contracted = put_back_r (Δ ++ Σ) x (mem-++-l xInΔ) d''
         sub_delta : Δ ⊆ Δ'
         sub_delta y yIn = sub y (there yIn)
       in subset-weakening-right-gen sub_delta d_contracted
... | no xNotInΔ =
       let
         xInDelta' = sub x here
         deltaSub : Δ ⊆ remove-first x Δ' xInDelta'
         deltaSub y yIn = mem-remove-first x Δ' xInDelta' y (sub y (there yIn)) (λ p → xNotInΔ (subst (λ z → z ∈ Δ) (sym p) yIn))
         
         lem_red : Δ ++ remove-first x (x ∷ Σ) here ≡ Δ ++ Σ
         lem_red = refl
         d_casted = subst (λ D → Γ ⊢ x ∷ D) (sym lem_red) d
         d_perm = put_back_r (Δ ++ x ∷ Σ) x (mem-++-r Δ here) (subst (λ D → Γ ⊢ x ∷ D) (sym (remove-first-++-r x Δ (x ∷ Σ) here)) d_casted)
         ih_res = subset-weakening-right-gen deltaSub d_perm
         d_final_perm_raw = bring-to-front-r ((remove-first x Δ' xInDelta') ++ x ∷ Σ) x (mem-++-r _ here) ih_res
         d_final_perm = subst (λ D → Γ ⊢ x ∷ D) (remove-first-++-r x (remove-first x Δ' xInDelta') (x ∷ Σ) here) d_final_perm_raw
         res = put_back_r (Δ' ++ Σ) x (mem-++-l xInDelta') (subst (λ D → Γ ⊢ x ∷ D) (sym (remove-first-++-l x Δ' Σ xInDelta')) d_final_perm)
       in res

-- Structural rule: handles weakening, contraction, and exchange
structural : ∀ {Γ Δ Γ' Δ'} → Γ ⊆ Γ' → Δ ⊆ Δ' → (Γ ⊢ Δ) → (Γ' ⊢ Δ')
structural {Γ} {Δ} {Γ'} {Δ'} subG subD d =
  let
    step1 = subset-weakening-left-gen {Σ = []} subG (subst (λ G → G ⊢ Δ) (sym (++-unit-r Γ)) d)
    step1' = subst (λ G → G ⊢ Δ) (++-unit-r Γ') step1
    step2 = subset-weakening-right-gen {Σ = []} subD (subst (λ D → Γ' ⊢ D) (sym (++-unit-r Δ)) step1')
    step2' = subst (λ D → Γ' ⊢ D) (++-unit-r Δ') step2
  in step2'

