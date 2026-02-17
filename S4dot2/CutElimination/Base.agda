{-# OPTIONS --cubical --safe #-}

module S4dot2.CutElimination.Base where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl; sym; cong; cong₂; subst; subst2; transport; _∙_; J; substRefl; transportRefl)
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Cubical.Data.Empty renaming (rec to emptyRec; elim to ⊥-elim) using (⊥)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.List using (List; _∷_; []; _++_; ++-assoc; map)
open import Cubical.Data.List.Properties using (++-unit-r)
open import Cubical.Data.Bool using (Bool; true; false; not; _and_; if_then_else_)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (Dec; yes; no) renaming (¬_ to Neg)
open import Cubical.Data.Nat using (ℕ; max; _+_; discreteℕ; predℕ; suc; snotz; zero)
open import Cubical.Data.Nat.Order using (_≤_; ≤-antisym; ≤-refl; pred-≤-pred; ≤-suc; ≤-trans; left-≤-max; right-≤-max; ≤→<; ≤0→≡0; ≤-predℕ; _<_; suc-≤-suc; <-weaken; ¬-<-zero)
open import Cubical.Induction.WellFounded using (Acc; acc; WellFounded)
open import Cubical.Data.Nat.Properties using (suc-predℕ; +-zero; +-suc)
open import Cubical.Data.Sigma using (_,_; Σ)

open import Cubical.Data.Unit using (Unit; tt)

open import S4dot2.Syntax hiding (_⊢_; _≢_)
open import S4dot2.System hiding (discretePFormula)
open import S4dot2.System using (discretePFormula) public

-- Re-export lightweight definitions (degree, height, δ, isCutFree, leq-max-*, etc.)
open import S4dot2.CutElimination.Defs public

-- Import solver for removeAll
open import S4dot2.Solver.Subset hiding (_≢_)
open Solver discretePFormula hiding (removeAll-++) public

-- _-_ is just removeAll with arguments flipped (Ctx - element syntax)
_-_ : Ctx → PFormula → Ctx
Γ - A = removeAll A Γ

-- =============================================================================
-- Degree Preservation Lemmas
-- =============================================================================

-- Transporting a proof preserves degree (by path induction)
subst-preserves-δ : ∀ {Γ Δ Δ'} (eq : Δ ≡ Δ') (p : Γ ⊢ Δ) → δ (subst (Γ ⊢_) eq p) ≡ δ p
subst-preserves-δ {Γ} {Δ} eq p = J (λ Δ' eq' → δ (subst (Γ ⊢_) eq' p) ≡ δ p) (cong δ (substRefl {B = Γ ⊢_} p)) eq

subst-preserves-δ-ctx : ∀ {Γ Γ' Δ} (eq : Γ ≡ Γ') (p : Γ ⊢ Δ) → δ (subst (_⊢ Δ) eq p) ≡ δ p
subst-preserves-δ-ctx {Γ} {Δ = Δ} eq p = J (λ Γ' eq' → δ (subst (_⊢ Δ) eq' p) ≡ δ p) (cong δ (substRefl {B = _⊢ Δ} p)) eq

-- subst2 preserves δ for proof types of the form Γ ⊢ Δ where both Γ and Δ depend on parameters
subst2-preserves-δ : ∀ {Γ Γ' Δ Δ'}
                     (f : Ctx → Ctx) (g : Ctx → Ctx)
                     (eq1 : Γ ≡ Γ') (eq2 : Δ ≡ Δ')
                     (p : f Γ ⊢ g Δ)
                     → δ (subst2 (λ x y → f x ⊢ g y) eq1 eq2 p) ≡ δ p
subst2-preserves-δ {Γ} {Γ'} {Δ} {Δ'} f g eq1 eq2 p =
  J (λ _ eq1' → δ (subst2 (λ x y → f x ⊢ g y) eq1' eq2 p) ≡ δ p)
    (J (λ _ eq2' → δ (subst2 (λ x y → f x ⊢ g y) refl eq2' p) ≡ δ p)
       (cong δ (transportRefl p))
       eq2)
    eq1

-- bring-to-front-ctx preserves δ (uses only subst and Exc⊢, both preserve δ)
bring-to-front-ctx-preserves-δ : ∀ {Δ} (Γ₁ Γ₂ : Ctx) (x : PFormula) (p : x ∈ Γ₂)
                                → (d : Γ₁ ++ Γ₂ ⊢ Δ)
                                → δ (bring-to-front-ctx Γ₁ Γ₂ x p d) ≡ δ d
bring-to-front-ctx-preserves-δ Γ₁ ._ x (here {xs = Γ₂}) d = refl
bring-to-front-ctx-preserves-δ {Δ} Γ₁ ._ x@(B ^ t) (there {y = y@(A ^ s)} {xs = Γ₂} p) d =
  let
    d' = subst (λ G → G ⊢ Δ) (sym (++-assoc Γ₁ [ y ] Γ₂)) d
    step1 = bring-to-front-ctx (Γ₁ ++ [ y ]) Γ₂ x p d'
    step1_ready = subst (λ G → G ⊢ Δ) (sym (++-assoc (Γ₁ ++ [ y ]) [ x ] (remove-first x Γ₂ p))) step1
    step2_raw = Exc⊢ {Γ₁ = Γ₁} {Γ₂ = remove-first x Γ₂ p} step1_ready
    eq = ++-assoc (Γ₁ ++ [ x ]) [ y ] (remove-first x Γ₂ p) ∙ ++-assoc Γ₁ [ x ] (y ∷ remove-first x Γ₂ p)
    -- Chain: δ result = δ step2_raw = δ step1_ready = δ step1 = δ d' = δ d
    ih = bring-to-front-ctx-preserves-δ (Γ₁ ++ [ y ]) Γ₂ x p d'
    eq1 = subst-preserves-δ-ctx (sym (++-assoc Γ₁ [ y ] Γ₂)) d
    eq2 = subst-preserves-δ-ctx (sym (++-assoc (Γ₁ ++ [ y ]) [ x ] (remove-first x Γ₂ p))) step1
    eq3 = subst-preserves-δ-ctx eq step2_raw
  in eq3 ∙ eq2 ∙ ih ∙ eq1

bring-to-front-preserves-δ : ∀ {Δ} (Γ : Ctx) (x : PFormula) (p : x ∈ Γ)
                           → (d : Γ ⊢ Δ)
                           → δ (bring-to-front Γ x p d) ≡ δ d
bring-to-front-preserves-δ Γ x p d = bring-to-front-ctx-preserves-δ [] Γ x p d

-- bring-to-front-ctx-r preserves δ (uses only subst and ⊢Exc)
bring-to-front-ctx-r-preserves-δ : ∀ {Γ} (Δ₁ Δ₂ : Ctx) (x : PFormula) (p : x ∈ Δ₂)
                                  → (d : Γ ⊢ Δ₁ ++ Δ₂)
                                  → δ (bring-to-front-ctx-r Δ₁ Δ₂ x p d) ≡ δ d
bring-to-front-ctx-r-preserves-δ Δ₁ ._ x (here {xs = Δ₂}) d = refl
bring-to-front-ctx-r-preserves-δ {Γ} Δ₁ ._ x@(B ^ t) (there {y = y@(A ^ s)} {xs = Δ₂} p) d =
  let
    d' = subst (λ D → Γ ⊢ D) (sym (++-assoc Δ₁ [ y ] Δ₂)) d
    step1 = bring-to-front-ctx-r (Δ₁ ++ [ y ]) Δ₂ x p d'
    step1_ready = subst (λ D → Γ ⊢ D) (sym (++-assoc (Δ₁ ++ [ y ]) [ x ] (remove-first x Δ₂ p))) step1
    step2_raw = ⊢Exc {Δ₁ = Δ₁} {Δ₂ = remove-first x Δ₂ p} step1_ready
    eq = ++-assoc (Δ₁ ++ [ x ]) [ y ] (remove-first x Δ₂ p) ∙ ++-assoc Δ₁ [ x ] (y ∷ remove-first x Δ₂ p)
    ih = bring-to-front-ctx-r-preserves-δ (Δ₁ ++ [ y ]) Δ₂ x p d'
    eq1 = subst-preserves-δ (sym (++-assoc Δ₁ [ y ] Δ₂)) d
    eq2 = subst-preserves-δ (sym (++-assoc (Δ₁ ++ [ y ]) [ x ] (remove-first x Δ₂ p))) step1
    eq3 = subst-preserves-δ eq step2_raw
  in eq3 ∙ eq2 ∙ ih ∙ eq1

bring-to-front-r-preserves-δ : ∀ {Γ} (Δ : Ctx) (x : PFormula) (p : x ∈ Δ)
                              → (d : Γ ⊢ Δ)
                              → δ (bring-to-front-r Δ x p d) ≡ δ d
bring-to-front-r-preserves-δ Δ x p d = bring-to-front-ctx-r-preserves-δ [] Δ x p d

-- bring-last-to-front preserves δ
bring-last-to-front-preserves-δ : ∀ {Δ} (Γ : Ctx) (x : PFormula)
                                 → (d : Γ ++ [ x ] ⊢ Δ)
                                 → δ (bring-last-to-front Γ x d) ≡ δ d
bring-last-to-front-preserves-δ {Δ} Γ x d =
  let p = mem-++-r Γ here
      step1 = bring-to-front (Γ ++ [ x ]) x p d
      lem = remove-first-++-r x Γ [ x ] here ∙ ++-unit-r Γ
      eq1 = bring-to-front-preserves-δ (Γ ++ [ x ]) x p d
      eq2 = subst-preserves-δ-ctx (cong (x ∷_) lem) step1
  in eq2 ∙ eq1

-- weakening-left-1 preserves δ (uses W⊢ and bring-last-to-front)
weakening-left-1-preserves-δ : ∀ {Γ Δ} (A : PFormula) → (d : Γ ⊢ Δ) → δ (weakening-left-1 A d) ≡ δ d
weakening-left-1-preserves-δ A d = bring-last-to-front-preserves-δ _ A (W⊢ d)

-- weakening-insert-left preserves δ
weakening-insert-left-preserves-δ : ∀ {Γ Δ} (Σ : Ctx) → (d : Γ ⊢ Δ) → δ (weakening-insert-left Σ d) ≡ δ d
weakening-insert-left-preserves-δ [] d = refl
weakening-insert-left-preserves-δ (x ∷ Σ) d = 
  weakening-left-1-preserves-δ x (weakening-insert-left Σ d) ∙ weakening-insert-left-preserves-δ Σ d

-- bring-last-to-front-r preserves δ
bring-last-to-front-r-preserves-δ : ∀ {Γ} (Δ : Ctx) (x : PFormula)
                                   → (d : Γ ⊢ Δ ++ [ x ])
                                   → δ (bring-last-to-front-r Δ x d) ≡ δ d
bring-last-to-front-r-preserves-δ {Γ} Δ x d =
  let p = mem-++-r Δ here
      step1 = bring-to-front-r (Δ ++ [ x ]) x p d
      lem = remove-first-++-r x Δ [ x ] here ∙ ++-unit-r Δ
      eq1 = bring-to-front-r-preserves-δ (Δ ++ [ x ]) x p d
      eq2 = subst-preserves-δ (cong (x ∷_) lem) step1
  in eq2 ∙ eq1

-- weakening-insert-right preserves δ
weakening-insert-right-preserves-δ : ∀ {Γ Δ} (Σ : Ctx) → (d : Γ ⊢ Δ) → δ (weakening-insert-right Σ d) ≡ δ d
weakening-insert-right-preserves-δ [] d = refl
weakening-insert-right-preserves-δ (x ∷ Σ) d = weakening-insert-right-preserves-δ Σ d

-- put_back_ctx preserves δ (follows exact structure of put_back_ctx)
put_back_ctx-preserves-δ : ∀ {Δ} (Γ₁ Γ₂ : Ctx) (x : PFormula) (p : x ∈ Γ₂)
                          → (d : Γ₁ ++ x ∷ remove-first x Γ₂ p ⊢ Δ)
                          → δ (put_back_ctx Γ₁ Γ₂ x p d) ≡ δ d
put_back_ctx-preserves-δ Γ₁ ._ x (here {xs = Γ₂}) d = refl
put_back_ctx-preserves-δ {Δ} Γ₁ ._ x@(A ^ s) (there {y = y@(B ^ t)} {xs = Γ₂} p) d =
  let
    eq = sym (++-assoc Γ₁ [ x ] (y ∷ remove-first x Γ₂ p)) ∙ sym (++-assoc (Γ₁ ++ [ x ]) [ y ] (remove-first x Γ₂ p))
    d_ready = subst (λ G → G ⊢ Δ) eq d
    d' = Exc⊢ {Γ₁ = Γ₁} {Γ₂ = remove-first x Γ₂ p} d_ready
    d'_ready = subst (λ G → G ⊢ Δ) (++-assoc (Γ₁ ++ [ y ]) [ x ] (remove-first x Γ₂ p)) d'
    res = put_back_ctx (Γ₁ ++ [ y ]) Γ₂ x p d'_ready
    -- δ chain: res → d'_ready → d' → d_ready → d
    eq1 = subst-preserves-δ-ctx eq d
    eq2 = subst-preserves-δ-ctx (++-assoc (Γ₁ ++ [ y ]) [ x ] (remove-first x Γ₂ p)) d'
    ih = put_back_ctx-preserves-δ (Γ₁ ++ [ y ]) Γ₂ x p d'_ready
    eq_final = subst-preserves-δ-ctx (++-assoc Γ₁ [ y ] Γ₂) res
  in eq_final ∙ ih ∙ eq2 ∙ eq1

-- put_back preserves δ
put_back-preserves-δ : ∀ {Δ} (Γ : Ctx) (x : PFormula) (p : x ∈ Γ)
                      → (d : x ∷ remove-first x Γ p ⊢ Δ)
                      → δ (put_back Γ x p d) ≡ δ d
put_back-preserves-δ Γ x p d = put_back_ctx-preserves-δ [] Γ x p d

-- put_back_ctx-r preserves δ (follows exact structure of put_back_ctx-r)
put_back_ctx-r-preserves-δ : ∀ {Γ} (Δ₁ Δ₂ : Ctx) (x : PFormula) (p : x ∈ Δ₂)
                            → (d : Γ ⊢ Δ₁ ++ x ∷ remove-first x Δ₂ p)
                            → δ (put_back_ctx-r Δ₁ Δ₂ x p d) ≡ δ d
put_back_ctx-r-preserves-δ Δ₁ ._ x (here {xs = Δ₂}) d = refl
put_back_ctx-r-preserves-δ {Γ} Δ₁ ._ x@(A ^ s) (there {y = y@(B ^ t)} {xs = Δ₂} p) d =
  let
    eq = sym (++-assoc Δ₁ [ x ] (y ∷ remove-first x Δ₂ p)) ∙ sym (++-assoc (Δ₁ ++ [ x ]) [ y ] (remove-first x Δ₂ p))
    d_ready = subst (λ D → Γ ⊢ D) eq d
    d' = ⊢Exc {Δ₁ = Δ₁} {Δ₂ = remove-first x Δ₂ p} d_ready
    d'_ready = subst (λ D → Γ ⊢ D) (++-assoc (Δ₁ ++ [ y ]) [ x ] (remove-first x Δ₂ p)) d'
    res = put_back_ctx-r (Δ₁ ++ [ y ]) Δ₂ x p d'_ready
    eq1 = subst-preserves-δ eq d
    eq2 = subst-preserves-δ (++-assoc (Δ₁ ++ [ y ]) [ x ] (remove-first x Δ₂ p)) d'
    ih = put_back_ctx-r-preserves-δ (Δ₁ ++ [ y ]) Δ₂ x p d'_ready
    eq_final = subst-preserves-δ (++-assoc Δ₁ [ y ] Δ₂) res
  in eq_final ∙ ih ∙ eq2 ∙ eq1

put_back_r-preserves-δ : ∀ {Γ} (Δ : Ctx) (x : PFormula) (p : x ∈ Δ)
                        → (d : Γ ⊢ x ∷ remove-first x Δ p)
                        → δ (put_back_r Δ x p d) ≡ δ d
put_back_r-preserves-δ Δ x p d = put_back_ctx-r-preserves-δ [] Δ x p d

-- contract-left preserves δ (uses C⊢, bring-to-front, put_back, subst)
contract-left-preserves-δ : ∀ {Γ Δ} (x : PFormula) → (d : x ∷ x ∷ Γ ⊢ Δ) → δ (contract-left x d) ≡ δ d
contract-left-preserves-δ {Γ} {Δ} x d =
  let
    p = mem-++-r Γ here
    lem = remove-first-++-r x Γ [ x ] here ∙ ++-unit-r Γ
    d_casted = subst (λ G → x ∷ x ∷ G ⊢ Δ) (sym lem) d
    d1 = put_back_ctx [ x ] (Γ ++ [ x ]) x p d_casted
    p2 = mem-++-r (Γ ++ [ x ]) here
    lem2 = remove-first-++-r x (Γ ++ [ x ]) [ x ] here ∙ ++-unit-r (Γ ++ [ x ])
    d1_casted = subst (λ G → x ∷ G ⊢ Δ) (sym lem2) d1
    d2 = put_back ((Γ ++ [ x ]) ++ [ x ]) x p2 d1_casted
    d3 = C⊢ {Γ = Γ} {Δ = Δ} d2
    d4 = bring-last-to-front Γ x d3
    -- δ chain: d4 → d3 → d2 → d1_casted → d1 → d_casted → d
    eq_d_casted = subst-preserves-δ-ctx (cong (x ∷_) (cong (x ∷_) (sym lem))) d
    eq_d1 = put_back_ctx-preserves-δ [ x ] (Γ ++ [ x ]) x p d_casted
    eq_d1_casted = subst-preserves-δ-ctx (cong (x ∷_) (sym lem2)) d1
    eq_d2 = put_back-preserves-δ ((Γ ++ [ x ]) ++ [ x ]) x p2 d1_casted
    -- d3 = C⊢ d2, and δ (C⊢ p) = δ p
    eq_d4 = bring-last-to-front-preserves-δ Γ x d3
  in eq_d4 ∙ eq_d2 ∙ eq_d1_casted ∙ eq_d1 ∙ eq_d_casted

neq-from-degree : ∀ {A B} → degree A < degree B → A ≢ B
neq-from-degree {A} {B} lt eq = <→≢ lt (cong degree eq)

-- subset-weakening-left-gen preserves δ
subset-weakening-left-gen-preserves-δ : ∀ {Γ Γ' Σ Δ} (sub : Γ ⊆ Γ') (d : Γ ++ Σ ⊢ Δ) 
                                       → δ (subset-weakening-left-gen sub d) ≡ δ d
subset-weakening-left-gen-preserves-δ {[]} {Γ'} {Σ} sub d = weakening-insert-left-preserves-δ Γ' d
subset-weakening-left-gen-preserves-δ {x ∷ Γ} {Γ'} {Σ} {Δ} sub d with x ∈? Γ
... | yes xInΓ =
  let
    d' = bring-to-front-ctx [ x ] (Γ ++ Σ) x (mem-++-l xInΓ) d
    d'' = contract-left x d'
    d_contracted = put_back (Γ ++ Σ) x (mem-++-l xInΓ) d''
    sub_gamma = λ y yIn → sub y (there yIn)
    -- Chain: δ result = δ d_contracted = δ d'' = δ d' = δ d
    eq1 = bring-to-front-ctx-preserves-δ [ x ] (Γ ++ Σ) x (mem-++-l xInΓ) d
    eq2 = contract-left-preserves-δ x d'
    eq3 = put_back-preserves-δ (Γ ++ Σ) x (mem-++-l xInΓ) d''
    ih = subset-weakening-left-gen-preserves-δ sub_gamma d_contracted
  in ih ∙ eq3 ∙ eq2 ∙ eq1

... | no xNotInΓ =
  let
    xInGamma' = sub x here
    gammaSub = λ y yIn →
      let yInGamma' = sub y (there yIn)
          neq = λ p → xNotInΓ (subst (λ z → z ∈ Γ) (sym p) yIn)
      in mem-remove-first x Γ' xInGamma' y yInGamma' neq
    lem_red : Γ ++ remove-first x (x ∷ Σ) here ≡ Γ ++ Σ
    lem_red = refl
    d_casted = subst (λ G → x ∷ G ⊢ Δ) (sym lem_red) d
    d_perm = put_back (Γ ++ x ∷ Σ) x (mem-++-r Γ here) (subst (λ G → x ∷ G ⊢ Δ) (sym (remove-first-++-r x Γ (x ∷ Σ) here)) d_casted)
    ih_res = subset-weakening-left-gen gammaSub d_perm
    d_final_perm_raw = bring-to-front ((remove-first x Γ' xInGamma') ++ x ∷ Σ) x (mem-++-r _ here) ih_res
    d_final_perm = subst (λ G → x ∷ G ⊢ Δ) (remove-first-++-r x (remove-first x Γ' xInGamma') (x ∷ Σ) here) d_final_perm_raw
    res = put_back (Γ' ++ Σ) x (mem-++-l xInGamma') (subst (λ G → x ∷ G ⊢ Δ) (sym (remove-first-++-l x Γ' Σ xInGamma')) d_final_perm)
    -- Chain for degrees - this is complex due to many subst and helper functions
    eq_d_casted = subst-preserves-δ-ctx (cong (x ∷_) (sym lem_red)) d
    eq_d_perm = put_back-preserves-δ (Γ ++ x ∷ Σ) x (mem-++-r Γ here) _ ∙ 
                subst-preserves-δ-ctx (cong (x ∷_) (sym (remove-first-++-r x Γ (x ∷ Σ) here))) d_casted
    ih = subset-weakening-left-gen-preserves-δ gammaSub d_perm
    eq_final_raw = bring-to-front-preserves-δ ((remove-first x Γ' xInGamma') ++ x ∷ Σ) x (mem-++-r _ here) ih_res
    eq_final_perm = subst-preserves-δ-ctx (cong (x ∷_) (remove-first-++-r x (remove-first x Γ' xInGamma') (x ∷ Σ) here)) d_final_perm_raw
    eq_res = put_back-preserves-δ (Γ' ++ Σ) x (mem-++-l xInGamma') _ ∙
             subst-preserves-δ-ctx (cong (x ∷_) (sym (remove-first-++-l x Γ' Σ xInGamma'))) d_final_perm
  in eq_res ∙ eq_final_perm ∙ eq_final_raw ∙ ih ∙ eq_d_perm ∙ eq_d_casted

-- subset-weakening-right-gen preserves δ
subset-weakening-right-gen-preserves-δ : ∀ {Δ Δ' Σ Γ} (sub : Δ ⊆ Δ') (d : Γ ⊢ Δ ++ Σ) 
                                        → δ (subset-weakening-right-gen sub d) ≡ δ d
subset-weakening-right-gen-preserves-δ {[]} {Δ'} {Σ} sub d = weakening-insert-right-preserves-δ Δ' d
subset-weakening-right-gen-preserves-δ {x ∷ Δ} {Δ'} {Σ} {Γ} sub d with x ∈? Δ
... | yes xInΔ =
  let
    d' = bring-to-front-ctx-r [ x ] (Δ ++ Σ) x (mem-++-l xInΔ) d
    d'' = ⊢C {Γ = Γ} {Δ = remove-first x (Δ ++ Σ) (mem-++-l xInΔ)} d'
    d_contracted = put_back_r (Δ ++ Σ) x (mem-++-l xInΔ) d''
    sub_delta = λ y yIn → sub y (there yIn)
    eq1 = bring-to-front-ctx-r-preserves-δ [ x ] (Δ ++ Σ) x (mem-++-l xInΔ) d
    eq2 = put_back_r-preserves-δ (Δ ++ Σ) x (mem-++-l xInΔ) d''
    ih = subset-weakening-right-gen-preserves-δ sub_delta d_contracted
  in ih ∙ eq2 ∙ eq1

... | no xNotInΔ =
  let
    xInDelta' = sub x here
    deltaSub = λ y yIn → mem-remove-first x Δ' xInDelta' y (sub y (there yIn)) (λ p → xNotInΔ (subst (λ z → z ∈ Δ) (sym p) yIn))
    lem_red : Δ ++ remove-first x (x ∷ Σ) here ≡ Δ ++ Σ
    lem_red = refl
    d_casted = subst (λ D → Γ ⊢ x ∷ D) (sym lem_red) d
    d_perm = put_back_r (Δ ++ x ∷ Σ) x (mem-++-r Δ here) (subst (λ D → Γ ⊢ x ∷ D) (sym (remove-first-++-r x Δ (x ∷ Σ) here)) d_casted)
    ih_res = subset-weakening-right-gen deltaSub d_perm
    d_final_perm_raw = bring-to-front-r ((remove-first x Δ' xInDelta') ++ x ∷ Σ) x (mem-++-r _ here) ih_res
    d_final_perm = subst (λ D → Γ ⊢ x ∷ D) (remove-first-++-r x (remove-first x Δ' xInDelta') (x ∷ Σ) here) d_final_perm_raw
    res = put_back_r (Δ' ++ Σ) x (mem-++-l xInDelta') (subst (λ D → Γ ⊢ x ∷ D) (sym (remove-first-++-l x Δ' Σ xInDelta')) d_final_perm)
    eq_d_casted = subst-preserves-δ (cong (x ∷_) (sym lem_red)) d
    eq_d_perm = put_back_r-preserves-δ (Δ ++ x ∷ Σ) x (mem-++-r Δ here) _ ∙ 
                subst-preserves-δ (cong (x ∷_) (sym (remove-first-++-r x Δ (x ∷ Σ) here))) d_casted
    ih = subset-weakening-right-gen-preserves-δ deltaSub d_perm
    eq_final_raw = bring-to-front-r-preserves-δ ((remove-first x Δ' xInDelta') ++ x ∷ Σ) x (mem-++-r _ here) ih_res
    eq_final_perm = subst-preserves-δ (cong (x ∷_) (remove-first-++-r x (remove-first x Δ' xInDelta') (x ∷ Σ) here)) d_final_perm_raw
    eq_res = put_back_r-preserves-δ (Δ' ++ Σ) x (mem-++-l xInDelta') _ ∙
             subst-preserves-δ (cong (x ∷_) (sym (remove-first-++-l x Δ' Σ xInDelta'))) d_final_perm
  in eq_res ∙ eq_final_perm ∙ eq_final_raw ∙ ih ∙ eq_d_perm ∙ eq_d_casted

-- structural preserves δ
structural-preserves-δ : ∀ {Γ Δ Γ' Δ'} (subG : Γ ⊆ Γ') (subD : Δ ⊆ Δ') (p : Γ ⊢ Δ) → δ (structural subG subD p) ≡ δ p
structural-preserves-δ {Γ} {Δ} {Γ'} {Δ'} subG subD d =
  let
    step1 = subset-weakening-left-gen {Σ = []} subG (subst (λ G → G ⊢ Δ) (sym (++-unit-r Γ)) d)
    step1' = subst (λ G → G ⊢ Δ) (++-unit-r Γ') step1
    step2 = subset-weakening-right-gen {Σ = []} subD (subst (λ D → Γ' ⊢ D) (sym (++-unit-r Δ)) step1')
    step2' = subst (λ D → Γ' ⊢ D) (++-unit-r Δ') step2
    -- Chain: δ step2' = δ step2 = δ step1' = δ step1 = δ d
    eq1 = subst-preserves-δ-ctx (sym (++-unit-r Γ)) d
    eq2 = subset-weakening-left-gen-preserves-δ subG (subst (λ G → G ⊢ Δ) (sym (++-unit-r Γ)) d)
    eq3 = subst-preserves-δ-ctx (++-unit-r Γ') step1
    eq4 = subst-preserves-δ (sym (++-unit-r Δ)) step1'
    eq5 = subset-weakening-right-gen-preserves-δ subD (subst (λ D → Γ' ⊢ D) (sym (++-unit-r Δ)) step1')
    eq6 = subst-preserves-δ (++-unit-r Δ') step2
  in eq6 ∙ eq5 ∙ eq4 ∙ eq3 ∙ eq2 ∙ eq1


-- Dec-based removeAll lemmas
removeAll-no : ∀ pf y Γ → pf ≢ y → (y ∷ Γ) - pf ≡ y ∷ (Γ - pf)
removeAll-no pf y Γ neq with discretePFormula pf y
... | yes p = ⊥-elim (neq p)
... | no _ = refl

removeAll-yes : ∀ pf y Γ → pf ≡ y → (y ∷ Γ) - pf ≡ Γ - pf
removeAll-yes pf y Γ eq with discretePFormula pf y
... | yes _ = refl
... | no ¬p = emptyRec (¬p eq)

removeAll-cons-neq : ∀ {A C s r} {Δ} → A ≢ C → ((C ^ r) ∷ Δ) - (A ^ s) ≡ (C ^ r) ∷ (Δ - (A ^ s))
removeAll-cons-neq {A} {C} {s} {r} {Δ} neq with discretePFormula (A ^ s) (C ^ r)
... | yes p = ⊥-elim (neq (cong PFormula.form p))
... | no _ = refl

-- removeAll distributes over ++
removeAll-++ : ∀ (pf : PFormula) (Γ1 Γ2 : Ctx) → (Γ1 ++ Γ2) - pf ≡ (Γ1 - pf) ++ (Γ2 - pf)
removeAll-++ pf [] Γ2 = refl
removeAll-++ pf (x ∷ Γ1) Γ2 with discretePFormula pf x
... | yes _ = removeAll-++ pf Γ1 Γ2
... | no _ = cong (x ∷_) (removeAll-++ pf Γ1 Γ2)

-- removeAll of singleton when not equal
removeAll-singleton-neq : ∀ {pf1 pf2 : PFormula} → pf1 ≢ pf2 → [ pf2 ] - pf1 ≡ [ pf2 ]
removeAll-singleton-neq {pf1} {pf2} neq = removeAll-no pf1 pf2 [] neq

-- removeAll of singleton when equal
removeAll-singleton-eq : ∀ {pf1 pf2 : PFormula} → pf1 ≡ pf2 → [ pf2 ] - pf1 ≡ []
removeAll-singleton-eq {pf1} {pf2} eq = removeAll-yes pf1 pf2 [] eq

removeAll-++-r-neq : ∀ {A B s t} {Δ} → A ≢ B → (Δ ++ [ B ^ t ]) - (A ^ s) ≡ (Δ - (A ^ s)) ++ [ B ^ t ]
removeAll-++-r-neq {A} {B} {s} {t} {Δ} neq =
  let pf-neq : (A ^ s) ≢ (B ^ t)
      pf-neq p = neq (cong PFormula.form p)
  in trans (removeAll-++ (A ^ s) Δ [ B ^ t ]) (cong ((Δ - (A ^ s)) ++_) (removeAll-singleton-neq pf-neq))

-- Version that takes PFormula inequality instead of Formula inequality
removeAll-++-r-pf-neq : ∀ {pf1 pf2 : PFormula} {Δ} → pf1 ≢ pf2 → (Δ ++ [ pf2 ]) - pf1 ≡ (Δ - pf1) ++ [ pf2 ]
removeAll-++-r-pf-neq {pf1} {pf2} {Δ} neq =
  trans (removeAll-++ pf1 Δ [ pf2 ]) (cong ((Δ - pf1) ++_) (removeAll-singleton-neq neq))

-- Left-prepend version: removeAll distributes over cons when positioned formulas differ
-- This is the key lemma for cross-cuts: removing A from ([B] ,, Δ) preserves B when B ≠ A
removeAll-cons-pf-neq : ∀ {pf1 pf2 : PFormula} {Δ} → pf1 ≢ pf2 → (pf2 ∷ Δ) - pf1 ≡ pf2 ∷ (Δ - pf1)
removeAll-cons-pf-neq {pf1} {pf2} {Δ} neq = removeAll-no pf1 pf2 Δ neq

-- Prepend version using _,,_ syntax: [pf2] ,, Δ = pf2 ∷ Δ
-- For cross-cuts: ([ B ^ t ] ,, Δ) - (A ^ s) ≡ [ B ^ t ] ,, (Δ - (A ^ s)) when (B ^ t) ≢ (A ^ s)
removeAll-prepend-pf-neq : ∀ {pf1 pf2 : PFormula} {Δ} → pf1 ≢ pf2 → ([ pf2 ] ++ Δ) - pf1 ≡ [ pf2 ] ++ (Δ - pf1)
removeAll-prepend-pf-neq {pf1} {pf2} {Δ} neq = removeAll-no pf1 pf2 Δ neq

-- removeAll when elements are equal
lemma-removeAll-eq : ∀ {A B : PFormula} {Γ : Ctx} → A ≡ B → (Γ ++ [ B ]) - A ≡ Γ - A
lemma-removeAll-eq {A} {B} {Γ} eq =
  trans (removeAll-++ A Γ [ B ]) (trans (cong ((Γ - A) ++_) (removeAll-singleton-eq eq)) (++-unit-r (Γ - A)))


-- mem-++-split is now in Defs






-- Lemma 3.3 (Mix Lemma)
mutual

  removeAll-cons-eq : ∀ {A B s t} {Δ} → (A ^ s) ≡ (B ^ t) → ((B ^ t) ∷ Δ) - (A ^ s) ≡ Δ - (A ^ s)
  removeAll-cons-eq {A} {B} {s} {t} {Δ} eq = removeAll-yes (A ^ s) (B ^ t) Δ eq


  mem-removeAll : ∀ {x y : PFormula} {Γ : Ctx} → y ∈ Γ → x ≢ y → y ∈ (Γ - x)
  mem-removeAll {x} {y} {[]} () neq
  mem-removeAll {x} {y} {z ∷ Γ} here neq with discretePFormula x z
  ... | yes p = ⊥-elim (neq p)
  ... | no _ = here
  mem-removeAll {x} {y} {z ∷ Γ} (there yIn') neq with discretePFormula x z
  ... | yes _ = mem-removeAll yIn' neq
  ... | no _ = there (mem-removeAll yIn' neq)


mutual
  removeAll-mem : ∀ {x y : PFormula} {Γ : Ctx} → y ∈ (Γ - x) → (y ∈ Γ) × Neg (x ≡ y)
  removeAll-mem {x} {y} {[]} ()
  removeAll-mem {x} {y} {z ∷ Γ} yIn with discretePFormula x z
  ... | yes _ =
      let (yInG , neq) = removeAll-mem {x} {y} {Γ} yIn
      in (there yInG , neq)
  ... | no ¬p with yIn
  ... | here = (here , λ x≡y → ¬p (trans x≡y refl))
  ... | there yIn' =
      let (yInG , neq) = removeAll-mem {x} {y} {Γ} yIn'
      in (there yInG , neq)

  mem-remove-prefix : ∀ {Γ Σ : Ctx} (x : PFormula) → x ∈ Γ ++ Σ → Neg (x ∈ Γ) → x ∈ Σ
  mem-remove-prefix {[]} {Σ} x xIn neq = xIn
  mem-remove-prefix {y ∷ Γ} {Σ} x here neq = ⊥-elim (neq here)
  mem-remove-prefix {y ∷ Γ} {Σ} x (there xIn) neq = mem-remove-prefix {Γ} {Σ} x xIn (λ p → neq (there p))




-- Lemma: Every element y of Γ is either equal to A (so y ∈ [A]) or y ≠ A (so y ∈ Γ - A)
-- Delegated to the solver's elem-or-removeAll companion lemma.
subset-elem-or-removeAll : ∀ {A : PFormula} {Γ : Ctx} → Γ ⊆ ([ A ] ++ (Γ - A))
subset-elem-or-removeAll {A} {Γ} = elem-or-removeAll A Γ

-- Dual version: (Γ - A) ++ [A] ⊇ Γ
subset-removeAll-or-elem : ∀ {A : PFormula} {Γ : Ctx} → Γ ⊆ ((Γ - A) ++ [ A ])
subset-removeAll-or-elem {A} {Γ} = removeAll-or-elem A Γ

-- Lemma: removeAll on element not in list is identity
-- If pf ∉ Γ then Γ - pf ≡ Γ
removeAll-not-in : ∀ (pf : PFormula) (Γ : Ctx) → (∀ y → y ∈ Γ → pf ≢ y) → Γ - pf ≡ Γ
removeAll-not-in pf [] _ = refl
removeAll-not-in pf (x ∷ Γ) notIn with discretePFormula pf x
... | yes pf≡x = ⊥-elim (notIn x here pf≡x)
... | no pf≢x = cong (x ∷_) (removeAll-not-in pf Γ (λ y yIn pf≡y → notIn y (there yIn) pf≡y))

-- Corollary: if A ≢ B and A not in Γ, removeAll A on (B ∷ Γ) equals B ∷ Γ
removeAll-different-formula : ∀ {A B : Formula} {s t : Position} {Γ : Ctx}
                            → A ≢ B
                            → (∀ y → y ∈ Γ → (A ^ s) ≢ y)
                            → ((B ^ t) ∷ Γ) - (A ^ s) ≡ (B ^ t) ∷ Γ
removeAll-different-formula {A} {B} {s} {t} {Γ} A≢B notIn with discretePFormula (A ^ s) (B ^ t)
... | yes eq = ⊥-elim (A≢B (cong PFormula.form eq))
... | no neq = cong ((B ^ t) ∷_) (removeAll-not-in (A ^ s) Γ notIn)


-- Helper: Reflexivity of subset
subset-refl : ∀ {ℓ} {A : Type ℓ} {Γ : List A} → Γ ⊆ Γ
subset-refl _ xIn = xIn

-- Helper subset for contraction
subset-contract : ∀ {A : PFormula} {Δ : Ctx} → (A ∷ Δ) ⊆ (A ∷ (Δ - A))
subset-contract _ here = here
subset-contract {A} {Δ} _ (there yInDelta) = subset-elem-or-removeAll {A} {Δ} _ yInDelta

-- Contract all occurrences of A in Δ into the head A
contract-occurrences : ∀ {Γ Δ A s} → (Γ ⊢ [ A ^ s ] ,, Δ) → Γ ⊢ [ A ^ s ] ,, (Δ - (A ^ s))
contract-occurrences {Γ} {Δ} {A} {s} p = structural subset-refl (subset-contract {A ^ s} {Δ}) p

-- Preservation lemma
contract-occurrences-preserves-δ : ∀ {Γ Δ A s} → (p : Γ ⊢ [ A ^ s ] ,, Δ) → δ (contract-occurrences p) ≡ δ p
contract-occurrences-preserves-δ {Γ} {Δ} {A} {s} p = structural-preserves-δ subset-refl (subset-contract {A ^ s} {Δ}) p

-- =============================================================================
-- Well-Founded Recursion Infrastructure for Mix Lemma
-- =============================================================================

-- Basic lemma: n < suc n
n<suc-n : ∀ n → n < suc n
n<suc-n n = suc-≤-suc ≤-refl

-- Basic lemma: n < suc (max n m)
n<suc-max-l : ∀ n m → n < suc (max n m)
n<suc-max-l n m = suc-≤-suc left-≤-max

-- Basic lemma: m < suc (max n m)
n<suc-max-r : ∀ n m → m < suc (max n m)
n<suc-max-r n m = suc-≤-suc (right-≤-max {m} {n})

-- Lemma: n + 1 ≡ suc n
+-suc-1 : ∀ n → n + 1 ≡ suc n
+-suc-1 n = +-suc n 0 ∙ cong suc (+-zero n)

-- Basic lemma: n < n + 1
n<n+1 : ∀ n → n < n + 1
n<n+1 n = subst (n <_) (sym (+-suc-1 n)) (n<suc-n n)

-- Basic lemma: n < max n m + 1
n<max+1-l : ∀ n m → n < max n m + 1
n<max+1-l n m = subst (n <_) (sym (+-suc-1 (max n m))) (n<suc-max-l n m)

-- Basic lemma: m < max n m + 1
n<max+1-r : ∀ n m → m < max n m + 1
n<max+1-r n m = subst (m <_) (sym (+-suc-1 (max n m))) (n<suc-max-r n m)

-- Well-foundedness of _<_ on ℕ
-- Prove: all numbers ≤ n are accessible under _<_
private
  acc≤ : (n : ℕ) → (m : ℕ) → m ≤ n → Acc _<_ m
  acc≤ n zero _ = acc λ k k<0 → emptyRec (¬-<-zero k<0)
  acc≤ zero (suc m) sm≤0 = emptyRec (¬-<-zero sm≤0)
  acc≤ (suc n) (suc m) sm≤sn = acc helper
    where
      helper : (k : ℕ) → k < suc m → Acc _<_ k
      helper k k<sm = acc≤ n k (≤-trans (pred-≤-pred k<sm) (pred-≤-pred sm≤sn))

<-wf : (n : ℕ) → Acc _<_ n
<-wf n = acc λ m m<n → acc≤ n m (<-weaken m<n)

-- =============================================================================
-- Height Decrease Lemmas - Generic Versions
-- =============================================================================
-- These lemmas express that height of subproofs is strictly less than
-- height of compound proofs. The specific rule types are complex, so we
-- provide simplified versions that can be applied at use sites.

-- For single-premise rules: height Π < height (Rule Π)
-- Since height (Rule p) = height p + 1, we have height p < height p + 1
height-subproof-1 : ∀ {Γ Δ} (p : Γ ⊢ Δ) → height p < height p + 1
height-subproof-1 p = n<n+1 (height p)

-- For two-premise rules: height Π₁ < height (Rule Π₁ Π₂) and height Π₂ < height (Rule Π₁ Π₂)
-- Since height (Rule p1 p2) = max (height p1) (height p2) + 1
height-subproof-2-l : ∀ {Γ₁ Δ₁ Γ₂ Δ₂} (p1 : Γ₁ ⊢ Δ₁) (p2 : Γ₂ ⊢ Δ₂)
                    → height p1 < max (height p1) (height p2) + 1
height-subproof-2-l p1 p2 = n<max+1-l (height p1) (height p2)

height-subproof-2-r : ∀ {Γ₁ Δ₁ Γ₂ Δ₂} (p1 : Γ₁ ⊢ Δ₁) (p2 : Γ₂ ⊢ Δ₂)
                    → height p2 < max (height p1) (height p2) + 1
height-subproof-2-r p1 p2 = n<max+1-r (height p1) (height p2)

-- =============================================================================
-- Combined Height Measure for Mix Lemma
-- =============================================================================

mixHeight : ∀ {Γ Δ Γ' Δ'} → (Γ ⊢ Δ) → (Γ' ⊢ Δ') → ℕ
mixHeight Π Π' = height Π + height Π'

-- Key lemma: decreasing left height decreases mixHeight
mixHeight-dec-l : ∀ {Γ Δ Γ₁ Δ₁ Γ' Δ'} (Π : Γ ⊢ Δ) (Π₁ : Γ₁ ⊢ Δ₁) (Π' : Γ' ⊢ Δ')
                → height Π₁ < height Π → mixHeight Π₁ Π' < mixHeight Π Π'
mixHeight-dec-l {Γ' = Γ'} {Δ' = Δ'} Π Π₁ Π' h1<h =
  let h' = height Π'
  in +-monoˡ-< h' h1<h
  where
    -- n + k < m + k when n < m
    +-monoˡ-< : ∀ k {n m} → n < m → n + k < m + k
    +-monoˡ-< zero {n} {m} n<m = subst2 _<_ (sym (+-zero n)) (sym (+-zero m)) n<m
    +-monoˡ-< (suc k) {n} {m} n<m = subst2 _<_ (sym (+-suc n k)) (sym (+-suc m k)) (suc-≤-suc (+-monoˡ-< k n<m))

-- Key lemma: decreasing right height decreases mixHeight
mixHeight-dec-r : ∀ {Γ Δ Γ' Δ' Γ'₁ Δ'₁} (Π : Γ ⊢ Δ) (Π' : Γ' ⊢ Δ') (Π'₁ : Γ'₁ ⊢ Δ'₁)
                → height Π'₁ < height Π' → mixHeight Π Π'₁ < mixHeight Π Π'
mixHeight-dec-r Π Π' Π'₁ h'1<h' =
  let h = height Π
  in +-monoʳ-< h h'1<h'
  where
    -- k + n < k + m when n < m
    +-monoʳ-< : ∀ k {n m} → n < m → k + n < k + m
    +-monoʳ-< zero n<m = n<m
    +-monoʳ-< (suc k) n<m = suc-≤-suc (+-monoʳ-< k n<m)

-- Height is preserved under subst on the antecedent formula
height-subst-antecedent : ∀ {Γ Δ P Q} (eq : P ≡ Q) (Π : Γ ,, [ P ] ⊢ Δ)
                        → height (subst (λ pf → Γ ,, [ pf ] ⊢ Δ) eq Π) ≡ height Π
height-subst-antecedent {Γ} {Δ} eq Π =
  J (λ Q p → height (subst (λ pf → Γ ,, [ pf ] ⊢ Δ) p Π) ≡ height Π)
    (cong height (substRefl {B = λ pf → Γ ,, [ pf ] ⊢ Δ} Π))
    eq

-- mixHeight is preserved when right proof is substituted on antecedent
mixHeight-subst-antecedent-r : ∀ {Γ Δ Γ' Δ' P Q} (Π : Γ ⊢ Δ)
                               (eq : P ≡ Q) (Π' : Γ' ,, [ P ] ⊢ Δ')
                             → mixHeight Π (subst (λ pf → Γ' ,, [ pf ] ⊢ Δ') eq Π') ≡ mixHeight Π Π'
mixHeight-subst-antecedent-r Π eq Π' = cong (height Π +_) (height-subst-antecedent eq Π')

-- =============================================================================
-- Lexicographic Ordering for Termination
-- =============================================================================
-- This ordering is used to prove termination of MixLemma/LemmaMix:
-- - Primary: degree of cut formula (decreases in principal cases)
-- - Secondary: mixHeight (decreases in non-principal cases)

-- Lexicographic ordering on pairs of natural numbers
_<Lex_ : (ℕ × ℕ) → (ℕ × ℕ) → Type
(d₁ , h₁) <Lex (d₂ , h₂) = (d₁ < d₂) ⊎ ((d₁ ≡ d₂) × (h₁ < h₂))

-- Well-foundedness of lexicographic order
-- We use the standard technique: prove accessibility by nested induction
-- First on the first component, then on the second component

private
  -- Inner: given fixed d, prove all (d, h) accessible for h accessible
  <Lex-acc-inner : ∀ d → (∀ d' → d' < d → ∀ h' → Acc _<Lex_ (d' , h'))
                 → ∀ h → Acc _<_ h → Acc _<Lex_ (d , h)
  <Lex-acc-inner d recD h (acc recH) = acc helper
    where
      helper : ∀ p → p <Lex (d , h) → Acc _<Lex_ p
      helper (d' , h') (inl d'<d) = recD d' d'<d h'
      helper (d' , h') (inr (d'≡d , h'<h)) =
        subst (λ x → Acc _<Lex_ (x , h')) (sym d'≡d)
              (<Lex-acc-inner d recD h' (recH h' h'<h))

  -- Outer: prove all (d, h) accessible by induction on d
  <Lex-acc-outer : ∀ d → Acc _<_ d → ∀ h → Acc _<Lex_ (d , h)
  <Lex-acc-outer d (acc recD) h = <Lex-acc-inner d (λ d' d'<d h' → <Lex-acc-outer d' (recD d' d'<d) h') h (<-wf h)

<Lex-wf : ∀ p → Acc _<Lex_ p
<Lex-wf (d , h) = <Lex-acc-outer d (<-wf d) h

-- Inversion for Acc: extract smaller accessibility proof
<Lex-inv : ∀ {p q} → Acc _<Lex_ p → q <Lex p → Acc _<Lex_ q
<Lex-inv (acc f) lt = f _ lt

-- =============================================================================
-- Degree Decrease Lemmas for Principal Cases
-- =============================================================================
-- In principal cases, the cut formula A is decomposed into subformulas.
-- These lemmas prove that subformula degrees are strictly smaller.

-- Conjunction: degree B < degree (B ∧ C) and degree C < degree (B ∧ C)
degree-∧-l : ∀ B C → degree B < degree (B ∧ C)
degree-∧-l B C = n<suc-max-l (degree B) (degree C)

degree-∧-r : ∀ B C → degree C < degree (B ∧ C)
degree-∧-r B C = n<suc-max-r (degree B) (degree C)

-- Disjunction: degree B < degree (B ∨ C) and degree C < degree (B ∨ C)
degree-∨-l : ∀ B C → degree B < degree (B ∨ C)
degree-∨-l B C = n<suc-max-l (degree B) (degree C)

degree-∨-r : ∀ B C → degree C < degree (B ∨ C)
degree-∨-r B C = n<suc-max-r (degree B) (degree C)

-- Implication: degree B < degree (B ⇒ C) and degree C < degree (B ⇒ C)
degree-⇒-l : ∀ B C → degree B < degree (B ⇒ C)
degree-⇒-l B C = n<suc-max-l (degree B) (degree C)

degree-⇒-r : ∀ B C → degree C < degree (B ⇒ C)
degree-⇒-r B C = n<suc-max-r (degree B) (degree C)

-- Negation: degree B < degree (¬ B)
degree-¬ : ∀ B → degree B < degree (¬ B)
degree-¬ B = n<suc-n (degree B)

-- Box: degree B < degree (□ B)
degree-□ : ∀ B → degree B < degree (□ B)
degree-□ B = n<suc-n (degree B)

-- Diamond: degree B < degree (♢ B)
degree-♢ : ∀ B → degree B < degree (♢ B)
degree-♢ B = n<suc-n (degree B)

-- Formula injectivity lemmas (for principal case restructuring)
-- In Cubical Agda we use J instead of pattern matching on refl

private
  -- Helper to extract left component of ∨
  ∨-get-l : Formula → Formula → Formula
  ∨-get-l (A ∨ _) _ = A
  ∨-get-l _ default = default

  -- Helper to extract right component of ∨
  ∨-get-r : Formula → Formula → Formula
  ∨-get-r (_ ∨ B) _ = B
  ∨-get-r _ default = default

  -- Helper to extract left component of ∧
  ∧-get-l : Formula → Formula → Formula
  ∧-get-l (A ∧ _) _ = A
  ∧-get-l _ default = default

  -- Helper to extract right component of ∧
  ∧-get-r : Formula → Formula → Formula
  ∧-get-r (_ ∧ B) _ = B
  ∧-get-r _ default = default

  -- Helper to extract left component of ⇒
  ⇒-get-l : Formula → Formula → Formula
  ⇒-get-l (A ⇒ _) _ = A
  ⇒-get-l _ default = default

  -- Helper to extract right component of ⇒
  ⇒-get-r : Formula → Formula → Formula
  ⇒-get-r (_ ⇒ B) _ = B
  ⇒-get-r _ default = default

  -- Helper to extract inner formula of ¬
  ¬-get : Formula → Formula → Formula
  ¬-get (¬ A) _ = A
  ¬-get _ default = default

  -- Helper to extract inner formula of □
  □-get : Formula → Formula → Formula
  □-get (□ A) _ = A
  □-get _ default = default

  -- Helper to extract inner formula of ♢
  ♢-get : Formula → Formula → Formula
  ♢-get (♢ A) _ = A
  ♢-get _ default = default

∨-inj-l : ∀ {A B C D'} → A ∨ B ≡ C ∨ D' → A ≡ C
∨-inj-l {A} {B} {C} {D'} eq =
  J (λ x _ → ∨-get-l (A ∨ B) A ≡ ∨-get-l x C) refl eq

∨-inj-r : ∀ {A B C D'} → A ∨ B ≡ C ∨ D' → B ≡ D'
∨-inj-r {A} {B} {C} {D'} eq =
  J (λ x _ → ∨-get-r (A ∨ B) B ≡ ∨-get-r x D') refl eq

∧-inj-l : ∀ {A B C D'} → A ∧ B ≡ C ∧ D' → A ≡ C
∧-inj-l {A} {B} {C} {D'} eq =
  J (λ x _ → ∧-get-l (A ∧ B) A ≡ ∧-get-l x C) refl eq

∧-inj-r : ∀ {A B C D'} → A ∧ B ≡ C ∧ D' → B ≡ D'
∧-inj-r {A} {B} {C} {D'} eq =
  J (λ x _ → ∧-get-r (A ∧ B) B ≡ ∧-get-r x D') refl eq

⇒-inj-l : ∀ {A B C D'} → A ⇒ B ≡ C ⇒ D' → A ≡ C
⇒-inj-l {A} {B} {C} {D'} eq =
  J (λ x _ → ⇒-get-l (A ⇒ B) A ≡ ⇒-get-l x C) refl eq

⇒-inj-r : ∀ {A B C D'} → A ⇒ B ≡ C ⇒ D' → B ≡ D'
⇒-inj-r {A} {B} {C} {D'} eq =
  J (λ x _ → ⇒-get-r (A ⇒ B) B ≡ ⇒-get-r x D') refl eq

¬-inj : ∀ {A B} → ¬ A ≡ ¬ B → A ≡ B
¬-inj {A} {B} eq =
  J (λ x _ → ¬-get (¬ A) A ≡ ¬-get x B) refl eq

□-inj : ∀ {A B} → □ A ≡ □ B → A ≡ B
□-inj {A} {B} eq =
  J (λ x _ → □-get (□ A) A ≡ □-get x B) refl eq

♢-inj : ∀ {A B} → ♢ A ≡ ♢ B → A ≡ B
♢-inj {A} {B} eq =
  J (λ x _ → ♢-get (♢ A) A ≡ ♢-get x B) refl eq

-- =============================================================================
-- Subformula Inequality Lemmas for Cross-Cuts (Girard's Approach)
-- =============================================================================
-- In principal cases, we need to prove B^s ≢ (B∧C)^s etc., so that
-- removeAll on A = B∧C preserves occurrences of B (since B ≠ A).

-- Helper: lift formula inequality to PFormula inequality
pf-neq-from-form-neq : ∀ {A B : Formula} {s t : Position} → A ≢ B → (A ^ s) ≢ (B ^ t)
pf-neq-from-form-neq A≢B pf-eq = A≢B (cong PFormula.form pf-eq)

-- Subformula inequalities using degree (lifted to PFormula)
-- These are used to show that removeAll on compound formula A = B∧C
-- preserves occurrences of subformula B (since B ≠ A).

subformula-neq-∧-l : ∀ {B C s t} → (B ^ s) ≢ ((B ∧ C) ^ t)
subformula-neq-∧-l {B} {C} = pf-neq-from-form-neq (neq-from-degree (degree-∧-l B C))

subformula-neq-∧-r : ∀ {B C s t} → (C ^ s) ≢ ((B ∧ C) ^ t)
subformula-neq-∧-r {B} {C} = pf-neq-from-form-neq (neq-from-degree (degree-∧-r B C))

subformula-neq-∨-l : ∀ {B C s t} → (B ^ s) ≢ ((B ∨ C) ^ t)
subformula-neq-∨-l {B} {C} = pf-neq-from-form-neq (neq-from-degree (degree-∨-l B C))

subformula-neq-∨-r : ∀ {B C s t} → (C ^ s) ≢ ((B ∨ C) ^ t)
subformula-neq-∨-r {B} {C} = pf-neq-from-form-neq (neq-from-degree (degree-∨-r B C))

subformula-neq-⇒-l : ∀ {B C s t} → (B ^ s) ≢ ((B ⇒ C) ^ t)
subformula-neq-⇒-l {B} {C} = pf-neq-from-form-neq (neq-from-degree (degree-⇒-l B C))

subformula-neq-⇒-r : ∀ {B C s t} → (C ^ s) ≢ ((B ⇒ C) ^ t)
subformula-neq-⇒-r {B} {C} = pf-neq-from-form-neq (neq-from-degree (degree-⇒-r B C))

subformula-neq-¬ : ∀ {B s t} → (B ^ s) ≢ ((¬ B) ^ t)
subformula-neq-¬ {B} = pf-neq-from-form-neq (neq-from-degree (degree-¬ B))

subformula-neq-□ : ∀ {B s t} → (B ^ s) ≢ ((□ B) ^ t)
subformula-neq-□ {B} = pf-neq-from-form-neq (neq-from-degree (degree-□ B))

subformula-neq-♢ : ∀ {B s t} → (B ^ s) ≢ ((♢ B) ^ t)
subformula-neq-♢ {B} = pf-neq-from-form-neq (neq-from-degree (degree-♢ B))

-- =============================================================================
-- Cross-Cut Height Lemmas
-- =============================================================================
-- For Girard's cross-cuts approach, we need to show that using a subproof
-- gives a strictly smaller mixHeight.

-- For ⊢∧: height of left premise is smaller than height of ⊢∧
height-⊢∧-l : ∀ {Γ₁ Δ₁ Γ₂ Δ₂ A B s}
             (Π₁ : Γ₁ ⊢ [ A ^ s ] ,, Δ₁) (Π₂ : Γ₂ ⊢ [ B ^ s ] ,, Δ₂)
           → height Π₁ < height (⊢∧ Π₁ Π₂)
height-⊢∧-l Π₁ Π₂ = height-subproof-2-l Π₁ Π₂

height-⊢∧-r : ∀ {Γ₁ Δ₁ Γ₂ Δ₂ A B s}
             (Π₁ : Γ₁ ⊢ [ A ^ s ] ,, Δ₁) (Π₂ : Γ₂ ⊢ [ B ^ s ] ,, Δ₂)
           → height Π₂ < height (⊢∧ Π₁ Π₂)
height-⊢∧-r Π₁ Π₂ = height-subproof-2-r Π₁ Π₂

-- For ∧₁⊢/∧₂⊢: height of premise is smaller than height of rule application
height-∧₁⊢ : ∀ {Γ Δ A B s} (Π : Γ ,, [ A ^ s ] ⊢ Δ)
           → height Π < height (∧₁⊢ {B = B} Π)
height-∧₁⊢ Π = height-subproof-1 Π

height-∧₂⊢ : ∀ {Γ Δ A B s} (Π : Γ ,, [ B ^ s ] ⊢ Δ)
           → height Π < height (∧₂⊢ {A = A} Π)
height-∧₂⊢ Π = height-subproof-1 Π

-- For ∨⊢: height of each premise is smaller
height-∨⊢-l : ∀ {Γ₁ Δ₁ Γ₂ Δ₂ A B s}
             (Π₁ : Γ₁ ,, [ A ^ s ] ⊢ Δ₁) (Π₂ : Γ₂ ,, [ B ^ s ] ⊢ Δ₂)
           → height Π₁ < height (∨⊢ Π₁ Π₂)
height-∨⊢-l Π₁ Π₂ = height-subproof-2-l Π₁ Π₂

height-∨⊢-r : ∀ {Γ₁ Δ₁ Γ₂ Δ₂ A B s}
             (Π₁ : Γ₁ ,, [ A ^ s ] ⊢ Δ₁) (Π₂ : Γ₂ ,, [ B ^ s ] ⊢ Δ₂)
           → height Π₂ < height (∨⊢ Π₁ Π₂)
height-∨⊢-r Π₁ Π₂ = height-subproof-2-r Π₁ Π₂

-- For ⊢∨₁/⊢∨₂: height of premise is smaller
height-⊢∨₁ : ∀ {Γ Δ A B s} (Π : Γ ⊢ [ A ^ s ] ,, Δ)
           → height Π < height (⊢∨₁ {B = B} Π)
height-⊢∨₁ Π = height-subproof-1 Π

height-⊢∨₂ : ∀ {Γ Δ A B s} (Π : Γ ⊢ [ B ^ s ] ,, Δ)
           → height Π < height (⊢∨₂ {A = A} Π)
height-⊢∨₂ Π = height-subproof-1 Π

-- For ⇒⊢: height of each premise is smaller
-- Note: ⇒⊢ Π₁ Π₂ where Π₁ : Γ₁ ,, [ B ^ s ] ⊢ Δ₁ and Π₂ : Γ₂ ⊢ [ A ^ s ] ,, Δ₂
height-⇒⊢-l : ∀ {Γ₁ Δ₁ Γ₂ Δ₂ A B s}
             (Π₁ : Γ₁ ,, [ B ^ s ] ⊢ Δ₁) (Π₂ : Γ₂ ⊢ [ A ^ s ] ,, Δ₂)
           → height Π₁ < height (⇒⊢ Π₁ Π₂)
height-⇒⊢-l Π₁ Π₂ = height-subproof-2-l Π₁ Π₂

height-⇒⊢-r : ∀ {Γ₁ Δ₁ Γ₂ Δ₂ A B s}
             (Π₁ : Γ₁ ,, [ B ^ s ] ⊢ Δ₁) (Π₂ : Γ₂ ⊢ [ A ^ s ] ,, Δ₂)
           → height Π₂ < height (⇒⊢ Π₁ Π₂)
height-⇒⊢-r Π₁ Π₂ = height-subproof-2-r Π₁ Π₂

-- For ⊢⇒: height of premise is smaller
height-⊢⇒ : ∀ {Γ Δ A B s} (Π : Γ ,, [ A ^ s ] ⊢ [ B ^ s ] ,, Δ)
          → height Π < height (⊢⇒ Π)
height-⊢⇒ Π = height-subproof-1 Π

-- For ¬⊢/⊢¬: height of premise is smaller
height-¬⊢ : ∀ {Γ Δ A s} (Π : Γ ⊢ [ A ^ s ] ,, Δ)
          → height Π < height (¬⊢ Π)
height-¬⊢ Π = height-subproof-1 Π

height-⊢¬ : ∀ {Γ Δ A s} (Π : Γ ,, [ A ^ s ] ⊢ Δ)
          → height Π < height (⊢¬ Π)
height-⊢¬ Π = height-subproof-1 Π

-- For □⊢/⊢□ and ♢⊢/⊢♢: height lemmas deferred
-- The modal rules have complex position dependencies that make generic height
-- lemmas harder to state. For now, we'll handle them case-by-case in Mix.agda
-- using height-subproof-1 directly.
