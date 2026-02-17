{-# OPTIONS --cubical --safe #-}

-- Helper lemmas for Mix.agda
-- Extracted to keep Mix.agda focused on MixLemma/LemmaMix definitions

module S4dot2.CutElimination.MixHelpers where

open import Cubical.Foundations.Prelude using (Type; _≡_; refl; sym; cong; cong₂; subst; transport; _∙_; J; substRefl)
open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Cubical.Data.Empty renaming (rec to emptyRec; elim to ⊥-elim) using (⊥)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.List using (List; _∷_; []; map; _++_)
open import Cubical.Data.List.Properties using (++-assoc; ++-unit-r)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd)
open import Cubical.Relation.Nullary using (Dec; yes; no) renaming (¬_ to Neg)
open import Cubical.Data.Nat using (ℕ; _+_; suc; zero)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Unit using (Unit; tt)

open import S4dot2.Syntax hiding (_⊢_; _≢_)
open import S4dot2.System

open import S4dot2.CutElimination.Base
open import S4dot2.Solver.Subset hiding (_≢_)
open import S4dot2.CutElimination.ProofSubst using (maxEigenposToken)

-- =============================================================================
-- RemoveAll Helper Lemmas
-- =============================================================================

-- When A ≡ B, removing A from (Γ ++ [B]) gives (Γ - A)
lemma-removeAll-cons-eq : ∀ {A B : PFormula} {Γ : Ctx} → A ≡ B → (Γ ++ [ B ]) - A ≡ Γ - A
lemma-removeAll-cons-eq {A} {B} {Γ} eq = lemma-removeAll-eq {A} {B} {Γ} eq

-- When A ≢ B, removing A from (Γ ++ [B]) gives (Γ - A) ++ [B]
lemma-removeAll-cons-neq : ∀ {A B : PFormula} {Γ : Ctx} → A ≢ B → (Γ ++ [ B ]) - A ≡ (Γ - A) ++ [ B ]
lemma-removeAll-cons-neq {A} {B} {Γ} neq = removeAll-++-r-pf-neq {A} {B} {Γ} neq

-- When A ≡ B, removing A from (B ∷ Γ) gives (Γ - A)
lemma-removeAll-head-eq : ∀ {A B : PFormula} {Γ : Ctx} → A ≡ B → (B ∷ Γ) - A ≡ Γ - A
lemma-removeAll-head-eq {A} {B} {Γ} eq = removeAll-yes A B Γ eq

-- When A ≢ B, removing A from (B ∷ Γ) gives B ∷ (Γ - A)
lemma-removeAll-head-neq : ∀ {A B : PFormula} {Γ : Ctx} → A ≢ B → (B ∷ Γ) - A ≡ B ∷ (Γ - A)
lemma-removeAll-head-neq {A} {B} {Γ} neq = removeAll-no A B Γ neq

-- Lemma for [ B ] ,, Γ pattern (accounts for [] ++ in expansion)
lemma-removeAll-singleton-neq : ∀ {A B : PFormula} {Γ : Ctx} → A ≢ B → (([ B ] ,, Γ) - A) ≡ ([ B ] ,, (Γ - A))
lemma-removeAll-singleton-neq {A} {B} {Γ} neq = removeAll-no A B Γ neq

-- Helper: singleton ,, removes the [] ++ pattern issue
singleton-,,-eq : ∀ {B : PFormula} {Γ : Ctx} → ([ B ] ,, Γ) ≡ (B ∷ Γ)
singleton-,,-eq = refl

-- removeAll with yes condition for exchange cases
lemma-removeAll-yes-cond : ∀ {A B : PFormula} {Γ : Ctx} → A ≡ B → ((Γ ,, [ B ]) - A) ≡ (Γ - A)
lemma-removeAll-yes-cond {A} {B} {Γ} eq = lemma-removeAll-cons-eq {A} {B} {Γ} eq


-- =============================================================================
-- Token/Position Helper Lemmas
-- =============================================================================

-- Key lemma: If x ∉ t and ((s ∘ singleton-pos x) ∘ r) ⊑ t, contradiction
subset-needs-token : ∀ {x : Token} {s r t : Position}
                   → x ∉Pos t
                   → Neg (((s ∘ singleton-pos x) ∘ r) ⊑ t)
subset-needs-token {x} {s} {r} {t} x∉t sub = x∉t (sub x x∈merged)
  where
    -- x is in singleton-pos x
    x∈singleton : x ∈Pos (singleton-pos x)
    x∈singleton = insertToken-∈Pos x x ε (inl refl)
    -- x is in s ∘ singleton-pos x (right component of merge)
    x∈s∘singleton : x ∈Pos (s ∘ singleton-pos x)
    x∈s∘singleton = merge-∈Pos-r x s (singleton-pos x) x∈singleton
    -- x is in (s ∘ singleton-pos x) ∘ r (left component of merge)
    x∈merged : x ∈Pos ((s ∘ singleton-pos x) ∘ r)
    x∈merged = merge-∈Pos-l x (s ∘ singleton-pos x) r x∈s∘singleton

-- Helper: Construct IsSingleTokenExt from x ∉Pos s
mkSingleTokenExt : ∀ (s : Position) (x : Token) → x ∉Pos s → IsSingleTokenExt s (insertToken x s) x
mkSingleTokenExt s x x∉s = (sub , x∈extPos , x∉s , unique)
  where
    extPos = insertToken x s
    -- s ⊑ insertToken x s (inserting x preserves existing elements)
    sub : s ⊑ extPos
    sub t t∈s = insertToken-∈Pos x t s (inr t∈s)
    -- x ∈Pos (insertToken x s)
    x∈extPos : x ∈Pos extPos
    x∈extPos = insertToken-∈Pos x x s (inl refl)
    -- Uniqueness: the only element in extPos but not in s is x
    unique : ∀ t → t ∈Pos extPos → t ∉Pos s → t ≡ x
    unique t t∈extPos t∉s with ∈Pos-insertToken x t s t∈extPos
    ... | inl t≡x = t≡x
    ... | inr t∈s = emptyRec (t∉s t∈s)

-- TokenFresh implies IsEigenposition
TokenFresh→IsEigenposition : ∀ {s : Position} {x : Token} {Γ Δ : Ctx}
  → TokenFresh x (Γ ,, Δ)
  → IsEigenposition s x Γ Δ
TokenFresh→IsEigenposition {s} {x} {Γ} {Δ} fresh (pf , pf∈ , sub) =
  let x∈singleton : x ∈Pos (singleton-pos x)
      x∈singleton = insertToken-∈Pos x x ε (inl refl)
      x∈merged : x ∈Pos (s ∘ singleton-pos x)
      x∈merged = merge-∈Pos-r x s (singleton-pos x) x∈singleton
      x∈pf : x ∈Pos (PFormula.pos pf)
      x∈pf = sub x x∈merged
      x∉pf : x ∉Pos (PFormula.pos pf)
      x∉pf = helper (Γ ++ Δ) pf∈ fresh
  in x∉pf x∈pf
  where
    helper : (ctx : Ctx) → pf ∈ ctx → TokenFresh x ctx → x ∉Pos (PFormula.pos pf)
    helper (qf ∷ ctx) here (freshQf , freshRest) = freshQf
    helper (qf ∷ ctx) (there mem) (freshQf , freshRest) = helper ctx mem freshRest

-- Combine eigenposition from one derivation with token freshness from another
eigenpos-extend-cross : ∀ {s : Position} {x : Token} {Γ Δ Γ' Δ' : Ctx}
  → IsEigenposition s x Γ Δ
  → TokenFresh x (Γ' ,, Δ')
  → IsEigenposition s x (Γ ,, Γ') (Δ ,, Δ')
eigenpos-extend-cross {s} {x} {Γ} {Δ} {Γ'} {Δ'} eigenOrig freshExt inInit =
  case inInit of λ { (pf , pf∈ , pre) →
    split-mem pf pf∈ pre
  }
  where
    split-mem : (pf : PFormula) → pf ∈ ((Γ ++ Γ') ++ (Δ ++ Δ'))
              → (s ∘ singleton-pos x) ⊑ PFormula.pos pf → ⊥
    split-mem pf mem pre with mem-++-split {xs = Γ ++ Γ'} {ys = Δ ++ Δ'} mem
    ... | inl memL with mem-++-split {xs = Γ} {ys = Γ'} memL
    ...   | inl memΓ = eigenOrig (pf , mem-++-l memΓ , pre)
    ...   | inr memΓ' = TokenFresh→IsEigenposition {s = s} {Γ = Γ'} {Δ = []}
                          (subst (TokenFresh x) (sym (++-unit-r Γ')) (TokenFresh-fst Γ' Δ' freshExt))
                          (pf , subst (pf ∈_) (sym (++-unit-r Γ')) memΓ' , pre)
      where
        TokenFresh-fst : (A B : Ctx) → TokenFresh x (A ,, B) → TokenFresh x A
        TokenFresh-fst [] B _ = tt
        TokenFresh-fst (qf ∷ as) B (freshQf , rest) = freshQf , TokenFresh-fst as B rest
    split-mem pf mem pre | inr memR with mem-++-split {xs = Δ} {ys = Δ'} memR
    ...   | inl memΔ = eigenOrig (pf , mem-++-r Γ memΔ , pre)
    ...   | inr memΔ' = TokenFresh→IsEigenposition {s = s} {Γ = Δ'} {Δ = []}
                          (subst (TokenFresh x) (sym (++-unit-r Δ')) (TokenFresh-snd Γ' Δ' freshExt))
                          (pf , subst (pf ∈_) (sym (++-unit-r Δ')) memΔ' , pre)
      where
        TokenFresh-snd : (A B : Ctx) → TokenFresh x (A ,, B) → TokenFresh x B
        TokenFresh-snd [] B freshB = freshB
        TokenFresh-snd (_ ∷ as) B (_ , rest) = TokenFresh-snd as B rest


-- =============================================================================
-- Context Rearrangement Helpers
-- =============================================================================

-- Move element from front to back within prefix
send-back-at-left : ∀ {Δ B t Γ2} (prefix : Ctx) (Γ1 : Ctx) → (((prefix ,, [ B ^ t ]) ,, Γ1) ,, Γ2 ⊢ Δ) → (((prefix ,, Γ1) ,, [ B ^ t ]) ,, Γ2 ⊢ Δ)
send-back-at-left {_} {B} {t} {Γ2} prefix Γ1 p =
    let sub : (((prefix ,, [ B ^ t ]) ,, Γ1) ,, Γ2) ⊆ (((prefix ,, Γ1) ,, [ B ^ t ]) ,, Γ2)
        sub = solve (((var 0 ++ₑ elm 0) ++ₑ var 1) ++ₑ var 2) (((var 0 ++ₑ var 1) ++ₑ elm 0) ++ₑ var 2) ((prefix ∷ Γ1 ∷ Γ2 ∷ []) , (B ^ t ∷ [])) {refl}
    in structural sub subset-refl p

-- Move element from back to front within prefix
bring-to-front-at-left : ∀ {Δ B t Γ2} (prefix : Ctx) (Γ1 : Ctx) → (((prefix ,, Γ1) ,, [ B ^ t ]) ,, Γ2 ⊢ Δ) → (((prefix ,, [ B ^ t ]) ,, Γ1) ,, Γ2 ⊢ Δ)
bring-to-front-at-left {_} {B} {t} {Γ2} prefix Γ1 p =
    let sub : (((prefix ,, Γ1) ,, [ B ^ t ]) ,, Γ2) ⊆ (((prefix ,, [ B ^ t ]) ,, Γ1) ,, Γ2)
        sub = solve (((var 0 ++ₑ var 1) ++ₑ elm 0) ++ₑ var 2) (((var 0 ++ₑ elm 0) ++ₑ var 1) ++ₑ var 2) ((prefix ∷ Γ1 ∷ Γ2 ∷ []) , (B ^ t ∷ [])) {refl}
    in structural sub subset-refl p

-- Degree preservation for send-back
send-back-at-left-preserves-δ : ∀ {Δ B t Γ2} (prefix : Ctx) (Γ1 : Ctx) (p : ((prefix ,, [ B ^ t ]) ,, Γ1) ,, Γ2 ⊢ Δ) → δ (send-back-at-left prefix Γ1 p) ≡ δ p
send-back-at-left-preserves-δ {_} {B} {t} {Γ2} prefix Γ1 p =
    let sub : (((prefix ,, [ B ^ t ]) ,, Γ1) ,, Γ2) ⊆ (((prefix ,, Γ1) ,, [ B ^ t ]) ,, Γ2)
        sub = solve (((var 0 ++ₑ elm 0) ++ₑ var 1) ++ₑ var 2) (((var 0 ++ₑ var 1) ++ₑ elm 0) ++ₑ var 2) ((prefix ∷ Γ1 ∷ Γ2 ∷ []) , (B ^ t ∷ [])) {refl}
    in structural-preserves-δ sub subset-refl p

-- Degree preservation for bring-to-front
bring-to-front-at-left-preserves-δ : ∀ {Δ B t Γ2} (prefix : Ctx) (Γ1 : Ctx) (p : ((prefix ,, Γ1) ,, [ B ^ t ]) ,, Γ2 ⊢ Δ) → δ (bring-to-front-at-left prefix Γ1 p) ≡ δ p
bring-to-front-at-left-preserves-δ {_} {B} {t} {Γ2} prefix Γ1 p =
    let sub : (((prefix ,, Γ1) ,, [ B ^ t ]) ,, Γ2) ⊆ (((prefix ,, [ B ^ t ]) ,, Γ1) ,, Γ2)
        sub = solve (((var 0 ++ₑ var 1) ++ₑ elm 0) ++ₑ var 2) (((var 0 ++ₑ elm 0) ++ₑ var 1) ++ₑ var 2) ((prefix ∷ Γ1 ∷ Γ2 ∷ []) , (B ^ t ∷ [])) {refl}
    in structural-preserves-δ sub subset-refl p


-- =============================================================================
-- Exchange Case Lemmas
-- =============================================================================

-- When we remove A which equals one of two swapped elements (left)
lemma-removeAll-yes-cond-left : ∀ {A B C : PFormula} {Δ1 Δ2 : Ctx}
  → A ≡ B
  → ((((Δ1 ,, [ B ]) ,, [ C ]) ,, Δ2) - A) ≡ ((((Δ1 ,, [ C ]) ,, [ B ]) ,, Δ2) - A)
lemma-removeAll-yes-cond-left {A} {B} {C} {Δ1} {Δ2} eq =
  let lhs-step1 = S4dot2.CutElimination.Base.removeAll-++ A (((Δ1 ++ [ B ]) ++ [ C ])) Δ2
      lhs-step2 = S4dot2.CutElimination.Base.removeAll-++ A ((Δ1 ++ [ B ])) [ C ]
      lhs-step3 = S4dot2.CutElimination.Base.removeAll-++ A Δ1 [ B ]
      lhs-step4 = removeAll-singleton-eq eq

      rhs-step1 = S4dot2.CutElimination.Base.removeAll-++ A (((Δ1 ++ [ C ]) ++ [ B ])) Δ2
      rhs-step2 = S4dot2.CutElimination.Base.removeAll-++ A ((Δ1 ++ [ C ])) [ B ]
      rhs-step3 = S4dot2.CutElimination.Base.removeAll-++ A Δ1 [ C ]
      rhs-step4 = removeAll-singleton-eq eq

      lhs-simp = trans lhs-step1 (cong (_++ (Δ2 - A)) (trans lhs-step2 (cong (_++ ([ C ] - A)) (trans lhs-step3 (cong ((Δ1 - A) ++_) lhs-step4)))))
      rhs-simp = trans rhs-step1 (cong (_++ (Δ2 - A)) (trans rhs-step2 (cong ((Δ1 ++ [ C ]) - A ++_) rhs-step4 ∙ cong (_++ []) rhs-step3)))

      eq1 = cong (λ x → (x ++ ([ C ] - A)) ++ (Δ2 - A)) (++-unit-r (Δ1 - A))
      eq2 = cong (_++ (Δ2 - A)) (++-unit-r ((Δ1 - A) ++ ([ C ] - A)))

  in trans lhs-simp (trans eq1 (sym (trans rhs-simp eq2)))

-- When we remove A which equals one of two swapped elements (right)
lemma-removeAll-yes-cond-right-left : ∀ {A B C : PFormula} {Δ1 Δ2 : Ctx}
  → A ≡ C
  → ((((Δ1 ,, [ B ]) ,, [ C ]) ,, Δ2) - A) ≡ ((((Δ1 ,, [ C ]) ,, [ B ]) ,, Δ2) - A)
lemma-removeAll-yes-cond-right-left {A} {B} {C} {Δ1} {Δ2} eq =
  let lhs-step1 = S4dot2.CutElimination.Base.removeAll-++ A (((Δ1 ++ [ B ]) ++ [ C ])) Δ2
      lhs-step2 = S4dot2.CutElimination.Base.removeAll-++ A ((Δ1 ++ [ B ])) [ C ]
      lhs-step3 = S4dot2.CutElimination.Base.removeAll-++ A Δ1 [ B ]
      lhs-step4 = removeAll-singleton-eq eq

      rhs-step1 = S4dot2.CutElimination.Base.removeAll-++ A (((Δ1 ++ [ C ]) ++ [ B ])) Δ2
      rhs-step2 = S4dot2.CutElimination.Base.removeAll-++ A ((Δ1 ++ [ C ])) [ B ]
      rhs-step3 = S4dot2.CutElimination.Base.removeAll-++ A Δ1 [ C ]
      rhs-step4 = removeAll-singleton-eq eq

      lhs-simp = trans lhs-step1 (cong (_++ (Δ2 - A)) (trans lhs-step2 (cong (((Δ1 ++ [ B ]) - A) ++_) lhs-step4 ∙ cong (_++ []) lhs-step3)))
      rhs-simp = trans rhs-step1 (cong (_++ (Δ2 - A)) (trans rhs-step2 (cong (_++ ([ B ] - A)) (trans rhs-step3 (cong ((Δ1 - A) ++_) rhs-step4)))))

      eq1 = cong (_++ (Δ2 - A)) (++-unit-r ((Δ1 - A) ++ ([ B ] - A)))
      eq2 = cong (λ x → (x ++ ([ B ] - A)) ++ (Δ2 - A)) (++-unit-r (Δ1 - A))

  in trans lhs-simp (trans eq1 (sym (trans rhs-simp eq2)))

-- Distribute removeAll over concatenation when removing element not in appended parts
removeAll-++-distrib-neq : ∀ {A B C : PFormula} {Δ1 Δ2 : Ctx}
  → A ≢ B → A ≢ C
  → ((((Δ1 ,, [ B ]) ,, [ C ]) ,, Δ2) - A) ≡ ((((Δ1 - A) ,, [ B ]) ,, [ C ]) ,, (Δ2 - A))
removeAll-++-distrib-neq {A} {B} {C} {Δ1} {Δ2} neqB neqC =
  let step1 = S4dot2.CutElimination.Base.removeAll-++ A (((Δ1 ++ [ B ]) ++ [ C ])) Δ2
      step2 = S4dot2.CutElimination.Base.removeAll-++ A ((Δ1 ++ [ B ])) [ C ]
      step3 = S4dot2.CutElimination.Base.removeAll-++ A Δ1 [ B ]
      step4B = removeAll-singleton-neq neqB
      step4C = removeAll-singleton-neq neqC

      lhs-simp : (((Δ1 ++ [ B ]) ++ [ C ]) ++ Δ2) - A ≡ (((Δ1 - A) ++ [ B ]) ++ [ C ]) ++ (Δ2 - A)
      lhs-simp = trans step1 (cong (_++ (Δ2 - A)) (trans step2 (cong₂ _++_ (trans step3 (cong ((Δ1 - A) ++_) step4B)) step4C)))

  in lhs-simp


-- =============================================================================
-- Formula Inequality Helpers
-- =============================================================================

-- degree (□ A) = suc (degree A) > degree A, so □ A ≠ A
box-neq-inner : ∀ A → □ A ≢ A
box-neq-inner A eq = neq-from-degree {A} {□ A} (0 , refl) (sym eq)

-- degree (♢ A) = suc (degree A) > degree A, so ♢ A ≠ A
dia-neq-inner : ∀ A → ♢ A ≢ A
dia-neq-inner A eq = neq-from-degree {A} {♢ A} (0 , refl) (sym eq)

-- PFormula version: if forms differ, PFormulas differ
pformula-form-neq : ∀ {A B : Formula} {s t : Position} → A ≢ B → (A ^ s) ≢ (B ^ t)
pformula-form-neq neq eq = neq (cong PFormula.form eq)

-- Box formula at position r differs from subformula at position (r ∘ singleton-pos x)
box-pformula-neq-inner : ∀ {A : Formula} {r : Position} {x : Token} → ((□ A) ^ r) ≢ (A ^ (r ∘ singleton-pos x))
box-pformula-neq-inner eq = box-neq-inner _ (cong PFormula.form eq)

-- Diamond formula at position r differs from subformula at any position t
dia-pformula-neq-inner : ∀ {A : Formula} {r t : Position} → ((♢ A) ^ r) ≢ (A ^ t)
dia-pformula-neq-inner eq = dia-neq-inner _ (cong PFormula.form eq)


-- =============================================================================
-- Cross-Derivation Token Freshness Postulate
-- =============================================================================
--
-- SEMANTIC INVARIANT: When combining two derivations Π and Π' in MixLemma/LemmaMix,
-- eigenposition tokens introduced in one derivation do not appear in any position
-- of the other derivation's contexts.
--
-- JUSTIFICATION (from the paper, Proposition 3 - Eigenposition Renaming):
-- "Given a proof Π of an e-sequent Γ ⊢ Δ, we may always find a proof Π' ending
-- with Γ ⊢ Δ where all eigenpositions are distinct from one another.
-- In practice we will freely use such a renaming all the times it is necessary
-- (or, in other words, proofs are de facto equivalence classes modulo renaming
-- of eigenpositions)."
--
-- This postulate captures that we can always rename eigenposition tokens to be
-- fresh before combining proofs.
--
-- =============================================================================
-- HOW TO MAKE THIS CONSTRUCTIVE
-- =============================================================================
--
-- The constructive eigenposition infrastructure in ProofSubst.agda provides:
--
-- 1. Fresh token computation:
--    - freshTokenCtx : Ctx → Token
--    - freshTokenCtx-is-fresh : TokenFresh (freshTokenCtx Γ) Γ
--
-- 2. Eigenposition renaming:
--    - renameEigenpos-⊢□ : renames eigenposition token in ⊢□ premise
--    - renameEigenpos-♢⊢ : renames eigenposition token in ♢⊢ premise
--
-- 3. Combined fresh eigenposition:
--    - freshEigenpos-⊢□ : computes fresh token and renames proof
--    - freshEigenpos-♢⊢ : computes fresh token and renames proof
--
-- TO MAKE MixLemma FULLY CONSTRUCTIVE:
-- The eigenposition renaming must happen BEFORE the recursive mix call:
--
--   In ⊢□ case: Before recursively calling MixLemma on Π_sub
--   1. Compute x' = freshTokenCtx (all combined contexts)
--   2. Apply renameEigenpos-⊢□ to Π_sub to get Π_sub'
--   3. Recursively mix Π_sub' with Π'
--   4. Apply ⊢□ with token x' (provably fresh in combined contexts)
--
-- This restructuring is non-trivial as it requires changing the recursive
-- structure of MixLemma. The postulate below is a placeholder that captures
-- the semantic guarantee while avoiding this restructuring.
--
-- NOTE: The file still compiles with --safe. The postulates in ProofSubst.agda
-- (eigenpos-subst-ctx-id, subst-same-pos) are also well-justified semantic lemmas.

-- =============================================================================
-- Note: Eigenposition Well-Formedness
-- =============================================================================
--
-- The well-formedness condition for eigenposition tokens (maxEigenposToken Π < x)
-- is now enforced via the WellFormedProof predicate in ProofSubst.agda.
-- MixLemma/LemmaMix require WellFormedProof as a precondition, eliminating the
-- need for postulates here.
--
-- See ProofSubst.agda for:
-- - WellFormedProof : Proof → Type (definition)
-- - makeWellFormed : ∀ Π → Proof (transforms any proof to well-formed)
-- - makeWellFormed-WellFormed : WellFormedProof (makeWellFormed Π)


-- =============================================================================
-- Degree Preservation under Position Substitution
-- =============================================================================

-- Degree preservation under subst over positions (δ ignores positions)
-- Proven using J: when eq = refl, subst P refl Π = Π, so δ is preserved

-- For antecedent (♢⊢ case)
δ-subst-pos-antecedent : ∀ {r t : Position} {Γ Δ : Ctx} {A : Formula}
  → (eq : t ≡ r)
  → (Π : (Γ ,, [ A ^ t ]) ⊢ Δ)
  → δ (subst (λ p → (Γ ,, [ A ^ p ]) ⊢ Δ) eq Π) ≡ δ Π
δ-subst-pos-antecedent {r} {t} {Γ} {Δ} {A} eq Π =
  J (λ r' eq' → δ (subst (λ p → (Γ ,, [ A ^ p ]) ⊢ Δ) eq' Π) ≡ δ Π)
    (cong δ (substRefl {B = λ p → (Γ ,, [ A ^ p ]) ⊢ Δ} Π))
    eq

-- For succedent (⊢□ case)
δ-subst-pos-succedent : ∀ {r t : Position} {Γ Δ : Ctx} {A : Formula}
  → (eq : t ≡ r)
  → (Π : Γ ⊢ ([ A ^ t ] ,, Δ))
  → δ (subst (λ p → Γ ⊢ ([ A ^ p ] ,, Δ)) eq Π) ≡ δ Π
δ-subst-pos-succedent {r} {t} {Γ} {Δ} {A} eq Π =
  J (λ r' eq' → δ (subst (λ p → Γ ⊢ ([ A ^ p ] ,, Δ)) eq' Π) ≡ δ Π)
    (cong δ (substRefl {B = λ p → Γ ⊢ ([ A ^ p ] ,, Δ)} Π))
    eq
