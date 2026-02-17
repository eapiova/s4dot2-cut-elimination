{-# OPTIONS --cubical --safe #-}

-- Weak completeness for S4.2 modal logic with positions.
-- Proves: if ⊢S4dot2 A then [] ⊢ [ A ^ ε ]

module S4dot2.Equivalence.HilbertCompleteness where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; suc-≤-suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)

open import S4dot2.Syntax hiding (_⊢_) renaming (_∧_ to _and_; _∨_ to _or_)
open import S4dot2.System
open import S4dot2.CutElimination.ProofSubst using (
  NoEigenposInt; NoEigenposInt-singleton-fresh; maxEigenposToken)

-- Position lifting: prepend t to position s via merge
-- This replaces the old s ⟦ [] ⇝ t ⟧ = t ++ s notation
-- For SDL-based positions, we use merge instead of list concatenation
_↑_ : Position → Position → Position
s ↑ t = t ∘ s

infixl 50 _↑_

-- Lift a position-formula by merging t with its position
liftPFormula : Position → PFormula → PFormula
liftPFormula t (A ^ s) = A ^ (t ∘ s)

-- Lift a context by applying liftPFormula to each position-formula
liftCtx : Position → Ctx → Ctx
liftCtx t = map (liftPFormula t)

-- Lifting Lemma (Proposition 4.1 in the paper)
-- "If Γ ⊢ Δ is provable, so is liftCtx t Γ ⊢ liftCtx t Δ"

-- We need some properties of substitution and Init to prove the eigenvariable conditions.

-- Subset relation is preserved under merge (position prepending)
-- For SDL, _⊑_ means ∀ t → t ∈Pos s → t ∈Pos r
merge-preserves-⊑ : ∀ (t : Position) {s r : Position}
                  → s ⊑ r
                  → (t ∘ s) ⊑ (t ∘ r)
merge-preserves-⊑ t {s} {r} sub y y∈ts with ∈Pos-merge y t s y∈ts
... | inl y∈t = merge-∈Pos-l y t r y∈t
... | inr y∈s = merge-∈Pos-r y t r (sub y y∈s)

-- 1. Init is preserved under substitution (forward direction)
init-lift-⇒ : ∀ {s Γ} {t : Position}
            → s ∈Init Γ
            → (t ∘ s) ∈Init (map (liftPFormula t) Γ)
init-lift-⇒ {s} {[]} {t} (pf , () , sub)
init-lift-⇒ {s} {x ∷ Γ} {t} (pf , here , sub) =
  liftPFormula t x , here , merge-preserves-⊑ t sub
init-lift-⇒ {s} {x ∷ Γ} {t} (pf , there inTail , sub) =
  let (rec-pf , rec-in , rec-sub) = init-lift-⇒ {s} {Γ} {t} (pf , inTail , sub)
  in rec-pf , there rec-in , rec-sub

-- Local map++ (for contexts, which are still Lists)
my-map++ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) (xs ys : List A) → map f (xs ++ ys) ≡ map f xs ++ map f ys
my-map++ f [] ys = refl
my-map++ f (x ∷ xs) ys = cong (f x ∷_) (my-map++ f xs ys)

-- Subset relation (for Position, using ⊑) is preserved under merge
-- This is the SDL version of subset-preserves-merge
subset-preserves-merge : ∀ (t : Position) {s r : Position}
                       → s ⊑ r
                       → (t ∘ s) ⊑ (t ∘ r)
subset-preserves-merge = merge-preserves-⊑

-- Helpers for IsSingleTokenExt and TokenFresh under position substitution
-- These are postulates justified by the fact that eigenposition tokens are fresh
-- and don't appear in lifting positions.

-- Membership preserved when merging: x ∈Pos s → x ∈Pos (t ∘ s)
mem-merge-r : ∀ {x : Token} {s t : Position} → x ∈Pos s → x ∈Pos (t ∘ s)
mem-merge-r {x} {s} {t} xIn = merge-∈Pos-r x t s xIn

-- Re-export ∉Pos-merge from SortedPosition as local alias
∉Pos-∘ : ∀ {x : Token} {s t : Position} → x ∉Pos s → x ∉Pos t → x ∉Pos (s ∘ t)
∉Pos-∘ = ∉Pos-merge

-- TokenFresh for empty context
TokenFresh-[] : ∀ {x : Token} → TokenFresh x []
TokenFresh-[] = tt

-- Helper for proving token inequality
-- 1 ≢ 0 in ℕ
1≢0 : 1 ≢ 0
1≢0 eq = subst (λ { ℕ.zero → ⊥ ; (ℕ.suc _) → Unit }) eq tt

-- Helper: 1 is not in (singleton-pos 0) = pos-cons 0 ε _
-- 1 ∈Pos (pos-cons 0 ε _) = (1 ≡ 0) ⊎ (1 ∈Pos ε) = (1 ≡ 0) ⊎ ⊥
1∉singleton0 : 1 ∉Pos (singleton-pos 0)
1∉singleton0 (inl 1≡0) = 1≢0 1≡0
1∉singleton0 (inr ())

-- Helper: construct IsSingleTokenExt for the standard extension s ∘ singleton-pos x
-- Requires that x doesn't appear in s
-- For SDL-based Positions: the extended position is s ∘ singleton-pos x
mkSingleTokenExt : (s : Position) (x : Token) → x ∉Pos s → IsSingleTokenExt s (s ∘ singleton-pos x) x
mkSingleTokenExt s x x∉s = (sub , x-in , x∉s , uniq)
  where
    -- s is a subset of (s ∘ singleton-pos x)
    sub : s ⊑ (s ∘ singleton-pos x)
    sub = ⊑-merge-l s (singleton-pos x)

    -- x is in (s ∘ singleton-pos x) because x is in singleton-pos x
    x-in : x ∈Pos (s ∘ singleton-pos x)
    x-in = merge-∈Pos-r x s (singleton-pos x) (inl refl)

    -- Any t in the extended position that isn't in s must be x
    uniq : ∀ t → t ∈Pos (s ∘ singleton-pos x) → t ∉Pos s → t ≡ x
    uniq t t∈merged t∉s with ∈Pos-merge t s (singleton-pos x) t∈merged
    ... | inl t∈s = ⊥.rec (t∉s t∈s)
    ... | inr t∈singleton with t∈singleton
    ...   | inl t≡x = t≡x
    ...   | inr t∈ε = ⊥.rec t∈ε

-- TokenFresh for context with positions
-- Constructs TokenFresh x Γ when we can show x doesn't appear in any position in Γ
TokenFresh-singleton : ∀ {x : Token} {A : Formula} {s : Position}
                     → x ∉Pos s → TokenFresh x [ A ^ s ]
TokenFresh-singleton x∉s = x∉s , tt

TokenFresh-cons : ∀ {x : Token} {A : Formula} {s : Position} {Γ : Ctx}
                → x ∉Pos s → TokenFresh x Γ → TokenFresh x ((A ^ s) ∷ Γ)
TokenFresh-cons x∉s freshΓ = x∉s , freshΓ

-- IsSingleTokenExt preserved under position merge (lifting) with fresh prefix
-- Requires: x ∉Pos prefix (eigenposition token doesn't appear in lifting position)
singleTokenExt-subst-merge : (prefix : Position) {s eigent : Position} {x : Token}
                           → x ∉Pos prefix
                           → IsSingleTokenExt s eigent x
                           → IsSingleTokenExt (prefix ∘ s) (prefix ∘ eigent) x
singleTokenExt-subst-merge prefix {s} {eigent} {x} x∉prefix (sub , x∈t , x∉s , uniq) =
  sub' , x∈t' , x∉s' , uniq'
  where
    -- 1. Subset preserved: s ⊑ eigent → (prefix ∘ s) ⊑ (prefix ∘ eigent)
    sub' : (prefix ∘ s) ⊑ (prefix ∘ eigent)
    sub' = merge-preserves-⊑ prefix sub

    -- 2. Membership preserved: x ∈Pos eigent → x ∈Pos (prefix ∘ eigent)
    x∈t' : x ∈Pos (prefix ∘ eigent)
    x∈t' = merge-∈Pos-r x prefix eigent x∈t

    -- 3. Freshness: x ∉Pos prefix and x ∉Pos s → x ∉Pos (prefix ∘ s)
    x∉s' : x ∉Pos (prefix ∘ s)
    x∉s' = ∉Pos-∘ x∉prefix x∉s

    -- 4. Uniqueness: any t that's new in the merged extension must be x
    uniq' : ∀ t → t ∈Pos (prefix ∘ eigent) → t ∉Pos (prefix ∘ s) → t ≡ x
    uniq' t t∈merged t∉merged-s with ∈Pos-merge t prefix eigent t∈merged
    -- Case: t ∈Pos prefix
    -- Then t ∉Pos (prefix ∘ s) implies t ∉Pos prefix (contradiction)
    ... | inl t∈prefix = ⊥.rec (t∉merged-s (merge-∈Pos-l t prefix s t∈prefix))
    -- Case: t ∈Pos eigent
    -- t ∉Pos (prefix ∘ s) implies t ∉Pos prefix AND t ∉Pos s
    -- From t ∈Pos eigent and t ∉Pos s, the original uniqueness gives t ≡ x
    ... | inr t∈t = uniq t t∈t t∉s-only
      where
        t∉s-only : t ∉Pos s
        t∉s-only t∈s = t∉merged-s (merge-∈Pos-r t prefix s t∈s)

-- TokenFresh preserved under position lifting for contexts
-- Requires: x ∉Pos prefix (eigenposition token doesn't appear in lifting position)
TokenFresh-liftCtx : (prefix : Position) (Γ : Ctx) {x : Token}
                   → x ∉Pos prefix
                   → TokenFresh x Γ
                   → TokenFresh x (liftCtx prefix Γ)
TokenFresh-liftCtx prefix [] x∉prefix tt = tt
TokenFresh-liftCtx prefix ((A ^ s) ∷ Γ) {x} x∉prefix (x∉s , freshRest) =
  ∉Pos-∘ x∉prefix x∉s , TokenFresh-liftCtx prefix Γ x∉prefix freshRest

-- 4. Main Lifting Lemma
-- Precondition: NoEigenposInt t Π ensures eigenposition tokens in Π don't appear in t
lift-proof : ∀ {Γ Δ} (t : Position) (Π : Γ ⊢ Δ)
           → NoEigenposInt t Π
           → (liftCtx t Γ ⊢ liftCtx t Δ)
lift-proof t (Ax {A} {s}) _ = Ax {A = A} {s = s ↑ t}
lift-proof t (W⊢ {Γ} {Δ} {A} {s} p) nc =
  let
    p' = lift-proof t p nc
    Γ' = liftCtx t Γ
    Δ' = liftCtx t Δ
    s' = s ↑ t
    
    eq : liftCtx t (Γ ++ [ A ^ s ]) ≡ Γ' ++ [ A ^ s' ]
    eq = my-map++ (liftPFormula t) Γ [ A ^ s ]
  in subst (λ G → G ⊢ Δ') (sym eq) (W⊢ {Γ = Γ'} {Δ = Δ'} {A = A} {s = s'} p')
lift-proof t (⊢W {Γ} {Δ} {A} {s} p) nc =
  let
    p' = lift-proof t p nc
    Γ' = liftCtx t Γ
    Δ' = liftCtx t Δ
    s' = s ↑ t
    
    eq : liftCtx t ([ A ^ s ] ++ Δ) ≡ [ A ^ s' ] ++ Δ'
    eq = my-map++ (liftPFormula t) [ A ^ s ] Δ
  in subst (λ D → Γ' ⊢ D) (sym eq) (⊢W {Γ = Γ'} {Δ = Δ'} {A = A} {s = s'} p')
lift-proof t (Cut {Γ₁} {A} {s} {Δ₁} {Γ₂} {Δ₂} p1 p2) (nc₁ , nc₂) =
  let
    p1' = lift-proof t p1 nc₁
    p2' = lift-proof t p2 nc₂
    Γ₁' = liftCtx t Γ₁
    Δ₁' = liftCtx t Δ₁
    Γ₂' = liftCtx t Γ₂
    Δ₂' = liftCtx t Δ₂
    A' = A
    s' = s ↑ t
    
    -- Cut premise 1: Γ₁ ⊢ [ A ^ s ] ,, Δ₁
    -- So succedent is [ A ^ s ] ++ Δ₁.
    eqP1RHS : liftCtx t ([ A ^ s ] ++ Δ₁) ≡ [ A ^ s' ] ++ Δ₁'
    eqP1RHS = my-map++ (liftPFormula t) [ A ^ s ] Δ₁
    
    -- Cut premise 2: Γ₂ ,, [ A ^ s ] ⊢ Δ₂
    -- Context is Γ₂ ++ [ A ^ s ].
    eqP2LHS : liftCtx t (Γ₂ ++ [ A ^ s ]) ≡ Γ₂' ++ [ A ^ s' ]
    eqP2LHS = my-map++ (liftPFormula t) Γ₂ [ A ^ s ]
    
    -- Result: Γ₁ ,, Γ₂ ⊢ Δ₁ ,, Δ₂
    -- We need to prove equality for result context and succedent.
    eqGoalLHS : liftCtx t (Γ₁ ++ Γ₂) ≡ Γ₁' ++ Γ₂'
    eqGoalLHS = my-map++ (liftPFormula t) Γ₁ Γ₂
    
    eqGoalRHS : liftCtx t (Δ₁ ++ Δ₂) ≡ Δ₁' ++ Δ₂'
    eqGoalRHS = my-map++ (liftPFormula t) Δ₁ Δ₂
    
  in subst (λ G → G ⊢ liftCtx t (Δ₁ ++ Δ₂)) (sym eqGoalLHS)
       (subst (λ D → Γ₁' ++ Γ₂' ⊢ D) (sym eqGoalRHS)
         (Cut
           (subst (λ D → Γ₁' ⊢ D) eqP1RHS p1')
           (subst (λ G → G ⊢ Δ₂') eqP2LHS p2')))

lift-proof t (C⊢ {Γ} {A} {s} {Δ} p) nc =
  let
    p' = lift-proof t p nc
    Γ' = liftCtx t Γ
    Δ' = liftCtx t Δ
    s' = s ↑ t
    
    eq1 : liftCtx t ((Γ ++ [ A ^ s ]) ++ [ A ^ s ]) ≡ (Γ' ++ [ A ^ s' ]) ++ [ A ^ s' ]
    eq1 = my-map++ (liftPFormula t) (Γ ++ [ A ^ s ]) [ A ^ s ] ∙
          cong (λ l → l ++ [ A ^ s' ]) (my-map++ (liftPFormula t) Γ [ A ^ s ])
          
    eq2 : liftCtx t (Γ ++ [ A ^ s ]) ≡ Γ' ++ [ A ^ s' ]
    eq2 = my-map++ (liftPFormula t) Γ [ A ^ s ]
    
    apply-C⊢ : (Γ : Ctx) (Δ : Ctx) (A : Formula) (s : Position) → ((Γ ,, [ A ^ s ]) ,, [ A ^ s ] ⊢ Δ) → (Γ ,, [ A ^ s ] ⊢ Δ)
    apply-C⊢ _ _ _ _ p = C⊢ p
    
  in subst (λ G → G ⊢ Δ') (sym eq2) (apply-C⊢ Γ' Δ' A s' (subst (λ G → G ⊢ Δ') eq1 p'))

lift-proof t (⊢C {Γ} {A} {s} {Δ} p) nc =
  let
    p' = lift-proof t p nc
    Γ' = liftCtx t Γ
    Δ' = liftCtx t Δ
    s' = s ↑ t
    
    eq1 : liftCtx t (([ A ^ s ] ++ [ A ^ s ]) ++ Δ) ≡ ([ A ^ s' ] ++ [ A ^ s' ]) ++ Δ'
    eq1 = my-map++ (liftPFormula t) ([ A ^ s ] ++ [ A ^ s ]) Δ ∙
          cong (λ l → l ++ Δ') (my-map++ (liftPFormula t) [ A ^ s ] [ A ^ s ])
          
    apply-⊢C : (Γ : Ctx) (Δ : Ctx) (A : Formula) (s : Position) → (Γ ⊢ [ A ^ s ] ,, [ A ^ s ] ,, Δ) → (Γ ⊢ [ A ^ s ] ,, Δ)
    apply-⊢C _ _ _ _ p = ⊢C p
    
  in apply-⊢C Γ' Δ' A s' (subst (λ D → Γ' ⊢ D) eq1 p')

lift-proof t (Exc⊢ {Γ₁} {A} {s} {B} {r} {Γ₂} {Δ} p) nc =
  let
    p' = lift-proof t p nc
    Γ₁' = liftCtx t Γ₁
    Γ₂' = liftCtx t Γ₂
    Δ' = liftCtx t Δ
    s' = s ↑ t
    r' = r ↑ t
    
    -- Left associative proofs matching ((Γ₁ ++ [A]) ++ [B]) ++ Γ₂
    eq : liftCtx t (((Γ₁ ++ [ A ^ s ]) ++ [ B ^ r ]) ++ Γ₂) ≡ ((Γ₁' ++ [ A ^ s' ]) ++ [ B ^ r' ]) ++ Γ₂'
    eq = my-map++ (liftPFormula t) ((Γ₁ ++ [ A ^ s ]) ++ [ B ^ r ]) Γ₂ ∙
         cong (λ l → l ++ Γ₂') (my-map++ (liftPFormula t) (Γ₁ ++ [ A ^ s ]) [ B ^ r ] ∙
                                cong (λ l → l ++ [ B ^ r' ]) (my-map++ (liftPFormula t) Γ₁ [ A ^ s ]))
                                
    eq' : liftCtx t (((Γ₁ ++ [ B ^ r ]) ++ [ A ^ s ]) ++ Γ₂) ≡ ((Γ₁' ++ [ B ^ r' ]) ++ [ A ^ s' ]) ++ Γ₂'
    eq' = my-map++ (liftPFormula t) ((Γ₁ ++ [ B ^ r ]) ++ [ A ^ s ]) Γ₂ ∙
          cong (λ l → l ++ Γ₂') (my-map++ (liftPFormula t) (Γ₁ ++ [ B ^ r ]) [ A ^ s ] ∙
                                 cong (λ l → l ++ [ A ^ s' ]) (my-map++ (liftPFormula t) Γ₁ [ B ^ r ]))

    apply-Exc⊢ : (Γ₁ : Ctx) (A' : Formula) (s'' : Position) (B' : Formula) (r' : Position) (Γ₂ : Ctx) (Δ : Ctx)
               → (((Γ₁ ,, [ A' ^ s'' ]) ,, [ B' ^ r' ]) ,, Γ₂ ⊢ Δ)
               → (((Γ₁ ,, [ B' ^ r' ]) ,, [ A' ^ s'' ]) ,, Γ₂ ⊢ Δ)
    apply-Exc⊢ G1 A'' a B'' g G2 D' p = Exc⊢ {Γ₁ = G1} {A = A''} {s = a} {B = B''} {t = g} {Γ₂ = G2} {Δ = D'} p

  in subst (λ G → G ⊢ Δ') (sym eq') (apply-Exc⊢ Γ₁' A s' B r' Γ₂' Δ' (subst (λ G → G ⊢ Δ') eq p'))

lift-proof t (⊢Exc {Γ} {Δ₁} {A} {s} {B} {r} {Δ₂} p) nc =
  let
    p' = lift-proof t p nc
    Γ' = liftCtx t Γ
    Δ₁' = liftCtx t Δ₁
    Δ₂' = liftCtx t Δ₂
    s' = s ↑ t
    r' = r ↑ t
    
    eq : liftCtx t (((Δ₁ ++ [ A ^ s ]) ++ [ B ^ r ]) ++ Δ₂) ≡ ((Δ₁' ++ [ A ^ s' ]) ++ [ B ^ r' ]) ++ Δ₂'
    eq = my-map++ (liftPFormula t) ((Δ₁ ++ [ A ^ s ]) ++ [ B ^ r ]) Δ₂ ∙
         cong (λ l → l ++ Δ₂') (my-map++ (liftPFormula t) (Δ₁ ++ [ A ^ s ]) [ B ^ r ] ∙
                                cong (λ l → l ++ [ B ^ r' ]) (my-map++ (liftPFormula t) Δ₁ [ A ^ s ]))
                                
    eq' : liftCtx t (((Δ₁ ++ [ B ^ r ]) ++ [ A ^ s ]) ++ Δ₂) ≡ ((Δ₁' ++ [ B ^ r' ]) ++ [ A ^ s' ]) ++ Δ₂'
    eq' = my-map++ (liftPFormula t) ((Δ₁ ++ [ B ^ r ]) ++ [ A ^ s ]) Δ₂ ∙
          cong (λ l → l ++ Δ₂') (my-map++ (liftPFormula t) (Δ₁ ++ [ B ^ r ]) [ A ^ s ] ∙
                                 cong (λ l → l ++ [ A ^ s' ]) (my-map++ (liftPFormula t) Δ₁ [ B ^ r ]))

    apply-⊢Exc : (Γ : Ctx) (Δ₁ : Ctx) (A' : Formula) (s'' : Position) (B' : Formula) (r' : Position) (Δ₂ : Ctx)
               → (Γ ⊢ (((Δ₁ ,, [ A' ^ s'' ]) ,, [ B' ^ r' ]) ,, Δ₂))
               → (Γ ⊢ (((Δ₁ ,, [ B' ^ r' ]) ,, [ A' ^ s'' ]) ,, Δ₂))
    apply-⊢Exc G D1 A'' a B'' g D2 p = ⊢Exc {Γ = G} {Δ₁ = D1} {A = A''} {s = a} {B = B''} {t = g} {Δ₂ = D2} p

  in subst (λ D → Γ' ⊢ D) (sym eq') (apply-⊢Exc Γ' Δ₁' A s' B r' Δ₂' (subst (λ D → Γ' ⊢ D) eq p'))

lift-proof t (¬⊢ {Γ} {A} {s} {Δ} p) nc =
  let
    p' = lift-proof t p nc
    Γ' = liftCtx t Γ
    Δ' = liftCtx t Δ
    s' = s ↑ t

    eq1 = my-map++ (liftPFormula t) Γ [ (¬ A) ^ s ]
  in subst (λ G → G ⊢ Δ') (sym eq1) (¬⊢ p')

lift-proof t (⊢¬ {Γ} {A} {s} {Δ} p) nc =
  let
    p' = lift-proof t p nc
    Γ' = liftCtx t Γ
    Δ' = liftCtx t Δ
    s' = s ↑ t

    eq2 = my-map++ (liftPFormula t) Γ [ A ^ s ]
  in ⊢¬ (subst (λ G → G ⊢ Δ') eq2 p')

lift-proof t (∧₁⊢ {Γ} {A} {s} {Δ} {B} p) nc =
  let
    p' = lift-proof t p nc
    Γ' = liftCtx t Γ
    Δ' = liftCtx t Δ
    s' = s ↑ t

    eq1 = my-map++ (liftPFormula t) Γ [ (A and B) ^ s ]
    eq2 = my-map++ (liftPFormula t) Γ [ A ^ s ]
  in subst (λ G → G ⊢ Δ') (sym eq1) (∧₁⊢ (subst (λ G → G ⊢ Δ') eq2 p'))

lift-proof t (∧₂⊢ {Γ} {B} {s} {Δ} {A} p) nc =
  let
    p' = lift-proof t p nc
    Γ' = liftCtx t Γ
    Δ' = liftCtx t Δ
    s' = s ↑ t

    eq1 = my-map++ (liftPFormula t) Γ [ (A and B) ^ s ]
    eq2 = my-map++ (liftPFormula t) Γ [ B ^ s ]
  in subst (λ G → G ⊢ Δ') (sym eq1) (∧₂⊢ (subst (λ G → G ⊢ Δ') eq2 p'))


lift-proof t (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} p1 p2) (nc₁ , nc₂) =
  let
    p1' = lift-proof t p1 nc₁
    p2' = lift-proof t p2 nc₂
    Γ₁' = liftCtx t Γ₁
    Δ₁' = liftCtx t Δ₁
    Γ₂' = liftCtx t Γ₂
    Δ₂' = liftCtx t Δ₂
    s' = s ↑ t
    
    -- Premise 1: Γ₁ ⊢ [ A ^ s ] ,, Δ₁
    eqP1RHS : liftCtx t ([ A ^ s ] ++ Δ₁) ≡ [ A ^ s' ] ++ Δ₁'
    eqP1RHS = my-map++ (liftPFormula t) [ A ^ s ] Δ₁
    
    -- Premise 2: Γ₂ ⊢ [ B ^ s ] ,, Δ₂
    eqP2RHS : liftCtx t ([ B ^ s ] ++ Δ₂) ≡ [ B ^ s' ] ++ Δ₂'
    eqP2RHS = my-map++ (liftPFormula t) [ B ^ s ] Δ₂
    
    -- Goal LHS: Γ₁ ,, Γ₂
    eqGoalLHS : liftCtx t (Γ₁ ++ Γ₂) ≡ Γ₁' ++ Γ₂'
    eqGoalLHS = my-map++ (liftPFormula t) Γ₁ Γ₂
    
    -- Goal RHS: [ (A ∧ B) ^ s ] ,, Δ₁ ,, Δ₂
    eqGoalRHS : liftCtx t (([ (A and B) ^ s ] ++ Δ₁) ++ Δ₂) ≡ (([ (A and B) ^ s' ] ++ Δ₁') ++ Δ₂')
    eqGoalRHS = my-map++ (liftPFormula t) ([ (A and B) ^ s ] ++ Δ₁) Δ₂ ∙
                cong (_++ Δ₂') (my-map++ (liftPFormula t) [ (A and B) ^ s ] Δ₁)
    
  in subst (λ G → G ⊢ liftCtx t (([ (A and B) ^ s ] ++ Δ₁) ++ Δ₂)) (sym eqGoalLHS)
       (subst (λ D → Γ₁' ++ Γ₂' ⊢ D) (sym eqGoalRHS)
         (⊢∧
           (subst (λ D → Γ₁' ⊢ D) eqP1RHS p1')
           (subst (λ D → Γ₂' ⊢ D) eqP2RHS p2')))

lift-proof t (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} p1 p2) (nc₁ , nc₂) =
  let
    p1' = lift-proof t p1 nc₁
    p2' = lift-proof t p2 nc₂
    Γ₁' = liftCtx t Γ₁
    Δ₁' = liftCtx t Δ₁
    Γ₂' = liftCtx t Γ₂
    Δ₂' = liftCtx t Δ₂
    s' = s ↑ t

    -- Premise 1: Γ₁ ,, [ A ^ s ] ⊢ Δ₁
    eqP1LHS : liftCtx t (Γ₁ ++ [ A ^ s ]) ≡ Γ₁' ++ [ A ^ s' ]
    eqP1LHS = my-map++ (liftPFormula t) Γ₁ [ A ^ s ]

    -- Premise 2: Γ₂ ,, [ B ^ s ] ⊢ Δ₂
    eqP2LHS : liftCtx t (Γ₂ ++ [ B ^ s ]) ≡ Γ₂' ++ [ B ^ s' ]
    eqP2LHS = my-map++ (liftPFormula t) Γ₂ [ B ^ s ]

    -- Goal LHS: Γ₁ ,, Γ₂ ,, [ (A ∨ B) ^ s ] (right-associative: Γ₁ ++ (Γ₂ ++ [...]))
    eqGoalLHS : liftCtx t (Γ₁ ++ (Γ₂ ++ [ (A or B) ^ s ])) ≡ Γ₁' ++ (Γ₂' ++ [ (A or B) ^ s' ])
    eqGoalLHS = my-map++ (liftPFormula t) Γ₁ (Γ₂ ++ [ (A or B) ^ s ]) ∙
                cong (Γ₁' ++_) (my-map++ (liftPFormula t) Γ₂ [ (A or B) ^ s ])

    -- Goal RHS: Δ₁ ,, Δ₂
    eqGoalRHS : liftCtx t (Δ₁ ++ Δ₂) ≡ Δ₁' ++ Δ₂'
    eqGoalRHS = my-map++ (liftPFormula t) Δ₁ Δ₂

  in subst (λ G → G ⊢ liftCtx t (Δ₁ ++ Δ₂)) (sym eqGoalLHS)
       (subst (λ D → Γ₁' ++ (Γ₂' ++ [ (A or B) ^ s' ]) ⊢ D) (sym eqGoalRHS)
         (∨⊢
           (subst (λ G → G ⊢ Δ₁') eqP1LHS p1')
           (subst (λ G → G ⊢ Δ₂') eqP2LHS p2')))

lift-proof t (⊢∨₁ {Γ} {A} {s} {Δ} {B} p) nc =
  let
    p' = lift-proof t p nc
    Γ' = liftCtx t Γ
    Δ' = liftCtx t Δ
    s' = s ↑ t

  in ⊢∨₁ p'

lift-proof t (⊢∨₂ {Γ} {B} {s} {Δ} {A} p) nc =
  let
    p' = lift-proof t p nc
    Γ' = liftCtx t Γ
    Δ' = liftCtx t Δ
    s' = s ↑ t

  in ⊢∨₂ p'

lift-proof t (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} p1 p2) (nc₁ , nc₂) =
  let
    p1' = lift-proof t p1 nc₁
    p2' = lift-proof t p2 nc₂
    Γ₁' = liftCtx t Γ₁
    Δ₁' = liftCtx t Δ₁
    Γ₂' = liftCtx t Γ₂
    Δ₂' = liftCtx t Δ₂
    s' = s ↑ t
    
    -- Premise 1: Γ₁ ,, [ B ^ s ] ⊢ Δ₁
    eqP1LHS : liftCtx t (Γ₁ ++ [ B ^ s ]) ≡ Γ₁' ++ [ B ^ s' ]
    eqP1LHS = my-map++ (liftPFormula t) Γ₁ [ B ^ s ]
    
    -- Premise 2: Γ₂ ⊢ [ A ^ s ] ,, Δ₂
    eqP2RHS : liftCtx t ([ A ^ s ] ++ Δ₂) ≡ [ A ^ s' ] ++ Δ₂'
    eqP2RHS = my-map++ (liftPFormula t) [ A ^ s ] Δ₂
    
    -- Goal LHS: Γ₁ ,, Γ₂ ,, [ (A ⇒ B) ^ s ] (right-associative: Γ₁ ++ (Γ₂ ++ [...]))
    eqGoalLHS : liftCtx t (Γ₁ ++ (Γ₂ ++ [ (A ⇒ B) ^ s ])) ≡ Γ₁' ++ (Γ₂' ++ [ (A ⇒ B) ^ s' ])
    eqGoalLHS = my-map++ (liftPFormula t) Γ₁ (Γ₂ ++ [ (A ⇒ B) ^ s ]) ∙
                cong (Γ₁' ++_) (my-map++ (liftPFormula t) Γ₂ [ (A ⇒ B) ^ s ])

    -- Goal RHS: Δ₁ ,, Δ₂
    eqGoalRHS : liftCtx t (Δ₁ ++ Δ₂) ≡ Δ₁' ++ Δ₂'
    eqGoalRHS = my-map++ (liftPFormula t) Δ₁ Δ₂

  in subst (λ G → G ⊢ liftCtx t (Δ₁ ++ Δ₂)) (sym eqGoalLHS)
       (subst (λ D → Γ₁' ++ (Γ₂' ++ [ (A ⇒ B) ^ s' ]) ⊢ D) (sym eqGoalRHS)
         (⇒⊢
           (subst (λ G → G ⊢ Δ₁') eqP1LHS p1')
           (subst (λ D → Γ₂' ⊢ D) eqP2RHS p2')))

lift-proof t (⊢⇒ {Γ} {A} {s} {B} {Δ} p) nc =
  let
    p' = lift-proof t p nc
    Γ' = liftCtx t Γ
    Δ' = liftCtx t Δ
    s' = s ↑ t

    eqP-LHS : liftCtx t (Γ ++ [ A ^ s ]) ≡ Γ' ++ [ A ^ s' ]
    eqP-LHS = my-map++ (liftPFormula t) Γ [ A ^ s ]

    eqP-RHS : liftCtx t ([ B ^ s ] ++ Δ) ≡ [ B ^ s' ] ++ Δ'
    eqP-RHS = my-map++ (liftPFormula t) [ B ^ s ] Δ

    eqGoal-RHS : liftCtx t ([ (A ⇒ B) ^ s ] ++ Δ) ≡ [ (A ⇒ B) ^ s' ] ++ Δ'
    eqGoal-RHS = my-map++ (liftPFormula t) [ (A ⇒ B) ^ s ] Δ

  in subst (λ D → Γ' ⊢ D) (sym eqGoal-RHS)
       (⊢⇒
         (subst (λ G → G ⊢ [ B ^ s' ] ++ Δ') eqP-LHS
           (subst (λ D → liftCtx t (Γ ++ [ A ^ s ]) ⊢ D) eqP-RHS p')))

lift-proof t (□⊢ {Γ = Γ₀} {A = A₀} {s = s₀} {t = t'} {Δ = Δ₀} p) nc =
  let
    p' = lift-proof t p nc
    Γ' = liftCtx t Γ₀
    Δ' = liftCtx t Δ₀
    s' = s₀ ↑ t

    -- □⊢ : (Γ ,, [ A ^ (s ∘ t') ] ⊢ Δ) → (Γ ,, [ (□ A) ^ s ] ⊢ Δ)
    -- After lifting: p' : liftCtx t (Γ ++ [ A ^ (s ∘ t') ]) ⊢ liftCtx t Δ
    -- Need to convert to: Γ' ++ [ A ^ (s' ∘ t') ] ⊢ Δ'
    -- where s' = t ∘ s₀, and we need: t ∘ (s₀ ∘ t') ≡ (t ∘ s₀) ∘ t' by assoc

    -- my-map++ gives: liftCtx t (Γ₀ ++ [ A₀ ^ (s₀ ∘ t') ]) ≡ Γ' ++ [ A₀ ^ (t ∘ (s₀ ∘ t')) ]
    -- Need to compose with associativity: t ∘ (s₀ ∘ t') ≡ (t ∘ s₀) ∘ t' = s' ∘ t'
    eqP-LHS : liftCtx t (Γ₀ ++ [ A₀ ^ (s₀ ∘ t') ]) ≡ Γ' ++ [ A₀ ^ (s' ∘ t') ]
    eqP-LHS = my-map++ (liftPFormula t) Γ₀ [ A₀ ^ (s₀ ∘ t') ]
            ∙ cong (λ pos → Γ' ++ [ A₀ ^ pos ]) (sym (merge-assoc t s₀ t'))

    eqGoal-LHS : liftCtx t (Γ₀ ++ [ (□ A₀) ^ s₀ ]) ≡ Γ' ++ [ (□ A₀) ^ s' ]
    eqGoal-LHS = my-map++ (liftPFormula t) Γ₀ [ (□ A₀) ^ s₀ ]

  in subst (λ G → G ⊢ Δ') (sym eqGoal-LHS)
       (□⊢ {t = t'}
         (subst (λ G → G ⊢ Δ') eqP-LHS p'))

lift-proof t (⊢□ {x = x₀} {s = s₀} {Γ = Γ₀} {Δ = Δ₀} {A = A₀} x∉s freshΓ freshΔ p) (x∉t , nc-sub) =
  let
    p' = lift-proof t p nc-sub
    Γ' = liftCtx t Γ₀
    Δ' = liftCtx t Δ₀
    s' = s₀ ↑ t

    -- Premise type (from ⊢□ constructor): Γ₀ ⊢ [ A₀ ^ insertToken x₀ s₀ ] ,, Δ₀
    -- After lifting: Γ' ⊢ [ A₀ ^ (t ∘ insertToken x₀ s₀) ] ,, Δ'
    -- Need: t ∘ insertToken x₀ s₀ = insertToken x₀ s' where s' = t ∘ s₀
    -- Proof: t ∘ insertToken x₀ s₀ = t ∘ (s₀ ∘ [x₀]) = (t ∘ s₀) ∘ [x₀] = s' ∘ [x₀] = insertToken x₀ s'
    eqP-RHS : liftCtx t ([ A₀ ^ insertToken x₀ s₀ ] ++ Δ₀) ≡ [ A₀ ^ insertToken x₀ s' ] ++ Δ'
    eqP-RHS = my-map++ (liftPFormula t) [ A₀ ^ insertToken x₀ s₀ ] Δ₀
            ∙ cong (λ pos → [ A₀ ^ pos ] ++ Δ')
                   (cong (t ∘_) (sym (merge-singleton s₀ x₀))
                    ∙ sym (merge-assoc t s₀ (singleton-pos x₀))
                    ∙ merge-singleton s' x₀)

    -- Goal RHS: [ (□ A) ^ s' ] ,, Δ'
    eqGoal-RHS : liftCtx t ([ (□ A₀) ^ s₀ ] ++ Δ₀) ≡ [ (□ A₀) ^ s' ] ++ Δ'
    eqGoal-RHS = my-map++ (liftPFormula t) [ (□ A₀) ^ s₀ ] Δ₀

    -- x ∉Pos s' = x ∉Pos (t ∘ s)
    -- This requires x ∉Pos t and x ∉Pos s. We have x ∉Pos s from the rule.
    -- x ∉Pos t comes from NoEigenposInt precondition.
    x∉s' : x₀ ∉Pos s'
    x∉s' = ∉Pos-∘ x∉t x∉s

    -- Transform TokenFresh conditions
    freshΓ' : TokenFresh x₀ Γ'
    freshΓ' = TokenFresh-liftCtx t Γ₀ x∉t freshΓ

    freshΔ' : TokenFresh x₀ Δ'
    freshΔ' = TokenFresh-liftCtx t Δ₀ x∉t freshΔ

  in subst (λ D → Γ' ⊢ D) (sym eqGoal-RHS)
       (⊢□ {x = x₀} x∉s' freshΓ' freshΔ'
         (subst (λ D → Γ' ⊢ D) eqP-RHS p'))

lift-proof t (♢⊢ {x = x₀} {s = s₀} {Γ = Γ₀} {Δ = Δ₀} {A = A₀} x∉s freshΓ freshΔ p) (x∉t , nc-sub) =
  let
    p' = lift-proof t p nc-sub
    Γ' = liftCtx t Γ₀
    Δ' = liftCtx t Δ₀
    s' = s₀ ↑ t

    -- Premise type (from ♢⊢ constructor): Γ₀ ,, [ A₀ ^ insertToken x₀ s₀ ] ⊢ Δ₀
    -- After lifting: Γ' ,, [ A₀ ^ (t ∘ insertToken x₀ s₀) ] ⊢ Δ'
    -- Need: t ∘ insertToken x₀ s₀ = insertToken x₀ s'
    eqP-LHS : liftCtx t (Γ₀ ++ [ A₀ ^ insertToken x₀ s₀ ]) ≡ Γ' ++ [ A₀ ^ insertToken x₀ s' ]
    eqP-LHS = my-map++ (liftPFormula t) Γ₀ [ A₀ ^ insertToken x₀ s₀ ]
            ∙ cong (λ pos → Γ' ++ [ A₀ ^ pos ])
                   (cong (t ∘_) (sym (merge-singleton s₀ x₀))
                    ∙ sym (merge-assoc t s₀ (singleton-pos x₀))
                    ∙ merge-singleton s' x₀)

    -- Goal LHS: Γ' ,, [ (♢ A) ^ s' ]
    eqGoal-LHS : liftCtx t (Γ₀ ++ [ (♢ A₀) ^ s₀ ]) ≡ Γ' ++ [ (♢ A₀) ^ s' ]
    eqGoal-LHS = my-map++ (liftPFormula t) Γ₀ [ (♢ A₀) ^ s₀ ]

    -- x ∉Pos s' = x ∉Pos (t ∘ s)
    -- x ∉Pos t comes from NoEigenposInt precondition, x ∉Pos s from the rule.
    x∉s' : x₀ ∉Pos s'
    x∉s' = ∉Pos-∘ x∉t x∉s

    -- Transform TokenFresh conditions
    freshΓ' : TokenFresh x₀ Γ'
    freshΓ' = TokenFresh-liftCtx t Γ₀ x∉t freshΓ

    freshΔ' : TokenFresh x₀ Δ'
    freshΔ' = TokenFresh-liftCtx t Δ₀ x∉t freshΔ

  in subst (λ G → G ⊢ Δ') (sym eqGoal-LHS)
       (♢⊢ {x = x₀} x∉s' freshΓ' freshΔ'
         (subst (λ G → G ⊢ Δ') eqP-LHS p'))

lift-proof t (⊢♢ {Γ = Γ₀} {A = A₀} {s = s₀} {t = t'} {Δ = Δ₀} p) nc =
  let
    p' = lift-proof t p nc
    Γ' = liftCtx t Γ₀
    Δ' = liftCtx t Δ₀
    s' = s₀ ↑ t

    -- ⊢♢ : (Γ ⊢ [ A ^ (s ∘ t') ] ,, Δ) → (Γ ⊢ [ (♢ A) ^ s ] ,, Δ)
    -- After lifting: Γ' ⊢ [ A ^ (t ∘ (s₀ ∘ t')) ] ,, Δ'
    -- By merge associativity: t ∘ (s₀ ∘ t') = (t ∘ s₀) ∘ t' = s' ∘ t'

    eqP-RHS : liftCtx t ([ A₀ ^ (s₀ ∘ t') ] ++ Δ₀) ≡ [ A₀ ^ (s' ∘ t') ] ++ Δ'
    eqP-RHS = my-map++ (liftPFormula t) [ A₀ ^ (s₀ ∘ t') ] Δ₀
            ∙ cong (λ pos → [ A₀ ^ pos ] ++ Δ') (sym (merge-assoc t s₀ t'))

    eqGoal-RHS : liftCtx t ([ (♢ A₀) ^ s₀ ] ++ Δ₀) ≡ [ (♢ A₀) ^ s' ] ++ Δ'
    eqGoal-RHS = my-map++ (liftPFormula t) [ (♢ A₀) ^ s₀ ] Δ₀

  in subst (λ D → Γ' ⊢ D) (sym eqGoal-RHS)
       (⊢♢ {t = t'}
         (subst (λ D → Γ' ⊢ D) eqP-RHS p'))

-- Derivations of Axioms

derive-P1 : ∀ {A B : Formula} {s : Position} → [] ⊢ [ (A ⇒ (B ⇒ A)) ^ s ]
derive-P1 {A} {B} {s} = ⊢⇒ {Γ = []} {Δ = []} (⊢⇒ {Γ = [ A ^ s ]} {Δ = []} (W⊢ {Γ = [ A ^ s ]} {Δ = [ A ^ s ]} {A = B} {s = s} (Ax {A = A} {s = s})))

derive-P2 : ∀ {A B C : Formula} {s : Position}
           → [] ⊢ [ ((A ⇒ (B ⇒ C)) ⇒ ((A ⇒ B) ⇒ (A ⇒ C))) ^ s ]
derive-P2 {A} {B} {C} {s} = 
  ⊢⇒ {Γ = []} {A = A ⇒ (B ⇒ C)} {s = s} {B = (A ⇒ B) ⇒ (A ⇒ C)} {Δ = []}
  (⊢⇒ {Γ = [ (A ⇒ (B ⇒ C)) ^ s ]} {A = A ⇒ B} {s = s} {B = A ⇒ C} {Δ = []}
  (⊢⇒ {Γ = [ (A ⇒ (B ⇒ C)) ^ s ] ++ [ (A ⇒ B) ^ s ]} {A = A} {s = s} {B = C} {Δ = []}
  (C⊢ {Γ = [ (A ⇒ (B ⇒ C)) ^ s ] ++ [ (A ⇒ B) ^ s ]} {A = A} {s = s} {Δ = [ C ^ s ]}
  -- Goal: [ (A ⇒ (B ⇒ C)) ^ s, (A ⇒ B) ^ s, A ^ s, A ^ s ] ⊢ [ C ^ s ]
  -- Strategy: 
  -- 1. Use first ⇒⊢ to consume (A ⇒ (B ⇒ C)), need [B ⇒ C] in Γ₁ and provide A
  -- 2. Use second ⇒⊢ to consume (B ⇒ C), need [C] in Γ₁ and provide B  
  -- 3. Use third ⇒⊢ to consume (A ⇒ B), need [B] in Γ₁ and provide A
  
  -- Actually let's structure it as: use Cut to combine the pieces
  -- Or use ⇒⊢ multiple times with the right context splits
  
  -- ⇒⊢ : (Γ₁ ,, [ B ^ s ] ⊢ Δ₁) → (Γ₂ ⊢ [ A ^ s ] ,, Δ₂) → (Γ₁ ,, Γ₂ ,, [ (A ⇒ B) ^ s ] ⊢ Δ₁ ,, Δ₂)
  
  -- Use ⇒⊢ on (A ⇒ B) to get B, with Γ₁=[(A ⇒ (B ⇒ C))], Γ₂=[A,A]
  -- Then in Γ₁ we have [(A ⇒ (B ⇒ C)), B] and need [C]
  
  -- Actually let me try:
  -- Outer ⇒⊢ on (A ⇒ (B ⇒ C)): 
  --   Γ₁ ++ [B ⇒ C] ⊢ Δ₁  and  Γ₂ ⊢ [A] ++ Δ₂
  --   Result: Γ₁ ++ Γ₂ ++ [A ⇒ (B ⇒ C)] ⊢ Δ₁ ++ Δ₂
  --   
  -- Want result to be [(A ⇒ (B ⇒ C)), (A ⇒ B), A, A] ⊢ [C]
  -- After exchange, can get: [(A ⇒ B), A, A, (A ⇒ (B ⇒ C))] ⊢ [C]
  -- Setting Γ₁=[(A ⇒ B), A], Γ₂=[A], Δ₁=[C], Δ₂=[]
  -- Premise 1: [(A ⇒ B), A, (B ⇒ C)] ⊢ [C]
  -- Premise 2: [A] ⊢ [A]  (Ax!)
  
  -- First move (A ⇒ (B ⇒ C)) to the end using exchanges
  (Exc⊢ {Γ₁ = []} {A = A ⇒ B} {s = s} {B = A ⇒ (B ⇒ C)} {t = s} {Γ₂ = [ A ^ s ] ++ [ A ^ s ]} {Δ = [ C ^ s ]}
  (Exc⊢ {Γ₁ = [ (A ⇒ B) ^ s ]} {A = A} {s = s} {B = A ⇒ (B ⇒ C)} {t = s} {Γ₂ = [ A ^ s ]} {Δ = [ C ^ s ]}
  (Exc⊢ {Γ₁ = [ (A ⇒ B) ^ s ] ++ [ A ^ s ]} {A = A} {s = s} {B = A ⇒ (B ⇒ C)} {t = s} {Γ₂ = []} {Δ = [ C ^ s ]}
  -- Now: [(A ⇒ B), A, A, (A ⇒ (B ⇒ C))] ⊢ [C]
  (⇒⊢ {Γ₁ = [ (A ⇒ B) ^ s ] ++ [ A ^ s ]} {B = B ⇒ C} {s = s} {Δ₁ = [ C ^ s ]} 
      {Γ₂ = [ A ^ s ]} {A = A} {Δ₂ = []}
    -- Premise 1: [(A ⇒ B), A, (B ⇒ C)] ⊢ [C]
    -- Move to [(A ⇒ B), (B ⇒ C), A] with exchange, then use ⇒⊢ on (A ⇒ B)
    -- Exc⊢ conclusion: Γ₁ ,, [B] ,, [A] ,, Γ₂ ⊢ Δ
    -- Setting Γ₁=[(A ⇒ B)], B=A, A=B⇒C, Γ₂=[]
    -- Conclusion: [(A ⇒ B), A, (B ⇒ C)] ⊢ [C] ✓
    -- Premise: [(A ⇒ B), (B ⇒ C), A] ⊢ [C]
    (Exc⊢ {Γ₁ = [ (A ⇒ B) ^ s ]} {A = B ⇒ C} {s = s} {B = A} {t = s} {Γ₂ = []} {Δ = [ C ^ s ]}
    -- Premise: [(A ⇒ B), (B ⇒ C), A] ⊢ [C]
    -- Need to produce this as output of Exc⊢
    -- Setting A=B⇒C, B=A⇒B: conclusion=Γ₁,,[(A⇒B)],,[(B⇒C)],,Γ₂
    (Exc⊢ {Γ₁ = []} {A = B ⇒ C} {s = s} {B = A ⇒ B} {t = s} {Γ₂ = [ A ^ s ]} {Δ = [ C ^ s ]}
    -- Now: [(B ⇒ C), (A ⇒ B), A] ⊢ [C]
    (Exc⊢ {Γ₁ = [ (B ⇒ C) ^ s ]} {A = A} {s = s} {B = A ⇒ B} {t = s} {Γ₂ = []} {Δ = [ C ^ s ]}
    -- Now: [(B ⇒ C), A, (A ⇒ B)] ⊢ [C]
    (⇒⊢ {Γ₁ = [ (B ⇒ C) ^ s ]} {B = B} {s = s} {Δ₁ = [ C ^ s ]} 
        {Γ₂ = [ A ^ s ]} {A = A} {Δ₂ = []}
      -- Premise 1: [(B ⇒ C), B] ⊢ [C]
      -- inner ⇒⊢ gives [B, (B ⇒ C)] ⊢ [C]
      -- Exc⊢ to swap: premise=[B, (B ⇒ C)], conclusion=[(B ⇒ C), B]
      -- Setting A=B, B=B⇒C: conclusion=Γ₁,,[(B⇒C)],,[B],,Γ₂, premise=Γ₁,,[B],,[(B⇒C)],,Γ₂
      (Exc⊢ {Γ₁ = []} {A = B} {s = s} {B = B ⇒ C} {t = s} {Γ₂ = []} {Δ = [ C ^ s ]}
      -- Now: [B, (B ⇒ C)] ⊢ [C]
      (⇒⊢ {Γ₁ = []} {B = C} {s = s} {Δ₁ = [ C ^ s ]} 
          {Γ₂ = [ B ^ s ]} {A = B} {Δ₂ = []}
        (Ax {A = C} {s = s})
        (Ax {A = B} {s = s})))
      -- Premise 2: [A] ⊢ [A]
      (Ax {A = A} {s = s})))))
    -- Premise 2 of outer ⇒⊢: [A] ⊢ [A]
    (Ax {A = A} {s = s}))))))))

-- P3: (¬B ⇒ ¬A) ⇒ ((¬B ⇒ A) ⇒ B)
-- Classical tautology derivation
derive-P3 : ∀ {A B : Formula} {s : Position} → [] ⊢ [ (((¬ B) ⇒ (¬ A)) ⇒ (((¬ B) ⇒ A) ⇒ B)) ^ s ]
derive-P3 {A} {B} {s} = ⊢⇒ {Γ = []} {Δ = []} (⊢⇒ {Γ = [ ((¬ B) ⇒ (¬ A)) ^ s ]} {Δ = []}
  (⊢C {Γ = [ ((¬ B) ⇒ (¬ A)) ^ s ] ++ [ ((¬ B) ⇒ A) ^ s ]} {A = B} {s = s} {Δ = []}
    (⇒⊢ {Γ₁ = [ ((¬ B) ⇒ (¬ A)) ^ s ]} {B = A} {s = s} {Δ₁ = [ B ^ s ]} {Γ₂ = []} {A = ¬ B} {Δ₂ = [ B ^ s ]}
      -- Premise 1: [ ((¬ B) ⇒ (¬ A)), A ] ⊢ [ B ]
      -- Use Exc⊢ to swap: conclusion has [imp, A], premise has [A, imp]
      -- Exc⊢ {A = X, B = Y}: conclusion = [..., Y, X, ...], premise = [..., X, Y, ...]
      -- We want conclusion = [ (¬ B) ⇒ (¬ A), A ], so set A = A, B = (¬ B) ⇒ (¬ A)
      (Exc⊢ {Γ₁ = []} {A = A} {s = s} {B = (¬ B) ⇒ (¬ A)} {t = s} {Γ₂ = []} {Δ = [ B ^ s ]}
        -- Premise: [ A, (¬ B) ⇒ (¬ A) ] ⊢ [ B ]
        -- Use ⊢C to get [ B, B ], then ⇒⊢ on (¬ B) ⇒ (¬ A)
        (⊢C {Γ = [ A ^ s ] ++ [ ((¬ B) ⇒ (¬ A)) ^ s ]} {A = B} {s = s} {Δ = []}
          -- Goal: [ A, (¬ B) ⇒ (¬ A) ] ⊢ [ B, B ]
          (⇒⊢ {Γ₁ = [ A ^ s ]} {B = ¬ A} {s = s} {Δ₁ = [ B ^ s ]} {Γ₂ = []} {A = ¬ B} {Δ₂ = [ B ^ s ]}
            -- Premise 1: [ A, ¬A ] ⊢ [ B ]
            -- ¬⊢ on ¬A: (Γ ⊢ [ A ^ s ] ,, Δ) → (Γ ,, [ (¬ A) ^ s ] ⊢ Δ)
            -- We want [ A, ¬A ] ⊢ [ B ], so need [ A ] ⊢ [ A, B ] as premise
            -- Ax gives [A]⊢[A], ⊢W gives [A]⊢[B,A]
            -- ⊢Exc {A=B, B=A}: premise=[B,A], conclusion=[A,B] ✓
            (¬⊢ {Γ = [ A ^ s ]} {A = A} {s = s} {Δ = [ B ^ s ]}
              (⊢Exc {Γ = [ A ^ s ]} {Δ₁ = []} {A = B} {s = s} {B = A} {t = s} {Δ₂ = []}
                (⊢W {Γ = [ A ^ s ]} {Δ = [ A ^ s ]} {A = B} {s = s}
                  (Ax {A = A} {s = s}))))
            -- Premise 2: [] ⊢ [ ¬B, B ]
            (⊢¬ {Γ = []} {A = B} {s = s} {Δ = [ B ^ s ]}
              (Ax {A = B} {s = s})))))
      -- Premise 2 of outer ⇒⊢: [] ⊢ [ ¬B, B ]
      (⊢¬ {Γ = []} {A = B} {s = s} {Δ = [ B ^ s ]}
        (Ax {A = B} {s = s})))))


-- Helper for Identity: A ⊢ A
id-seq : ∀ {A s} → [ A ^ s ] ⊢ [ A ^ s ]
id-seq = Ax

-- Helper for cancellation
-- Helper for cancellation
-- Axiom K: □ (A ⇒ B) ⇒ (□ A ⇒ □ B)
-- Derivation tree (bottom-up):
-- Goal: [] ⊢ [ (□(A⇒B) ⇒ (□A ⇒ □B)) ^ s ]
-- 
-- Step 1: ⊢⇒ with Γ=[]
--   Premise: [□(A⇒B)^s] ⊢ [(□A ⇒ □B)^s]
--   Result: [] ⊢ [□(A⇒B) ⇒ (□A ⇒ □B)]^s
--
-- Step 2: ⊢⇒ with Γ=[□(A⇒B)^s]
--   Premise: [□(A⇒B)^s, □A^s] ⊢ [□B^s]
--   Result: [□(A⇒B)^s] ⊢ [(□A ⇒ □B)^s]
--
-- Step 3: ⊢□ with x=0
--   Premise: [□(A⇒B)^s, □A^s] ⊢ [B^t] where t = s++[0]
--   Result: [□(A⇒B)^s, □A^s] ⊢ [□B^s]
--
-- Step 4: Exc⊢ to swap □A and □(A⇒B)
--   Premise: [□A^s, □(A⇒B)^s] ⊢ [B^t]
--   Result: [□(A⇒B)^s, □A^s] ⊢ [B^t]
--
-- Step 5: □⊢ to unbox □(A⇒B) (now at end of context)
--   Premise: [□A^s, (A⇒B)^t] ⊢ [B^t]
--   Result: [□A^s, □(A⇒B)^s] ⊢ [B^t]
--
-- Step 6: Exc⊢ to swap (A⇒B) and □A
--   Premise: [(A⇒B)^t, □A^s] ⊢ [B^t]
--   Result: [□A^s, (A⇒B)^t] ⊢ [B^t]
--
-- Step 7: □⊢ to unbox □A (now at end of context)
--   Premise: [(A⇒B)^t, A^t] ⊢ [B^t]
--   Result: [(A⇒B)^t, □A^s] ⊢ [B^t]
--
-- Step 8: Exc⊢ to swap A and (A⇒B)
--   Premise: [A^t, (A⇒B)^t] ⊢ [B^t]
--   Result: [(A⇒B)^t, A^t] ⊢ [B^t]
--
-- Step 9: ⇒⊢ to apply implication
--   Premises: [B^t] ⊢ [B^t] and [A^t] ⊢ [A^t]
--   Result: [A^t, (A⇒B)^t] ⊢ [B^t]

-- Axiom K specialized to empty position for weak completeness
derive-K : ∀ {A B : Formula} → [] ⊢ [ (□ (A ⇒ B) ⇒ (□ A ⇒ □ B)) ^ ε ]
derive-K {A} {B} =
  let s : Position
      s = ε

      t : Position
      t = singleton-pos 0  -- s ∘ singleton-pos 0 = ε ∘ [0] = [0]

      -- Equality for converting between t and insertToken 0 s
      t≡insert : t ≡ insertToken 0 s
      t≡insert = merge-singleton s 0

      -- 0 is trivially fresh for empty position
      fresh-s : 0 ∉Pos s
      fresh-s = λ ()
      -- TokenFresh for contexts with position s = ε
      freshΓ-2 : TokenFresh 0 (((□ (A ⇒ B)) ^ s) ∷ ((□ A) ^ s) ∷ [])
      freshΓ-2 = TokenFresh-cons {x = 0} {A = □ (A ⇒ B)} {s = s} {Γ = ((□ A) ^ s) ∷ []} fresh-s (TokenFresh-singleton {x = 0} {A = □ A} {s = s} fresh-s)

      -- Step 9: ⇒⊢ from two axioms
      -- [A^t, (A⇒B)^t] ⊢ [B^t]
      step9 : [ A ^ t ] ++ [ (A ⇒ B) ^ t ] ⊢ [ B ^ t ]
      step9 = ⇒⊢ {Γ₁ = []} {B = B} {s = t} {Δ₁ = [ B ^ t ]} {Γ₂ = [ A ^ t ]} {A = A} {Δ₂ = []}
                (Ax {A = B} {s = t})
                (Ax {A = A} {s = t})

      -- Step 8: Exc⊢ to swap A and (A⇒B)
      -- [(A⇒B)^t, A^t] ⊢ [B^t]
      step8 : [ (A ⇒ B) ^ t ] ++ [ A ^ t ] ⊢ [ B ^ t ]
      step8 = Exc⊢ {Γ₁ = []} {A = A} {s = t} {B = A ⇒ B} {t = t} {Γ₂ = []} {Δ = [ B ^ t ]} step9

      -- Step 7: □⊢ to unbox □A at end of context
      -- [(A⇒B)^t, □A^s] ⊢ [B^t]
      -- □⊢ expects premise with A ^ (s ∘ singleton-pos 0) = A ^ t
      step7 : [ (A ⇒ B) ^ t ] ++ [ (□ A) ^ s ] ⊢ [ B ^ t ]
      step7 = □⊢ {Γ = [ (A ⇒ B) ^ t ]} {A = A} {s = s} {t = singleton-pos 0} {Δ = [ B ^ t ]} step8

      -- Step 6: Exc⊢ to swap (A⇒B) and □A
      -- [□A^s, (A⇒B)^t] ⊢ [B^t]
      step6 : [ (□ A) ^ s ] ++ [ (A ⇒ B) ^ t ] ⊢ [ B ^ t ]
      step6 = Exc⊢ {Γ₁ = []} {A = (A ⇒ B)} {s = t} {B = □ A} {t = s} {Γ₂ = []} {Δ = [ B ^ t ]} step7

      -- Step 5: □⊢ to unbox □(A⇒B) at end of context
      -- [□A^s, □(A⇒B)^s] ⊢ [B^t]
      -- □⊢ expects premise with (A⇒B) ^ (s ∘ singleton-pos 0) = (A⇒B) ^ t
      step5 : [ (□ A) ^ s ] ++ [ □ (A ⇒ B) ^ s ] ⊢ [ B ^ t ]
      step5 = □⊢ {Γ = [ (□ A) ^ s ]} {A = A ⇒ B} {s = s} {t = singleton-pos 0} {Δ = [ B ^ t ]} step6

      -- Step 4: Exc⊢ to swap □A and □(A⇒B)
      -- [□(A⇒B)^s, □A^s] ⊢ [B^t]
      step4 : [ □ (A ⇒ B) ^ s ] ++ [ (□ A) ^ s ] ⊢ [ B ^ t ]
      step4 = Exc⊢ {Γ₁ = []} {A = □ A} {s = s} {B = □ (A ⇒ B)} {t = s} {Γ₂ = []} {Δ = [ B ^ t ]} step5

      -- Step 3: ⊢□ needs premise with B ^ (insertToken 0 s), convert from B ^ t
      step4' : [ □ (A ⇒ B) ^ s ] ++ [ (□ A) ^ s ] ⊢ [ B ^ insertToken 0 s ]
      step4' = subst (λ pos → [ □ (A ⇒ B) ^ s ] ++ [ (□ A) ^ s ] ⊢ [ B ^ pos ]) t≡insert step4

  in
  ⊢⇒ {Γ = []}  -- Step 1
    (⊢⇒ {Γ = [ □ (A ⇒ B) ^ s ]}  -- Step 2
      (⊢□ {x = 0}  -- Step 3
        fresh-s freshΓ-2 (TokenFresh-[] {x = 0})
        step4'))

-- Axiom D: □ A ⇒ ♢ A
derive-D : ∀ {A : Formula} {s : Position} → [] ⊢ [ (□ A ⇒ ♢ A) ^ s ]
derive-D {A} {s} =
  let
    -- Ax gives: [ A ^ s ] ⊢ [ A ^ s ]
    -- □⊢ {t = ε} expects LHS: [ A ^ (s ∘ ε) ] and keeps RHS unchanged
    -- ⊢♢ {t = ε} expects RHS: [ A ^ (s ∘ ε) ] and keeps LHS unchanged
    -- So we need both sides to be [ A ^ (s ∘ ε) ]
    ax-subst : [ A ^ (s ∘ ε) ] ⊢ [ A ^ (s ∘ ε) ]
    ax-subst = subst (λ pos → [ A ^ pos ] ⊢ [ A ^ pos ]) (sym (merge-ε-r s)) (Ax {A = A} {s = s})

    -- After □⊢ {t = ε}: [ □ A ^ s ] ⊢ [ A ^ (s ∘ ε) ]
    step1 : [ (□ A) ^ s ] ⊢ [ A ^ (s ∘ ε) ]
    step1 = □⊢ {Γ = []} {A = A} {s = s} {t = ε} {Δ = [ A ^ (s ∘ ε) ]} ax-subst

    -- After ⊢♢ {t = ε}: [ □ A ^ s ] ⊢ [ ♢ A ^ s ]
    step2 : [ (□ A) ^ s ] ⊢ [ (♢ A) ^ s ]
    step2 = ⊢♢ {t = ε} step1
  in
  ⊢⇒ {Γ = []} {A = □ A} {s = s} {B = ♢ A} {Δ = []} step2

-- Axiom T: □ A ⇒ A
derive-T : ∀ {A : Formula} {s : Position} → [] ⊢ [ (□ A ⇒ A) ^ s ]
derive-T {A} {s} =
  let
    -- □⊢ {t = ε} expects LHS: [ A ^ (s ∘ ε) ]
    ax-subst-l : [ A ^ (s ∘ ε) ] ⊢ [ A ^ s ]
    ax-subst-l = subst (λ pos → [ A ^ pos ] ⊢ [ A ^ s ]) (sym (merge-ε-r s)) (Ax {A = A} {s = s})

    -- After □⊢: [ □ A ^ s ] ⊢ [ A ^ s ]
    step1 : [ (□ A) ^ s ] ⊢ [ A ^ s ]
    step1 = □⊢ {Γ = []} {A = A} {s = s} {t = ε} {Δ = [ A ^ s ]} ax-subst-l
  in
  ⊢⇒ {Γ = []} {A = □ A} {s = s} {B = A} {Δ = []} step1

-- Axiom 4: □ A ⇒ □ □ A (specialized to empty position for weak completeness)
-- Uses different tokens 0 and 1 for the two eigenposition extensions
derive-Ax4 : ∀ {A : Formula} → [] ⊢ [ (□ A ⇒ □ (□ A)) ^ ε ]
derive-Ax4 {A} =
  let s : Position
      s = ε
      -- 0 and 1 are trivially fresh for empty position
      fresh-s-0 : 0 ∉Pos s
      fresh-s-0 = λ ()
      fresh-s-1 : 1 ∉Pos s
      fresh-s-1 = λ ()
      t₁ : Position
      t₁ = s ∘ singleton-pos 0  -- eigenposition for first ⊢□
      -- For the □⊢, we need s ∘ t = t₂ where t₂ is the final position
      -- t₂ = insertToken 1 (insertToken 0 s) = insertToken 0 (insertToken 1 s)  (by swap)
      --    = s ∘ (merge [1] [0])
      [10] : Position
      [10] = merge (singleton-pos 1) (singleton-pos 0)  -- position {1, 0}
      t₂ : Position
      t₂ = s ∘ [10]  -- = merge s {1, 0}

      -- Show that t₁ with token 1 gives t₂
      -- insertToken 1 t₁ = insertToken 1 (s ∘ [0]) = insertToken 1 (merge s [0])
      --                  = merge s (insertToken 1 [0])  (by merge-insertToken-r)
      --                  = merge s [10]  (since insertToken 1 [0] = [10])
      --                  = t₂
      t₁≡insert : t₁ ≡ insertToken 0 s
      t₁≡insert = merge-singleton s 0

      -- t₂ = s ∘ [10] = merge s (merge [1] [0])
      -- By sym merge-assoc: merge s (merge [1] [0]) = merge (merge s [1]) [0]
      -- By merge-singleton: merge s [1] = insertToken 1 s, merge _ [0] = insertToken 0 _
      -- So: merge (merge s [1]) [0] = insertToken 0 (insertToken 1 s)
      -- By insertToken-swap: insertToken 0 (insertToken 1 s) = insertToken 1 (insertToken 0 s)
      t₂≡insert : t₂ ≡ insertToken 1 (insertToken 0 s)
      t₂≡insert = sym (merge-assoc s (singleton-pos 1) (singleton-pos 0))
                ∙ cong (λ p → merge p (singleton-pos 0)) (merge-singleton s 1)
                ∙ merge-singleton (insertToken 1 s) 0
                ∙ insertToken-swap 0 1 s

      -- For fresh-t₁-1: we need 1 ∉Pos t₁
      fresh-t₁-1 : 1 ∉Pos t₁
      fresh-t₁-1 = subst (1 ∉Pos_) (sym t₁≡insert) (∉Pos-insertToken 0 1 s fresh-s-1 1≢0)

      freshΓ₁-0 : TokenFresh 0 (((□ A) ^ s) ∷ [])
      freshΓ₁-0 = TokenFresh-singleton {x = 0} {A = □ A} {s = s} fresh-s-0
      freshΓ₁-1 : TokenFresh 1 (((□ A) ^ s) ∷ [])
      freshΓ₁-1 = TokenFresh-singleton {x = 1} {A = □ A} {s = s} fresh-s-1

      -- The axiom at position t₂
      ax-t₂ : [ A ^ t₂ ] ⊢ [ A ^ t₂ ]
      ax-t₂ = Ax {A = A} {s = t₂}

      -- □⊢ with t = [10]: [ A ^ (s ∘ [10]) ] ⊢ [ A ^ t₂ ] → [ □ A ^ s ] ⊢ [ A ^ t₂ ]
      -- Since s ∘ [10] = t₂, this works directly
      step-box : [ (□ A) ^ s ] ⊢ [ A ^ t₂ ]
      step-box = □⊢ {Γ = []} {A = A} {s = s} {t = [10]} {Δ = [ A ^ t₂ ]} ax-t₂

      -- Convert for ⊢□: need [ A ^ insertToken 1 (insertToken 0 s) ]
      step-box' : [ (□ A) ^ s ] ⊢ [ A ^ insertToken 1 (insertToken 0 s) ]
      step-box' = subst (λ p → [ (□ A) ^ s ] ⊢ [ A ^ p ]) t₂≡insert step-box

      -- Convert fresh-t₁-1 to work with insertToken form
      fresh-t₁-1' : 1 ∉Pos (insertToken 0 s)
      fresh-t₁-1' = subst (1 ∉Pos_) t₁≡insert fresh-t₁-1
  in
  ⊢⇒ {Γ = []} {A = □ A} {s = s} {B = □ (□ A)} {Δ = []}
    (⊢□ {x = 0}
      fresh-s-0 freshΓ₁-0 (TokenFresh-[] {x = 0})
      (⊢□ {x = 1}
        fresh-t₁-1' freshΓ₁-1 (TokenFresh-[] {x = 1})
        step-box'))

-- Axiom G: ♢ □ A ⇒ □ ♢ A
-- This requires a derivation using the interaction of □ and ♢
--
-- Derivation tree (bottom-up):
-- Goal: [] ⊢ [ (♢ (□ A) ⇒ □ (♢ A)) ^ s ]
--
-- Step 1: ⊢⇒
--   Premise: [ (♢ (□ A)) ^ s ] ⊢ [ (□ (♢ A)) ^ s ]
--
-- Step 2: ♢⊢ with eigenposition x=0
--   Premise: [ (□ A) ^ t ] ⊢ [ (□ (♢ A)) ^ s ] where t = s ∘ [0]
--
-- Step 3: ⊢□ with eigenposition y=1
--   Premise: [ (□ A) ^ t ] ⊢ [ (♢ A) ^ r ] where r = s ∘ [1]
--
-- Step 4: ⊢♢ with t' = [0]
--   Premise: [ (□ A) ^ t ] ⊢ [ A ^ δ ] where δ = r ∘ [0] = s ∘ [1] ∘ [0] = s ∘ [0] ∘ [1]
--
-- Step 5: □⊢ with t' = [1]
--   Premise: [ A ^ δ ] ⊢ [ A ^ δ ] where t ∘ [1] = s ∘ [0] ∘ [1] = δ
--
-- Step 6: Ax
-- Axiom G specialized to empty position for weak completeness
derive-AxC : ∀ {A : Formula} → [] ⊢ [ (♢ (□ A) ⇒ □ (♢ A)) ^ ε ]
derive-AxC {A} =
  let s : Position
      s = ε
      t = insertToken 0 s        -- position for □ A after ♢⊢
      r = insertToken 1 s        -- eigenposition for ⊢□
      δ = insertToken 1 t        -- shared position: insert 1 into (insert 0 s)
      -- 0 and 1 are trivially fresh for empty position
      fresh-s-0 : 0 ∉Pos s
      fresh-s-0 = λ ()
      fresh-s-1 : 1 ∉Pos s
      fresh-s-1 = λ ()
      -- TokenFresh for ♢⊢
      fresh-Δ-♢⊢ : TokenFresh 0 (((□ (♢ A)) ^ s) ∷ [])
      fresh-Δ-♢⊢ = TokenFresh-singleton {x = 0} {A = □ (♢ A)} {s = s} fresh-s-0
      -- TokenFresh 1 for context [ □ A ^ t ]
      -- t = insertToken 0 s, and 1 ∉Pos t requires 1 ∉Pos s and 1 ≢ 0
      fresh-t-1 : 1 ∉Pos t
      fresh-t-1 = ∉Pos-insertToken 0 1 s fresh-s-1 1≢0
      fresh-Γ-⊢□ : TokenFresh 1 (((□ A) ^ t) ∷ [])
      fresh-Γ-⊢□ = TokenFresh-singleton {x = 1} {A = □ A} {s = t} fresh-t-1

      -- Proof that r ∘ [0] ≡ δ
      -- r ∘ [0] = merge r [0] = insertToken 0 r (by merge-singleton)
      -- insertToken 0 (insertToken 1 s) = insertToken 1 (insertToken 0 s) = δ (by insertToken-swap)
      eq-r0-δ : r ∘ singleton-pos 0 ≡ δ
      eq-r0-δ = merge-singleton r 0 ∙ insertToken-swap 0 1 s

      -- Proof that t ∘ [1] ≡ δ (for □⊢ which expects LHS [ A ^ (t ∘ [1]) ])
      eq-t1-δ : t ∘ singleton-pos 1 ≡ δ
      eq-t1-δ = merge-singleton t 1

      -- Ax gives [ A ^ δ ] ⊢ [ A ^ δ ] but ⊢♢ expects RHS [ A ^ (r ∘ [0]) ]
      -- and □⊢ expects LHS [ A ^ (t ∘ [1]) ] = [ A ^ δ ]
      -- Need to convert RHS from δ to (r ∘ [0])
      ax-subst : [ A ^ δ ] ⊢ [ A ^ (r ∘ singleton-pos 0) ]
      ax-subst = subst (λ pos → [ A ^ δ ] ⊢ [ A ^ pos ]) (sym eq-r0-δ) (Ax {A = A} {s = δ})

      -- Convert LHS from δ to (t ∘ [1]) for □⊢
      ax-subst' : [ A ^ (t ∘ singleton-pos 1) ] ⊢ [ A ^ (r ∘ singleton-pos 0) ]
      ax-subst' = subst (λ pos → [ A ^ pos ] ⊢ [ A ^ (r ∘ singleton-pos 0) ]) (sym eq-t1-δ) ax-subst
  in
  ⊢⇒ {Γ = []} {A = ♢ (□ A)} {s = s} {B = □ (♢ A)} {Δ = []}
    -- Step 1: ⊢⇒ gives us [ ♢ (□ A) ^ s ] ⊢ [ □ (♢ A) ^ s ]
    (♢⊢ {x = 0}
      fresh-s-0 (TokenFresh-[] {x = 0}) fresh-Δ-♢⊢
      -- Step 2: ♢⊢ gives us [ □ A ^ t ] ⊢ [ □ (♢ A) ^ s ]
      (⊢□ {x = 1}
        fresh-s-1 fresh-Γ-⊢□ (TokenFresh-[] {x = 1})
        -- Step 3: ⊢□ gives us [ □ A ^ t ] ⊢ [ ♢ A ^ r ]
        (⊢♢ {t = singleton-pos 0}
          -- Step 4: ⊢♢ gives us [ □ A ^ t ] ⊢ [ A ^ (r ∘ [0]) ]
          (□⊢ {Γ = []} {A = A} {s = t} {t = singleton-pos 1} {Δ = [ A ^ (r ∘ singleton-pos 0) ]}
            -- Step 5: □⊢ gives us [ A ^ (t ∘ [1]) ] ⊢ [ A ^ (r ∘ [0]) ]
            ax-subst'))))

-- Completeness Theorem
completeness : ∀ {A} → ⊢S4dot2 A → [] ⊢ [ A ^ ε ]
completeness (ax (P1 {A} {B})) = derive-P1
completeness (ax P2) = derive-P2
completeness (ax P3) = derive-P3
completeness (ax K) = derive-K
completeness (ax D) = derive-D
completeness (ax T) = derive-T
completeness (ax Ax4) = derive-Ax4
completeness (ax AxC) = derive-AxC
completeness (MP {A} {B} p1 p2) =
  let
    -- MP : ⊢S4dot2 A → ⊢S4dot2 (A ⇒ B) → ⊢S4dot2 B
    -- p1 : ⊢S4dot2 A  →  completeness p1 : [] ⊢ [ A ^ ε ]
    -- p2 : ⊢S4dot2 (A ⇒ B)  →  completeness p2 : [] ⊢ [ (A ⇒ B) ^ ε ]
    -- We need [] ⊢ [ B ^ ε ]

    -- Step 1: [ A ⇒ B ] ⊢ [ B ]
    -- Using ⇒⊢ on Ax {B} and completeness p1
    -- ⇒⊢ : (Γ₁ ,, [ B ] ⊢ Δ₁) → (Γ₂ ⊢ [ A ] ,, Δ₂) → (Γ₁ ,, Γ₂ ,, [ A ⇒ B ] ⊢ Δ₁ ,, Δ₂)
    -- Premise 1: [ B ] ⊢ [ B ]. (Ax {B})  → Γ₁=[], Δ₁=[B]
    -- Premise 2: [] ⊢ [ A ]. (completeness p1)  → Γ₂=[], Δ₂=[]
    -- Result: [] ,, [] ,, [ A ⇒ B ] ⊢ [ B ] ,, []
    -- i.e. [ A ⇒ B ] ⊢ [ B ]

    proof-A⇒B-to-B : [ (A ⇒ B) ^ ε ] ⊢ [ B ^ ε ]
    proof-A⇒B-to-B = ⇒⊢ {Γ₁ = []} {B = B} {s = ε} {Δ₁ = [ B ^ ε ]} {Γ₂ = []} {A = A} {Δ₂ = []}
                       (Ax {A = B} {s = ε}) (completeness p1)

    -- Step 2: Cut with p2 (which proves A ⇒ B)
    -- completeness p2 : [] ⊢ [ (A ⇒ B) ^ ε ]
    -- Cut : (Γ₁ ⊢ [ C ] ,, Δ₁) → (Γ₂ ,, [ C ] ⊢ Δ₂) → (Γ₁ ,, Γ₂ ⊢ Δ₁ ,, Δ₂)
    -- Γ₁=[], Δ₁=[]. C = A ⇒ B.
    -- Γ₂=[], Δ₂=[B].
    -- Result: [] ⊢ [ B ].

  in Cut (completeness p2) proof-A⇒B-to-B

completeness (NEC {A} p) =
  let
    -- p : ⊢ A
    -- IH: [] ⊢ [ A ^ ε ]
    -- Goal: [] ⊢ [ (□ A) ^ ε ]
    -- Use ⊢□ with new signature.
    -- Γ=[], Δ=[], s=ε, eigenposition x chosen to be fresh.
    -- Premise: [] ⊢ [ A ^ (ε ∘ singleton-pos x) ] = [] ⊢ [ A ^ singleton-pos x ]

    ih : [] ⊢ [ A ^ ε ]
    ih = completeness p

    -- Use a fresh token greater than any eigenposition in ih
    x : Token
    x = suc (maxEigenposToken ih)

    t : Position
    t = singleton-pos x

    -- NoEigenposInt holds because x > all eigenpositions in ih
    nc : NoEigenposInt t ih
    nc = NoEigenposInt-singleton-fresh x ih (suc-≤-suc ≤-refl)

    lifted : [] ⊢ [ A ^ t ]
    lifted = lift-proof t ih nc

    -- x is fresh for empty position (trivially true)
    fresh-ε : x ∉Pos ε
    fresh-ε = λ ()

  in ⊢□ {x = x} fresh-ε (TokenFresh-[] {x = x}) (TokenFresh-[] {x = x}) lifted
