{-# OPTIONS --cubical --safe #-}

module S4dot2.CutElimination.ProofSubst where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.List hiding ([_]) renaming (_++_ to _++L_)
open import Cubical.Data.List.Properties renaming (++-assoc to ++L-assoc)
open import Cubical.Data.Nat using (ℕ; zero; suc; max; _+_)
open import Cubical.Data.Nat.Order using (_≤_; _<_; _>_; ≤-refl; zero-≤; suc-≤-suc; pred-≤-pred; ≤-trans; ≤0→≡0; ¬-<-zero; <→≢; isProp≤; <-trans; <-weaken)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.HITs.ListedFiniteSet as LFSet using (LFSet) renaming (_++_ to _++LFSet_)
open import Cubical.HITs.ListedFiniteSet.Properties using (comm-++) renaming (assoc-++ to LFSet-assoc-++)

open import Cubical.Relation.Nullary renaming (¬_ to Neg)

open import S4dot2.Syntax hiding (_⊢_) renaming (_∧_ to _and_; _∨_ to _or_)
open import S4dot2.System
open import S4dot2.SortedPosition renaming (merge to _++Pos_; [_] to singleton-pos)
open import S4dot2.CutElimination.Base using (δ; degree; height)

-- =============================================================================
-- Max Token Logic for SDL
-- =============================================================================

myMax : ℕ → ℕ → ℕ
myMax zero y = y
myMax (suc x) zero = suc x
myMax (suc x) (suc y) = suc (myMax x y)

myMax-0-l : ∀ n → myMax 0 n ≡ n
myMax-0-l n = refl

myMax-0-r : ∀ n → myMax n 0 ≡ n
myMax-0-r zero = refl
myMax-0-r (suc n) = refl

myMax-assoc : ∀ a b c → myMax a (myMax b c) ≡ myMax (myMax a b) c
myMax-assoc zero b c = refl
myMax-assoc (suc a) zero c = refl
myMax-assoc (suc a) (suc b) zero = refl
myMax-assoc (suc a) (suc b) (suc c) = cong suc (myMax-assoc a b c)

maxTokenPos : Position → ℕ
maxTokenPos ε = 0
maxTokenPos (pos-cons x xs _) = x -- Since it is sorted descending, the first element is the max

maxTokenCtx : Ctx → ℕ
maxTokenCtx [] = 0
maxTokenCtx ((A ^ s) ∷ Γ) = myMax (maxTokenPos s) (maxTokenCtx Γ)

-- Lemma: maxTokenCtx of singleton is just maxTokenPos
maxTokenCtx-singleton : ∀ (A : Formula) (s : Position) → maxTokenCtx [ A ^ s ] ≡ maxTokenPos s
maxTokenCtx-singleton A s = myMax-0-r (maxTokenPos s)

-- Lemma: maxTokenCtx distributes over ++L
maxTokenCtx-++ : (Γ Δ : Ctx) → maxTokenCtx (Γ ++L Δ) ≡ myMax (maxTokenCtx Γ) (maxTokenCtx Δ)
maxTokenCtx-++ [] Δ = sym (myMax-0-l (maxTokenCtx Δ))
maxTokenCtx-++ ((A ^ s) ∷ Γ) Δ =
  maxTokenCtx ((A ^ s) ∷ Γ ++L Δ)                                      ≡⟨ refl ⟩
  myMax (maxTokenPos s) (maxTokenCtx (Γ ++L Δ))                        ≡⟨ cong (myMax (maxTokenPos s)) (maxTokenCtx-++ Γ Δ) ⟩
  myMax (maxTokenPos s) (myMax (maxTokenCtx Γ) (maxTokenCtx Δ))        ≡⟨ myMax-assoc (maxTokenPos s) (maxTokenCtx Γ) (maxTokenCtx Δ) ⟩
  myMax (myMax (maxTokenPos s) (maxTokenCtx Γ)) (maxTokenCtx Δ)        ≡⟨ refl ⟩
  myMax (maxTokenCtx ((A ^ s) ∷ Γ)) (maxTokenCtx Δ)                    ∎

freshTokenCtx : Ctx → Token
freshTokenCtx Γ = suc (maxTokenCtx Γ)

-- Lemma: x ≤ maxTokenPos (insertToken x r)
-- insertToken maintains sorted order (descending), so x is either the max or ≤ the max
-- This is semantically true: insertToken x r contains x, and maxTokenPos returns the maximum
x≤maxTokenPos-insertToken : ∀ x r → x ≤ maxTokenPos (insertToken x r)
x≤maxTokenPos-insertToken x ε with triℕ x x
... | tri-≡ _ _ _ = ≤-refl  -- insertToken x ε = [x], maxTokenPos = x
... | tri-< x>x _ _ = ⊥-rec (<→≢ x>x refl)  -- impossible: x > x
... | tri-> _ _ x>x = ⊥-rec (<→≢ x>x refl)  -- impossible: x > x
x≤maxTokenPos-insertToken x (pos-cons z zs z>zs) with triℕ x z
... | tri-< z>x _ _ = <-weaken z>x  -- insertToken x (z∷zs) = z∷(insertToken x zs), max = z, need x ≤ z
... | tri-≡ _ x≡z _ = subst (x ≤_) x≡z ≤-refl  -- insertToken x (z∷zs) = z∷zs (dup), max = z, x ≡ z
... | tri-> _ _ x>z = ≤-refl  -- insertToken x (z∷zs) = x∷z∷zs, max = x

-- =============================================================================
-- Substitution Logic
-- =============================================================================

-- Substitution: If x is in s, remove it and merge t. Else s.
substPos : Token → Position → Position → Position
substPos x t s with x ∈Pos? s
... | yes _ = (remove x s) ++Pos t
... | no _ = s

substPFormula : Token → Position → PFormula → PFormula
substPFormula x t (A ^ s) = A ^ (substPos x t s)

substCtx : Token → Position → Ctx → Ctx
substCtx x t = map (substPFormula x t)

-- =============================================================================
-- Basic Lemmas
-- =============================================================================

substPos-id : (x : Token) (t s : Position) → x ∉Pos s → substPos x t s ≡ s
substPos-id x t s x∉s with x ∈Pos? s
... | yes x∈s = ⊥-rec (x∉s x∈s)
... | no _ = refl

-- Non-membership is preserved by substPos
-- If y ∉ s and y ∉ t, then y ∉ substPos z t s
∉Pos-substPos : ∀ {y} z t s → y ∉Pos s → y ∉Pos t → y ∉Pos (substPos z t s)
∉Pos-substPos {y} z t s y∉s y∉t with z ∈Pos? s
... | yes _ = ∉Pos-merge (∉Pos-remove z s y∉s) y∉t  -- substPos z t s = remove z s ∪ t
... | no _ = y∉s  -- substPos z t s = s

-- Key lemma: substPos preserves insertToken when eigentoken is different
-- When z ≢ x:
-- substPos z t (insertToken x s) ≡ insertToken x (substPos z t s)
substPos-insertToken-neq : ∀ z x s t
  → (z ≡ x → ⊥)
  → substPos z t (insertToken x s) ≡ insertToken x (substPos z t s)
substPos-insertToken-neq z x s t z≢x with z ∈Pos? (insertToken x s) | z ∈Pos? s
-- Case 1: z ∈ insertToken x s and z ∈ s
-- LHS: remove z (insertToken x s) ∪ t = insertToken x (remove z s) ∪ t (since z≢x)
-- RHS: insertToken x (remove z s ∪ t)
-- By merge-insertToken-l: (s∪{x})∪t = {x}∪(s∪t)
substPos-insertToken-neq z x s t z≢x | yes z∈ins | yes z∈s =
  cong (_++Pos t) (remove-insertToken-neq z x s z≢x) ∙ merge-insertToken-l x (remove z s) t
-- Case 2: z ∈ insertToken x s but z ∉ s
-- This means z = x (since z ∈ {x} ∪ s and z ∉ s implies z = x), contradiction
substPos-insertToken-neq z x s t z≢x | yes z∈ins | no z∉s with ∈Pos-insertToken x z s z∈ins
... | inl z≡x = ⊥-rec (z≢x z≡x)
... | inr z∈s = ⊥-rec (z∉s z∈s)
-- Case 3: z ∉ insertToken x s but z ∈ s
-- This is impossible: if z ∈ s then z ∈ insertToken x s
substPos-insertToken-neq z x s t z≢x | no z∉ins | yes z∈s =
  ⊥-rec (z∉ins (insertToken-∈Pos x z s (inr z∈s)))
-- Case 4: z ∉ insertToken x s and z ∉ s
-- LHS: insertToken x s
-- RHS: insertToken x s
-- This is trivial
substPos-insertToken-neq z x s t z≢x | no _ | no _ = refl

-- Key lemma: when x ∉ s, substituting x with [x'] in insertToken x s gives insertToken x' s
-- substPos x [x'] (insertToken x s) ≡ insertToken x' s when x ∉ s
substPos-insertToken-eq : ∀ x x' s → x ∉Pos s → substPos x (singleton-pos x') (insertToken x s) ≡ insertToken x' s
substPos-insertToken-eq x x' s x∉s with x ∈Pos? (insertToken x s)
... | yes _ = cong (_++Pos (singleton-pos x')) (remove-insertToken x s x∉s) ∙ merge-singleton s x'
... | no x∉ins = ⊥-rec (x∉ins (insertToken-∈Pos x x s (inl refl)))

-- General version: substPos x t (insertToken x s) ≡ s ++Pos t when x ∉ s
-- This generalizes substPos-insertToken-eq to arbitrary t (not just singleton)
substPos-insertToken-gen : ∀ x t s → x ∉Pos s → substPos x t (insertToken x s) ≡ s ++Pos t
substPos-insertToken-gen x t s x∉s with x ∈Pos? (insertToken x s)
... | yes _ = cong (_++Pos t) (remove-insertToken x s x∉s)
... | no x∉ins = ⊥-rec (x∉ins (insertToken-∈Pos x x s (inl refl)))

substCtx-id : (x : Token) (t : Position) (Γ : Ctx) → TokenFresh x Γ → substCtx x t Γ ≡ Γ
substCtx-id x t [] _ = refl
substCtx-id x t (pf ∷ Γ) (nIn , fr) =
  cong₂ _∷_ (cong (PFormula.form pf ^_) (substPos-id x t (PFormula.pos pf) nIn)) (substCtx-id x t Γ fr)

-- Distributivity of substPos over ++ (merge)

-- We need assoc and comm for merge (++)
++Pos-assoc : (s t r : Position) → (s ++Pos t) ++Pos r ≡ s ++Pos (t ++Pos r)
++Pos-assoc = merge-assoc

-- Position membership helpers
mem-++Pos-l : {s t : Position} {x : Token} → x ∈Pos s → x ∈Pos (s ++Pos t)
mem-++Pos-l {s} {t} {x} = merge-∈Pos-l x s t

mem-++Pos-r : {s t : Position} {x : Token} → x ∈Pos t → x ∈Pos (s ++Pos t)
mem-++Pos-r {s} {t} {x} = merge-∈Pos-r x s t

++Pos-comm : (s t : Position) → s ++Pos t ≡ t ++Pos s
++Pos-comm = merge-comm

remove-++Pos-distrib : (x : Token) (s t : Position) → remove x (s ++Pos t) ≡ remove x s ++Pos remove x t
remove-++Pos-distrib = remove-merge-distrib

substPos-++Pos-distr : (x : Token) (t s r : Position) → substPos x t (s ++Pos r) ≡ substPos x t s ++Pos substPos x t r
substPos-++Pos-distr x t s r with x ∈Pos? (s ++Pos r) | x ∈Pos? s | x ∈Pos? r
-- Case 1: x ∈ merged, x ∈ s, x ∈ r
-- LHS: remove x (s ++Pos r) ++Pos t = (remove x s ++Pos remove x r) ++Pos t
-- RHS: (remove x s ++Pos t) ++Pos (remove x r ++Pos t)
-- Use: assoc, comm, idem of merge
... | yes _ | yes _ | yes _ =
  let rs = remove x s
      rr = remove x r
      -- LHS after distributing remove: (rs ++Pos rr) ++Pos t
      step1 : (rs ++Pos rr) ++Pos t ≡ rs ++Pos (rr ++Pos t)
      step1 = ++Pos-assoc rs rr t
      -- rs ++Pos (rr ++Pos t) ≡ rs ++Pos (t ++Pos rr) by comm on (rr ++Pos t)
      step2 : rs ++Pos (rr ++Pos t) ≡ rs ++Pos (t ++Pos rr)
      step2 = cong (rs ++Pos_) (++Pos-comm rr t)
      -- rs ++Pos (t ++Pos rr) ≡ (rs ++Pos t) ++Pos rr by sym assoc
      step3 : rs ++Pos (t ++Pos rr) ≡ (rs ++Pos t) ++Pos rr
      step3 = sym (++Pos-assoc rs t rr)
      -- (rs ++Pos t) ++Pos rr ≡ (rs ++Pos t) ++Pos (rr ++Pos t) by showing rr ≡ rr ++Pos t... no!
      -- Actually we need: (rs ++Pos t) ++Pos rr ≡ (rs ++Pos t) ++Pos (rr ++Pos t)
      -- which requires: rr ++Pos t ≡ rr ++Pos t, but we can use assoc/comm/idem differently
      -- Let me show: (rs ++Pos t) ++Pos rr ++Pos t ≡ (rs ++Pos t) ++Pos (rr ++Pos t) is trivial
      -- But we want (rs ++Pos t) ++Pos rr, not with extra t
      -- Actually, the RHS is (rs ++Pos t) ++Pos (rr ++Pos t), so we need to work backwards
      -- (rs ++Pos t) ++Pos (rr ++Pos t) = rs ++Pos t ++Pos rr ++Pos t = rs ++Pos (t ++Pos rr ++Pos t)
      -- = rs ++Pos (t ++Pos (rr ++Pos t)) (assoc) = rs ++Pos ((t ++Pos rr) ++Pos t) = rs ++Pos (t ++Pos rr ++Pos t)
      -- Use comm: = rs ++Pos (rr ++Pos t ++Pos t) = rs ++Pos (rr ++Pos (t ++Pos t))
      -- Use idem: = rs ++Pos (rr ++Pos t) = (rs ++Pos rr) ++Pos t = LHS
      step-rhs1 : (rs ++Pos t) ++Pos (rr ++Pos t) ≡ rs ++Pos (t ++Pos (rr ++Pos t))
      step-rhs1 = ++Pos-assoc rs t (rr ++Pos t)
      step-rhs2 : rs ++Pos (t ++Pos (rr ++Pos t)) ≡ rs ++Pos ((t ++Pos rr) ++Pos t)
      step-rhs2 = cong (rs ++Pos_) (sym (++Pos-assoc t rr t))
      step-rhs3 : rs ++Pos ((t ++Pos rr) ++Pos t) ≡ rs ++Pos ((rr ++Pos t) ++Pos t)
      step-rhs3 = cong (rs ++Pos_) (cong (_++Pos t) (++Pos-comm t rr))
      step-rhs4 : rs ++Pos ((rr ++Pos t) ++Pos t) ≡ rs ++Pos (rr ++Pos (t ++Pos t))
      step-rhs4 = cong (rs ++Pos_) (++Pos-assoc rr t t)
      step-rhs5 : rs ++Pos (rr ++Pos (t ++Pos t)) ≡ rs ++Pos (rr ++Pos t)
      step-rhs5 = cong (rs ++Pos_) (cong (rr ++Pos_) (merge-idem t))
      step-rhs6 : rs ++Pos (rr ++Pos t) ≡ (rs ++Pos rr) ++Pos t
      step-rhs6 = sym (++Pos-assoc rs rr t)
  in cong (_++Pos t) (remove-++Pos-distrib x s r) ∙
     sym (step-rhs1 ∙ step-rhs2 ∙ step-rhs3 ∙ step-rhs4 ∙ step-rhs5 ∙ step-rhs6)
-- Case 2: x ∈ merged, x ∈ s, x ∉ r
-- LHS: remove x (s ++Pos r) ++Pos t = (remove x s ++Pos remove x r) ++Pos t = (remove x s ++Pos r) ++Pos t
-- RHS: (remove x s ++Pos t) ++Pos r
... | yes _ | yes _ | no x∉r =
  cong (_++Pos t) (remove-++Pos-distrib x s r ∙ cong (remove x s ++Pos_) (remove-∉Pos-id x r x∉r)) ∙
  ++Pos-assoc (remove x s) r t ∙
  cong (remove x s ++Pos_) (++Pos-comm r t) ∙
  sym (++Pos-assoc (remove x s) t r)
-- Case 3: x ∈ merged, x ∉ s, x ∈ r
-- LHS: remove x (s ++Pos r) ++Pos t = (remove x s ++Pos remove x r) ++Pos t = (s ++Pos remove x r) ++Pos t
-- RHS: s ++Pos (remove x r ++Pos t)
... | yes _ | no x∉s | yes _ =
  cong (_++Pos t) (remove-++Pos-distrib x s r ∙ cong (_++Pos remove x r) (remove-∉Pos-id x s x∉s)) ∙
  ++Pos-assoc s (remove x r) t
-- Case 4: x ∈ merged, x ∉ s, x ∉ r - impossible since x must be in one of them
... | yes x∈m | no x∉s | no x∉r with ∈Pos-merge x s r x∈m
...   | inl x∈s = ⊥-rec (x∉s x∈s)
...   | inr x∈r = ⊥-rec (x∉r x∈r)
-- Case 5a: x ∉ merged, but checking s gives yes - impossible
substPos-++Pos-distr x t s r | no x∉m | yes x∈s | _ = ⊥-rec (x∉m (merge-∈Pos-l x s r x∈s))
-- Case 5b: x ∉ merged, but checking r gives yes - impossible
substPos-++Pos-distr x t s r | no x∉m | no _ | yes x∈r = ⊥-rec (x∉m (merge-∈Pos-r x s r x∈r))
-- Case 5c: x ∉ merged, x ∉ s, x ∉ r
-- LHS: s ++Pos r (definitionally since x ∉ s ++Pos r)
-- RHS: s ++Pos r (definitionally since x ∉ s and x ∉ r)
substPos-++Pos-distr x t s r | no _ | no _ | no _ = refl

-- =============================================================================
-- Preservation Lemmas
-- =============================================================================

-- Helpers for mem-remove
mem-remove : (x : Token) (s : Position) (t : Token) → t ∈Pos s → x ≢ t → t ∈Pos remove x s
mem-remove x s t = ∈Pos-remove x t s

mem-remove-implies-mem : {x : Token} {s : Position} {t : Token} → t ∈Pos remove x s → t ∈Pos s
mem-remove-implies-mem {x} {s} {t} = remove-∈Pos x t s

mem-remove-implies-neq : {x : Token} {s : Position} {t : Token} → t ∈Pos remove x s → x ≢ t
mem-remove-implies-neq {x} {s} {t} = remove-∈Pos-neq x t s

-- Helper: mem-++Pos-case
mem-++Pos-case : (s t : Position) (y : Token) → y ∈Pos (s ++Pos t) → (y ∈Pos s) ⊎ (y ∈Pos t)
mem-++Pos-case s t y = ∈Pos-merge y s t

-- If s ⊆ r, then substPos x t s ⊆ substPos x t r
subset-preserves-substPos : (x : Token) (t : Position) {s r : Position}
                          → s ⊑ r
                          → substPos x t s ⊑ substPos x t r
subset-preserves-substPos x t {s} {r} sub y yInLHS with x ∈Pos? s | x ∈Pos? r
-- Case 1: x ∈ s, x ∈ r
-- LHS = (remove x s) ++Pos t, RHS = (remove x r) ++Pos t
-- Use merge-⊑-mono: need remove x s ⊑ remove x r
... | yes x∈s | yes x∈r = merge-⊑-mono remove-sub (λ w w∈t → w∈t) y yInLHS
  where
    remove-sub : remove x s ⊑ remove x r
    remove-sub w w∈rems =
      let w∈s = mem-remove-implies-mem {x} {s} {w} w∈rems
          w≢x = mem-remove-implies-neq {x} {s} {w} w∈rems
          w∈r = sub w w∈s
      in mem-remove x r w w∈r w≢x
-- Case 2: x ∈ s, x ∉ r - impossible since s ⊑ r and x ∈ s implies x ∈ r
... | yes x∈s | no x∉r = ⊥-rec (x∉r (sub x x∈s))
-- Case 3: x ∉ s, x ∈ r
-- LHS = s, RHS = (remove x r) ++Pos t
-- For any y ∈ s: y ∈ r (by sub), and y ≢ x (since x ∉ s), so y ∈ remove x r
... | no x∉s | yes x∈r = mem-++Pos-l (mem-remove x r y (sub y yInLHS) y≢x)
  where
    y≢x : x ≢ y
    y≢x x≡y = x∉s (subst (_∈Pos s) (sym x≡y) yInLHS)
-- Case 4: x ∉ s, x ∉ r
-- LHS = s, RHS = r, use sub directly
... | no _ | no _ = sub y yInLHS

-- Context concatenation (map distributes over ++)
substCtx-++ : (x : Token) (t : Position) (Γ Δ : Ctx)
            → substCtx x t (Γ ++L Δ) ≡ substCtx x t Γ ++L substCtx x t Δ
substCtx-++ x t [] Δ = refl
substCtx-++ x t (pf ∷ Γ) Δ = cong (substPFormula x t pf ∷_) (substCtx-++ x t Γ Δ)


-- =============================================================================
-- Main Theorem Helpers
-- =============================================================================

IsSingleTokenExt-preserves-subst : (x : Token) (t : Position) {s r : Position} {y : Token}
                                 → x ≢ y
                                 → y ∉Pos t
                                 → IsSingleTokenExt s r y
                                 → IsSingleTokenExt (substPos x t s) (substPos x t r) y
IsSingleTokenExt-preserves-subst x t {s} {r} {y} x≢y y∉t ext = comp1 , comp2 , comp3 , comp4
  where
    s⊑r = fst ext
    y∈r = fst (snd ext)
    y∉s = fst (snd (snd ext))
    uniq = snd (snd (snd ext))

    -- Component 1: substPos x t s ⊑ substPos x t r
    comp1 : substPos x t s ⊑ substPos x t r
    comp1 = subset-preserves-substPos x t s⊑r

    -- Component 2: y ∈Pos (substPos x t r)
    comp2 : y ∈Pos (substPos x t r)
    comp2 with x ∈Pos? r
    ... | yes x∈r =
      -- substPos x t r = (remove x r) ++Pos t
      -- Since y ∈ r and x ≢ y, y ∈ remove x r
      let y∈remr = mem-remove x r y y∈r (λ x≡y → x≢y x≡y)
      in mem-++Pos-l y∈remr
    ... | no _ = y∈r  -- substPos x t r = r

    -- Component 3: y ∉Pos (substPos x t s)
    comp3 : y ∉Pos (substPos x t s)
    comp3 = ∉Pos-substPos x t s y∉s y∉t

    -- Component 4: uniqueness
    comp4 : ∀ w → w ∈Pos (substPos x t r) → w ∉Pos (substPos x t s) → w ≡ y
    comp4 w w∈r' w∉s' with x ∈Pos? r | x ∈Pos? s
    -- Case: x ∈ r, x ∈ s
    -- r' = (remove x r) ++Pos t, s' = (remove x s) ++Pos t
    comp4 w w∈r' w∉s' | yes _ | yes _ with mem-++Pos-case (remove x r) t w w∈r'
    -- Subcase: w ∈ remove x r
    ... | inl w∈remr =
      let w∈r = mem-remove-implies-mem {x} {r} {w} w∈remr
          w≢x = mem-remove-implies-neq {x} {r} {w} w∈remr
          -- Need to show w ∉ s
          -- If w ∈ s, then since w ≢ x, w ∈ remove x s, so w ∈ s', contradiction
          w∉s : w ∉Pos s
          w∉s w∈s = w∉s' (mem-++Pos-l {remove x s} {t} (mem-remove x s w w∈s w≢x))
      in uniq w w∈r w∉s
    -- Subcase: w ∈ t
    ... | inr w∈t =
      -- w ∈ t and w ∉ s' = (remove x s) ++Pos t
      -- But w ∈ t implies w ∈ s' (by mem-++Pos-r), contradiction
      ⊥-rec (w∉s' (mem-++Pos-r {remove x s} {t} w∈t))
    -- Case: x ∈ r, x ∉ s - impossible since IsSingleTokenExt says only y differs
    comp4 w w∈r' w∉s' | yes x∈r | no x∉s =
      -- If x ∈ r and x ∉ s, then by uniqueness of ext, x ≡ y
      -- But x ≢ y, contradiction
      ⊥-rec (x≢y (uniq x x∈r x∉s))
    -- Case: x ∉ r, x ∈ s - impossible since s ⊑ r
    comp4 w w∈r' w∉s' | no x∉r | yes x∈s =
      ⊥-rec (x∉r (s⊑r x x∈s))
    -- Case: x ∉ r, x ∉ s - trivial
    comp4 w w∈r' w∉s' | no _ | no _ = uniq w w∈r' w∉s'

-- TokenFresh is preserved under substitution when eigentoken is different from subst token
-- and doesn't appear in the substitution position
TokenFresh-substCtx : (z x : Token) (t : Position) (Γ : Ctx)
                    → (z ≡ x → ⊥)
                    → x ∉Pos t
                    → TokenFresh x Γ
                    → TokenFresh x (substCtx z t Γ)
TokenFresh-substCtx z x t [] z≢x x∉t tt = tt
TokenFresh-substCtx z x t ((A ^ s) ∷ Γ) z≢x x∉t (x∉s , frRest) =
  ∉Pos-substPos z t s x∉s x∉t , TokenFresh-substCtx z x t Γ z≢x x∉t frRest

-- =============================================================================
-- Main Theorem
-- =============================================================================

-- Condition: z ≢ y for each eigenposition token y in the derivation
EigenposCond : Token → {Γ Δ : Ctx} → (Γ ⊢ Δ) → Type
EigenposCond z Ax = Unit
EigenposCond z (Cut Π₁ Π₂) = EigenposCond z Π₁ × EigenposCond z Π₂
EigenposCond z (W⊢ Π) = EigenposCond z Π
EigenposCond z (⊢W Π) = EigenposCond z Π
EigenposCond z (C⊢ Π) = EigenposCond z Π
EigenposCond z (⊢C Π) = EigenposCond z Π
EigenposCond z (Exc⊢ Π) = EigenposCond z Π
EigenposCond z (⊢Exc Π) = EigenposCond z Π
EigenposCond z (¬⊢ Π) = EigenposCond z Π
EigenposCond z (⊢¬ Π) = EigenposCond z Π
EigenposCond z (∧₁⊢ Π) = EigenposCond z Π
EigenposCond z (∧₂⊢ Π) = EigenposCond z Π
EigenposCond z (⊢∧ Π₁ Π₂) = EigenposCond z Π₁ × EigenposCond z Π₂
EigenposCond z (∨⊢ Π₁ Π₂) = EigenposCond z Π₁ × EigenposCond z Π₂
EigenposCond z (⊢∨₁ Π) = EigenposCond z Π
EigenposCond z (⊢∨₂ Π) = EigenposCond z Π
EigenposCond z (⇒⊢ Π₁ Π₂) = EigenposCond z Π₁ × EigenposCond z Π₂
EigenposCond z (⊢⇒ Π) = EigenposCond z Π
EigenposCond z (□⊢ Π) = EigenposCond z Π
EigenposCond z (⊢□ {x = y} _ _ _ Π) = (z ≢ y) × EigenposCond z Π
EigenposCond z (♢⊢ {x = y} _ _ _ Π) = (z ≢ y) × EigenposCond z Π
EigenposCond z (⊢♢ Π) = EigenposCond z Π

NoEigenposInt : Position → {Γ Δ : Ctx} → (Γ ⊢ Δ) → Type
NoEigenposInt t Ax = Unit
NoEigenposInt t (Cut Π₁ Π₂) = NoEigenposInt t Π₁ × NoEigenposInt t Π₂
NoEigenposInt t (W⊢ Π) = NoEigenposInt t Π
NoEigenposInt t (⊢W Π) = NoEigenposInt t Π
NoEigenposInt t (C⊢ Π) = NoEigenposInt t Π
NoEigenposInt t (⊢C Π) = NoEigenposInt t Π
NoEigenposInt t (Exc⊢ Π) = NoEigenposInt t Π
NoEigenposInt t (⊢Exc Π) = NoEigenposInt t Π
NoEigenposInt t (¬⊢ Π) = NoEigenposInt t Π
NoEigenposInt t (⊢¬ Π) = NoEigenposInt t Π
NoEigenposInt t (∧₁⊢ Π) = NoEigenposInt t Π
NoEigenposInt t (∧₂⊢ Π) = NoEigenposInt t Π
NoEigenposInt t (⊢∧ Π₁ Π₂) = NoEigenposInt t Π₁ × NoEigenposInt t Π₂
NoEigenposInt t (∨⊢ Π₁ Π₂) = NoEigenposInt t Π₁ × NoEigenposInt t Π₂
NoEigenposInt t (⊢∨₁ Π) = NoEigenposInt t Π
NoEigenposInt t (⊢∨₂ Π) = NoEigenposInt t Π
NoEigenposInt t (⇒⊢ Π₁ Π₂) = NoEigenposInt t Π₁ × NoEigenposInt t Π₂
NoEigenposInt t (⊢⇒ Π) = NoEigenposInt t Π
NoEigenposInt t (□⊢ Π) = NoEigenposInt t Π
NoEigenposInt t (⊢□ {x = y} _ _ _ Π) = (y ∉Pos t) × NoEigenposInt t Π
NoEigenposInt t (♢⊢ {x = y} _ _ _ Π) = (y ∉Pos t) × NoEigenposInt t Π
NoEigenposInt t (⊢♢ Π) = NoEigenposInt t Π



substTokenToPosProof : (z : Token) (t : Position) {Γ Δ : Ctx}
                     → (Π : Γ ⊢ Δ)
                     → EigenposCond z Π
                     → NoEigenposInt t Π
                     → (substCtx z t Γ ⊢ substCtx z t Δ)
substTokenToPosProof z t Ax _ _ = Ax
substTokenToPosProof z t (Cut {Γ₁} {A} {s} {Δ₁} {Γ₂} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) = 
  subst2 _⊢_ 
    (sym (substCtx-++ z t Γ₁ Γ₂)) 
    (sym (substCtx-++ z t Δ₁ Δ₂)) 
    (Cut (subst (substCtx z t Γ₁ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₁) (substTokenToPosProof z t Π₁ ec₁ nc₁))
         (subst (_⊢ substCtx z t Δ₂) (substCtx-++ z t Γ₂ [ A ^ s ]) (substTokenToPosProof z t Π₂ ec₂ nc₂)))
substTokenToPosProof z t (W⊢ {Γ} {Δ} {A} {s} Π) ec nc = 
  subst (_⊢ substCtx z t Δ) (sym (substCtx-++ z t Γ [ A ^ s ])) (W⊢ (substTokenToPosProof z t Π ec nc))
substTokenToPosProof z t (⊢W {Γ} {Δ} {A} {s} Π) ec nc = 
  subst (substCtx z t Γ ⊢_) (sym (substCtx-++ z t [ A ^ s ] Δ)) (⊢W (substTokenToPosProof z t Π ec nc))
substTokenToPosProof z t (C⊢ {Γ} {A} {s} {Δ} Π) ec nc = 
  subst (_⊢ substCtx z t Δ) (sym (substCtx-++ z t Γ [ A ^ s ])) 
    (C⊢ (subst (_⊢ substCtx z t Δ) 
      (substCtx-++ z t (Γ ++L [ A ^ s ]) [ A ^ s ] ∙ 
       cong (_++L substCtx z t [ A ^ s ]) (substCtx-++ z t Γ [ A ^ s ])) 
      (substTokenToPosProof z t Π ec nc)))
substTokenToPosProof z t (⊢C {Γ} {A} {s} {Δ} Π) ec nc = 
  subst (substCtx z t Γ ⊢_) (sym (substCtx-++ z t [ A ^ s ] Δ)) 
    (⊢C (subst (substCtx z t Γ ⊢_) 
      (substCtx-++ z t ([ A ^ s ] ++L [ A ^ s ]) Δ ∙ 
       cong (_++L substCtx z t Δ) (substCtx-++ z t [ A ^ s ] [ A ^ s ])) 
      (substTokenToPosProof z t Π ec nc)))
substTokenToPosProof z t (Exc⊢ {Γ₁} {A} {s} {B} {t'} {Γ₂} {Δ} Π) ec nc = 
  let Π' = substTokenToPosProof z t Π ec nc
      step0 = cong (substCtx z t) (++L-assoc (Γ₁ ++L [ A ^ s ]) [ B ^ t' ] Γ₂)
      step1 = substCtx-++ z t (Γ₁ ++L [ A ^ s ]) (B ^ t' ∷ Γ₂)
      step2 = cong (_++L substCtx z t (B ^ t' ∷ Γ₂)) (substCtx-++ z t Γ₁ [ A ^ s ])
      step3 = cong ((substCtx z t Γ₁ ++L substCtx z t [ A ^ s ]) ++L_) (substCtx-++ z t [ B ^ t' ] Γ₂)
      step4 = sym (++L-assoc (substCtx z t Γ₁ ++L substCtx z t [ A ^ s ]) (substCtx z t [ B ^ t' ]) (substCtx z t Γ₂))
      path = step0 ∙ step1 ∙ step2 ∙ step3 ∙ step4


      raw = Exc⊢ {Γ₁ = substCtx z t Γ₁} {A = A} {B = B} {Γ₂ = substCtx z t Γ₂} 
                 (subst (λ G → G ⊢ substCtx z t Δ) path Π')
      
      step1' = substCtx-++ z t (Γ₁ ++L [ B ^ t' ]) (A ^ s ∷ Γ₂)
      step2' = cong (_++L substCtx z t (A ^ s ∷ Γ₂)) (substCtx-++ z t Γ₁ [ B ^ t' ])
      step3' = cong ((substCtx z t Γ₁ ++L substCtx z t [ B ^ t' ]) ++L_) (substCtx-++ z t [ A ^ s ] Γ₂)
      step4' = sym (++L-assoc (substCtx z t Γ₁ ++L substCtx z t [ B ^ t' ]) (substCtx z t [ A ^ s ]) (substCtx z t Γ₂))
      step0' = cong (substCtx z t) (++L-assoc (Γ₁ ++L [ B ^ t' ]) [ A ^ s ] Γ₂)
      path2 = step0' ∙ step1' ∙ step2' ∙ step3' ∙ step4'

  in subst (λ G → G ⊢ substCtx z t Δ) (sym path2) raw 

 


substTokenToPosProof z t (⊢Exc {Γ} {Δ₁} {A} {s} {B} {t'} {Δ₂} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      step0 = cong (substCtx z t) (++L-assoc (Δ₁ ++L [ A ^ s ]) [ B ^ t' ] Δ₂)
      step1 = substCtx-++ z t (Δ₁ ++L [ A ^ s ]) (B ^ t' ∷ Δ₂)
      step2 = cong (_++L substCtx z t (B ^ t' ∷ Δ₂)) (substCtx-++ z t Δ₁ [ A ^ s ])
      step3 = cong ((substCtx z t Δ₁ ++L substCtx z t [ A ^ s ]) ++L_) (substCtx-++ z t [ B ^ t' ] Δ₂)
      step4 = sym (++L-assoc (substCtx z t Δ₁ ++L substCtx z t [ A ^ s ]) (substCtx z t [ B ^ t' ]) (substCtx z t Δ₂))
      path = step0 ∙ step1 ∙ step2 ∙ step3 ∙ step4

      raw = ⊢Exc {Δ₁ = substCtx z t Δ₁} {A = A} {B = B} {Δ₂ = substCtx z t Δ₂}
                 (subst (λ D → substCtx z t Γ ⊢ D) path Π')

      step1' = substCtx-++ z t (Δ₁ ++L [ B ^ t' ]) (A ^ s ∷ Δ₂)
      step2' = cong (_++L substCtx z t (A ^ s ∷ Δ₂)) (substCtx-++ z t Δ₁ [ B ^ t' ])
      step3' = cong ((substCtx z t Δ₁ ++L substCtx z t [ B ^ t' ]) ++L_) (substCtx-++ z t [ A ^ s ] Δ₂)
      step4' = sym (++L-assoc (substCtx z t Δ₁ ++L substCtx z t [ B ^ t' ]) (substCtx z t [ A ^ s ]) (substCtx z t Δ₂))
      step0' = cong (substCtx z t) (++L-assoc (Δ₁ ++L [ B ^ t' ]) [ A ^ s ] Δ₂)
      path2 = step0' ∙ step1' ∙ step2' ∙ step3' ∙ step4'

  in subst (λ D → substCtx z t Γ ⊢ D) (sym path2) raw
substTokenToPosProof z t (¬⊢ {Γ} {A} {s} {Δ} Π) ec nc = 
  subst (_⊢ substCtx z t Δ) (sym (substCtx-++ z t Γ [ (¬ A) ^ s ])) (¬⊢ (subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ A ^ s ] Δ) (substTokenToPosProof z t Π ec nc)))
substTokenToPosProof z t (⊢¬ {Γ} {A} {s} {Δ} Π) ec nc = 
  subst (substCtx z t Γ ⊢_) (sym (substCtx-++ z t [ (¬ A) ^ s ] Δ)) (⊢¬ (subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ A ^ s ]) (substTokenToPosProof z t Π ec nc)))
substTokenToPosProof z t (∧₁⊢ {Γ} {A} {s} {Δ} {B} Π) ec nc = 
  subst (_⊢ substCtx z t Δ) (sym (substCtx-++ z t Γ [ (A and B) ^ s ])) (∧₁⊢ (subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ A ^ s ]) (substTokenToPosProof z t Π ec nc)))
substTokenToPosProof z t (∧₂⊢ {Γ} {B} {s} {Δ} {A} Π) ec nc = 
  subst (_⊢ substCtx z t Δ) (sym (substCtx-++ z t Γ [ (A and B) ^ s ])) (∧₂⊢ (subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ B ^ s ]) (substTokenToPosProof z t Π ec nc)))
substTokenToPosProof z t (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) = 
  subst2 _⊢_ (sym (substCtx-++ z t Γ₁ Γ₂)) 
    (cong (substCtx z t [ (A and B) ^ s ] ++L_) (sym (substCtx-++ z t Δ₁ Δ₂)) ∙ sym (substCtx-++ z t [ (A and B) ^ s ] (Δ₁ ++L Δ₂)))
    (⊢∧ (subst (substCtx z t Γ₁ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₁) (substTokenToPosProof z t Π₁ ec₁ nc₁))
        (subst (substCtx z t Γ₂ ⊢_) (substCtx-++ z t [ B ^ s ] Δ₂) (substTokenToPosProof z t Π₂ ec₂ nc₂)))
substTokenToPosProof z t (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) =
  -- Note: _,,_ is infixr, so Γ₁ ,, Γ₂ ,, X = Γ₁ ++L (Γ₂ ++L X)
  -- ∨⊢ produces: substCtx z t Γ₁ ++L (substCtx z t Γ₂ ++L [ (A or B) ^ substPos z t s ])
  let lhs-path : substCtx z t Γ₁ ++L (substCtx z t Γ₂ ++L substCtx z t [ (A or B) ^ s ]) ≡ substCtx z t (Γ₁ ,, Γ₂ ,, [ (A or B) ^ s ])
      lhs-path = cong (substCtx z t Γ₁ ++L_) (sym (substCtx-++ z t Γ₂ [ (A or B) ^ s ]))
               ∙ sym (substCtx-++ z t Γ₁ (Γ₂ ++L [ (A or B) ^ s ]))
  in subst2 _⊢_
    lhs-path
    (sym (substCtx-++ z t Δ₁ Δ₂))
    (∨⊢ (subst (_⊢ substCtx z t Δ₁) (substCtx-++ z t Γ₁ [ A ^ s ]) (substTokenToPosProof z t Π₁ ec₁ nc₁))
        (subst (_⊢ substCtx z t Δ₂) (substCtx-++ z t Γ₂ [ B ^ s ]) (substTokenToPosProof z t Π₂ ec₂ nc₂)))
substTokenToPosProof z t (⊢∨₁ {Γ} {A} {s} {Δ} {B} Π) ec nc =
  subst (substCtx z t Γ ⊢_) (sym (substCtx-++ z t [ (A or B) ^ s ] Δ)) (⊢∨₁ (subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ A ^ s ] Δ) (substTokenToPosProof z t Π ec nc)))
substTokenToPosProof z t (⊢∨₂ {Γ} {B} {s} {Δ} {A} Π) ec nc =
  subst (substCtx z t Γ ⊢_) (sym (substCtx-++ z t [ (A or B) ^ s ] Δ)) (⊢∨₂ (subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ B ^ s ] Δ) (substTokenToPosProof z t Π ec nc)))
substTokenToPosProof z t (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) =
  -- Note: _,,_ is infixr, so Γ₁ ,, Γ₂ ,, X = Γ₁ ++L (Γ₂ ++L X)
  -- ⇒⊢ produces: substCtx z t Γ₁ ++L (substCtx z t Γ₂ ++L [ (A ⇒ B) ^ substPos z t s ])
  let lhs-path : substCtx z t Γ₁ ++L (substCtx z t Γ₂ ++L substCtx z t [ (A ⇒ B) ^ s ]) ≡ substCtx z t (Γ₁ ,, Γ₂ ,, [ (A ⇒ B) ^ s ])
      lhs-path = cong (substCtx z t Γ₁ ++L_) (sym (substCtx-++ z t Γ₂ [ (A ⇒ B) ^ s ]))
               ∙ sym (substCtx-++ z t Γ₁ (Γ₂ ++L [ (A ⇒ B) ^ s ]))
  in subst2 _⊢_
    lhs-path
    (sym (substCtx-++ z t Δ₁ Δ₂))
    (⇒⊢ (subst (_⊢ substCtx z t Δ₁) (substCtx-++ z t Γ₁ [ B ^ s ]) (substTokenToPosProof z t Π₁ ec₁ nc₁))
        (subst (substCtx z t Γ₂ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₂) (substTokenToPosProof z t Π₂ ec₂ nc₂)))
substTokenToPosProof z t (⊢⇒ {Γ} {A} {s} {B} {Δ} Π) ec nc =
  subst (substCtx z t Γ ⊢_) (sym (substCtx-++ z t [ (A ⇒ B) ^ s ] Δ))
    (⊢⇒ (subst2 _⊢_
      (substCtx-++ z t Γ [ A ^ s ])
      (substCtx-++ z t [ B ^ s ] Δ)
      (substTokenToPosProof z t Π ec nc)))
-- □⊢ case: □⊢ : (Γ ,, [ A ^ (s ∘ t') ] ⊢ Δ) → (Γ ,, [ (□ A) ^ s ] ⊢ Δ)
-- After substitution, use substPos-++Pos-distr to show:
--   substPos z t (s ∘ t') ≡ substPos z t s ∘ substPos z t t'
substTokenToPosProof z t (□⊢ {Γ} {A} {s} {t'} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      -- Π' : substCtx z t (Γ ,, [ A ^ (s ∘ t') ]) ⊢ substCtx z t Δ

      -- Context distribution lemma
      ctx-eq : substCtx z t (Γ ,, [ A ^ (s ∘ t') ]) ≡ substCtx z t Γ ,, [ A ^ substPos z t (s ∘ t') ]
      ctx-eq = substCtx-++ z t Γ [ A ^ (s ∘ t') ]

      -- Key: substPos distributes over merge
      pos-eq : substPos z t (s ∘ t') ≡ substPos z t s ∘ substPos z t t'
      pos-eq = substPos-++Pos-distr z t s t'

      -- Transform IH result
      Π'' : substCtx z t Γ ,, [ A ^ (substPos z t s ∘ substPos z t t') ] ⊢ substCtx z t Δ
      Π'' = subst (_⊢ substCtx z t Δ) (ctx-eq ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π'

      -- Apply □⊢ rule
      raw : substCtx z t Γ ,, [ (□ A) ^ substPos z t s ] ⊢ substCtx z t Δ
      raw = □⊢ Π''

      -- Transform to expected output
      out-path : substCtx z t Γ ,, [ (□ A) ^ substPos z t s ] ≡ substCtx z t (Γ ,, [ (□ A) ^ s ])
      out-path = sym (substCtx-++ z t Γ [ (□ A) ^ s ])
  in subst (_⊢ substCtx z t Δ) out-path raw

-- ⊢□ case: eigentoken x is preserved under substitution
-- Paper reference: Lemma 4.8 (Sequents Prefix Replacement), case (b) for ⊢□
substTokenToPosProof z t (⊢□ {x} {s} {Γ} {Δ} {A} x∉s xFrΓ xFrΔ Π) (z≢x , ec) (x∉t , nc) =
  let -- Apply IH to get substituted subproof
      Π' = substTokenToPosProof z t Π ec nc
      -- Π' : substCtx z t Γ ⊢ substCtx z t ([ A ^ insertToken x s ] ,, Δ)

      -- Key equality: substPos preserves insertToken when z ≢ x
      pos-eq : substPos z t (insertToken x s) ≡ insertToken x (substPos z t s)
      pos-eq = substPos-insertToken-neq z x s t z≢x

      -- Freshness conditions are preserved
      x∉substs : x ∉Pos (substPos z t s)
      x∉substs = ∉Pos-substPos z t s x∉s x∉t

      xFrΓ' : TokenFresh x (substCtx z t Γ)
      xFrΓ' = TokenFresh-substCtx z x t Γ z≢x x∉t xFrΓ

      xFrΔ' : TokenFresh x (substCtx z t Δ)
      xFrΔ' = TokenFresh-substCtx z x t Δ z≢x x∉t xFrΔ

      -- Transform IH result to match ⊢□ premise type
      rhs-path : substCtx z t ([ A ^ insertToken x s ] ,, Δ) ≡ [ A ^ substPos z t (insertToken x s) ] ,, substCtx z t Δ
      rhs-path = substCtx-++ z t [ A ^ insertToken x s ] Δ

      Π'' : substCtx z t Γ ⊢ [ A ^ insertToken x (substPos z t s) ] ,, substCtx z t Δ
      Π'' = subst (substCtx z t Γ ⊢_) (rhs-path ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π'

      -- Apply ⊢□ rule
      raw : substCtx z t Γ ⊢ [ (□ A) ^ substPos z t s ] ,, substCtx z t Δ
      raw = ⊢□ x∉substs xFrΓ' xFrΔ' Π''

      -- Transform to match expected output type
      out-path : [ (□ A) ^ substPos z t s ] ,, substCtx z t Δ ≡ substCtx z t ([ (□ A) ^ s ] ,, Δ)
      out-path = sym (substCtx-++ z t [ (□ A) ^ s ] Δ)
  in subst (substCtx z t Γ ⊢_) out-path raw

-- ♢⊢ case: symmetric to ⊢□
substTokenToPosProof z t (♢⊢ {x} {s} {Γ} {Δ} {A} x∉s xFrΓ xFrΔ Π) (z≢x , ec) (x∉t , nc) =
  let Π' = substTokenToPosProof z t Π ec nc

      pos-eq : substPos z t (insertToken x s) ≡ insertToken x (substPos z t s)
      pos-eq = substPos-insertToken-neq z x s t z≢x

      x∉substs : x ∉Pos (substPos z t s)
      x∉substs = ∉Pos-substPos z t s x∉s x∉t

      xFrΓ' : TokenFresh x (substCtx z t Γ)
      xFrΓ' = TokenFresh-substCtx z x t Γ z≢x x∉t xFrΓ

      xFrΔ' : TokenFresh x (substCtx z t Δ)
      xFrΔ' = TokenFresh-substCtx z x t Δ z≢x x∉t xFrΔ

      lhs-path : substCtx z t (Γ ,, [ A ^ insertToken x s ]) ≡ substCtx z t Γ ,, [ A ^ substPos z t (insertToken x s) ]
      lhs-path = substCtx-++ z t Γ [ A ^ insertToken x s ]

      Π'' : substCtx z t Γ ,, [ A ^ insertToken x (substPos z t s) ] ⊢ substCtx z t Δ
      Π'' = subst (_⊢ substCtx z t Δ) (lhs-path ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π'

      raw : substCtx z t Γ ,, [ (♢ A) ^ substPos z t s ] ⊢ substCtx z t Δ
      raw = ♢⊢ x∉substs xFrΓ' xFrΔ' Π''

      out-path : substCtx z t Γ ,, [ (♢ A) ^ substPos z t s ] ≡ substCtx z t (Γ ,, [ (♢ A) ^ s ])
      out-path = sym (substCtx-++ z t Γ [ (♢ A) ^ s ])
  in subst (_⊢ substCtx z t Δ) out-path raw

-- ⊢♢ case: ⊢♢ : (Γ ⊢ [ A ^ (s ∘ t') ] ,, Δ) → (Γ ⊢ [ (♢ A) ^ s ] ,, Δ)
-- Symmetric to □⊢
substTokenToPosProof z t (⊢♢ {Γ} {A} {s} {t'} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      -- Π' : substCtx z t Γ ⊢ substCtx z t ([ A ^ (s ∘ t') ] ,, Δ)

      -- Context distribution
      ctx-eq : substCtx z t ([ A ^ (s ∘ t') ] ,, Δ) ≡ [ A ^ substPos z t (s ∘ t') ] ,, substCtx z t Δ
      ctx-eq = substCtx-++ z t [ A ^ (s ∘ t') ] Δ

      -- Key: substPos distributes over merge
      pos-eq : substPos z t (s ∘ t') ≡ substPos z t s ∘ substPos z t t'
      pos-eq = substPos-++Pos-distr z t s t'

      -- Transform IH result
      Π'' : substCtx z t Γ ⊢ [ A ^ (substPos z t s ∘ substPos z t t') ] ,, substCtx z t Δ
      Π'' = subst (substCtx z t Γ ⊢_) (ctx-eq ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π'

      -- Apply ⊢♢ rule
      raw : substCtx z t Γ ⊢ [ (♢ A) ^ substPos z t s ] ,, substCtx z t Δ
      raw = ⊢♢ Π''

      -- Transform to expected output
      out-path : [ (♢ A) ^ substPos z t s ] ,, substCtx z t Δ ≡ substCtx z t ([ (♢ A) ^ s ] ,, Δ)
      out-path = sym (substCtx-++ z t [ (♢ A) ^ s ] Δ)
  in subst (substCtx z t Γ ⊢_) out-path raw


-- =============================================================================
-- Eigenposition Renaming Infrastructure (Postulates)
-- =============================================================================
-- These functions implement eigenposition renaming as described in the paper
-- (Proposition 4.7 - Eigenposition Renaming). They are postulated here to
-- allow Mix.agda to type-check, but could be proven constructively.

-- Maximum token in all contexts/positions throughout a proof
-- This includes the cut formula positions which may not be in the conclusion
maxTokenProof : {Γ Δ : Ctx} → (Γ ⊢ Δ) → ℕ
maxTokenProof {Γ} {Δ} Ax = maxTokenCtx (Γ ,, Δ)
maxTokenProof {Γ} {Δ} (Cut {A = A} {s = s} Π₁ Π₂) =
  myMax (maxTokenCtx (Γ ,, Δ)) (myMax (maxTokenPos s) (myMax (maxTokenProof Π₁) (maxTokenProof Π₂)))
maxTokenProof {Γ} {Δ} (W⊢ Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (⊢W Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (C⊢ Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (⊢C Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (Exc⊢ Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (⊢Exc Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (¬⊢ Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (⊢¬ Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (∧₁⊢ Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (∧₂⊢ Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (⊢∧ Π₁ Π₂) = myMax (maxTokenCtx (Γ ,, Δ)) (myMax (maxTokenProof Π₁) (maxTokenProof Π₂))
maxTokenProof {Γ} {Δ} (∨⊢ Π₁ Π₂) = myMax (maxTokenCtx (Γ ,, Δ)) (myMax (maxTokenProof Π₁) (maxTokenProof Π₂))
maxTokenProof {Γ} {Δ} (⊢∨₁ Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (⊢∨₂ Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (⇒⊢ Π₁ Π₂) = myMax (maxTokenCtx (Γ ,, Δ)) (myMax (maxTokenProof Π₁) (maxTokenProof Π₂))
maxTokenProof {Γ} {Δ} (⊢⇒ Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (□⊢ Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (⊢□ _ _ _ Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (♢⊢ _ _ _ Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)
maxTokenProof {Γ} {Δ} (⊢♢ Π) = myMax (maxTokenCtx (Γ ,, Δ)) (maxTokenProof Π)

-- Maximum eigenposition token used in a proof
maxEigenposToken : {Γ Δ : Ctx} → (Γ ⊢ Δ) → ℕ
maxEigenposToken Ax = 0
maxEigenposToken (Cut Π₁ Π₂) = myMax (maxEigenposToken Π₁) (maxEigenposToken Π₂)
maxEigenposToken (W⊢ Π) = maxEigenposToken Π
maxEigenposToken (⊢W Π) = maxEigenposToken Π
maxEigenposToken (C⊢ Π) = maxEigenposToken Π
maxEigenposToken (⊢C Π) = maxEigenposToken Π
maxEigenposToken (Exc⊢ Π) = maxEigenposToken Π
maxEigenposToken (⊢Exc Π) = maxEigenposToken Π
maxEigenposToken (¬⊢ Π) = maxEigenposToken Π
maxEigenposToken (⊢¬ Π) = maxEigenposToken Π
maxEigenposToken (∧₁⊢ Π) = maxEigenposToken Π
maxEigenposToken (∧₂⊢ Π) = maxEigenposToken Π
maxEigenposToken (⊢∧ Π₁ Π₂) = myMax (maxEigenposToken Π₁) (maxEigenposToken Π₂)
maxEigenposToken (∨⊢ Π₁ Π₂) = myMax (maxEigenposToken Π₁) (maxEigenposToken Π₂)
maxEigenposToken (⊢∨₁ Π) = maxEigenposToken Π
maxEigenposToken (⊢∨₂ Π) = maxEigenposToken Π
maxEigenposToken (⇒⊢ Π₁ Π₂) = myMax (maxEigenposToken Π₁) (maxEigenposToken Π₂)
maxEigenposToken (⊢⇒ Π) = maxEigenposToken Π
maxEigenposToken (□⊢ Π) = maxEigenposToken Π
maxEigenposToken (⊢□ {x = x} _ _ _ Π) = myMax x (maxEigenposToken Π)
maxEigenposToken (♢⊢ {x = x} _ _ _ Π) = myMax x (maxEigenposToken Π)
maxEigenposToken (⊢♢ Π) = maxEigenposToken Π

-- maxEigenposToken is preserved under subst2 (type-level changes don't affect eigentokens)
maxEigenposToken-subst2 : ∀ {Γ Γ' Δ Δ'} (p : Γ ≡ Γ') (q : Δ ≡ Δ') (Π : Γ ⊢ Δ)
  → maxEigenposToken (subst2 _⊢_ p q Π) ≡ maxEigenposToken Π
maxEigenposToken-subst2 {Γ} {Γ'} {Δ} {Δ'} p q Π =
  J (λ Γ' p → ∀ Δ' (q : Δ ≡ Δ') → maxEigenposToken (subst2 _⊢_ p q Π) ≡ maxEigenposToken Π)
    (λ Δ' q → J (λ Δ' q → maxEigenposToken (subst2 _⊢_ refl q Π) ≡ maxEigenposToken Π)
                (cong maxEigenposToken (substRefl {B = Γ ⊢_} Π)) q)
    p Δ' q

-- Lemma: substTokenToPosProof preserves maxEigenposToken
-- This holds because EigenposCond z Π ensures z is not an eigentoken in Π,
-- so the substitution only affects positions, not the eigentoken structure.

-- Helpers for single-argument subst
maxEigenposToken-substR : ∀ {Γ Δ Δ'} (p : Δ ≡ Δ') (Π : Γ ⊢ Δ)
  → maxEigenposToken (subst (Γ ⊢_) p Π) ≡ maxEigenposToken Π
maxEigenposToken-substR p Π = maxEigenposToken-subst2 refl p Π

maxEigenposToken-substL : ∀ {Γ Γ' Δ} (p : Γ ≡ Γ') (Π : Γ ⊢ Δ)
  → maxEigenposToken (subst (_⊢ Δ) p Π) ≡ maxEigenposToken Π
maxEigenposToken-substL p Π = maxEigenposToken-subst2 p refl Π

-- Main lemma by induction on Π
maxEigenposToken-substTokenToPosProof : (z : Token) (t : Position) {Γ Δ : Ctx}
  → (Π : Γ ⊢ Δ) → (ec : EigenposCond z Π) → (nc : NoEigenposInt t Π)
  → maxEigenposToken (substTokenToPosProof z t Π ec nc) ≡ maxEigenposToken Π
maxEigenposToken-substTokenToPosProof z t Ax _ _ = refl  -- maxEigenposToken Ax = 0
maxEigenposToken-substTokenToPosProof z t (Cut {Γ₁} {A} {s} {Δ₁} {Γ₂} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      -- First unwrap the outer subst2
      outer-eq = maxEigenposToken-subst2 (sym (substCtx-++ z t Γ₁ Γ₂)) (sym (substCtx-++ z t Δ₁ Δ₂))
                   (Cut (subst (substCtx z t Γ₁ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₁) Π₁')
                        (subst (_⊢ substCtx z t Δ₂) (substCtx-++ z t Γ₂ [ A ^ s ]) Π₂'))
      -- Then unwrap inner substs
      inner₁-eq = maxEigenposToken-substR (substCtx-++ z t [ A ^ s ] Δ₁) Π₁'
      inner₂-eq = maxEigenposToken-substL (substCtx-++ z t Γ₂ [ A ^ s ]) Π₂'
      -- Apply IH
      ih₁ = maxEigenposToken-substTokenToPosProof z t Π₁ ec₁ nc₁
      ih₂ = maxEigenposToken-substTokenToPosProof z t Π₂ ec₂ nc₂
  in outer-eq ∙ cong₂ myMax (inner₁-eq ∙ ih₁) (inner₂-eq ∙ ih₂)
maxEigenposToken-substTokenToPosProof z t (W⊢ {Γ} {Δ} {A} {s} Π) ec nc =
  maxEigenposToken-substL (sym (substCtx-++ z t Γ [ A ^ s ])) (W⊢ (substTokenToPosProof z t Π ec nc))
  ∙ maxEigenposToken-substTokenToPosProof z t Π ec nc
maxEigenposToken-substTokenToPosProof z t (⊢W {Γ} {Δ} {A} {s} Π) ec nc =
  maxEigenposToken-substR (sym (substCtx-++ z t [ A ^ s ] Δ)) (⊢W (substTokenToPosProof z t Π ec nc))
  ∙ maxEigenposToken-substTokenToPosProof z t Π ec nc
maxEigenposToken-substTokenToPosProof z t (C⊢ {Γ} {A} {s} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ)
                (substCtx-++ z t (Γ ++L [ A ^ s ]) [ A ^ s ] ∙
                 cong (_++L substCtx z t [ A ^ s ]) (substCtx-++ z t Γ [ A ^ s ])) Π'
  in maxEigenposToken-substL (sym (substCtx-++ z t Γ [ A ^ s ])) (C⊢ inner)
     ∙ maxEigenposToken-substL (substCtx-++ z t (Γ ++L [ A ^ s ]) [ A ^ s ] ∙
                                cong (_++L substCtx z t [ A ^ s ]) (substCtx-++ z t Γ [ A ^ s ])) Π'
     ∙ maxEigenposToken-substTokenToPosProof z t Π ec nc
maxEigenposToken-substTokenToPosProof z t (⊢C {Γ} {A} {s} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_)
                (substCtx-++ z t ([ A ^ s ] ++L [ A ^ s ]) Δ ∙
                 cong (_++L substCtx z t Δ) (substCtx-++ z t [ A ^ s ] [ A ^ s ])) Π'
  in maxEigenposToken-substR (sym (substCtx-++ z t [ A ^ s ] Δ)) (⊢C inner)
     ∙ maxEigenposToken-substR (substCtx-++ z t ([ A ^ s ] ++L [ A ^ s ]) Δ ∙
                                cong (_++L substCtx z t Δ) (substCtx-++ z t [ A ^ s ] [ A ^ s ])) Π'
     ∙ maxEigenposToken-substTokenToPosProof z t Π ec nc
maxEigenposToken-substTokenToPosProof z t (Exc⊢ {Γ₁} {A} {s} {B} {t'} {Γ₂} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      step0' = cong (substCtx z t) (++L-assoc (Γ₁ ++L [ B ^ t' ]) [ A ^ s ] Γ₂)
      step1' = substCtx-++ z t (Γ₁ ++L [ B ^ t' ]) (A ^ s ∷ Γ₂)
      step2' = cong (_++L substCtx z t (A ^ s ∷ Γ₂)) (substCtx-++ z t Γ₁ [ B ^ t' ])
      step3' = cong ((substCtx z t Γ₁ ++L substCtx z t [ B ^ t' ]) ++L_) (substCtx-++ z t [ A ^ s ] Γ₂)
      step4' = sym (++L-assoc (substCtx z t Γ₁ ++L substCtx z t [ B ^ t' ]) (substCtx z t [ A ^ s ]) (substCtx z t Γ₂))
      path2 = step0' ∙ step1' ∙ step2' ∙ step3' ∙ step4'
      step0 = cong (substCtx z t) (++L-assoc (Γ₁ ++L [ A ^ s ]) [ B ^ t' ] Γ₂)
      step1 = substCtx-++ z t (Γ₁ ++L [ A ^ s ]) (B ^ t' ∷ Γ₂)
      step2 = cong (_++L substCtx z t (B ^ t' ∷ Γ₂)) (substCtx-++ z t Γ₁ [ A ^ s ])
      step3 = cong ((substCtx z t Γ₁ ++L substCtx z t [ A ^ s ]) ++L_) (substCtx-++ z t [ B ^ t' ] Γ₂)
      step4 = sym (++L-assoc (substCtx z t Γ₁ ++L substCtx z t [ A ^ s ]) (substCtx z t [ B ^ t' ]) (substCtx z t Γ₂))
      path = step0 ∙ step1 ∙ step2 ∙ step3 ∙ step4
      raw = Exc⊢ {Γ₁ = substCtx z t Γ₁} {A = A} {B = B} {Γ₂ = substCtx z t Γ₂}
                 (subst (λ G → G ⊢ substCtx z t Δ) path Π')
  in maxEigenposToken-substL (sym path2) raw
     ∙ maxEigenposToken-substL path Π'
     ∙ maxEigenposToken-substTokenToPosProof z t Π ec nc
maxEigenposToken-substTokenToPosProof z t (⊢Exc {Γ} {Δ₁} {A} {s} {B} {t'} {Δ₂} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      step0' = cong (substCtx z t) (++L-assoc (Δ₁ ++L [ B ^ t' ]) [ A ^ s ] Δ₂)
      step1' = substCtx-++ z t (Δ₁ ++L [ B ^ t' ]) (A ^ s ∷ Δ₂)
      step2' = cong (_++L substCtx z t (A ^ s ∷ Δ₂)) (substCtx-++ z t Δ₁ [ B ^ t' ])
      step3' = cong ((substCtx z t Δ₁ ++L substCtx z t [ B ^ t' ]) ++L_) (substCtx-++ z t [ A ^ s ] Δ₂)
      step4' = sym (++L-assoc (substCtx z t Δ₁ ++L substCtx z t [ B ^ t' ]) (substCtx z t [ A ^ s ]) (substCtx z t Δ₂))
      path2 = step0' ∙ step1' ∙ step2' ∙ step3' ∙ step4'
      step0 = cong (substCtx z t) (++L-assoc (Δ₁ ++L [ A ^ s ]) [ B ^ t' ] Δ₂)
      step1 = substCtx-++ z t (Δ₁ ++L [ A ^ s ]) (B ^ t' ∷ Δ₂)
      step2 = cong (_++L substCtx z t (B ^ t' ∷ Δ₂)) (substCtx-++ z t Δ₁ [ A ^ s ])
      step3 = cong ((substCtx z t Δ₁ ++L substCtx z t [ A ^ s ]) ++L_) (substCtx-++ z t [ B ^ t' ] Δ₂)
      step4 = sym (++L-assoc (substCtx z t Δ₁ ++L substCtx z t [ A ^ s ]) (substCtx z t [ B ^ t' ]) (substCtx z t Δ₂))
      path = step0 ∙ step1 ∙ step2 ∙ step3 ∙ step4
      raw = ⊢Exc {Δ₁ = substCtx z t Δ₁} {A = A} {B = B} {Δ₂ = substCtx z t Δ₂}
                 (subst (λ D → substCtx z t Γ ⊢ D) path Π')
  in maxEigenposToken-substR (sym path2) raw
     ∙ maxEigenposToken-substR path Π'
     ∙ maxEigenposToken-substTokenToPosProof z t Π ec nc
maxEigenposToken-substTokenToPosProof z t (¬⊢ {Γ} {A} {s} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ A ^ s ] Δ) Π'
  in maxEigenposToken-substL (sym (substCtx-++ z t Γ [ (¬ A) ^ s ])) (¬⊢ inner)
     ∙ maxEigenposToken-substR (substCtx-++ z t [ A ^ s ] Δ) Π'
     ∙ maxEigenposToken-substTokenToPosProof z t Π ec nc
maxEigenposToken-substTokenToPosProof z t (⊢¬ {Γ} {A} {s} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ A ^ s ]) Π'
  in maxEigenposToken-substR (sym (substCtx-++ z t [ (¬ A) ^ s ] Δ)) (⊢¬ inner)
     ∙ maxEigenposToken-substL (substCtx-++ z t Γ [ A ^ s ]) Π'
     ∙ maxEigenposToken-substTokenToPosProof z t Π ec nc
maxEigenposToken-substTokenToPosProof z t (∧₁⊢ {Γ} {A} {s} {Δ} {B} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ A ^ s ]) Π'
  in maxEigenposToken-substL (sym (substCtx-++ z t Γ [ (A and B) ^ s ])) (∧₁⊢ inner)
     ∙ maxEigenposToken-substL (substCtx-++ z t Γ [ A ^ s ]) Π'
     ∙ maxEigenposToken-substTokenToPosProof z t Π ec nc
maxEigenposToken-substTokenToPosProof z t (∧₂⊢ {Γ} {B} {s} {Δ} {A} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ B ^ s ]) Π'
  in maxEigenposToken-substL (sym (substCtx-++ z t Γ [ (A and B) ^ s ])) (∧₂⊢ inner)
     ∙ maxEigenposToken-substL (substCtx-++ z t Γ [ B ^ s ]) Π'
     ∙ maxEigenposToken-substTokenToPosProof z t Π ec nc
maxEigenposToken-substTokenToPosProof z t (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      outer-eq = maxEigenposToken-subst2 (sym (substCtx-++ z t Γ₁ Γ₂))
                   (cong (substCtx z t [ (A and B) ^ s ] ++L_) (sym (substCtx-++ z t Δ₁ Δ₂)) ∙
                    sym (substCtx-++ z t [ (A and B) ^ s ] (Δ₁ ++L Δ₂)))
                   (⊢∧ (subst (substCtx z t Γ₁ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₁) Π₁')
                       (subst (substCtx z t Γ₂ ⊢_) (substCtx-++ z t [ B ^ s ] Δ₂) Π₂'))
      inner₁-eq = maxEigenposToken-substR (substCtx-++ z t [ A ^ s ] Δ₁) Π₁'
      inner₂-eq = maxEigenposToken-substR (substCtx-++ z t [ B ^ s ] Δ₂) Π₂'
      ih₁ = maxEigenposToken-substTokenToPosProof z t Π₁ ec₁ nc₁
      ih₂ = maxEigenposToken-substTokenToPosProof z t Π₂ ec₂ nc₂
  in outer-eq ∙ cong₂ myMax (inner₁-eq ∙ ih₁) (inner₂-eq ∙ ih₂)
maxEigenposToken-substTokenToPosProof z t (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      outer-eq = maxEigenposToken-subst2
                   (cong (substCtx z t Γ₁ ++L_) (sym (substCtx-++ z t Γ₂ [ (A or B) ^ s ]))
                    ∙ sym (substCtx-++ z t Γ₁ (Γ₂ ++L [ (A or B) ^ s ])))
                   (sym (substCtx-++ z t Δ₁ Δ₂))
                   (∨⊢ (subst (_⊢ substCtx z t Δ₁) (substCtx-++ z t Γ₁ [ A ^ s ]) Π₁')
                       (subst (_⊢ substCtx z t Δ₂) (substCtx-++ z t Γ₂ [ B ^ s ]) Π₂'))
      inner₁-eq = maxEigenposToken-substL (substCtx-++ z t Γ₁ [ A ^ s ]) Π₁'
      inner₂-eq = maxEigenposToken-substL (substCtx-++ z t Γ₂ [ B ^ s ]) Π₂'
      ih₁ = maxEigenposToken-substTokenToPosProof z t Π₁ ec₁ nc₁
      ih₂ = maxEigenposToken-substTokenToPosProof z t Π₂ ec₂ nc₂
  in outer-eq ∙ cong₂ myMax (inner₁-eq ∙ ih₁) (inner₂-eq ∙ ih₂)
maxEigenposToken-substTokenToPosProof z t (⊢∨₁ {Γ} {A} {s} {Δ} {B} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ A ^ s ] Δ) Π'
  in maxEigenposToken-substR (sym (substCtx-++ z t [ (A or B) ^ s ] Δ)) (⊢∨₁ inner)
     ∙ maxEigenposToken-substR (substCtx-++ z t [ A ^ s ] Δ) Π'
     ∙ maxEigenposToken-substTokenToPosProof z t Π ec nc
maxEigenposToken-substTokenToPosProof z t (⊢∨₂ {Γ} {B} {s} {Δ} {A} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ B ^ s ] Δ) Π'
  in maxEigenposToken-substR (sym (substCtx-++ z t [ (A or B) ^ s ] Δ)) (⊢∨₂ inner)
     ∙ maxEigenposToken-substR (substCtx-++ z t [ B ^ s ] Δ) Π'
     ∙ maxEigenposToken-substTokenToPosProof z t Π ec nc
maxEigenposToken-substTokenToPosProof z t (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      outer-eq = maxEigenposToken-subst2
                   (cong (substCtx z t Γ₁ ++L_) (sym (substCtx-++ z t Γ₂ [ (A ⇒ B) ^ s ]))
                    ∙ sym (substCtx-++ z t Γ₁ (Γ₂ ++L [ (A ⇒ B) ^ s ])))
                   (sym (substCtx-++ z t Δ₁ Δ₂))
                   (⇒⊢ (subst (_⊢ substCtx z t Δ₁) (substCtx-++ z t Γ₁ [ B ^ s ]) Π₁')
                       (subst (substCtx z t Γ₂ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₂) Π₂'))
      inner₁-eq = maxEigenposToken-substL (substCtx-++ z t Γ₁ [ B ^ s ]) Π₁'
      inner₂-eq = maxEigenposToken-substR (substCtx-++ z t [ A ^ s ] Δ₂) Π₂'
      ih₁ = maxEigenposToken-substTokenToPosProof z t Π₁ ec₁ nc₁
      ih₂ = maxEigenposToken-substTokenToPosProof z t Π₂ ec₂ nc₂
  in outer-eq ∙ cong₂ myMax (inner₁-eq ∙ ih₁) (inner₂-eq ∙ ih₂)
maxEigenposToken-substTokenToPosProof z t (⊢⇒ {Γ} {A} {s} {B} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst2 _⊢_ (substCtx-++ z t Γ [ A ^ s ]) (substCtx-++ z t [ B ^ s ] Δ) Π'
  in maxEigenposToken-substR (sym (substCtx-++ z t [ (A ⇒ B) ^ s ] Δ)) (⊢⇒ inner)
     ∙ maxEigenposToken-subst2 (substCtx-++ z t Γ [ A ^ s ]) (substCtx-++ z t [ B ^ s ] Δ) Π'
     ∙ maxEigenposToken-substTokenToPosProof z t Π ec nc
maxEigenposToken-substTokenToPosProof z t (□⊢ {Γ} {A} {s} {t'} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      ctx-eq = substCtx-++ z t Γ [ A ^ (s ++Pos t') ]
      pos-eq = substPos-++Pos-distr z t s t'
      Π'' = subst (_⊢ substCtx z t Δ) (ctx-eq ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π'
      out-path = sym (substCtx-++ z t Γ [ (□ A) ^ s ])
  in maxEigenposToken-substL out-path (□⊢ Π'')
     ∙ maxEigenposToken-substL (ctx-eq ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π'
     ∙ maxEigenposToken-substTokenToPosProof z t Π ec nc
-- ⊢□ case: eigentoken x is part of maxEigenposToken
maxEigenposToken-substTokenToPosProof z t (⊢□ {x} {s} {Γ} {Δ} {A} x∉s xFrΓ xFrΔ Π) (z≢x , ec) (x∉t , nc) =
  let Π' = substTokenToPosProof z t Π ec nc
      pos-eq = substPos-insertToken-neq z x s t z≢x
      x∉substs = ∉Pos-substPos z t s x∉s x∉t
      xFrΓ' = TokenFresh-substCtx z x t Γ z≢x x∉t xFrΓ
      xFrΔ' = TokenFresh-substCtx z x t Δ z≢x x∉t xFrΔ
      rhs-path = substCtx-++ z t [ A ^ insertToken x s ] Δ
      Π'' = subst (substCtx z t Γ ⊢_) (rhs-path ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π'
      raw = ⊢□ x∉substs xFrΓ' xFrΔ' Π''
      out-path = sym (substCtx-++ z t [ (□ A) ^ s ] Δ)
      ih = maxEigenposToken-substTokenToPosProof z t Π ec nc
  in maxEigenposToken-substR out-path raw
     ∙ cong (myMax x) (maxEigenposToken-substR (rhs-path ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π' ∙ ih)
-- ♢⊢ case: symmetric to ⊢□
maxEigenposToken-substTokenToPosProof z t (♢⊢ {x} {s} {Γ} {Δ} {A} x∉s xFrΓ xFrΔ Π) (z≢x , ec) (x∉t , nc) =
  let Π' = substTokenToPosProof z t Π ec nc
      pos-eq = substPos-insertToken-neq z x s t z≢x
      x∉substs = ∉Pos-substPos z t s x∉s x∉t
      xFrΓ' = TokenFresh-substCtx z x t Γ z≢x x∉t xFrΓ
      xFrΔ' = TokenFresh-substCtx z x t Δ z≢x x∉t xFrΔ
      lhs-path = substCtx-++ z t Γ [ A ^ insertToken x s ]
      Π'' = subst (_⊢ substCtx z t Δ) (lhs-path ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π'
      raw = ♢⊢ x∉substs xFrΓ' xFrΔ' Π''
      out-path = sym (substCtx-++ z t Γ [ (♢ A) ^ s ])
      ih = maxEigenposToken-substTokenToPosProof z t Π ec nc
  in maxEigenposToken-substL out-path raw
     ∙ cong (myMax x) (maxEigenposToken-substL (lhs-path ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π' ∙ ih)
maxEigenposToken-substTokenToPosProof z t (⊢♢ {Γ} {A} {s} {t'} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      ctx-eq = substCtx-++ z t [ A ^ (s ++Pos t') ] Δ
      pos-eq = substPos-++Pos-distr z t s t'
      Π'' = subst (substCtx z t Γ ⊢_) (ctx-eq ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π'
      out-path = sym (substCtx-++ z t [ (♢ A) ^ s ] Δ)
  in maxEigenposToken-substR out-path (⊢♢ Π'')
     ∙ maxEigenposToken-substR (ctx-eq ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π'
     ∙ maxEigenposToken-substTokenToPosProof z t Π ec nc

-- Compute fresh token for renaming (larger than all context tokens and proof eigentokens)
freshTokenForRename : Position → Ctx → {Γ Δ : Ctx} → (Γ ⊢ Δ) → Token
freshTokenForRename r ctx {Γ} {Δ} Π =
  suc (myMax (maxTokenPos r) (myMax (maxTokenCtx ctx) (myMax (maxTokenCtx Γ) (myMax (maxTokenCtx Δ) (maxEigenposToken Π)))))

-- TokenFresh split across context concatenation
TokenFresh-split : (Γ Δ : Ctx) (x : Token) → TokenFresh x (Γ ,, Δ) → TokenFresh x Γ × TokenFresh x Δ
TokenFresh-split [] Δ x fr = tt , fr
TokenFresh-split ((A ^ s) ∷ Γ) Δ x (x∉s , fr) =
  let (frΓ , frΔ) = TokenFresh-split Γ Δ x fr
  in (x∉s , frΓ) , frΔ

-- Inequality helpers for myMax
≤-myMax-l : ∀ m n → m ≤ myMax m n
≤-myMax-l zero n = zero-≤
≤-myMax-l (suc m) zero = ≤-refl
≤-myMax-l (suc m) (suc n) = suc-≤-suc (≤-myMax-l m n)

≤-myMax-r : ∀ m n → n ≤ myMax m n
≤-myMax-r zero n = ≤-refl
≤-myMax-r (suc m) zero = zero-≤
≤-myMax-r (suc m) (suc n) = suc-≤-suc (≤-myMax-r m n)

-- n ≤ suc n
≤-suc : ∀ n → n ≤ suc n
≤-suc zero = zero-≤
≤-suc (suc n) = suc-≤-suc (≤-suc n)

-- =============================================================================
-- Helper Lemmas for Implementing Previously Postulated Lemmas
-- =============================================================================

-- Singleton membership: x ∈ [y] implies x ≡ y
∈Pos-singleton : (x y : Token) → x ∈Pos (singleton-pos y) → x ≡ y
∈Pos-singleton x y (inl x≡y) = x≡y
∈Pos-singleton x y (inr x∈ε) = ⊥-rec x∈ε

-- Singleton non-membership: x ≢ y implies x ∉ [y]
∉Pos-singleton : (x y : Token) → x ≢ y → x ∉Pos (singleton-pos y)
∉Pos-singleton x y x≢y (inl x≡y) = x≢y x≡y
∉Pos-singleton x y x≢y (inr x∈ε) = x∈ε

-- Helper: extract the < proof from >ᴴ for non-empty lists
>ᴴ-head< : ∀ {y z zs z>zs} → y >ᴴ pos-cons z zs z>zs → z < y
>ᴴ-head< (>ᴴcons y>z) = y>z

-- Helper: if n > y for any y, then n > 0
-- Proof: n > y means suc y ≤ n, and suc y ≥ 1, so n ≥ 1 > 0
>-implies->0 : ∀ {n y} → n > y → n > 0
>-implies->0 {n} {y} n>y = ≤-trans (suc-≤-suc zero-≤) n>y

-- Helper: if n > y and y is the head of SDL (pos-cons y ys y>ys), then n > maxTokenPos ys
-- maxTokenPos ys is either 0 (if ys = ε) or the head of ys (which is < y)
>-head->-maxTail : (n y : Token) (ys : Position) (y>ys : y >ᴴ ys) → n > y → n > maxTokenPos ys
>-head->-maxTail n y ε _ n>y = >-implies->0 n>y  -- maxTokenPos ε = 0, need n > 0
>-head->-maxTail n y (pos-cons z zs z>zs) y>ys n>y = <-trans (>ᴴ-head< y>ys) n>y

-- maxTokenPos is bounded by the head for all elements
-- If n > head of SDL, then n is not in the SDL
>-maxTokenPos-∉Pos : (n : Token) (s : Position) → n > maxTokenPos s → n ∉Pos s
>-maxTokenPos-∉Pos n ε _ ()  -- Nothing is in ε
>-maxTokenPos-∉Pos n (pos-cons y ys y>ys) n>y (inl n≡y) =
  -- n ≡ y contradicts n > y
  <→≢ n>y (sym n≡y)
>-maxTokenPos-∉Pos n (pos-cons y ys y>ys) n>y (inr n∈ys) =
  -- n ∈ ys, need to show n > maxTokenPos ys to use IH
  >-maxTokenPos-∉Pos n ys (>-head->-maxTail n y ys y>ys n>y) n∈ys

-- Helper: n > myMax a b implies n > a and n > b
>-myMax-split : ∀ {n a b} → n > myMax a b → (n > a) × (n > b)
>-myMax-split {n} {a} {b} n>max =
  (≤-trans (suc-≤-suc (≤-myMax-l a b)) n>max) ,
  (≤-trans (suc-≤-suc (≤-myMax-r a b)) n>max)

-- If n > maxTokenCtx ctx, then TokenFresh n ctx
>-maxTokenCtx-TokenFresh : (n : Token) (ctx : Ctx) → n > maxTokenCtx ctx → TokenFresh n ctx
>-maxTokenCtx-TokenFresh n [] _ = tt
>-maxTokenCtx-TokenFresh n ((A ^ s) ∷ Γ) n>max =
  let (n>maxPos , n>maxΓ) = >-myMax-split n>max
  in >-maxTokenPos-∉Pos n s n>maxPos , >-maxTokenCtx-TokenFresh n Γ n>maxΓ

-- =============================================================================
-- Implementations of previously postulated lemmas
-- =============================================================================

-- freshTokenForRename produces a fresh token for the combined context
freshTokenForRename-fresh : (r : Position) (ctx : Ctx) {Γ Δ : Ctx} (Π : Γ ⊢ Δ)
  → TokenFresh (freshTokenForRename r ctx Π) ctx
freshTokenForRename-fresh r ctx {Γ} {Δ} Π = >-maxTokenCtx-TokenFresh (freshTokenForRename r ctx Π) ctx n>maxCtx
  where
    -- freshTokenForRename = suc (myMax (maxTokenPos r) (myMax (maxTokenCtx ctx) (myMax (maxTokenCtx Γ) (myMax (maxTokenCtx Δ) (maxEigenposToken Π)))))
    -- We need to show this is > maxTokenCtx ctx
    inner = myMax (maxTokenCtx ctx) (myMax (maxTokenCtx Γ) (myMax (maxTokenCtx Δ) (maxEigenposToken Π)))
    n>maxCtx : freshTokenForRename r ctx Π > maxTokenCtx ctx
    n>maxCtx = ≤-trans (suc-≤-suc (≤-trans (≤-myMax-l (maxTokenCtx ctx) _) (≤-myMax-r (maxTokenPos r) inner))) ≤-refl

-- freshTokenForRename produces a token larger than all eigentokens in Π
freshTokenForRename-eigenpos : (r : Position) (ctx : Ctx) {Γ Δ : Ctx} (Π : Γ ⊢ Δ)
  → maxEigenposToken Π < freshTokenForRename r ctx Π
freshTokenForRename-eigenpos r ctx {Γ} {Δ} Π = suc-≤-suc (≤-trans step1 (≤-myMax-r (maxTokenPos r) inner))
  where
    inner = myMax (maxTokenCtx ctx) (myMax (maxTokenCtx Γ) (myMax (maxTokenCtx Δ) (maxEigenposToken Π)))
    step1 : maxEigenposToken Π ≤ inner
    step1 = ≤-trans (≤-trans (≤-trans (≤-myMax-r (maxTokenCtx Δ) (maxEigenposToken Π))
                                       (≤-myMax-r (maxTokenCtx Γ) _))
                              (≤-myMax-r (maxTokenCtx ctx) _))
                    ≤-refl

-- freshTokenForRename produces a token not in r
freshTokenForRename-∉r : (r : Position) (ctx : Ctx) {Γ Δ : Ctx} (Π : Γ ⊢ Δ)
  → freshTokenForRename r ctx Π ∉Pos r
freshTokenForRename-∉r r ctx {Γ} {Δ} Π = >-maxTokenPos-∉Pos (freshTokenForRename r ctx Π) r n>maxr
  where
    inner = myMax (maxTokenCtx ctx) (myMax (maxTokenCtx Γ) (myMax (maxTokenCtx Δ) (maxEigenposToken Π)))
    n>maxr : freshTokenForRename r ctx Π > maxTokenPos r
    n>maxr = suc-≤-suc (≤-myMax-l (maxTokenPos r) inner)

-- IsSingleTokenExt preserved under token renaming
singleTokenExt-rename : ∀ {r t : Position} {x x' : Token}
  → IsSingleTokenExt r t x
  → x' ∉Pos r
  → IsSingleTokenExt r (substPos x (singleton-pos x') t) x'
singleTokenExt-rename {r} {t} {x} {x'} ext x'∉r with x ∈Pos? t
... | no x∉t =
  -- substPos x [x'] t = t since x ∉ t
  -- But ext says x ∈ t, contradiction
  ⊥-rec (x∉t (fst (snd ext)))
... | yes x∈t =
  -- substPos x [x'] t = (remove x t) ++Pos [x']
  -- Need to construct IsSingleTokenExt r ((remove x t) ++Pos [x']) x'
  (comp1 , comp2 , x'∉r , comp4)
  where
    s⊑t = fst ext
    x∈t' = fst (snd ext)
    x∉r = fst (snd (snd ext))
    uniq = snd (snd (snd ext))

    result = (remove x t) ++Pos (singleton-pos x')

    -- Component 1: r ⊑ result
    -- For any w ∈ r: w ∈ t (by s⊑t), w ≢ x (since x ∉ r), so w ∈ remove x t, so w ∈ result
    comp1 : r ⊑ result
    comp1 w w∈r =
      let w∈t = s⊑t w w∈r
          w≢x : x ≢ w
          w≢x x≡w = x∉r (subst (_∈Pos r) (sym x≡w) w∈r)
          w∈rem = mem-remove x t w w∈t w≢x
      in mem-++Pos-l w∈rem

    -- Component 2: x' ∈ result
    comp2 : x' ∈Pos result
    comp2 = mem-++Pos-r {remove x t} {singleton-pos x'} (inl refl)

    -- Component 4: uniqueness - any w ∈ result with w ∉ r must be x'
    comp4 : ∀ w → w ∈Pos result → w ∉Pos r → w ≡ x'
    comp4 w w∈result w∉r with mem-++Pos-case (remove x t) (singleton-pos x') w w∈result
    ... | inr w∈singleton = ∈Pos-singleton w x' w∈singleton
    ... | inl w∈rem =
      -- w ∈ remove x t, so w ∈ t and w ≢ x
      let w∈t = mem-remove-implies-mem {x} {t} {w} w∈rem
          w≢x = mem-remove-implies-neq {x} {t} {w} w∈rem
          -- Since w ∉ r and w ∈ t, by ext.uniq, w ≡ x
          w≡x = uniq w w∈t w∉r
      -- But w ≢ x, contradiction
      in ⊥-rec (w≢x (sym w≡x))

-- EigenposCond from well-foundedness: if all eigentokens in Π are < x, then EigenposCond x Π
EigenposCond-from-wf : (x : Token) {Γ Δ : Ctx} (Π : Γ ⊢ Δ) → maxEigenposToken Π < x → EigenposCond x Π
EigenposCond-from-wf x Ax _ = tt
EigenposCond-from-wf x (Cut Π₁ Π₂) wf =
  EigenposCond-from-wf x Π₁ (≤-trans (suc-≤-suc (≤-myMax-l _ _)) wf) ,
  EigenposCond-from-wf x Π₂ (≤-trans (suc-≤-suc (≤-myMax-r _ _)) wf)
EigenposCond-from-wf x (W⊢ Π) wf = EigenposCond-from-wf x Π wf
EigenposCond-from-wf x (⊢W Π) wf = EigenposCond-from-wf x Π wf
EigenposCond-from-wf x (C⊢ Π) wf = EigenposCond-from-wf x Π wf
EigenposCond-from-wf x (⊢C Π) wf = EigenposCond-from-wf x Π wf
EigenposCond-from-wf x (Exc⊢ Π) wf = EigenposCond-from-wf x Π wf
EigenposCond-from-wf x (⊢Exc Π) wf = EigenposCond-from-wf x Π wf
EigenposCond-from-wf x (¬⊢ Π) wf = EigenposCond-from-wf x Π wf
EigenposCond-from-wf x (⊢¬ Π) wf = EigenposCond-from-wf x Π wf
EigenposCond-from-wf x (∧₁⊢ Π) wf = EigenposCond-from-wf x Π wf
EigenposCond-from-wf x (∧₂⊢ Π) wf = EigenposCond-from-wf x Π wf
EigenposCond-from-wf x (⊢∧ Π₁ Π₂) wf =
  EigenposCond-from-wf x Π₁ (≤-trans (suc-≤-suc (≤-myMax-l _ _)) wf) ,
  EigenposCond-from-wf x Π₂ (≤-trans (suc-≤-suc (≤-myMax-r _ _)) wf)
EigenposCond-from-wf x (∨⊢ Π₁ Π₂) wf =
  EigenposCond-from-wf x Π₁ (≤-trans (suc-≤-suc (≤-myMax-l _ _)) wf) ,
  EigenposCond-from-wf x Π₂ (≤-trans (suc-≤-suc (≤-myMax-r _ _)) wf)
EigenposCond-from-wf x (⊢∨₁ Π) wf = EigenposCond-from-wf x Π wf
EigenposCond-from-wf x (⊢∨₂ Π) wf = EigenposCond-from-wf x Π wf
EigenposCond-from-wf x (⇒⊢ Π₁ Π₂) wf =
  EigenposCond-from-wf x Π₁ (≤-trans (suc-≤-suc (≤-myMax-l _ _)) wf) ,
  EigenposCond-from-wf x Π₂ (≤-trans (suc-≤-suc (≤-myMax-r _ _)) wf)
EigenposCond-from-wf x (⊢⇒ Π) wf = EigenposCond-from-wf x Π wf
EigenposCond-from-wf x (□⊢ Π) wf = EigenposCond-from-wf x Π wf
EigenposCond-from-wf x (⊢□ {x = y} _ _ _ Π) wf =
  -- EigenposCond x (⊢□ ...) = (x ≢ y) × EigenposCond x Π
  -- maxEigenposToken (⊢□ ...) = myMax y (maxEigenposToken Π)
  -- y ≤ myMax y (...) < x, so y < x, hence y ≢ x
  let y<x : y < x
      y<x = ≤-trans (suc-≤-suc (≤-myMax-l y _)) wf
      x≢y : x ≢ y
      x≢y x≡y = <→≢ y<x (sym x≡y)
  in x≢y , EigenposCond-from-wf x Π (≤-trans (suc-≤-suc (≤-myMax-r y _)) wf)
EigenposCond-from-wf x (♢⊢ {x = y} _ _ _ Π) wf =
  let y<x = ≤-trans (suc-≤-suc (≤-myMax-l y _)) wf
      x≢y = λ x≡y → <→≢ y<x (sym x≡y)
  in x≢y , EigenposCond-from-wf x Π (≤-trans (suc-≤-suc (≤-myMax-r y _)) wf)
EigenposCond-from-wf x (⊢♢ Π) wf = EigenposCond-from-wf x Π wf

-- NoEigenposInt for singleton: if all eigentokens < x', then they are ∉ [x']
NoEigenposInt-singleton-fresh : (x' : Token) {Γ Δ : Ctx} (Π : Γ ⊢ Δ)
  → maxEigenposToken Π < x' → NoEigenposInt (singleton-pos x') Π
NoEigenposInt-singleton-fresh x' Ax _ = tt
NoEigenposInt-singleton-fresh x' (Cut Π₁ Π₂) wf =
  NoEigenposInt-singleton-fresh x' Π₁ (≤-trans (suc-≤-suc (≤-myMax-l _ _)) wf) ,
  NoEigenposInt-singleton-fresh x' Π₂ (≤-trans (suc-≤-suc (≤-myMax-r _ _)) wf)
NoEigenposInt-singleton-fresh x' (W⊢ Π) wf = NoEigenposInt-singleton-fresh x' Π wf
NoEigenposInt-singleton-fresh x' (⊢W Π) wf = NoEigenposInt-singleton-fresh x' Π wf
NoEigenposInt-singleton-fresh x' (C⊢ Π) wf = NoEigenposInt-singleton-fresh x' Π wf
NoEigenposInt-singleton-fresh x' (⊢C Π) wf = NoEigenposInt-singleton-fresh x' Π wf
NoEigenposInt-singleton-fresh x' (Exc⊢ Π) wf = NoEigenposInt-singleton-fresh x' Π wf
NoEigenposInt-singleton-fresh x' (⊢Exc Π) wf = NoEigenposInt-singleton-fresh x' Π wf
NoEigenposInt-singleton-fresh x' (¬⊢ Π) wf = NoEigenposInt-singleton-fresh x' Π wf
NoEigenposInt-singleton-fresh x' (⊢¬ Π) wf = NoEigenposInt-singleton-fresh x' Π wf
NoEigenposInt-singleton-fresh x' (∧₁⊢ Π) wf = NoEigenposInt-singleton-fresh x' Π wf
NoEigenposInt-singleton-fresh x' (∧₂⊢ Π) wf = NoEigenposInt-singleton-fresh x' Π wf
NoEigenposInt-singleton-fresh x' (⊢∧ Π₁ Π₂) wf =
  NoEigenposInt-singleton-fresh x' Π₁ (≤-trans (suc-≤-suc (≤-myMax-l _ _)) wf) ,
  NoEigenposInt-singleton-fresh x' Π₂ (≤-trans (suc-≤-suc (≤-myMax-r _ _)) wf)
NoEigenposInt-singleton-fresh x' (∨⊢ Π₁ Π₂) wf =
  NoEigenposInt-singleton-fresh x' Π₁ (≤-trans (suc-≤-suc (≤-myMax-l _ _)) wf) ,
  NoEigenposInt-singleton-fresh x' Π₂ (≤-trans (suc-≤-suc (≤-myMax-r _ _)) wf)
NoEigenposInt-singleton-fresh x' (⊢∨₁ Π) wf = NoEigenposInt-singleton-fresh x' Π wf
NoEigenposInt-singleton-fresh x' (⊢∨₂ Π) wf = NoEigenposInt-singleton-fresh x' Π wf
NoEigenposInt-singleton-fresh x' (⇒⊢ Π₁ Π₂) wf =
  NoEigenposInt-singleton-fresh x' Π₁ (≤-trans (suc-≤-suc (≤-myMax-l _ _)) wf) ,
  NoEigenposInt-singleton-fresh x' Π₂ (≤-trans (suc-≤-suc (≤-myMax-r _ _)) wf)
NoEigenposInt-singleton-fresh x' (⊢⇒ Π) wf = NoEigenposInt-singleton-fresh x' Π wf
NoEigenposInt-singleton-fresh x' (□⊢ Π) wf = NoEigenposInt-singleton-fresh x' Π wf
NoEigenposInt-singleton-fresh x' (⊢□ {x = y} _ _ _ Π) wf =
  -- NoEigenposInt [x'] (⊢□ ...) = (y ∉Pos [x']) × NoEigenposInt [x'] Π
  -- Need to show y ∉ [x']. Since y < x' (from maxEigenpos), y ≢ x', so y ∉ [x']
  let y<x' = ≤-trans (suc-≤-suc (≤-myMax-l y _)) wf
      y≢x' : y ≢ x'
      y≢x' y≡x' = <→≢ y<x' y≡x'
      y∉singleton = ∉Pos-singleton y x' y≢x'
  in y∉singleton , NoEigenposInt-singleton-fresh x' Π (≤-trans (suc-≤-suc (≤-myMax-r y _)) wf)
NoEigenposInt-singleton-fresh x' (♢⊢ {x = y} _ _ _ Π) wf =
  let y<x' = ≤-trans (suc-≤-suc (≤-myMax-l y _)) wf
      y≢x' = λ y≡x' → <→≢ y<x' y≡x'
      y∉singleton = ∉Pos-singleton y x' y≢x'
  in y∉singleton , NoEigenposInt-singleton-fresh x' Π (≤-trans (suc-≤-suc (≤-myMax-r y _)) wf)
NoEigenposInt-singleton-fresh x' (⊢♢ Π) wf = NoEigenposInt-singleton-fresh x' Π wf

-- Eigenposition renaming for ♢⊢ premise (generalized)
renameEigenpos-♢⊢-premise-gen : ∀ {r t : Position} {x : Token} {Γ Δ : Ctx} {A : Formula}
  → (Π : (Γ ,, [ A ^ t ]) ⊢ Δ)
  → (ext : IsSingleTokenExt r t x)
  → (freshΓ : TokenFresh x Γ)
  → (freshΔ : TokenFresh x Δ)
  → (wf : maxEigenposToken Π < x)
  → (x' : Token)
  → (x'-eigenpos : maxEigenposToken Π < x')
  → (x'∉r : x' ∉Pos r)
  → Σ ((Γ ,, [ A ^ substPos x (singleton-pos x') t ]) ⊢ Δ)
      (λ Π' → IsSingleTokenExt r (substPos x (singleton-pos x') t) x')
renameEigenpos-♢⊢-premise-gen {r} {t} {x} {Γ} {Δ} {A} Π ext freshΓ freshΔ wf x' x'-eigenpos x'∉r =
  Π' , ext'
  where
    -- Build EigenposCond x Π (x is different from all eigentokens in Π)
    ec : EigenposCond x Π
    ec = EigenposCond-from-wf x Π wf

    -- Build NoEigenposInt [x'] Π (no eigentoken is x')
    nc : NoEigenposInt (singleton-pos x') Π
    nc = NoEigenposInt-singleton-fresh x' Π x'-eigenpos

    -- Apply substTokenToPosProof to get the transformed proof
    -- substTokenToPosProof x [x'] Π : substCtx x [x'] (Γ ,, [ A ^ t ]) ⊢ substCtx x [x'] Δ
    Π-subst : substCtx x (singleton-pos x') (Γ ,, [ A ^ t ]) ⊢ substCtx x (singleton-pos x') Δ
    Π-subst = substTokenToPosProof x (singleton-pos x') Π ec nc

    -- TokenFresh x Δ means substCtx x [x'] Δ = Δ
    Δ-unchanged : substCtx x (singleton-pos x') Δ ≡ Δ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ freshΔ

    -- For Γ, TokenFresh x Γ means substCtx x [x'] Γ = Γ
    Γ-unchanged : substCtx x (singleton-pos x') Γ ≡ Γ
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ freshΓ

    -- The formula position t gets substituted to substPos x [x'] t
    -- substCtx x [x'] (Γ ,, [ A ^ t ]) = substCtx x [x'] Γ ,, [ A ^ substPos x [x'] t ]
    --                                  = Γ ,, [ A ^ substPos x [x'] t ]
    ctx-eq : substCtx x (singleton-pos x') (Γ ,, [ A ^ t ]) ≡ Γ ,, [ A ^ substPos x (singleton-pos x') t ]
    ctx-eq = substCtx-++ x (singleton-pos x') Γ [ A ^ t ] ∙ cong (_++L [ A ^ substPos x (singleton-pos x') t ]) Γ-unchanged

    -- Combine to get the transformed proof with correct type
    Π' : (Γ ,, [ A ^ substPos x (singleton-pos x') t ]) ⊢ Δ
    Π' = subst2 _⊢_ ctx-eq Δ-unchanged Π-subst

    -- Build the extension property
    ext' : IsSingleTokenExt r (substPos x (singleton-pos x') t) x'
    ext' = singleTokenExt-rename ext x'∉r

-- Eigenposition renaming for ⊢□ premise (generalized)
renameEigenpos-⊢□-premise-gen : ∀ {r t : Position} {x : Token} {Γ Δ : Ctx} {A : Formula}
  → (Π : Γ ⊢ ([ A ^ t ] ,, Δ))
  → (ext : IsSingleTokenExt r t x)
  → (freshΓ : TokenFresh x Γ)
  → (freshΔ : TokenFresh x Δ)
  → (wf : maxEigenposToken Π < x)
  → (x' : Token)
  → (x'-eigenpos : maxEigenposToken Π < x')
  → (x'∉r : x' ∉Pos r)
  → Σ (Γ ⊢ ([ A ^ substPos x (singleton-pos x') t ] ,, Δ))
      (λ Π' → IsSingleTokenExt r (substPos x (singleton-pos x') t) x')
renameEigenpos-⊢□-premise-gen {r} {t} {x} {Γ} {Δ} {A} Π ext freshΓ freshΔ wf x' x'-eigenpos x'∉r =
  Π' , ext'
  where
    ec : EigenposCond x Π
    ec = EigenposCond-from-wf x Π wf

    nc : NoEigenposInt (singleton-pos x') Π
    nc = NoEigenposInt-singleton-fresh x' Π x'-eigenpos

    Π-subst : substCtx x (singleton-pos x') Γ ⊢ substCtx x (singleton-pos x') ([ A ^ t ] ,, Δ)
    Π-subst = substTokenToPosProof x (singleton-pos x') Π ec nc

    Γ-unchanged : substCtx x (singleton-pos x') Γ ≡ Γ
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ freshΓ

    Δ-unchanged : substCtx x (singleton-pos x') Δ ≡ Δ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ freshΔ

    ctx-eq : substCtx x (singleton-pos x') ([ A ^ t ] ,, Δ) ≡ [ A ^ substPos x (singleton-pos x') t ] ,, Δ
    ctx-eq = substCtx-++ x (singleton-pos x') [ A ^ t ] Δ ∙ cong ([ A ^ substPos x (singleton-pos x') t ] ++L_) Δ-unchanged

    Π' : Γ ⊢ ([ A ^ substPos x (singleton-pos x') t ] ,, Δ)
    Π' = subst2 _⊢_ Γ-unchanged ctx-eq Π-subst

    ext' : IsSingleTokenExt r (substPos x (singleton-pos x') t) x'
    ext' = singleTokenExt-rename ext x'∉r


-- =============================================================================
-- Eigenposition Renaming Proposition (Proposition teo:eigenpos1)
-- =============================================================================
-- "Given a proof Π of an e-sequent Γ ⊢ Δ, we may always find a proof Π'
-- ending with Γ ⊢ Δ where all eigenpositions are distinct from one another
-- and satisfy the well-formedness condition: maxEigenposToken Π_sub < eigentoken."

-- Predicate: y is an eigentoken in Π
isEigentoken : Token → {Γ Δ : Ctx} → Γ ⊢ Δ → Type
isEigentoken y Ax = ⊥
isEigentoken y (Cut Π₁ Π₂) = isEigentoken y Π₁ ⊎ isEigentoken y Π₂
isEigentoken y (W⊢ Π) = isEigentoken y Π
isEigentoken y (⊢W Π) = isEigentoken y Π
isEigentoken y (C⊢ Π) = isEigentoken y Π
isEigentoken y (⊢C Π) = isEigentoken y Π
isEigentoken y (Exc⊢ Π) = isEigentoken y Π
isEigentoken y (⊢Exc Π) = isEigentoken y Π
isEigentoken y (¬⊢ Π) = isEigentoken y Π
isEigentoken y (⊢¬ Π) = isEigentoken y Π
isEigentoken y (∧₁⊢ Π) = isEigentoken y Π
isEigentoken y (∧₂⊢ Π) = isEigentoken y Π
isEigentoken y (⊢∧ Π₁ Π₂) = isEigentoken y Π₁ ⊎ isEigentoken y Π₂
isEigentoken y (∨⊢ Π₁ Π₂) = isEigentoken y Π₁ ⊎ isEigentoken y Π₂
isEigentoken y (⊢∨₁ Π) = isEigentoken y Π
isEigentoken y (⊢∨₂ Π) = isEigentoken y Π
isEigentoken y (⇒⊢ Π₁ Π₂) = isEigentoken y Π₁ ⊎ isEigentoken y Π₂
isEigentoken y (⊢⇒ Π) = isEigentoken y Π
isEigentoken y (□⊢ Π) = isEigentoken y Π
isEigentoken y (⊢□ {x = z} _ _ _ Π) = (y ≡ z) ⊎ isEigentoken y Π
isEigentoken y (♢⊢ {x = z} _ _ _ Π) = (y ≡ z) ⊎ isEigentoken y Π
isEigentoken y (⊢♢ Π) = isEigentoken y Π

-- NoEigenposInt for general positions: if all eigentokens are ≥ base > maxTokenPos t,
-- then no eigentoken appears in t
NoEigenposInt-from-allGe : (t : Position) (base : Token) {Γ Δ : Ctx} (Π : Γ ⊢ Δ)
  → maxTokenPos t < base
  → ((y : Token) → isEigentoken y Π → base ≤ y)
  → NoEigenposInt t Π
NoEigenposInt-from-allGe t base Ax _ _ = tt
NoEigenposInt-from-allGe t base (Cut Π₁ Π₂) t<base allGe =
  NoEigenposInt-from-allGe t base Π₁ t<base (λ y yIn → allGe y (inl yIn)) ,
  NoEigenposInt-from-allGe t base Π₂ t<base (λ y yIn → allGe y (inr yIn))
NoEigenposInt-from-allGe t base (W⊢ Π) t<base allGe = NoEigenposInt-from-allGe t base Π t<base allGe
NoEigenposInt-from-allGe t base (⊢W Π) t<base allGe = NoEigenposInt-from-allGe t base Π t<base allGe
NoEigenposInt-from-allGe t base (C⊢ Π) t<base allGe = NoEigenposInt-from-allGe t base Π t<base allGe
NoEigenposInt-from-allGe t base (⊢C Π) t<base allGe = NoEigenposInt-from-allGe t base Π t<base allGe
NoEigenposInt-from-allGe t base (Exc⊢ Π) t<base allGe = NoEigenposInt-from-allGe t base Π t<base allGe
NoEigenposInt-from-allGe t base (⊢Exc Π) t<base allGe = NoEigenposInt-from-allGe t base Π t<base allGe
NoEigenposInt-from-allGe t base (¬⊢ Π) t<base allGe = NoEigenposInt-from-allGe t base Π t<base allGe
NoEigenposInt-from-allGe t base (⊢¬ Π) t<base allGe = NoEigenposInt-from-allGe t base Π t<base allGe
NoEigenposInt-from-allGe t base (∧₁⊢ Π) t<base allGe = NoEigenposInt-from-allGe t base Π t<base allGe
NoEigenposInt-from-allGe t base (∧₂⊢ Π) t<base allGe = NoEigenposInt-from-allGe t base Π t<base allGe
NoEigenposInt-from-allGe t base (⊢∧ Π₁ Π₂) t<base allGe =
  NoEigenposInt-from-allGe t base Π₁ t<base (λ y yIn → allGe y (inl yIn)) ,
  NoEigenposInt-from-allGe t base Π₂ t<base (λ y yIn → allGe y (inr yIn))
NoEigenposInt-from-allGe t base (∨⊢ Π₁ Π₂) t<base allGe =
  NoEigenposInt-from-allGe t base Π₁ t<base (λ y yIn → allGe y (inl yIn)) ,
  NoEigenposInt-from-allGe t base Π₂ t<base (λ y yIn → allGe y (inr yIn))
NoEigenposInt-from-allGe t base (⊢∨₁ Π) t<base allGe = NoEigenposInt-from-allGe t base Π t<base allGe
NoEigenposInt-from-allGe t base (⊢∨₂ Π) t<base allGe = NoEigenposInt-from-allGe t base Π t<base allGe
NoEigenposInt-from-allGe t base (⇒⊢ Π₁ Π₂) t<base allGe =
  NoEigenposInt-from-allGe t base Π₁ t<base (λ y yIn → allGe y (inl yIn)) ,
  NoEigenposInt-from-allGe t base Π₂ t<base (λ y yIn → allGe y (inr yIn))
NoEigenposInt-from-allGe t base (⊢⇒ Π) t<base allGe = NoEigenposInt-from-allGe t base Π t<base allGe
NoEigenposInt-from-allGe t base (□⊢ Π) t<base allGe = NoEigenposInt-from-allGe t base Π t<base allGe
NoEigenposInt-from-allGe t base (⊢□ {x = y} _ _ _ Π) t<base allGe =
  >-maxTokenPos-∉Pos y t (≤-trans t<base (allGe y (inl refl))) ,
  NoEigenposInt-from-allGe t base Π t<base (λ z zIn → allGe z (inr zIn))
NoEigenposInt-from-allGe t base (♢⊢ {x = y} _ _ _ Π) t<base allGe =
  >-maxTokenPos-∉Pos y t (≤-trans t<base (allGe y (inl refl))) ,
  NoEigenposInt-from-allGe t base Π t<base (λ z zIn → allGe z (inr zIn))
NoEigenposInt-from-allGe t base (⊢♢ Π) t<base allGe = NoEigenposInt-from-allGe t base Π t<base allGe

-- Lemma: isEigentoken is preserved (backwards) by subst2
-- Type-level transport doesn't affect eigentokens
isEigentoken-subst2 : ∀ {Γ Γ' Δ Δ'} (p : Γ ≡ Γ') (q : Δ ≡ Δ') (Π : Γ ⊢ Δ)
  → (y : Token) → isEigentoken y (subst2 _⊢_ p q Π) → isEigentoken y Π
isEigentoken-subst2 {Γ} {Γ'} {Δ} {Δ'} p q Π y =
  J (λ Γ' p → ∀ Δ' (q : Δ ≡ Δ') → isEigentoken y (subst2 _⊢_ p q Π) → isEigentoken y Π)
    (λ Δ' q → J (λ Δ' q → isEigentoken y (subst2 _⊢_ refl q Π) → isEigentoken y Π)
                (subst (isEigentoken y) (substRefl {B = Γ ⊢_} Π)) q)
    p Δ' q

-- Helpers for single-argument subst (for convenience in the inductive proof)
isEigentoken-substR : ∀ {Γ Δ Δ'} (p : Δ ≡ Δ') (Π : Γ ⊢ Δ)
  → (y : Token) → isEigentoken y (subst (Γ ⊢_) p Π) → isEigentoken y Π
isEigentoken-substR p Π = isEigentoken-subst2 refl p Π

isEigentoken-substL : ∀ {Γ Γ' Δ} (p : Γ ≡ Γ') (Π : Γ ⊢ Δ)
  → (y : Token) → isEigentoken y (subst (_⊢ Δ) p Π) → isEigentoken y Π
isEigentoken-substL p Π = isEigentoken-subst2 p refl Π

-- Lemma: isEigentoken is preserved (backwards) by substTokenToPosProof
-- If y is an eigentoken in the result, it was an eigentoken in the original
-- This is proved by induction on Π
isEigentoken-substTokenToPosProof : (z : Token) (t : Position) {Γ Δ : Ctx}
  → (Π : Γ ⊢ Δ) → (ec : EigenposCond z Π) → (nc : NoEigenposInt t Π)
  → (y : Token) → isEigentoken y (substTokenToPosProof z t Π ec nc) → isEigentoken y Π
isEigentoken-substTokenToPosProof z t Ax _ _ y ()  -- No eigentokens in Ax
isEigentoken-substTokenToPosProof z t (Cut {Γ₁} {A} {s} {Δ₁} {Γ₂} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) y yIn
  with isEigentoken-subst2 (sym (substCtx-++ z t Γ₁ Γ₂)) (sym (substCtx-++ z t Δ₁ Δ₂))
         (Cut (subst (substCtx z t Γ₁ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₁) (substTokenToPosProof z t Π₁ ec₁ nc₁))
              (subst (_⊢ substCtx z t Δ₂) (substCtx-++ z t Γ₂ [ A ^ s ]) (substTokenToPosProof z t Π₂ ec₂ nc₂))) y yIn
... | inl yIn₁ = inl (isEigentoken-substTokenToPosProof z t Π₁ ec₁ nc₁ y
                       (isEigentoken-substR (substCtx-++ z t [ A ^ s ] Δ₁) (substTokenToPosProof z t Π₁ ec₁ nc₁) y yIn₁))
... | inr yIn₂ = inr (isEigentoken-substTokenToPosProof z t Π₂ ec₂ nc₂ y
                       (isEigentoken-substL (substCtx-++ z t Γ₂ [ A ^ s ]) (substTokenToPosProof z t Π₂ ec₂ nc₂) y yIn₂))
isEigentoken-substTokenToPosProof z t (W⊢ {Γ} {Δ} {A} {s} Π) ec nc y yIn =
  isEigentoken-substTokenToPosProof z t Π ec nc y
    (isEigentoken-substL (sym (substCtx-++ z t Γ [ A ^ s ])) (W⊢ (substTokenToPosProof z t Π ec nc)) y yIn)
isEigentoken-substTokenToPosProof z t (⊢W {Γ} {Δ} {A} {s} Π) ec nc y yIn =
  isEigentoken-substTokenToPosProof z t Π ec nc y
    (isEigentoken-substR (sym (substCtx-++ z t [ A ^ s ] Δ)) (⊢W (substTokenToPosProof z t Π ec nc)) y yIn)
isEigentoken-substTokenToPosProof z t (C⊢ {Γ} {A} {s} {Δ} Π) ec nc y yIn =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ)
                (substCtx-++ z t (Γ ++L [ A ^ s ]) [ A ^ s ] ∙
                 cong (_++L substCtx z t [ A ^ s ]) (substCtx-++ z t Γ [ A ^ s ])) Π'
      yIn' = isEigentoken-substL (sym (substCtx-++ z t Γ [ A ^ s ])) (C⊢ inner) y yIn
      yIn'' = isEigentoken-substL (substCtx-++ z t (Γ ++L [ A ^ s ]) [ A ^ s ] ∙
                                    cong (_++L substCtx z t [ A ^ s ]) (substCtx-++ z t Γ [ A ^ s ])) Π' y yIn'
  in isEigentoken-substTokenToPosProof z t Π ec nc y yIn''
isEigentoken-substTokenToPosProof z t (⊢C {Γ} {A} {s} {Δ} Π) ec nc y yIn =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_)
                (substCtx-++ z t ([ A ^ s ] ++L [ A ^ s ]) Δ ∙
                 cong (_++L substCtx z t Δ) (substCtx-++ z t [ A ^ s ] [ A ^ s ])) Π'
      yIn' = isEigentoken-substR (sym (substCtx-++ z t [ A ^ s ] Δ)) (⊢C inner) y yIn
      yIn'' = isEigentoken-substR (substCtx-++ z t ([ A ^ s ] ++L [ A ^ s ]) Δ ∙
                                    cong (_++L substCtx z t Δ) (substCtx-++ z t [ A ^ s ] [ A ^ s ])) Π' y yIn'
  in isEigentoken-substTokenToPosProof z t Π ec nc y yIn''
isEigentoken-substTokenToPosProof z t (Exc⊢ {Γ₁} {A} {s} {B} {t'} {Γ₂} {Δ} Π) ec nc y yIn =
  -- The Exc⊢ case involves complex path manipulations, but eigentoken comes from Π
  let Π' = substTokenToPosProof z t Π ec nc
      step0' = cong (substCtx z t) (++L-assoc (Γ₁ ++L [ B ^ t' ]) [ A ^ s ] Γ₂)
      step1' = substCtx-++ z t (Γ₁ ++L [ B ^ t' ]) (A ^ s ∷ Γ₂)
      step2' = cong (_++L substCtx z t (A ^ s ∷ Γ₂)) (substCtx-++ z t Γ₁ [ B ^ t' ])
      step3' = cong ((substCtx z t Γ₁ ++L substCtx z t [ B ^ t' ]) ++L_) (substCtx-++ z t [ A ^ s ] Γ₂)
      step4' = sym (++L-assoc (substCtx z t Γ₁ ++L substCtx z t [ B ^ t' ]) (substCtx z t [ A ^ s ]) (substCtx z t Γ₂))
      path2 = step0' ∙ step1' ∙ step2' ∙ step3' ∙ step4'
      step0 = cong (substCtx z t) (++L-assoc (Γ₁ ++L [ A ^ s ]) [ B ^ t' ] Γ₂)
      step1 = substCtx-++ z t (Γ₁ ++L [ A ^ s ]) (B ^ t' ∷ Γ₂)
      step2 = cong (_++L substCtx z t (B ^ t' ∷ Γ₂)) (substCtx-++ z t Γ₁ [ A ^ s ])
      step3 = cong ((substCtx z t Γ₁ ++L substCtx z t [ A ^ s ]) ++L_) (substCtx-++ z t [ B ^ t' ] Γ₂)
      step4 = sym (++L-assoc (substCtx z t Γ₁ ++L substCtx z t [ A ^ s ]) (substCtx z t [ B ^ t' ]) (substCtx z t Γ₂))
      path = step0 ∙ step1 ∙ step2 ∙ step3 ∙ step4
      raw = Exc⊢ {Γ₁ = substCtx z t Γ₁} {A = A} {B = B} {Γ₂ = substCtx z t Γ₂}
                 (subst (λ G → G ⊢ substCtx z t Δ) path Π')
      yIn' = isEigentoken-substL (sym path2) raw y yIn
      yIn'' = isEigentoken-substL path Π' y yIn'
  in isEigentoken-substTokenToPosProof z t Π ec nc y yIn''
isEigentoken-substTokenToPosProof z t (⊢Exc {Γ} {Δ₁} {A} {s} {B} {t'} {Δ₂} Π) ec nc y yIn =
  let Π' = substTokenToPosProof z t Π ec nc
      step0' = cong (substCtx z t) (++L-assoc (Δ₁ ++L [ B ^ t' ]) [ A ^ s ] Δ₂)
      step1' = substCtx-++ z t (Δ₁ ++L [ B ^ t' ]) (A ^ s ∷ Δ₂)
      step2' = cong (_++L substCtx z t (A ^ s ∷ Δ₂)) (substCtx-++ z t Δ₁ [ B ^ t' ])
      step3' = cong ((substCtx z t Δ₁ ++L substCtx z t [ B ^ t' ]) ++L_) (substCtx-++ z t [ A ^ s ] Δ₂)
      step4' = sym (++L-assoc (substCtx z t Δ₁ ++L substCtx z t [ B ^ t' ]) (substCtx z t [ A ^ s ]) (substCtx z t Δ₂))
      path2 = step0' ∙ step1' ∙ step2' ∙ step3' ∙ step4'
      step0 = cong (substCtx z t) (++L-assoc (Δ₁ ++L [ A ^ s ]) [ B ^ t' ] Δ₂)
      step1 = substCtx-++ z t (Δ₁ ++L [ A ^ s ]) (B ^ t' ∷ Δ₂)
      step2 = cong (_++L substCtx z t (B ^ t' ∷ Δ₂)) (substCtx-++ z t Δ₁ [ A ^ s ])
      step3 = cong ((substCtx z t Δ₁ ++L substCtx z t [ A ^ s ]) ++L_) (substCtx-++ z t [ B ^ t' ] Δ₂)
      step4 = sym (++L-assoc (substCtx z t Δ₁ ++L substCtx z t [ A ^ s ]) (substCtx z t [ B ^ t' ]) (substCtx z t Δ₂))
      path = step0 ∙ step1 ∙ step2 ∙ step3 ∙ step4
      raw = ⊢Exc {Δ₁ = substCtx z t Δ₁} {A = A} {B = B} {Δ₂ = substCtx z t Δ₂}
                 (subst (λ D → substCtx z t Γ ⊢ D) path Π')
      yIn' = isEigentoken-substR (sym path2) raw y yIn
      yIn'' = isEigentoken-substR path Π' y yIn'
  in isEigentoken-substTokenToPosProof z t Π ec nc y yIn''
isEigentoken-substTokenToPosProof z t (¬⊢ {Γ} {A} {s} {Δ} Π) ec nc y yIn =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ A ^ s ] Δ) Π'
      yIn' = isEigentoken-substL (sym (substCtx-++ z t Γ [ (¬ A) ^ s ])) (¬⊢ inner) y yIn
      yIn'' = isEigentoken-substR (substCtx-++ z t [ A ^ s ] Δ) Π' y yIn'
  in isEigentoken-substTokenToPosProof z t Π ec nc y yIn''
isEigentoken-substTokenToPosProof z t (⊢¬ {Γ} {A} {s} {Δ} Π) ec nc y yIn =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ A ^ s ]) Π'
      yIn' = isEigentoken-substR (sym (substCtx-++ z t [ (¬ A) ^ s ] Δ)) (⊢¬ inner) y yIn
      yIn'' = isEigentoken-substL (substCtx-++ z t Γ [ A ^ s ]) Π' y yIn'
  in isEigentoken-substTokenToPosProof z t Π ec nc y yIn''
isEigentoken-substTokenToPosProof z t (∧₁⊢ {Γ} {A} {s} {Δ} {B} Π) ec nc y yIn =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ A ^ s ]) Π'
      yIn' = isEigentoken-substL (sym (substCtx-++ z t Γ [ (A and B) ^ s ])) (∧₁⊢ inner) y yIn
      yIn'' = isEigentoken-substL (substCtx-++ z t Γ [ A ^ s ]) Π' y yIn'
  in isEigentoken-substTokenToPosProof z t Π ec nc y yIn''
isEigentoken-substTokenToPosProof z t (∧₂⊢ {Γ} {B} {s} {Δ} {A} Π) ec nc y yIn =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ B ^ s ]) Π'
      yIn' = isEigentoken-substL (sym (substCtx-++ z t Γ [ (A and B) ^ s ])) (∧₂⊢ inner) y yIn
      yIn'' = isEigentoken-substL (substCtx-++ z t Γ [ B ^ s ]) Π' y yIn'
  in isEigentoken-substTokenToPosProof z t Π ec nc y yIn''
isEigentoken-substTokenToPosProof z t (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) y yIn
  with isEigentoken-subst2 (sym (substCtx-++ z t Γ₁ Γ₂))
         (cong (substCtx z t [ (A and B) ^ s ] ++L_) (sym (substCtx-++ z t Δ₁ Δ₂)) ∙
          sym (substCtx-++ z t [ (A and B) ^ s ] (Δ₁ ++L Δ₂)))
         (⊢∧ (subst (substCtx z t Γ₁ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₁) (substTokenToPosProof z t Π₁ ec₁ nc₁))
             (subst (substCtx z t Γ₂ ⊢_) (substCtx-++ z t [ B ^ s ] Δ₂) (substTokenToPosProof z t Π₂ ec₂ nc₂))) y yIn
... | inl yIn₁ = inl (isEigentoken-substTokenToPosProof z t Π₁ ec₁ nc₁ y
                       (isEigentoken-substR (substCtx-++ z t [ A ^ s ] Δ₁) (substTokenToPosProof z t Π₁ ec₁ nc₁) y yIn₁))
... | inr yIn₂ = inr (isEigentoken-substTokenToPosProof z t Π₂ ec₂ nc₂ y
                       (isEigentoken-substR (substCtx-++ z t [ B ^ s ] Δ₂) (substTokenToPosProof z t Π₂ ec₂ nc₂) y yIn₂))
isEigentoken-substTokenToPosProof z t (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) y yIn
  with isEigentoken-subst2
         (cong (substCtx z t Γ₁ ++L_) (sym (substCtx-++ z t Γ₂ [ (A or B) ^ s ]))
          ∙ sym (substCtx-++ z t Γ₁ (Γ₂ ++L [ (A or B) ^ s ])))
         (sym (substCtx-++ z t Δ₁ Δ₂))
         (∨⊢ (subst (_⊢ substCtx z t Δ₁) (substCtx-++ z t Γ₁ [ A ^ s ]) (substTokenToPosProof z t Π₁ ec₁ nc₁))
             (subst (_⊢ substCtx z t Δ₂) (substCtx-++ z t Γ₂ [ B ^ s ]) (substTokenToPosProof z t Π₂ ec₂ nc₂))) y yIn
... | inl yIn₁ = inl (isEigentoken-substTokenToPosProof z t Π₁ ec₁ nc₁ y
                       (isEigentoken-substL (substCtx-++ z t Γ₁ [ A ^ s ]) (substTokenToPosProof z t Π₁ ec₁ nc₁) y yIn₁))
... | inr yIn₂ = inr (isEigentoken-substTokenToPosProof z t Π₂ ec₂ nc₂ y
                       (isEigentoken-substL (substCtx-++ z t Γ₂ [ B ^ s ]) (substTokenToPosProof z t Π₂ ec₂ nc₂) y yIn₂))
isEigentoken-substTokenToPosProof z t (⊢∨₁ {Γ} {A} {s} {Δ} {B} Π) ec nc y yIn =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ A ^ s ] Δ) Π'
      yIn' = isEigentoken-substR (sym (substCtx-++ z t [ (A or B) ^ s ] Δ)) (⊢∨₁ inner) y yIn
      yIn'' = isEigentoken-substR (substCtx-++ z t [ A ^ s ] Δ) Π' y yIn'
  in isEigentoken-substTokenToPosProof z t Π ec nc y yIn''
isEigentoken-substTokenToPosProof z t (⊢∨₂ {Γ} {B} {s} {Δ} {A} Π) ec nc y yIn =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ B ^ s ] Δ) Π'
      yIn' = isEigentoken-substR (sym (substCtx-++ z t [ (A or B) ^ s ] Δ)) (⊢∨₂ inner) y yIn
      yIn'' = isEigentoken-substR (substCtx-++ z t [ B ^ s ] Δ) Π' y yIn'
  in isEigentoken-substTokenToPosProof z t Π ec nc y yIn''
isEigentoken-substTokenToPosProof z t (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) y yIn
  with isEigentoken-subst2
         (cong (substCtx z t Γ₁ ++L_) (sym (substCtx-++ z t Γ₂ [ (A ⇒ B) ^ s ]))
          ∙ sym (substCtx-++ z t Γ₁ (Γ₂ ++L [ (A ⇒ B) ^ s ])))
         (sym (substCtx-++ z t Δ₁ Δ₂))
         (⇒⊢ (subst (_⊢ substCtx z t Δ₁) (substCtx-++ z t Γ₁ [ B ^ s ]) (substTokenToPosProof z t Π₁ ec₁ nc₁))
             (subst (substCtx z t Γ₂ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₂) (substTokenToPosProof z t Π₂ ec₂ nc₂))) y yIn
... | inl yIn₁ = inl (isEigentoken-substTokenToPosProof z t Π₁ ec₁ nc₁ y
                       (isEigentoken-substL (substCtx-++ z t Γ₁ [ B ^ s ]) (substTokenToPosProof z t Π₁ ec₁ nc₁) y yIn₁))
... | inr yIn₂ = inr (isEigentoken-substTokenToPosProof z t Π₂ ec₂ nc₂ y
                       (isEigentoken-substR (substCtx-++ z t [ A ^ s ] Δ₂) (substTokenToPosProof z t Π₂ ec₂ nc₂) y yIn₂))
isEigentoken-substTokenToPosProof z t (⊢⇒ {Γ} {A} {s} {B} {Δ} Π) ec nc y yIn =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst2 _⊢_ (substCtx-++ z t Γ [ A ^ s ]) (substCtx-++ z t [ B ^ s ] Δ) Π'
      yIn' = isEigentoken-substR (sym (substCtx-++ z t [ (A ⇒ B) ^ s ] Δ)) (⊢⇒ inner) y yIn
      yIn'' = isEigentoken-subst2 (substCtx-++ z t Γ [ A ^ s ]) (substCtx-++ z t [ B ^ s ] Δ) Π' y yIn'
  in isEigentoken-substTokenToPosProof z t Π ec nc y yIn''
isEigentoken-substTokenToPosProof z t (□⊢ {Γ} {A} {s} {t'} {Δ} Π) ec nc y yIn =
  let Π' = substTokenToPosProof z t Π ec nc
      ctx-eq = substCtx-++ z t Γ [ A ^ (s ++Pos t') ]
      pos-eq = substPos-++Pos-distr z t s t'
      Π'' = subst (_⊢ substCtx z t Δ) (ctx-eq ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π'
      out-path = sym (substCtx-++ z t Γ [ (□ A) ^ s ])
      yIn' = isEigentoken-substL out-path (□⊢ Π'') y yIn
      yIn'' = isEigentoken-substL (ctx-eq ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π' y yIn'
  in isEigentoken-substTokenToPosProof z t Π ec nc y yIn''
-- ⊢□ case: eigentoken x is preserved, and result may have y ≡ x or eigentoken from subproof
isEigentoken-substTokenToPosProof z t (⊢□ {x} {s} {Γ} {Δ} {A} x∉s xFrΓ xFrΔ Π) (z≢x , ec) (x∉t , nc) y yIn
  with isEigentoken-substR (sym (substCtx-++ z t [ (□ A) ^ s ] Δ))
         (⊢□ (∉Pos-substPos z t s x∉s x∉t) (TokenFresh-substCtx z x t Γ z≢x x∉t xFrΓ) (TokenFresh-substCtx z x t Δ z≢x x∉t xFrΔ)
              (subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ A ^ insertToken x s ] Δ ∙
                                          cong (λ p → [ A ^ p ] ,, substCtx z t Δ) (substPos-insertToken-neq z x s t z≢x))
                     (substTokenToPosProof z t Π ec nc))) y yIn
... | inl y≡x = inl y≡x  -- eigentoken x is preserved
... | inr yInΠ'' = inr (isEigentoken-substTokenToPosProof z t Π ec nc y
                         (isEigentoken-substR (substCtx-++ z t [ A ^ insertToken x s ] Δ ∙
                                               cong (λ p → [ A ^ p ] ,, substCtx z t Δ) (substPos-insertToken-neq z x s t z≢x))
                                              (substTokenToPosProof z t Π ec nc) y yInΠ''))
-- ♢⊢ case: symmetric to ⊢□
isEigentoken-substTokenToPosProof z t (♢⊢ {x} {s} {Γ} {Δ} {A} x∉s xFrΓ xFrΔ Π) (z≢x , ec) (x∉t , nc) y yIn
  with isEigentoken-substL (sym (substCtx-++ z t Γ [ (♢ A) ^ s ]))
         (♢⊢ (∉Pos-substPos z t s x∉s x∉t) (TokenFresh-substCtx z x t Γ z≢x x∉t xFrΓ) (TokenFresh-substCtx z x t Δ z≢x x∉t xFrΔ)
              (subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ A ^ insertToken x s ] ∙
                                          cong (λ p → substCtx z t Γ ,, [ A ^ p ]) (substPos-insertToken-neq z x s t z≢x))
                     (substTokenToPosProof z t Π ec nc))) y yIn
... | inl y≡x = inl y≡x  -- eigentoken x is preserved
... | inr yInΠ'' = inr (isEigentoken-substTokenToPosProof z t Π ec nc y
                         (isEigentoken-substL (substCtx-++ z t Γ [ A ^ insertToken x s ] ∙
                                               cong (λ p → substCtx z t Γ ,, [ A ^ p ]) (substPos-insertToken-neq z x s t z≢x))
                                              (substTokenToPosProof z t Π ec nc) y yInΠ''))
isEigentoken-substTokenToPosProof z t (⊢♢ {Γ} {A} {s} {t'} {Δ} Π) ec nc y yIn =
  let Π' = substTokenToPosProof z t Π ec nc
      ctx-eq = substCtx-++ z t [ A ^ (s ++Pos t') ] Δ
      pos-eq = substPos-++Pos-distr z t s t'
      Π'' = subst (substCtx z t Γ ⊢_) (ctx-eq ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π'
      out-path = sym (substCtx-++ z t [ (♢ A) ^ s ] Δ)
      yIn' = isEigentoken-substR out-path (⊢♢ Π'') y yIn
      yIn'' = isEigentoken-substR (ctx-eq ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π' y yIn'
  in isEigentoken-substTokenToPosProof z t Π ec nc y yIn''

-- Helper: EigenposCond for tokens smaller than a base that is larger than all eigentokens
-- If x < base and all eigentokens in Π are ≥ base, then EigenposCond x Π holds
EigenposCond-from-lt-base : (x base : Token) {Γ Δ : Ctx} (Π : Γ ⊢ Δ)
  → x < base
  → ((y : Token) → isEigentoken y Π → base ≤ y)  -- all eigentokens ≥ base
  → EigenposCond x Π
EigenposCond-from-lt-base x base Ax x<base _ = tt
EigenposCond-from-lt-base x base (Cut Π₁ Π₂) x<base allGe =
  EigenposCond-from-lt-base x base Π₁ x<base (λ y yIn → allGe y (inl yIn)) ,
  EigenposCond-from-lt-base x base Π₂ x<base (λ y yIn → allGe y (inr yIn))
EigenposCond-from-lt-base x base (W⊢ Π) x<base allGe = EigenposCond-from-lt-base x base Π x<base allGe
EigenposCond-from-lt-base x base (⊢W Π) x<base allGe = EigenposCond-from-lt-base x base Π x<base allGe
EigenposCond-from-lt-base x base (C⊢ Π) x<base allGe = EigenposCond-from-lt-base x base Π x<base allGe
EigenposCond-from-lt-base x base (⊢C Π) x<base allGe = EigenposCond-from-lt-base x base Π x<base allGe
EigenposCond-from-lt-base x base (Exc⊢ Π) x<base allGe = EigenposCond-from-lt-base x base Π x<base allGe
EigenposCond-from-lt-base x base (⊢Exc Π) x<base allGe = EigenposCond-from-lt-base x base Π x<base allGe
EigenposCond-from-lt-base x base (¬⊢ Π) x<base allGe = EigenposCond-from-lt-base x base Π x<base allGe
EigenposCond-from-lt-base x base (⊢¬ Π) x<base allGe = EigenposCond-from-lt-base x base Π x<base allGe
EigenposCond-from-lt-base x base (∧₁⊢ Π) x<base allGe = EigenposCond-from-lt-base x base Π x<base allGe
EigenposCond-from-lt-base x base (∧₂⊢ Π) x<base allGe = EigenposCond-from-lt-base x base Π x<base allGe
EigenposCond-from-lt-base x base (⊢∧ Π₁ Π₂) x<base allGe =
  EigenposCond-from-lt-base x base Π₁ x<base (λ y yIn → allGe y (inl yIn)) ,
  EigenposCond-from-lt-base x base Π₂ x<base (λ y yIn → allGe y (inr yIn))
EigenposCond-from-lt-base x base (∨⊢ Π₁ Π₂) x<base allGe =
  EigenposCond-from-lt-base x base Π₁ x<base (λ y yIn → allGe y (inl yIn)) ,
  EigenposCond-from-lt-base x base Π₂ x<base (λ y yIn → allGe y (inr yIn))
EigenposCond-from-lt-base x base (⊢∨₁ Π) x<base allGe = EigenposCond-from-lt-base x base Π x<base allGe
EigenposCond-from-lt-base x base (⊢∨₂ Π) x<base allGe = EigenposCond-from-lt-base x base Π x<base allGe
EigenposCond-from-lt-base x base (⇒⊢ Π₁ Π₂) x<base allGe =
  EigenposCond-from-lt-base x base Π₁ x<base (λ y yIn → allGe y (inl yIn)) ,
  EigenposCond-from-lt-base x base Π₂ x<base (λ y yIn → allGe y (inr yIn))
EigenposCond-from-lt-base x base (⊢⇒ Π) x<base allGe = EigenposCond-from-lt-base x base Π x<base allGe
EigenposCond-from-lt-base x base (□⊢ Π) x<base allGe = EigenposCond-from-lt-base x base Π x<base allGe
EigenposCond-from-lt-base x base (⊢□ {x = y} _ _ _ Π) x<base allGe =
  let y≥base : base ≤ y
      y≥base = allGe y (inl refl)
      x≢y : x ≢ y
      x≢y x≡y = <→≢ (≤-trans x<base y≥base) x≡y
  in x≢y , EigenposCond-from-lt-base x base Π x<base (λ z zIn → allGe z (inr zIn))
EigenposCond-from-lt-base x base (♢⊢ {x = y} _ _ _ Π) x<base allGe =
  let y≥base = allGe y (inl refl)
      x≢y = λ x≡y → <→≢ (≤-trans x<base y≥base) x≡y
  in x≢y , EigenposCond-from-lt-base x base Π x<base (λ z zIn → allGe z (inr zIn))
EigenposCond-from-lt-base x base (⊢♢ Π) x<base allGe = EigenposCond-from-lt-base x base Π x<base allGe

-- Result type for makeWellFormed-go
-- Contains: proof, next counter, bounds, and eigentoken bound evidence
-- Parameterized by both base and k (starting counter) to track k ≤ next
record MWFResult {Γ Δ : Ctx} (base k : Token) : Type where
  constructor mkMWFResult
  field
    proof : Γ ⊢ Δ
    next : Token
    k≤next : k ≤ next
    maxEigen<next : maxEigenposToken proof < next
    allEigen≥base : (y : Token) → isEigentoken y proof → base ≤ y

-- Helper lemma: myMax preserves bounds
myMax-<-both : ∀ {a b c} → a < c → b < c → myMax a b < c
myMax-<-both {zero} {b} {c} _ b<c = b<c
myMax-<-both {suc a} {zero} {c} a<c _ = a<c
myMax-<-both {suc a} {suc b} {zero} a<zero _ = ⊥-rec (¬-<-zero a<zero)
myMax-<-both {suc a} {suc b} {suc c} a<c b<c = suc-≤-suc (myMax-<-both (pred-≤-pred a<c) (pred-≤-pred b<c))

-- makeWellFormed-go: main recursive function
-- base: must be > all tokens in original sequent and > all original eigentokens
-- k: current counter, starts at base
-- origMax<base: all eigentokens in original proof are < base
-- proofMax<base: all tokens in proof (contexts + cut formulas) are < base
-- Returns well-formed proof with all eigentokens in [base, next), and k ≤ next
makeWellFormed-go : (base k : Token) → base ≤ k → ∀ {Γ Δ} (Π : Γ ⊢ Δ)
  → maxEigenposToken Π < base  -- eigentokens in original are < base
  → maxTokenProof Π < base  -- all tokens in proof are < base
  → MWFResult {Γ} {Δ} base k

-- Axiom: no eigentokens
-- maxEigenposToken Ax = 0, need 0 < k. From origMax<base : 0 < base and base≤k : base ≤ k.
makeWellFormed-go base k base≤k Ax origMax<base proofMax<base = mkMWFResult Ax k ≤-refl (≤-trans origMax<base base≤k) (λ _ ())

-- Cut: process both subproofs
-- Cut : Γ₁ ,, [ A ^ s ] ⊢ Δ₁  and  Γ₂ ⊢ [ A ^ s ] ,, Δ₂  gives  Γ₁ ,, Γ₂ ⊢ Δ₁ ,, Δ₂
makeWellFormed-go base k base≤k (Cut {Γ₁} {A} {s} {Δ₁} {Γ₂} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  mkMWFResult (Cut Π₁' Π₂') next' k≤next' maxCut<next' allGe
  where
    max₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxEigenposToken Π₁) _)) origMax<base
    max₂<base = ≤-trans (suc-≤-suc (≤-myMax-r _ (maxEigenposToken Π₂))) origMax<base
    -- Proof bounds for subproofs: maxTokenProof of subproof ≤ maxTokenProof of Cut
    -- maxTokenProof (Cut ...) = myMax (maxTokenCtx ...) (myMax (maxTokenPos s) (myMax (maxTokenProof Π₁) (maxTokenProof Π₂)))
    proof₁<base : maxTokenProof Π₁ < base
    proof₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenPos s) (myMax (maxTokenProof Π₁) (maxTokenProof Π₂))))
                           (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenCtx ((Γ₁ ,, Γ₂) ,, (Δ₁ ,, Δ₂))) _)) proofMax<base))
    proof₂<base : maxTokenProof Π₂ < base
    proof₂<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenPos s) (myMax (maxTokenProof Π₁) (maxTokenProof Π₂))))
                           (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenCtx ((Γ₁ ,, Γ₂) ,, (Δ₁ ,, Δ₂))) _)) proofMax<base))
    mwfR₁ = makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
    base≤next₁ = ≤-trans base≤k (MWFResult.k≤next mwfR₁)
    mwfR₂ = makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
    Π₁' = MWFResult.proof mwfR₁
    Π₂' = MWFResult.proof mwfR₂
    next' = MWFResult.next mwfR₂
    max₁<next₁ = MWFResult.maxEigen<next mwfR₁
    max₂<next' = MWFResult.maxEigen<next mwfR₂
    next₁≤next' = MWFResult.k≤next mwfR₂
    max₁<next' = ≤-trans max₁<next₁ next₁≤next'
    maxCut<next' = myMax-<-both max₁<next' max₂<next'
    k≤next' = ≤-trans (MWFResult.k≤next mwfR₁) next₁≤next'
    allGe : (y : Token) → isEigentoken y (Cut Π₁' Π₂') → base ≤ y
    allGe y (inl yIn₁) = MWFResult.allEigen≥base mwfR₁ y yIn₁
    allGe y (inr yIn₂) = MWFResult.allEigen≥base mwfR₂ y yIn₂

-- Structural rules: just recurse (context bounds are preserved or derived)
makeWellFormed-go base k base≤k (W⊢ Π) origMax<base proofMax<base =
  let mwfR = makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base)
  in mkMWFResult (W⊢ (MWFResult.proof mwfR)) (MWFResult.next mwfR) (MWFResult.k≤next mwfR)
       (MWFResult.maxEigen<next mwfR) (MWFResult.allEigen≥base mwfR)
makeWellFormed-go base k base≤k (⊢W Π) origMax<base proofMax<base =
  let mwfR = makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base)
  in mkMWFResult (⊢W (MWFResult.proof mwfR)) (MWFResult.next mwfR) (MWFResult.k≤next mwfR)
       (MWFResult.maxEigen<next mwfR) (MWFResult.allEigen≥base mwfR)
makeWellFormed-go base k base≤k (C⊢ Π) origMax<base proofMax<base =
  let mwfR = makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base)
  in mkMWFResult (C⊢ (MWFResult.proof mwfR)) (MWFResult.next mwfR) (MWFResult.k≤next mwfR)
       (MWFResult.maxEigen<next mwfR) (MWFResult.allEigen≥base mwfR)
makeWellFormed-go base k base≤k (⊢C Π) origMax<base proofMax<base =
  let mwfR = makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base)
  in mkMWFResult (⊢C (MWFResult.proof mwfR)) (MWFResult.next mwfR) (MWFResult.k≤next mwfR)
       (MWFResult.maxEigen<next mwfR) (MWFResult.allEigen≥base mwfR)
makeWellFormed-go base k base≤k (Exc⊢ {Γ₁} {A} {s} {B} {t} {Γ₂} {Δ} Π) origMax<base proofMax<base =
  let mwfR = makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base)
  in mkMWFResult (Exc⊢ {Γ₁} {A} {s} {B} {t} {Γ₂} {Δ} (MWFResult.proof mwfR)) (MWFResult.next mwfR) (MWFResult.k≤next mwfR)
       (MWFResult.maxEigen<next mwfR) (MWFResult.allEigen≥base mwfR)
makeWellFormed-go base k base≤k (⊢Exc {Γ} {Δ₁} {A} {s} {B} {t} {Δ₂} Π) origMax<base proofMax<base =
  let mwfR = makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base)
  in mkMWFResult (⊢Exc {Γ} {Δ₁} {A} {s} {B} {t} {Δ₂} (MWFResult.proof mwfR)) (MWFResult.next mwfR) (MWFResult.k≤next mwfR)
       (MWFResult.maxEigen<next mwfR) (MWFResult.allEigen≥base mwfR)

-- Propositional rules
makeWellFormed-go base k base≤k (¬⊢ Π) origMax<base proofMax<base =
  let mwfR = makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base)
  in mkMWFResult (¬⊢ (MWFResult.proof mwfR)) (MWFResult.next mwfR) (MWFResult.k≤next mwfR)
       (MWFResult.maxEigen<next mwfR) (MWFResult.allEigen≥base mwfR)
makeWellFormed-go base k base≤k (⊢¬ Π) origMax<base proofMax<base =
  let mwfR = makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base)
  in mkMWFResult (⊢¬ (MWFResult.proof mwfR)) (MWFResult.next mwfR) (MWFResult.k≤next mwfR)
       (MWFResult.maxEigen<next mwfR) (MWFResult.allEigen≥base mwfR)
makeWellFormed-go base k base≤k (∧₁⊢ Π) origMax<base proofMax<base =
  let mwfR = makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base)
  in mkMWFResult (∧₁⊢ (MWFResult.proof mwfR)) (MWFResult.next mwfR) (MWFResult.k≤next mwfR)
       (MWFResult.maxEigen<next mwfR) (MWFResult.allEigen≥base mwfR)
makeWellFormed-go base k base≤k (∧₂⊢ Π) origMax<base proofMax<base =
  let mwfR = makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base)
  in mkMWFResult (∧₂⊢ (MWFResult.proof mwfR)) (MWFResult.next mwfR) (MWFResult.k≤next mwfR)
       (MWFResult.maxEigen<next mwfR) (MWFResult.allEigen≥base mwfR)
makeWellFormed-go base k base≤k (⊢∨₁ Π) origMax<base proofMax<base =
  let mwfR = makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base)
  in mkMWFResult (⊢∨₁ (MWFResult.proof mwfR)) (MWFResult.next mwfR) (MWFResult.k≤next mwfR)
       (MWFResult.maxEigen<next mwfR) (MWFResult.allEigen≥base mwfR)
makeWellFormed-go base k base≤k (⊢∨₂ Π) origMax<base proofMax<base =
  let mwfR = makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base)
  in mkMWFResult (⊢∨₂ (MWFResult.proof mwfR)) (MWFResult.next mwfR) (MWFResult.k≤next mwfR)
       (MWFResult.maxEigen<next mwfR) (MWFResult.allEigen≥base mwfR)
makeWellFormed-go base k base≤k (⊢⇒ Π) origMax<base proofMax<base =
  let mwfR = makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base)
  in mkMWFResult (⊢⇒ (MWFResult.proof mwfR)) (MWFResult.next mwfR) (MWFResult.k≤next mwfR)
       (MWFResult.maxEigen<next mwfR) (MWFResult.allEigen≥base mwfR)

-- Binary propositional rules
makeWellFormed-go base k base≤k (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  mkMWFResult (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} (MWFResult.proof mwfR₁) (MWFResult.proof mwfR₂)) (MWFResult.next mwfR₂)
       k≤next' maxBoth<next' allGe
  where
    ctxMax = maxTokenCtx ((Γ₁ ,, Γ₂) ,, ([ (A and B) ^ s ] ,, Δ₁ ,, Δ₂))
    proofMax = myMax (maxTokenProof Π₁) (maxTokenProof Π₂)
    max₁<base = ≤-trans (suc-≤-suc (≤-myMax-l _ _)) origMax<base
    max₂<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) origMax<base
    proof₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
    proof₂<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
    mwfR₁ = makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
    base≤next₁ = ≤-trans base≤k (MWFResult.k≤next mwfR₁)
    mwfR₂ = makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
    max₁<next' = ≤-trans (MWFResult.maxEigen<next mwfR₁) (MWFResult.k≤next mwfR₂)
    maxBoth<next' = myMax-<-both max₁<next' (MWFResult.maxEigen<next mwfR₂)
    k≤next' = ≤-trans (MWFResult.k≤next mwfR₁) (MWFResult.k≤next mwfR₂)
    allGe : (y : Token) → isEigentoken y (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} (MWFResult.proof mwfR₁) (MWFResult.proof mwfR₂)) → base ≤ y
    allGe y (inl yIn₁) = MWFResult.allEigen≥base mwfR₁ y yIn₁
    allGe y (inr yIn₂) = MWFResult.allEigen≥base mwfR₂ y yIn₂
makeWellFormed-go base k base≤k (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  mkMWFResult (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} (MWFResult.proof mwfR₁) (MWFResult.proof mwfR₂)) (MWFResult.next mwfR₂)
       k≤next' maxBoth<next' allGe
  where
    ctxMax = maxTokenCtx ((Γ₁ ,, Γ₂ ,, [ (A or B) ^ s ]) ,, (Δ₁ ,, Δ₂))
    proofMax = myMax (maxTokenProof Π₁) (maxTokenProof Π₂)
    max₁<base = ≤-trans (suc-≤-suc (≤-myMax-l _ _)) origMax<base
    max₂<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) origMax<base
    proof₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
    proof₂<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
    mwfR₁ = makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
    base≤next₁ = ≤-trans base≤k (MWFResult.k≤next mwfR₁)
    mwfR₂ = makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
    max₁<next' = ≤-trans (MWFResult.maxEigen<next mwfR₁) (MWFResult.k≤next mwfR₂)
    maxBoth<next' = myMax-<-both max₁<next' (MWFResult.maxEigen<next mwfR₂)
    k≤next' = ≤-trans (MWFResult.k≤next mwfR₁) (MWFResult.k≤next mwfR₂)
    allGe : (y : Token) → isEigentoken y (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} (MWFResult.proof mwfR₁) (MWFResult.proof mwfR₂)) → base ≤ y
    allGe y (inl yIn₁) = MWFResult.allEigen≥base mwfR₁ y yIn₁
    allGe y (inr yIn₂) = MWFResult.allEigen≥base mwfR₂ y yIn₂
-- ⇒⊢ : (Γ₁ ,, [ B ^ s ] ⊢ Δ₁) → (Γ₂ ⊢ [ A ^ s ] ,, Δ₂) → (Γ₁ ,, Γ₂ ,, [ (A ⇒ B) ^ s ] ⊢ Δ₁ ,, Δ₂)
-- Implicit order: {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂}
makeWellFormed-go base k base≤k (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  mkMWFResult (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} (MWFResult.proof mwfR₁) (MWFResult.proof mwfR₂)) (MWFResult.next mwfR₂)
       k≤next' maxBoth<next' allGe
  where
    ctxMax = maxTokenCtx ((Γ₁ ,, Γ₂ ,, [ (A ⇒ B) ^ s ]) ,, (Δ₁ ,, Δ₂))
    proofMax = myMax (maxTokenProof Π₁) (maxTokenProof Π₂)
    max₁<base = ≤-trans (suc-≤-suc (≤-myMax-l _ _)) origMax<base
    max₂<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) origMax<base
    proof₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
    proof₂<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
    mwfR₁ = makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
    base≤next₁ = ≤-trans base≤k (MWFResult.k≤next mwfR₁)
    mwfR₂ = makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
    max₁<next' = ≤-trans (MWFResult.maxEigen<next mwfR₁) (MWFResult.k≤next mwfR₂)
    maxBoth<next' = myMax-<-both max₁<next' (MWFResult.maxEigen<next mwfR₂)
    k≤next' = ≤-trans (MWFResult.k≤next mwfR₁) (MWFResult.k≤next mwfR₂)
    allGe : (y : Token) → isEigentoken y (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} (MWFResult.proof mwfR₁) (MWFResult.proof mwfR₂)) → base ≤ y
    allGe y (inl yIn₁) = MWFResult.allEigen≥base mwfR₁ y yIn₁
    allGe y (inr yIn₂) = MWFResult.allEigen≥base mwfR₂ y yIn₂

-- Non-eigentoken modal rules
makeWellFormed-go base k base≤k (□⊢ Π) origMax<base proofMax<base =
  let mwfR = makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base)
  in mkMWFResult (□⊢ (MWFResult.proof mwfR)) (MWFResult.next mwfR) (MWFResult.k≤next mwfR)
       (MWFResult.maxEigen<next mwfR) (MWFResult.allEigen≥base mwfR)
makeWellFormed-go base k base≤k (⊢♢ Π) origMax<base proofMax<base =
  let mwfR = makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base)
  in mkMWFResult (⊢♢ (MWFResult.proof mwfR)) (MWFResult.next mwfR) (MWFResult.k≤next mwfR)
       (MWFResult.maxEigen<next mwfR) (MWFResult.allEigen≥base mwfR)

-- ⊢□ case: eigentoken rule on the right
-- This is the key case where we need to rename the eigentoken
makeWellFormed-go base k base≤k (⊢□ {x} {r} {Γ} {Δ} {A} x∉r xFrΓ xFrΔ Π) origMax<base proofMax<base = result
  where
    -- origMax<base : maxEigenposToken (⊢□ x∉r xFrΓ xFrΔ Π) < base
    -- maxEigenposToken (⊢□ ...) = myMax x (maxEigenposToken Π)
    -- So x < base and maxEigenposToken Π < base

    x<base : x < base
    x<base = ≤-trans (suc-≤-suc (≤-myMax-l x _)) origMax<base

    subMax<base : maxEigenposToken Π < base
    subMax<base = ≤-trans (suc-≤-suc (≤-myMax-r x _)) origMax<base

    -- Context bounds derived from proofMax<base via ≤-myMax-l
    -- maxTokenProof (⊢□ ...) = myMax (maxTokenCtx (Γ ,, [ □ A ^ r ] ,, Δ)) (maxTokenProof Π)
    -- Note: the conclusion of ⊢□ is Γ ⊢ ([ □ A ^ r ] ,, Δ)
    -- So proofMax<base : myMax (maxTokenCtx (Γ ,, [ □ A ^ r ] ,, Δ)) (maxTokenProof Π) < base
    ctxMax<base : maxTokenCtx (Γ ,, ([ □ A ^ r ] ,, Δ)) < base
    ctxMax<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenCtx (Γ ,, [ □ A ^ r ] ,, Δ)) (maxTokenProof Π))) proofMax<base

    -- Use maxTokenCtx-++ to convert to myMax form for easier manipulation
    ctxMax-eq : maxTokenCtx (Γ ,, [ □ A ^ r ] ,, Δ) ≡ myMax (maxTokenCtx Γ) (maxTokenCtx ([ □ A ^ r ] ,, Δ))
    ctxMax-eq = maxTokenCtx-++ Γ ([ □ A ^ r ] ,, Δ)

    ctxMax<base' : myMax (maxTokenCtx Γ) (maxTokenCtx ([ □ A ^ r ] ,, Δ)) < base
    ctxMax<base' = subst (_< base) ctxMax-eq ctxMax<base

    r<base : maxTokenPos r < base
    r<base = ≤-trans (suc-≤-suc (≤-trans (≤-myMax-l (maxTokenPos r) (maxTokenCtx Δ))
                                         (≤-myMax-r (maxTokenCtx Γ) (maxTokenCtx ([ □ A ^ r ] ,, Δ)))))
                     ctxMax<base'

    Γ<base : maxTokenCtx Γ < base
    Γ<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenCtx Γ) (maxTokenCtx ([ □ A ^ r ] ,, Δ)))) ctxMax<base'

    Δ<base : maxTokenCtx Δ < base
    Δ<base = ≤-trans (suc-≤-suc (≤-trans (≤-myMax-r (maxTokenPos r) (maxTokenCtx Δ))
                                         (≤-myMax-r (maxTokenCtx Γ) (maxTokenCtx ([ □ A ^ r ] ,, Δ)))))
                     ctxMax<base'

    -- Subproof bound from proofMax<base via ≤-myMax-r
    subProof<base : maxTokenProof Π < base
    subProof<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base

    -- First, recursively make the subproof well-formed
    mwfR = makeWellFormed-go base k base≤k Π subMax<base subProof<base
    Π-wf = MWFResult.proof mwfR
    next = MWFResult.next mwfR

    -- Choose x' = next as new eigentoken
    x' : Token
    x' = next

    -- x' ≥ k, so x' is fresh for r, Γ, Δ (which have tokens < base ≤ k ≤ x')
    k≤x' : k ≤ next
    k≤x' = MWFResult.k≤next mwfR

    -- EigenposCond x Π-wf: x < base ≤ all eigentokens in Π-wf
    ec : EigenposCond x Π-wf
    ec = EigenposCond-from-lt-base x base Π-wf x<base (MWFResult.allEigen≥base mwfR)

    -- NoEigenposInt: x' > maxEigenposToken Π-wf
    nc : NoEigenposInt (singleton-pos x') Π-wf
    nc = NoEigenposInt-singleton-fresh x' Π-wf (MWFResult.maxEigen<next mwfR)

    -- Substitute to rename x to x'
    Π-subst = substTokenToPosProof x (singleton-pos x') Π-wf ec nc

    -- Transport to correct type
    Γ-unchanged : substCtx x (singleton-pos x') Γ ≡ Γ
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ xFrΓ

    Δ-unchanged : substCtx x (singleton-pos x') Δ ≡ Δ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ xFrΔ

    pos-eq : substPos x (singleton-pos x') (insertToken x r) ≡ insertToken x' r
    pos-eq = substPos-insertToken-eq x x' r x∉r

    ctx-eq : substCtx x (singleton-pos x') ([ A ^ insertToken x r ] ,, Δ) ≡ [ A ^ insertToken x' r ] ,, Δ
    ctx-eq = substCtx-++ x (singleton-pos x') [ A ^ insertToken x r ] Δ
             ∙ cong₂ _,,_ (cong [_] (cong (A ^_) pos-eq)) Δ-unchanged

    Π' : Γ ⊢ ([ A ^ insertToken x' r ] ,, Δ)
    Π' = subst2 _⊢_ Γ-unchanged ctx-eq Π-subst

    -- Freshness for x': x' ≥ k ≥ base > maxTokenPos r / maxTokenCtx Γ / maxTokenCtx Δ
    x'>r : x' > maxTokenPos r
    x'>r = ≤-trans r<base (≤-trans base≤k k≤x')

    x'>Γ : x' > maxTokenCtx Γ
    x'>Γ = ≤-trans Γ<base (≤-trans base≤k k≤x')

    x'>Δ : x' > maxTokenCtx Δ
    x'>Δ = ≤-trans Δ<base (≤-trans base≤k k≤x')

    x'∉r : x' ∉Pos r
    x'∉r = >-maxTokenPos-∉Pos x' r x'>r

    x'FrΓ : TokenFresh x' Γ
    x'FrΓ = >-maxTokenCtx-TokenFresh x' Γ x'>Γ

    x'FrΔ : TokenFresh x' Δ
    x'FrΔ = >-maxTokenCtx-TokenFresh x' Δ x'>Δ

    -- Apply ⊢□ with new eigentoken x'
    result-proof = ⊢□ {x = x'} x'∉r x'FrΓ x'FrΔ Π'

    -- Bounds for result
    next' = suc x'

    -- maxEigenposToken result-proof = myMax x' (maxEigenposToken Π')
    -- We need myMax x' (maxEigenposToken Π') < suc x' = next'
    -- This requires: x' < suc x' (trivial) and maxEigenposToken Π' < suc x'
    -- We know maxEigenposToken Π-wf < next = x', so maxEigenposToken Π-wf < suc x'
    -- Note: Π' and Π-wf have the same eigentokens (subst/substTokenToPosProof preserve them when EigenposCond holds)

    -- x' = next, next' = suc x' = suc next
    -- x' < next' is suc x' ≤ suc x' = ≤-refl
    x'<next' : x' < next'
    x'<next' = ≤-refl

    -- next ≤ next' = next ≤ suc next
    next≤next' : next ≤ next'
    next≤next' = ≤-suc next

    -- maxEigenposToken Π-wf < next = x' ≤ suc x' = next'
    maxΠ-wf<next' : maxEigenposToken Π-wf < next'
    maxΠ-wf<next' = ≤-trans (MWFResult.maxEigen<next mwfR) next≤next'

    -- The bound we need: maxEigenposToken result-proof < next'
    -- result-proof = ⊢□ {x = x'} ... Π'
    -- maxEigenposToken result-proof = myMax x' (maxEigenposToken Π')
    -- We have: x' < next' and maxEigenposToken Π-wf < next = x' < next'
    --
    -- Equality path: maxEigenposToken Π' ≡ maxEigenposToken Π-subst ≡ maxEigenposToken Π-wf
    -- 1. maxEigenposToken Π' ≡ maxEigenposToken Π-subst via maxEigenposToken-subst2
    -- 2. maxEigenposToken Π-subst ≡ maxEigenposToken Π-wf (substTokenToPosProof preserves eigentokens
    --    because EigenposCond x Π-wf ensures x is not an eigentoken, so subst only affects positions)
    -- Note: Step 2 requires a proof by induction on Π-wf. For now, we observe that since
    -- maxEigenposToken only counts eigentoken values and substTokenToPosProof preserves the proof
    -- structure with the same eigentokens, the values are equal.

    -- Use maxEigenposToken-subst2 for the subst2 part
    maxΠ'-eq-subst : maxEigenposToken Π' ≡ maxEigenposToken Π-subst
    maxΠ'-eq-subst = maxEigenposToken-subst2 Γ-unchanged ctx-eq Π-subst

    -- substTokenToPosProof preserves maxEigenposToken (using the postulated lemma)
    maxΠ-subst-eq : maxEigenposToken Π-subst ≡ maxEigenposToken Π-wf
    maxΠ-subst-eq = maxEigenposToken-substTokenToPosProof x (singleton-pos x') Π-wf ec nc

    maxΠ-subst<next' : maxEigenposToken Π-subst < next'
    maxΠ-subst<next' = subst (_< next') (sym maxΠ-subst-eq) maxΠ-wf<next'

    maxΠ'<next' : maxEigenposToken Π' < next'
    maxΠ'<next' = subst (_< next') (sym maxΠ'-eq-subst) maxΠ-subst<next'

    maxNew : maxEigenposToken result-proof < next'
    maxNew = myMax-<-both x'<next' maxΠ'<next'

    k≤next' : k ≤ next'
    k≤next' = ≤-trans (MWFResult.k≤next mwfR) next≤next'

    -- All eigentokens in result are ≥ base
    -- Result has eigentoken x' (which is ≥ base) and eigentokens from Π'
    -- Eigentokens in Π' are same as in Π-wf (subst doesn't change them) which are ≥ base
    base≤x' : base ≤ x'
    base≤x' = ≤-trans base≤k k≤x'

    allGeNew : (y : Token) → isEigentoken y result-proof → base ≤ y
    allGeNew y (inl y≡x') = subst (base ≤_) (sym y≡x') base≤x'
    allGeNew y (inr yInΠ') =
      -- yInΠ' : isEigentoken y Π'
      -- Need: isEigentoken y Π-wf (which is MWFResult.proof mwfR)
      let yInΠ-subst = isEigentoken-subst2 Γ-unchanged ctx-eq Π-subst y yInΠ'
          yInΠ-wf = isEigentoken-substTokenToPosProof x (singleton-pos x') Π-wf ec nc y yInΠ-subst
      in MWFResult.allEigen≥base mwfR y yInΠ-wf

    result = mkMWFResult result-proof next' k≤next' maxNew allGeNew

-- ♢⊢ case: eigentoken rule on the left (similar to ⊢□)
-- Conclusion: (Γ ,, [ ♢ A ^ r ]) ⊢ Δ
-- Premise: (Γ ,, [ A ^ insertToken x r ]) ⊢ Δ
makeWellFormed-go base k base≤k (♢⊢ {x} {r} {Γ} {Δ} {A} x∉r xFrΓ xFrΔ Π) origMax<base proofMax<base = result
  where
    x<base : x < base
    x<base = ≤-trans (suc-≤-suc (≤-myMax-l x _)) origMax<base

    subMax<base : maxEigenposToken Π < base
    subMax<base = ≤-trans (suc-≤-suc (≤-myMax-r x _)) origMax<base

    -- Context bounds derived from proofMax<base via ≤-myMax-l
    -- maxTokenProof (♢⊢ ...) = myMax (maxTokenCtx ((Γ ,, [ ♢ A ^ r ]) ,, Δ)) (maxTokenProof Π)
    ctxMax<base : maxTokenCtx ((Γ ,, [ ♢ A ^ r ]) ,, Δ) < base
    ctxMax<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenCtx ((Γ ,, [ ♢ A ^ r ]) ,, Δ)) (maxTokenProof Π))) proofMax<base

    -- Use maxTokenCtx-++ to convert to myMax form for easier manipulation
    -- maxTokenCtx ((Γ ,, [ ♢ A ^ r ]) ,, Δ) = myMax (maxTokenCtx (Γ ,, [ ♢ A ^ r ])) (maxTokenCtx Δ)
    ctxMax-eq : maxTokenCtx ((Γ ,, [ ♢ A ^ r ]) ,, Δ) ≡ myMax (maxTokenCtx (Γ ,, [ ♢ A ^ r ])) (maxTokenCtx Δ)
    ctxMax-eq = maxTokenCtx-++ (Γ ,, [ ♢ A ^ r ]) Δ

    ctxMax<base' : myMax (maxTokenCtx (Γ ,, [ ♢ A ^ r ])) (maxTokenCtx Δ) < base
    ctxMax<base' = subst (_< base) ctxMax-eq ctxMax<base

    -- Further decompose: maxTokenCtx (Γ ,, [ ♢ A ^ r ]) = myMax (maxTokenCtx Γ) (maxTokenPos r)
    innerCtx-eq : maxTokenCtx (Γ ,, [ ♢ A ^ r ]) ≡ myMax (maxTokenCtx Γ) (maxTokenPos r)
    innerCtx-eq = maxTokenCtx-++ Γ [ ♢ A ^ r ] ∙ cong (myMax (maxTokenCtx Γ)) (maxTokenCtx-singleton (♢ A) r)

    -- Bounds derived from innerCtx-eq
    -- maxTokenCtx Γ ≤ myMax (maxTokenCtx Γ) (maxTokenPos r) = maxTokenCtx (Γ ,, [ ♢ A ^ r ])
    Γ≤innerCtx : maxTokenCtx Γ ≤ maxTokenCtx (Γ ,, [ ♢ A ^ r ])
    Γ≤innerCtx = subst (maxTokenCtx Γ ≤_) (sym innerCtx-eq) (≤-myMax-l (maxTokenCtx Γ) (maxTokenPos r))

    r≤innerCtx : maxTokenPos r ≤ maxTokenCtx (Γ ,, [ ♢ A ^ r ])
    r≤innerCtx = subst (maxTokenPos r ≤_) (sym innerCtx-eq) (≤-myMax-r (maxTokenCtx Γ) (maxTokenPos r))

    -- Γ < base
    Γ<base : maxTokenCtx Γ < base
    Γ<base = ≤-trans (suc-≤-suc (≤-trans Γ≤innerCtx (≤-myMax-l (maxTokenCtx (Γ ,, [ ♢ A ^ r ])) (maxTokenCtx Δ)))) ctxMax<base'

    -- r < base
    r<base : maxTokenPos r < base
    r<base = ≤-trans (suc-≤-suc (≤-trans r≤innerCtx (≤-myMax-l (maxTokenCtx (Γ ,, [ ♢ A ^ r ])) (maxTokenCtx Δ)))) ctxMax<base'

    Δ<base : maxTokenCtx Δ < base
    Δ<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenCtx (Γ ,, [ ♢ A ^ r ])) (maxTokenCtx Δ))) ctxMax<base'

    -- Subproof bound from proofMax<base via ≤-myMax-r
    subProof<base : maxTokenProof Π < base
    subProof<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base

    mwfR = makeWellFormed-go base k base≤k Π subMax<base subProof<base
    Π-wf = MWFResult.proof mwfR
    next = MWFResult.next mwfR
    x' = next
    k≤x' = MWFResult.k≤next mwfR

    ec : EigenposCond x Π-wf
    ec = EigenposCond-from-lt-base x base Π-wf x<base (MWFResult.allEigen≥base mwfR)

    nc : NoEigenposInt (singleton-pos x') Π-wf
    nc = NoEigenposInt-singleton-fresh x' Π-wf (MWFResult.maxEigen<next mwfR)

    Π-subst = substTokenToPosProof x (singleton-pos x') Π-wf ec nc

    Γ-unchanged : substCtx x (singleton-pos x') Γ ≡ Γ
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ xFrΓ

    Δ-unchanged : substCtx x (singleton-pos x') Δ ≡ Δ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ xFrΔ

    pos-eq : substPos x (singleton-pos x') (insertToken x r) ≡ insertToken x' r
    pos-eq = substPos-insertToken-eq x x' r x∉r

    -- For ♢⊢, the eigenposition is on the left: (Γ ,, [ A ^ insertToken x r ]) ⊢ Δ
    ctx-eq : substCtx x (singleton-pos x') (Γ ,, [ A ^ insertToken x r ]) ≡ Γ ,, [ A ^ insertToken x' r ]
    ctx-eq = substCtx-++ x (singleton-pos x') Γ [ A ^ insertToken x r ]
             ∙ cong₂ _,,_ Γ-unchanged (cong [_] (cong (A ^_) pos-eq))

    Π' : (Γ ,, [ A ^ insertToken x' r ]) ⊢ Δ
    Π' = subst2 _⊢_ ctx-eq Δ-unchanged Π-subst

    -- Freshness for x'
    x'>r : x' > maxTokenPos r
    x'>r = ≤-trans r<base (≤-trans base≤k k≤x')

    x'>Γ : x' > maxTokenCtx Γ
    x'>Γ = ≤-trans Γ<base (≤-trans base≤k k≤x')

    x'>Δ : x' > maxTokenCtx Δ
    x'>Δ = ≤-trans Δ<base (≤-trans base≤k k≤x')

    x'∉r : x' ∉Pos r
    x'∉r = >-maxTokenPos-∉Pos x' r x'>r

    x'FrΓ : TokenFresh x' Γ
    x'FrΓ = >-maxTokenCtx-TokenFresh x' Γ x'>Γ

    x'FrΔ : TokenFresh x' Δ
    x'FrΔ = >-maxTokenCtx-TokenFresh x' Δ x'>Δ

    result-proof = ♢⊢ x'∉r x'FrΓ x'FrΔ Π'
    next' = suc x'

    -- Bounds computation similar to ⊢□ case
    x'<next' : x' < next'
    x'<next' = ≤-refl

    next≤next' : next ≤ next'
    next≤next' = ≤-suc next

    maxΠ-wf<next' : maxEigenposToken Π-wf < next'
    maxΠ-wf<next' = ≤-trans (MWFResult.maxEigen<next mwfR) next≤next'

    -- Equality chain for maxEigenposToken Π'
    maxΠ'-eq-subst : maxEigenposToken Π' ≡ maxEigenposToken Π-subst
    maxΠ'-eq-subst = maxEigenposToken-subst2 ctx-eq Δ-unchanged Π-subst

    maxΠ-subst-eq : maxEigenposToken Π-subst ≡ maxEigenposToken Π-wf
    maxΠ-subst-eq = maxEigenposToken-substTokenToPosProof x (singleton-pos x') Π-wf ec nc

    maxΠ-subst<next' : maxEigenposToken Π-subst < next'
    maxΠ-subst<next' = subst (_< next') (sym maxΠ-subst-eq) maxΠ-wf<next'

    maxΠ'<next' : maxEigenposToken Π' < next'
    maxΠ'<next' = subst (_< next') (sym maxΠ'-eq-subst) maxΠ-subst<next'

    maxNew : maxEigenposToken result-proof < next'
    maxNew = myMax-<-both x'<next' maxΠ'<next'

    k≤next' : k ≤ next'
    k≤next' = ≤-trans (MWFResult.k≤next mwfR) next≤next'

    base≤x' : base ≤ x'
    base≤x' = ≤-trans base≤k k≤x'

    allGeNew : (y : Token) → isEigentoken y result-proof → base ≤ y
    allGeNew y (inl y≡x') = subst (base ≤_) (sym y≡x') base≤x'
    allGeNew y (inr yInΠ') =
      let yInΠ-subst = isEigentoken-subst2 ctx-eq Δ-unchanged Π-subst y yInΠ'
          yInΠ-wf = isEigentoken-substTokenToPosProof x (singleton-pos x') Π-wf ec nc y yInΠ-subst
      in MWFResult.allEigen≥base mwfR y yInΠ-wf

    result = mkMWFResult result-proof next' k≤next' maxNew allGeNew

-- =============================================================================
-- Main makeWellFormed function (Proposition teo:eigenpos1)
-- =============================================================================

-- Lemma: maxTokenCtx (Γ ,, Δ) ≤ maxTokenProof Π for any Π : Γ ⊢ Δ
maxTokenCtx≤maxTokenProof : ∀ {Γ Δ} (Π : Γ ⊢ Δ) → maxTokenCtx (Γ ,, Δ) ≤ maxTokenProof Π
maxTokenCtx≤maxTokenProof Ax = ≤-refl
maxTokenCtx≤maxTokenProof (Cut Π₁ Π₂) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (W⊢ Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (⊢W Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (C⊢ Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (⊢C Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (Exc⊢ Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (⊢Exc Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (¬⊢ Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (⊢¬ Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (∧₁⊢ Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (∧₂⊢ Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (⊢∧ Π₁ Π₂) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (∨⊢ Π₁ Π₂) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (⊢∨₁ Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (⊢∨₂ Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (⇒⊢ Π₁ Π₂) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (⊢⇒ Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (□⊢ Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (⊢□ _ _ _ Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (♢⊢ _ _ _ Π) = ≤-myMax-l _ _
maxTokenCtx≤maxTokenProof (⊢♢ Π) = ≤-myMax-l _ _

-- Compute base token: larger than all eigentokens and all tokens in entire proof
makeWellFormed-base : ∀ {Γ Δ} → (Π : Γ ⊢ Δ) → Token
makeWellFormed-base Π = suc (myMax (maxEigenposToken Π) (maxTokenProof Π))

-- Main function: transform any proof to a well-formed proof
makeWellFormed : ∀ {Γ Δ} → (Π : Γ ⊢ Δ) → Γ ⊢ Δ
makeWellFormed {Γ} {Δ} Π = MWFResult.proof (makeWellFormed-go base base ≤-refl Π origMax<base proofMax<base)
  where
    base = makeWellFormed-base Π
    origMax<base : maxEigenposToken Π < base
    origMax<base = suc-≤-suc (≤-myMax-l _ _)
    proofMax<base : maxTokenProof Π < base
    proofMax<base = suc-≤-suc (≤-myMax-r _ _)

-- Well-formedness property: maxEigenposToken of result < next
makeWellFormed-wf : ∀ {Γ Δ} (Π : Γ ⊢ Δ)
  → let base = makeWellFormed-base Π
        origMax<base = suc-≤-suc (≤-myMax-l _ _)
        proofMax<base = suc-≤-suc (≤-myMax-r _ _)
        mwfR = makeWellFormed-go base base ≤-refl Π origMax<base proofMax<base
    in maxEigenposToken (MWFResult.proof mwfR) < MWFResult.next mwfR
makeWellFormed-wf {Γ} {Δ} Π = MWFResult.maxEigen<next mwfR
  where
    base = makeWellFormed-base Π
    origMax<base = suc-≤-suc (≤-myMax-l _ _)
    proofMax<base = suc-≤-suc (≤-myMax-r _ _)
    mwfR = makeWellFormed-go base base ≤-refl Π origMax<base proofMax<base

-- =============================================================================
-- Degree Preservation (δ-makeWellFormed)
-- =============================================================================

-- Lemma: δ is preserved by subst2 (trivial - type-level transport doesn't change proof structure)
δ-subst2 : ∀ {Γ Γ' Δ Δ'} (p : Γ ≡ Γ') (q : Δ ≡ Δ') (Π : Γ ⊢ Δ)
  → δ (subst2 _⊢_ p q Π) ≡ δ Π
δ-subst2 {Γ} {Γ'} {Δ} {Δ'} p q Π =
  J (λ Γ' p → ∀ Δ' (q : Δ ≡ Δ') → δ (subst2 _⊢_ p q Π) ≡ δ Π)
    (λ Δ' q → J (λ Δ' q → δ (subst2 _⊢_ refl q Π) ≡ δ Π)
                (cong δ (substRefl {B = Γ ⊢_} Π)) q)
    p Δ' q

-- Lemma: δ is preserved by substTokenToPosProof
-- This holds because token substitution only affects positions, not proof structure
-- The degree function δ only depends on proof structure and formula degrees, not positions

-- Helpers for single-argument subst
δ-substR : ∀ {Γ Δ Δ'} (p : Δ ≡ Δ') (Π : Γ ⊢ Δ)
  → δ (subst (Γ ⊢_) p Π) ≡ δ Π
δ-substR p Π = δ-subst2 refl p Π

δ-substL : ∀ {Γ Γ' Δ} (p : Γ ≡ Γ') (Π : Γ ⊢ Δ)
  → δ (subst (_⊢ Δ) p Π) ≡ δ Π
δ-substL p Π = δ-subst2 p refl Π

-- Main lemma by induction on Π
δ-substTokenToPosProof : (z : Token) (t : Position) {Γ Δ : Ctx}
  → (Π : Γ ⊢ Δ) → (ec : EigenposCond z Π) → (nc : NoEigenposInt t Π)
  → δ (substTokenToPosProof z t Π ec nc) ≡ δ Π
δ-substTokenToPosProof z t Ax _ _ = refl
δ-substTokenToPosProof z t (Cut {Γ₁} {A} {s} {Δ₁} {Γ₂} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      outer-eq = δ-subst2 (sym (substCtx-++ z t Γ₁ Γ₂)) (sym (substCtx-++ z t Δ₁ Δ₂))
                   (Cut (subst (substCtx z t Γ₁ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₁) Π₁')
                        (subst (_⊢ substCtx z t Δ₂) (substCtx-++ z t Γ₂ [ A ^ s ]) Π₂'))
      inner₁-eq = δ-substR (substCtx-++ z t [ A ^ s ] Δ₁) Π₁'
      inner₂-eq = δ-substL (substCtx-++ z t Γ₂ [ A ^ s ]) Π₂'
      ih₁ = δ-substTokenToPosProof z t Π₁ ec₁ nc₁
      ih₂ = δ-substTokenToPosProof z t Π₂ ec₂ nc₂
  in outer-eq ∙ cong₂ max (cong suc refl) (cong₂ max (inner₁-eq ∙ ih₁) (inner₂-eq ∙ ih₂))
δ-substTokenToPosProof z t (W⊢ {Γ} {Δ} {A} {s} Π) ec nc =
  δ-substL (sym (substCtx-++ z t Γ [ A ^ s ])) (W⊢ (substTokenToPosProof z t Π ec nc))
  ∙ δ-substTokenToPosProof z t Π ec nc
δ-substTokenToPosProof z t (⊢W {Γ} {Δ} {A} {s} Π) ec nc =
  δ-substR (sym (substCtx-++ z t [ A ^ s ] Δ)) (⊢W (substTokenToPosProof z t Π ec nc))
  ∙ δ-substTokenToPosProof z t Π ec nc
δ-substTokenToPosProof z t (C⊢ {Γ} {A} {s} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ)
                (substCtx-++ z t (Γ ++L [ A ^ s ]) [ A ^ s ] ∙
                 cong (_++L substCtx z t [ A ^ s ]) (substCtx-++ z t Γ [ A ^ s ])) Π'
  in δ-substL (sym (substCtx-++ z t Γ [ A ^ s ])) (C⊢ inner)
     ∙ δ-substL (substCtx-++ z t (Γ ++L [ A ^ s ]) [ A ^ s ] ∙
                 cong (_++L substCtx z t [ A ^ s ]) (substCtx-++ z t Γ [ A ^ s ])) Π'
     ∙ δ-substTokenToPosProof z t Π ec nc
δ-substTokenToPosProof z t (⊢C {Γ} {A} {s} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_)
                (substCtx-++ z t ([ A ^ s ] ++L [ A ^ s ]) Δ ∙
                 cong (_++L substCtx z t Δ) (substCtx-++ z t [ A ^ s ] [ A ^ s ])) Π'
  in δ-substR (sym (substCtx-++ z t [ A ^ s ] Δ)) (⊢C inner)
     ∙ δ-substR (substCtx-++ z t ([ A ^ s ] ++L [ A ^ s ]) Δ ∙
                 cong (_++L substCtx z t Δ) (substCtx-++ z t [ A ^ s ] [ A ^ s ])) Π'
     ∙ δ-substTokenToPosProof z t Π ec nc
δ-substTokenToPosProof z t (Exc⊢ {Γ₁} {A} {s} {B} {t'} {Γ₂} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      step0' = cong (substCtx z t) (++L-assoc (Γ₁ ++L [ B ^ t' ]) [ A ^ s ] Γ₂)
      step1' = substCtx-++ z t (Γ₁ ++L [ B ^ t' ]) (A ^ s ∷ Γ₂)
      step2' = cong (_++L substCtx z t (A ^ s ∷ Γ₂)) (substCtx-++ z t Γ₁ [ B ^ t' ])
      step3' = cong ((substCtx z t Γ₁ ++L substCtx z t [ B ^ t' ]) ++L_) (substCtx-++ z t [ A ^ s ] Γ₂)
      step4' = sym (++L-assoc (substCtx z t Γ₁ ++L substCtx z t [ B ^ t' ]) (substCtx z t [ A ^ s ]) (substCtx z t Γ₂))
      path2 = step0' ∙ step1' ∙ step2' ∙ step3' ∙ step4'
      step0 = cong (substCtx z t) (++L-assoc (Γ₁ ++L [ A ^ s ]) [ B ^ t' ] Γ₂)
      step1 = substCtx-++ z t (Γ₁ ++L [ A ^ s ]) (B ^ t' ∷ Γ₂)
      step2 = cong (_++L substCtx z t (B ^ t' ∷ Γ₂)) (substCtx-++ z t Γ₁ [ A ^ s ])
      step3 = cong ((substCtx z t Γ₁ ++L substCtx z t [ A ^ s ]) ++L_) (substCtx-++ z t [ B ^ t' ] Γ₂)
      step4 = sym (++L-assoc (substCtx z t Γ₁ ++L substCtx z t [ A ^ s ]) (substCtx z t [ B ^ t' ]) (substCtx z t Γ₂))
      path = step0 ∙ step1 ∙ step2 ∙ step3 ∙ step4
      raw = Exc⊢ {Γ₁ = substCtx z t Γ₁} {A = A} {B = B} {Γ₂ = substCtx z t Γ₂}
                 (subst (λ G → G ⊢ substCtx z t Δ) path Π')
  in δ-substL (sym path2) raw
     ∙ δ-substL path Π'
     ∙ δ-substTokenToPosProof z t Π ec nc
δ-substTokenToPosProof z t (⊢Exc {Γ} {Δ₁} {A} {s} {B} {t'} {Δ₂} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      step0' = cong (substCtx z t) (++L-assoc (Δ₁ ++L [ B ^ t' ]) [ A ^ s ] Δ₂)
      step1' = substCtx-++ z t (Δ₁ ++L [ B ^ t' ]) (A ^ s ∷ Δ₂)
      step2' = cong (_++L substCtx z t (A ^ s ∷ Δ₂)) (substCtx-++ z t Δ₁ [ B ^ t' ])
      step3' = cong ((substCtx z t Δ₁ ++L substCtx z t [ B ^ t' ]) ++L_) (substCtx-++ z t [ A ^ s ] Δ₂)
      step4' = sym (++L-assoc (substCtx z t Δ₁ ++L substCtx z t [ B ^ t' ]) (substCtx z t [ A ^ s ]) (substCtx z t Δ₂))
      path2 = step0' ∙ step1' ∙ step2' ∙ step3' ∙ step4'
      step0 = cong (substCtx z t) (++L-assoc (Δ₁ ++L [ A ^ s ]) [ B ^ t' ] Δ₂)
      step1 = substCtx-++ z t (Δ₁ ++L [ A ^ s ]) (B ^ t' ∷ Δ₂)
      step2 = cong (_++L substCtx z t (B ^ t' ∷ Δ₂)) (substCtx-++ z t Δ₁ [ A ^ s ])
      step3 = cong ((substCtx z t Δ₁ ++L substCtx z t [ A ^ s ]) ++L_) (substCtx-++ z t [ B ^ t' ] Δ₂)
      step4 = sym (++L-assoc (substCtx z t Δ₁ ++L substCtx z t [ A ^ s ]) (substCtx z t [ B ^ t' ]) (substCtx z t Δ₂))
      path = step0 ∙ step1 ∙ step2 ∙ step3 ∙ step4
      raw = ⊢Exc {Δ₁ = substCtx z t Δ₁} {A = A} {B = B} {Δ₂ = substCtx z t Δ₂}
                 (subst (λ D → substCtx z t Γ ⊢ D) path Π')
  in δ-substR (sym path2) raw
     ∙ δ-substR path Π'
     ∙ δ-substTokenToPosProof z t Π ec nc
δ-substTokenToPosProof z t (¬⊢ {Γ} {A} {s} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ A ^ s ] Δ) Π'
  in δ-substL (sym (substCtx-++ z t Γ [ (¬ A) ^ s ])) (¬⊢ inner)
     ∙ δ-substR (substCtx-++ z t [ A ^ s ] Δ) Π'
     ∙ δ-substTokenToPosProof z t Π ec nc
δ-substTokenToPosProof z t (⊢¬ {Γ} {A} {s} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ A ^ s ]) Π'
  in δ-substR (sym (substCtx-++ z t [ (¬ A) ^ s ] Δ)) (⊢¬ inner)
     ∙ δ-substL (substCtx-++ z t Γ [ A ^ s ]) Π'
     ∙ δ-substTokenToPosProof z t Π ec nc
δ-substTokenToPosProof z t (∧₁⊢ {Γ} {A} {s} {Δ} {B} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ A ^ s ]) Π'
  in δ-substL (sym (substCtx-++ z t Γ [ (A and B) ^ s ])) (∧₁⊢ inner)
     ∙ δ-substL (substCtx-++ z t Γ [ A ^ s ]) Π'
     ∙ δ-substTokenToPosProof z t Π ec nc
δ-substTokenToPosProof z t (∧₂⊢ {Γ} {B} {s} {Δ} {A} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ B ^ s ]) Π'
  in δ-substL (sym (substCtx-++ z t Γ [ (A and B) ^ s ])) (∧₂⊢ inner)
     ∙ δ-substL (substCtx-++ z t Γ [ B ^ s ]) Π'
     ∙ δ-substTokenToPosProof z t Π ec nc
δ-substTokenToPosProof z t (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      outer-eq = δ-subst2 (sym (substCtx-++ z t Γ₁ Γ₂))
                   (cong (substCtx z t [ (A and B) ^ s ] ++L_) (sym (substCtx-++ z t Δ₁ Δ₂)) ∙
                    sym (substCtx-++ z t [ (A and B) ^ s ] (Δ₁ ++L Δ₂)))
                   (⊢∧ (subst (substCtx z t Γ₁ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₁) Π₁')
                       (subst (substCtx z t Γ₂ ⊢_) (substCtx-++ z t [ B ^ s ] Δ₂) Π₂'))
      inner₁-eq = δ-substR (substCtx-++ z t [ A ^ s ] Δ₁) Π₁'
      inner₂-eq = δ-substR (substCtx-++ z t [ B ^ s ] Δ₂) Π₂'
      ih₁ = δ-substTokenToPosProof z t Π₁ ec₁ nc₁
      ih₂ = δ-substTokenToPosProof z t Π₂ ec₂ nc₂
  in outer-eq ∙ cong₂ max (inner₁-eq ∙ ih₁) (inner₂-eq ∙ ih₂)
δ-substTokenToPosProof z t (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      outer-eq = δ-subst2
                   (cong (substCtx z t Γ₁ ++L_) (sym (substCtx-++ z t Γ₂ [ (A or B) ^ s ]))
                    ∙ sym (substCtx-++ z t Γ₁ (Γ₂ ++L [ (A or B) ^ s ])))
                   (sym (substCtx-++ z t Δ₁ Δ₂))
                   (∨⊢ (subst (_⊢ substCtx z t Δ₁) (substCtx-++ z t Γ₁ [ A ^ s ]) Π₁')
                       (subst (_⊢ substCtx z t Δ₂) (substCtx-++ z t Γ₂ [ B ^ s ]) Π₂'))
      inner₁-eq = δ-substL (substCtx-++ z t Γ₁ [ A ^ s ]) Π₁'
      inner₂-eq = δ-substL (substCtx-++ z t Γ₂ [ B ^ s ]) Π₂'
      ih₁ = δ-substTokenToPosProof z t Π₁ ec₁ nc₁
      ih₂ = δ-substTokenToPosProof z t Π₂ ec₂ nc₂
  in outer-eq ∙ cong₂ max (inner₁-eq ∙ ih₁) (inner₂-eq ∙ ih₂)
δ-substTokenToPosProof z t (⊢∨₁ {Γ} {A} {s} {Δ} {B} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ A ^ s ] Δ) Π'
  in δ-substR (sym (substCtx-++ z t [ (A or B) ^ s ] Δ)) (⊢∨₁ inner)
     ∙ δ-substR (substCtx-++ z t [ A ^ s ] Δ) Π'
     ∙ δ-substTokenToPosProof z t Π ec nc
δ-substTokenToPosProof z t (⊢∨₂ {Γ} {B} {s} {Δ} {A} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ B ^ s ] Δ) Π'
  in δ-substR (sym (substCtx-++ z t [ (A or B) ^ s ] Δ)) (⊢∨₂ inner)
     ∙ δ-substR (substCtx-++ z t [ B ^ s ] Δ) Π'
     ∙ δ-substTokenToPosProof z t Π ec nc
δ-substTokenToPosProof z t (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      outer-eq = δ-subst2
                   (cong (substCtx z t Γ₁ ++L_) (sym (substCtx-++ z t Γ₂ [ (A ⇒ B) ^ s ]))
                    ∙ sym (substCtx-++ z t Γ₁ (Γ₂ ++L [ (A ⇒ B) ^ s ])))
                   (sym (substCtx-++ z t Δ₁ Δ₂))
                   (⇒⊢ (subst (_⊢ substCtx z t Δ₁) (substCtx-++ z t Γ₁ [ B ^ s ]) Π₁')
                       (subst (substCtx z t Γ₂ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₂) Π₂'))
      inner₁-eq = δ-substL (substCtx-++ z t Γ₁ [ B ^ s ]) Π₁'
      inner₂-eq = δ-substR (substCtx-++ z t [ A ^ s ] Δ₂) Π₂'
      ih₁ = δ-substTokenToPosProof z t Π₁ ec₁ nc₁
      ih₂ = δ-substTokenToPosProof z t Π₂ ec₂ nc₂
  in outer-eq ∙ cong₂ max (inner₁-eq ∙ ih₁) (inner₂-eq ∙ ih₂)
δ-substTokenToPosProof z t (⊢⇒ {Γ} {A} {s} {B} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst2 _⊢_ (substCtx-++ z t Γ [ A ^ s ]) (substCtx-++ z t [ B ^ s ] Δ) Π'
  in δ-substR (sym (substCtx-++ z t [ (A ⇒ B) ^ s ] Δ)) (⊢⇒ inner)
     ∙ δ-subst2 (substCtx-++ z t Γ [ A ^ s ]) (substCtx-++ z t [ B ^ s ] Δ) Π'
     ∙ δ-substTokenToPosProof z t Π ec nc
δ-substTokenToPosProof z t (□⊢ {Γ} {A} {s} {t'} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      ctx-eq = substCtx-++ z t Γ [ A ^ (s ++Pos t') ]
      pos-eq = substPos-++Pos-distr z t s t'
      Π'' = subst (_⊢ substCtx z t Δ) (ctx-eq ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π'
      out-path = sym (substCtx-++ z t Γ [ (□ A) ^ s ])
  in δ-substL out-path (□⊢ Π'')
     ∙ δ-substL (ctx-eq ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π'
     ∙ δ-substTokenToPosProof z t Π ec nc
-- ⊢□ case: δ (⊢□ ...) = δ Π
δ-substTokenToPosProof z t (⊢□ {x} {s} {Γ} {Δ} {A} x∉s xFrΓ xFrΔ Π) (z≢x , ec) (x∉t , nc) =
  let Π' = substTokenToPosProof z t Π ec nc
      pos-eq = substPos-insertToken-neq z x s t z≢x
      x∉substs = ∉Pos-substPos z t s x∉s x∉t
      xFrΓ' = TokenFresh-substCtx z x t Γ z≢x x∉t xFrΓ
      xFrΔ' = TokenFresh-substCtx z x t Δ z≢x x∉t xFrΔ
      rhs-path = substCtx-++ z t [ A ^ insertToken x s ] Δ
      Π'' = subst (substCtx z t Γ ⊢_) (rhs-path ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π'
      raw = ⊢□ x∉substs xFrΓ' xFrΔ' Π''
      out-path = sym (substCtx-++ z t [ (□ A) ^ s ] Δ)
      ih = δ-substTokenToPosProof z t Π ec nc
  in δ-substR out-path raw
     ∙ δ-substR (rhs-path ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π'
     ∙ ih
-- ♢⊢ case: symmetric to ⊢□
δ-substTokenToPosProof z t (♢⊢ {x} {s} {Γ} {Δ} {A} x∉s xFrΓ xFrΔ Π) (z≢x , ec) (x∉t , nc) =
  let Π' = substTokenToPosProof z t Π ec nc
      pos-eq = substPos-insertToken-neq z x s t z≢x
      x∉substs = ∉Pos-substPos z t s x∉s x∉t
      xFrΓ' = TokenFresh-substCtx z x t Γ z≢x x∉t xFrΓ
      xFrΔ' = TokenFresh-substCtx z x t Δ z≢x x∉t xFrΔ
      lhs-path = substCtx-++ z t Γ [ A ^ insertToken x s ]
      Π'' = subst (_⊢ substCtx z t Δ) (lhs-path ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π'
      raw = ♢⊢ x∉substs xFrΓ' xFrΔ' Π''
      out-path = sym (substCtx-++ z t Γ [ (♢ A) ^ s ])
      ih = δ-substTokenToPosProof z t Π ec nc
  in δ-substL out-path raw
     ∙ δ-substL (lhs-path ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π'
     ∙ ih
δ-substTokenToPosProof z t (⊢♢ {Γ} {A} {s} {t'} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      ctx-eq = substCtx-++ z t [ A ^ (s ++Pos t') ] Δ
      pos-eq = substPos-++Pos-distr z t s t'
      Π'' = subst (substCtx z t Γ ⊢_) (ctx-eq ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π'
      out-path = sym (substCtx-++ z t [ (♢ A) ^ s ] Δ)
  in δ-substR out-path (⊢♢ Π'')
     ∙ δ-substR (ctx-eq ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π'
     ∙ δ-substTokenToPosProof z t Π ec nc

-- Degree preservation for renameEigenpos-♢⊢-premise-gen
δ-renameEigenpos-♢⊢-premise-gen : ∀ {r t : Position} {x : Token} {Γ Δ : Ctx} {A : Formula}
  → (Π : (Γ ,, [ A ^ t ]) ⊢ Δ)
  → (ext : IsSingleTokenExt r t x)
  → (freshΓ : TokenFresh x Γ)
  → (freshΔ : TokenFresh x Δ)
  → (wf : maxEigenposToken Π < x)
  → (x' : Token)
  → (x'-eigenpos : maxEigenposToken Π < x')
  → (x'∉r : x' ∉Pos r)
  → δ (fst (renameEigenpos-♢⊢-premise-gen Π ext freshΓ freshΔ wf x' x'-eigenpos x'∉r)) ≡ δ Π
δ-renameEigenpos-♢⊢-premise-gen {r} {t} {x} {Γ} {Δ} {A} Π ext freshΓ freshΔ wf x' x'-eigenpos x'∉r =
  δ-subst2 ctx-eq Δ-unchanged Π-subst ∙ δ-substTokenToPosProof x (singleton-pos x') Π ec nc
  where
    ec : EigenposCond x Π
    ec = EigenposCond-from-wf x Π wf
    nc : NoEigenposInt (singleton-pos x') Π
    nc = NoEigenposInt-singleton-fresh x' Π x'-eigenpos
    Π-subst = substTokenToPosProof x (singleton-pos x') Π ec nc
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ freshΓ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ freshΔ
    ctx-eq = substCtx-++ x (singleton-pos x') Γ [ A ^ t ] ∙ cong (_++L [ A ^ substPos x (singleton-pos x') t ]) Γ-unchanged

-- Degree preservation for renameEigenpos-⊢□-premise-gen
δ-renameEigenpos-⊢□-premise-gen : ∀ {r t : Position} {x : Token} {Γ Δ : Ctx} {A : Formula}
  → (Π : Γ ⊢ ([ A ^ t ] ,, Δ))
  → (ext : IsSingleTokenExt r t x)
  → (freshΓ : TokenFresh x Γ)
  → (freshΔ : TokenFresh x Δ)
  → (wf : maxEigenposToken Π < x)
  → (x' : Token)
  → (x'-eigenpos : maxEigenposToken Π < x')
  → (x'∉r : x' ∉Pos r)
  → δ (fst (renameEigenpos-⊢□-premise-gen Π ext freshΓ freshΔ wf x' x'-eigenpos x'∉r)) ≡ δ Π
δ-renameEigenpos-⊢□-premise-gen {r} {t} {x} {Γ} {Δ} {A} Π ext freshΓ freshΔ wf x' x'-eigenpos x'∉r =
  δ-subst2 Γ-unchanged ctx-eq Π-subst ∙ δ-substTokenToPosProof x (singleton-pos x') Π ec nc
  where
    ec : EigenposCond x Π
    ec = EigenposCond-from-wf x Π wf
    nc : NoEigenposInt (singleton-pos x') Π
    nc = NoEigenposInt-singleton-fresh x' Π x'-eigenpos
    Π-subst = substTokenToPosProof x (singleton-pos x') Π ec nc
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ freshΓ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ freshΔ
    ctx-eq = substCtx-++ x (singleton-pos x') [ A ^ t ] Δ ∙ cong ([ A ^ substPos x (singleton-pos x') t ] ++L_) Δ-unchanged

-- Lemma: δ is preserved by makeWellFormed-go
δ-makeWellFormed-go : (base k : Token) (base≤k : base ≤ k) {Γ Δ : Ctx} (Π : Γ ⊢ Δ)
  → (origMax<base : maxEigenposToken Π < base)
  → (proofMax<base : maxTokenProof Π < base)
  → δ (MWFResult.proof (makeWellFormed-go base k base≤k Π origMax<base proofMax<base)) ≡ δ Π
δ-makeWellFormed-go base k base≤k Ax _ _ = refl
δ-makeWellFormed-go base k base≤k (Cut {Γ₁} {A} {s} {Δ₁} {Γ₂} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  cong (max (suc (degree A))) (cong₂ max ih₁ ih₂)
  where
    max₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxEigenposToken Π₁) _)) origMax<base
    max₂<base = ≤-trans (suc-≤-suc (≤-myMax-r _ (maxEigenposToken Π₂))) origMax<base
    proof₁<base : maxTokenProof Π₁ < base
    proof₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenPos s) (myMax (maxTokenProof Π₁) (maxTokenProof Π₂))))
                           (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenCtx ((Γ₁ ,, Γ₂) ,, (Δ₁ ,, Δ₂))) _)) proofMax<base))
    proof₂<base : maxTokenProof Π₂ < base
    proof₂<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenPos s) (myMax (maxTokenProof Π₁) (maxTokenProof Π₂))))
                           (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenCtx ((Γ₁ ,, Γ₂) ,, (Δ₁ ,, Δ₂))) _)) proofMax<base))
    mwfR₁ = makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
    base≤next₁ = ≤-trans base≤k (MWFResult.k≤next mwfR₁)
    mwfR₂ = makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
    ih₁ = δ-makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
    ih₂ = δ-makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
δ-makeWellFormed-go base k base≤k (W⊢ Π) origMax<base proofMax<base =
  δ-makeWellFormed-go base k base≤k Π origMax<base _
δ-makeWellFormed-go base k base≤k (⊢W Π) origMax<base proofMax<base =
  δ-makeWellFormed-go base k base≤k Π origMax<base _
δ-makeWellFormed-go base k base≤k (C⊢ Π) origMax<base proofMax<base =
  δ-makeWellFormed-go base k base≤k Π origMax<base _
δ-makeWellFormed-go base k base≤k (⊢C Π) origMax<base proofMax<base =
  δ-makeWellFormed-go base k base≤k Π origMax<base _
δ-makeWellFormed-go base k base≤k (Exc⊢ {Γ₁} {A} {s} {B} {t} {Γ₂} {Δ} Π) origMax<base proofMax<base =
  δ-makeWellFormed-go base k base≤k Π origMax<base _
δ-makeWellFormed-go base k base≤k (⊢Exc {Γ} {Δ₁} {A} {s} {B} {t} {Δ₂} Π) origMax<base proofMax<base =
  δ-makeWellFormed-go base k base≤k Π origMax<base _
δ-makeWellFormed-go base k base≤k (¬⊢ Π) origMax<base proofMax<base =
  δ-makeWellFormed-go base k base≤k Π origMax<base _
δ-makeWellFormed-go base k base≤k (⊢¬ Π) origMax<base proofMax<base =
  δ-makeWellFormed-go base k base≤k Π origMax<base _
δ-makeWellFormed-go base k base≤k (∧₁⊢ Π) origMax<base proofMax<base =
  δ-makeWellFormed-go base k base≤k Π origMax<base _
δ-makeWellFormed-go base k base≤k (∧₂⊢ Π) origMax<base proofMax<base =
  δ-makeWellFormed-go base k base≤k Π origMax<base _
δ-makeWellFormed-go base k base≤k (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  cong₂ max (δ-makeWellFormed-go base k base≤k Π₁ _ _)
            (δ-makeWellFormed-go base _ _ Π₂ _ _)
δ-makeWellFormed-go base k base≤k (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  cong₂ max (δ-makeWellFormed-go base k base≤k Π₁ _ _)
            (δ-makeWellFormed-go base _ _ Π₂ _ _)
δ-makeWellFormed-go base k base≤k (⊢∨₁ Π) origMax<base proofMax<base =
  δ-makeWellFormed-go base k base≤k Π origMax<base _
δ-makeWellFormed-go base k base≤k (⊢∨₂ Π) origMax<base proofMax<base =
  δ-makeWellFormed-go base k base≤k Π origMax<base _
δ-makeWellFormed-go base k base≤k (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  cong₂ max (δ-makeWellFormed-go base k base≤k Π₁ _ _)
            (δ-makeWellFormed-go base _ _ Π₂ _ _)
δ-makeWellFormed-go base k base≤k (⊢⇒ Π) origMax<base proofMax<base =
  δ-makeWellFormed-go base k base≤k Π origMax<base _
δ-makeWellFormed-go base k base≤k (□⊢ Π) origMax<base proofMax<base =
  δ-makeWellFormed-go base k base≤k Π origMax<base _
δ-makeWellFormed-go base k base≤k (⊢□ {x} {r} {Γ} {Δ} {A} x∉r xFrΓ xFrΔ Π) origMax<base proofMax<base =
  -- The result-proof = ⊢□ ... Π', where Π' is derived from Π-wf via substitution and transport
  -- δ (⊢□ ... Π') = δ Π' and δ (⊢□ ... Π) = δ Π
  -- We need: δ Π' ≡ δ Π
  -- Chain: δ Π' ≡ δ Π-subst ≡ δ Π-wf ≡ δ Π
  δ-subst2 Γ-unchanged ctx-eq Π-subst ∙ δ-substTokenToPosProof x (singleton-pos x') Π-wf ec nc
    ∙ δ-makeWellFormed-go base k base≤k Π subMax<base subProof<base
  where
    x<base = ≤-trans (suc-≤-suc (≤-myMax-l x _)) origMax<base
    subMax<base = ≤-trans (suc-≤-suc (≤-myMax-r x _)) origMax<base
    ctxMax<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenCtx (Γ ,, [ □ A ^ r ] ,, Δ)) (maxTokenProof Π))) proofMax<base
    ctxMax-eq = maxTokenCtx-++ Γ ([ □ A ^ r ] ,, Δ)
    ctxMax<base' = subst (_< base) ctxMax-eq ctxMax<base
    r<base = ≤-trans (suc-≤-suc (≤-trans (≤-myMax-l (maxTokenPos r) (maxTokenCtx Δ))
                                         (≤-myMax-r (maxTokenCtx Γ) (maxTokenCtx ([ □ A ^ r ] ,, Δ)))))
                     ctxMax<base'
    Γ<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenCtx Γ) (maxTokenCtx ([ □ A ^ r ] ,, Δ)))) ctxMax<base'
    Δ<base = ≤-trans (suc-≤-suc (≤-trans (≤-myMax-r (maxTokenPos r) (maxTokenCtx Δ))
                                         (≤-myMax-r (maxTokenCtx Γ) (maxTokenCtx ([ □ A ^ r ] ,, Δ)))))
                     ctxMax<base'
    subProof<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base
    mwfR = makeWellFormed-go base k base≤k Π subMax<base subProof<base
    Π-wf = MWFResult.proof mwfR
    next = MWFResult.next mwfR
    x' = next
    k≤x' = MWFResult.k≤next mwfR
    ec = EigenposCond-from-lt-base x base Π-wf x<base (MWFResult.allEigen≥base mwfR)
    nc = NoEigenposInt-singleton-fresh x' Π-wf (MWFResult.maxEigen<next mwfR)
    Π-subst = substTokenToPosProof x (singleton-pos x') Π-wf ec nc
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ xFrΓ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ xFrΔ
    pos-eq = substPos-insertToken-eq x x' r x∉r
    ctx-eq = substCtx-++ x (singleton-pos x') [ A ^ insertToken x r ] Δ
             ∙ cong₂ _,,_ (cong [_] (cong (A ^_) pos-eq)) Δ-unchanged
δ-makeWellFormed-go base k base≤k (♢⊢ {x} {r} {Γ} {Δ} {A} x∉r xFrΓ xFrΔ Π) origMax<base proofMax<base =
  δ-subst2 ctx-eq Δ-unchanged Π-subst ∙ δ-substTokenToPosProof x (singleton-pos x') Π-wf ec nc
    ∙ δ-makeWellFormed-go base k base≤k Π subMax<base subProof<base
  where
    x<base = ≤-trans (suc-≤-suc (≤-myMax-l x _)) origMax<base
    subMax<base = ≤-trans (suc-≤-suc (≤-myMax-r x _)) origMax<base
    ctxMax<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenCtx ((Γ ,, [ ♢ A ^ r ]) ,, Δ)) (maxTokenProof Π))) proofMax<base
    ctxMax-eq = maxTokenCtx-++ (Γ ,, [ ♢ A ^ r ]) Δ
    ctxMax<base' = subst (_< base) ctxMax-eq ctxMax<base
    innerCtx-eq = maxTokenCtx-++ Γ [ ♢ A ^ r ] ∙ cong (myMax (maxTokenCtx Γ)) (maxTokenCtx-singleton (♢ A) r)
    Γ≤innerCtx = subst (maxTokenCtx Γ ≤_) (sym innerCtx-eq) (≤-myMax-l (maxTokenCtx Γ) (maxTokenPos r))
    r≤innerCtx = subst (maxTokenPos r ≤_) (sym innerCtx-eq) (≤-myMax-r (maxTokenCtx Γ) (maxTokenPos r))
    Γ<base = ≤-trans (suc-≤-suc (≤-trans Γ≤innerCtx (≤-myMax-l (maxTokenCtx (Γ ,, [ ♢ A ^ r ])) (maxTokenCtx Δ)))) ctxMax<base'
    r<base = ≤-trans (suc-≤-suc (≤-trans r≤innerCtx (≤-myMax-l (maxTokenCtx (Γ ,, [ ♢ A ^ r ])) (maxTokenCtx Δ)))) ctxMax<base'
    Δ<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenCtx (Γ ,, [ ♢ A ^ r ])) (maxTokenCtx Δ))) ctxMax<base'
    subProof<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base
    mwfR = makeWellFormed-go base k base≤k Π subMax<base subProof<base
    Π-wf = MWFResult.proof mwfR
    next = MWFResult.next mwfR
    x' = next
    k≤x' = MWFResult.k≤next mwfR
    ec = EigenposCond-from-lt-base x base Π-wf x<base (MWFResult.allEigen≥base mwfR)
    nc = NoEigenposInt-singleton-fresh x' Π-wf (MWFResult.maxEigen<next mwfR)
    Π-subst = substTokenToPosProof x (singleton-pos x') Π-wf ec nc
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ xFrΓ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ xFrΔ
    pos-eq = substPos-insertToken-eq x x' r x∉r
    ctx-eq = substCtx-++ x (singleton-pos x') Γ [ A ^ insertToken x r ]
             ∙ cong₂ _,,_ Γ-unchanged (cong [_] (cong (A ^_) pos-eq))
δ-makeWellFormed-go base k base≤k (⊢♢ Π) origMax<base proofMax<base =
  δ-makeWellFormed-go base k base≤k Π origMax<base _

-- Main theorem: makeWellFormed preserves degree
δ-makeWellFormed : ∀ {Γ Δ} (Π : Γ ⊢ Δ) → δ (makeWellFormed Π) ≡ δ Π
δ-makeWellFormed {Γ} {Δ} Π = δ-makeWellFormed-go base base ≤-refl Π origMax<base proofMax<base
  where
    base = makeWellFormed-base Π
    origMax<base = suc-≤-suc (≤-myMax-l _ _)
    proofMax<base = suc-≤-suc (≤-myMax-r _ _)

-- =============================================================================
-- Well-Formedness Predicate (Proposition 7.1)
-- =============================================================================

-- A proof is well-formed if every ⊢□/♢⊢ rule has its eigentoken larger than
-- all eigenposition tokens in its subproof
WellFormedProof : ∀ {Γ Δ} → Γ ⊢ Δ → Type
WellFormedProof Ax = Unit
WellFormedProof (Cut Π₁ Π₂) = WellFormedProof Π₁ × WellFormedProof Π₂
WellFormedProof (W⊢ Π) = WellFormedProof Π
WellFormedProof (⊢W Π) = WellFormedProof Π
WellFormedProof (C⊢ Π) = WellFormedProof Π
WellFormedProof (⊢C Π) = WellFormedProof Π
WellFormedProof (Exc⊢ Π) = WellFormedProof Π
WellFormedProof (⊢Exc Π) = WellFormedProof Π
WellFormedProof (¬⊢ Π) = WellFormedProof Π
WellFormedProof (⊢¬ Π) = WellFormedProof Π
WellFormedProof (∧₁⊢ Π) = WellFormedProof Π
WellFormedProof (∧₂⊢ Π) = WellFormedProof Π
WellFormedProof (⊢∧ Π₁ Π₂) = WellFormedProof Π₁ × WellFormedProof Π₂
WellFormedProof (∨⊢ Π₁ Π₂) = WellFormedProof Π₁ × WellFormedProof Π₂
WellFormedProof (⊢∨₁ Π) = WellFormedProof Π
WellFormedProof (⊢∨₂ Π) = WellFormedProof Π
WellFormedProof (⇒⊢ Π₁ Π₂) = WellFormedProof Π₁ × WellFormedProof Π₂
WellFormedProof (⊢⇒ Π) = WellFormedProof Π
WellFormedProof (□⊢ Π) = WellFormedProof Π
WellFormedProof (⊢□ {x = x} _ _ _ Π) = (maxEigenposToken Π < x) × WellFormedProof Π
WellFormedProof (♢⊢ {x = x} _ _ _ Π) = (maxEigenposToken Π < x) × WellFormedProof Π
WellFormedProof (⊢♢ Π) = WellFormedProof Π

-- Well-formedness is preserved by subst2 (transport)
WellFormed-subst2 : ∀ {Γ Γ' Δ Δ'} (p : Γ ≡ Γ') (q : Δ ≡ Δ') (Π : Γ ⊢ Δ)
  → WellFormedProof Π → WellFormedProof (subst2 _⊢_ p q Π)
WellFormed-subst2 {Γ} {Γ'} {Δ} {Δ'} p q Π wf =
  J (λ Γ' p → ∀ Δ' (q : Δ ≡ Δ') → WellFormedProof (subst2 _⊢_ p q Π))
    (λ Δ' q → J (λ Δ' q → WellFormedProof (subst2 _⊢_ refl q Π))
                (subst WellFormedProof (sym (substRefl {B = Γ ⊢_} Π)) wf) q)
    p Δ' q

-- Well-formedness is preserved by token substitution
-- This is because token substitution doesn't change the proof structure or eigentokens

-- Helpers for single-argument subst
WellFormed-substR : ∀ {Γ Δ Δ'} (p : Δ ≡ Δ') (Π : Γ ⊢ Δ)
  → WellFormedProof Π → WellFormedProof (subst (Γ ⊢_) p Π)
WellFormed-substR p Π = WellFormed-subst2 refl p Π

WellFormed-substL : ∀ {Γ Γ' Δ} (p : Γ ≡ Γ') (Π : Γ ⊢ Δ)
  → WellFormedProof Π → WellFormedProof (subst (_⊢ Δ) p Π)
WellFormed-substL p Π = WellFormed-subst2 p refl Π

-- Main lemma by induction on Π
WellFormed-substTokenToPosProof : (z : Token) (t : Position) {Γ Δ : Ctx}
  → (Π : Γ ⊢ Δ) → (ec : EigenposCond z Π) → (nc : NoEigenposInt t Π)
  → WellFormedProof Π → WellFormedProof (substTokenToPosProof z t Π ec nc)
WellFormed-substTokenToPosProof z t Ax _ _ wf = tt
WellFormed-substTokenToPosProof z t (Cut {Γ₁} {A} {s} {Δ₁} {Γ₂} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) (wf₁ , wf₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      ih₁ = WellFormed-substTokenToPosProof z t Π₁ ec₁ nc₁ wf₁
      ih₂ = WellFormed-substTokenToPosProof z t Π₂ ec₂ nc₂ wf₂
      wf₁' = WellFormed-substR (substCtx-++ z t [ A ^ s ] Δ₁) Π₁' ih₁
      wf₂' = WellFormed-substL (substCtx-++ z t Γ₂ [ A ^ s ]) Π₂' ih₂
  in WellFormed-subst2 (sym (substCtx-++ z t Γ₁ Γ₂)) (sym (substCtx-++ z t Δ₁ Δ₂))
       (Cut (subst (substCtx z t Γ₁ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₁) Π₁')
            (subst (_⊢ substCtx z t Δ₂) (substCtx-++ z t Γ₂ [ A ^ s ]) Π₂'))
       (wf₁' , wf₂')
WellFormed-substTokenToPosProof z t (W⊢ {Γ} {Δ} {A} {s} Π) ec nc wf =
  let ih = WellFormed-substTokenToPosProof z t Π ec nc wf
  in WellFormed-substL (sym (substCtx-++ z t Γ [ A ^ s ])) (W⊢ (substTokenToPosProof z t Π ec nc)) ih
WellFormed-substTokenToPosProof z t (⊢W {Γ} {Δ} {A} {s} Π) ec nc wf =
  let ih = WellFormed-substTokenToPosProof z t Π ec nc wf
  in WellFormed-substR (sym (substCtx-++ z t [ A ^ s ] Δ)) (⊢W (substTokenToPosProof z t Π ec nc)) ih
WellFormed-substTokenToPosProof z t (C⊢ {Γ} {A} {s} {Δ} Π) ec nc wf =
  let Π' = substTokenToPosProof z t Π ec nc
      ih = WellFormed-substTokenToPosProof z t Π ec nc wf
      inner = subst (_⊢ substCtx z t Δ)
                (substCtx-++ z t (Γ ++L [ A ^ s ]) [ A ^ s ] ∙
                 cong (_++L substCtx z t [ A ^ s ]) (substCtx-++ z t Γ [ A ^ s ])) Π'
      wf-inner = WellFormed-substL (substCtx-++ z t (Γ ++L [ A ^ s ]) [ A ^ s ] ∙
                                    cong (_++L substCtx z t [ A ^ s ]) (substCtx-++ z t Γ [ A ^ s ])) Π' ih
  in WellFormed-substL (sym (substCtx-++ z t Γ [ A ^ s ])) (C⊢ inner) wf-inner
WellFormed-substTokenToPosProof z t (⊢C {Γ} {A} {s} {Δ} Π) ec nc wf =
  let Π' = substTokenToPosProof z t Π ec nc
      ih = WellFormed-substTokenToPosProof z t Π ec nc wf
      inner = subst (substCtx z t Γ ⊢_)
                (substCtx-++ z t ([ A ^ s ] ++L [ A ^ s ]) Δ ∙
                 cong (_++L substCtx z t Δ) (substCtx-++ z t [ A ^ s ] [ A ^ s ])) Π'
      wf-inner = WellFormed-substR (substCtx-++ z t ([ A ^ s ] ++L [ A ^ s ]) Δ ∙
                                    cong (_++L substCtx z t Δ) (substCtx-++ z t [ A ^ s ] [ A ^ s ])) Π' ih
  in WellFormed-substR (sym (substCtx-++ z t [ A ^ s ] Δ)) (⊢C inner) wf-inner
WellFormed-substTokenToPosProof z t (Exc⊢ {Γ₁} {A} {s} {B} {t'} {Γ₂} {Δ} Π) ec nc wf =
  let Π' = substTokenToPosProof z t Π ec nc
      ih = WellFormed-substTokenToPosProof z t Π ec nc wf
      step0' = cong (substCtx z t) (++L-assoc (Γ₁ ++L [ B ^ t' ]) [ A ^ s ] Γ₂)
      step1' = substCtx-++ z t (Γ₁ ++L [ B ^ t' ]) (A ^ s ∷ Γ₂)
      step2' = cong (_++L substCtx z t (A ^ s ∷ Γ₂)) (substCtx-++ z t Γ₁ [ B ^ t' ])
      step3' = cong ((substCtx z t Γ₁ ++L substCtx z t [ B ^ t' ]) ++L_) (substCtx-++ z t [ A ^ s ] Γ₂)
      step4' = sym (++L-assoc (substCtx z t Γ₁ ++L substCtx z t [ B ^ t' ]) (substCtx z t [ A ^ s ]) (substCtx z t Γ₂))
      path2 = step0' ∙ step1' ∙ step2' ∙ step3' ∙ step4'
      step0 = cong (substCtx z t) (++L-assoc (Γ₁ ++L [ A ^ s ]) [ B ^ t' ] Γ₂)
      step1 = substCtx-++ z t (Γ₁ ++L [ A ^ s ]) (B ^ t' ∷ Γ₂)
      step2 = cong (_++L substCtx z t (B ^ t' ∷ Γ₂)) (substCtx-++ z t Γ₁ [ A ^ s ])
      step3 = cong ((substCtx z t Γ₁ ++L substCtx z t [ A ^ s ]) ++L_) (substCtx-++ z t [ B ^ t' ] Γ₂)
      step4 = sym (++L-assoc (substCtx z t Γ₁ ++L substCtx z t [ A ^ s ]) (substCtx z t [ B ^ t' ]) (substCtx z t Γ₂))
      path = step0 ∙ step1 ∙ step2 ∙ step3 ∙ step4
      raw = Exc⊢ {Γ₁ = substCtx z t Γ₁} {A = A} {B = B} {Γ₂ = substCtx z t Γ₂}
                 (subst (λ G → G ⊢ substCtx z t Δ) path Π')
      wf-inner = WellFormed-substL path Π' ih
  in WellFormed-substL (sym path2) raw wf-inner
WellFormed-substTokenToPosProof z t (⊢Exc {Γ} {Δ₁} {A} {s} {B} {t'} {Δ₂} Π) ec nc wf =
  let Π' = substTokenToPosProof z t Π ec nc
      ih = WellFormed-substTokenToPosProof z t Π ec nc wf
      step0' = cong (substCtx z t) (++L-assoc (Δ₁ ++L [ B ^ t' ]) [ A ^ s ] Δ₂)
      step1' = substCtx-++ z t (Δ₁ ++L [ B ^ t' ]) (A ^ s ∷ Δ₂)
      step2' = cong (_++L substCtx z t (A ^ s ∷ Δ₂)) (substCtx-++ z t Δ₁ [ B ^ t' ])
      step3' = cong ((substCtx z t Δ₁ ++L substCtx z t [ B ^ t' ]) ++L_) (substCtx-++ z t [ A ^ s ] Δ₂)
      step4' = sym (++L-assoc (substCtx z t Δ₁ ++L substCtx z t [ B ^ t' ]) (substCtx z t [ A ^ s ]) (substCtx z t Δ₂))
      path2 = step0' ∙ step1' ∙ step2' ∙ step3' ∙ step4'
      step0 = cong (substCtx z t) (++L-assoc (Δ₁ ++L [ A ^ s ]) [ B ^ t' ] Δ₂)
      step1 = substCtx-++ z t (Δ₁ ++L [ A ^ s ]) (B ^ t' ∷ Δ₂)
      step2 = cong (_++L substCtx z t (B ^ t' ∷ Δ₂)) (substCtx-++ z t Δ₁ [ A ^ s ])
      step3 = cong ((substCtx z t Δ₁ ++L substCtx z t [ A ^ s ]) ++L_) (substCtx-++ z t [ B ^ t' ] Δ₂)
      step4 = sym (++L-assoc (substCtx z t Δ₁ ++L substCtx z t [ A ^ s ]) (substCtx z t [ B ^ t' ]) (substCtx z t Δ₂))
      path = step0 ∙ step1 ∙ step2 ∙ step3 ∙ step4
      raw = ⊢Exc {Δ₁ = substCtx z t Δ₁} {A = A} {B = B} {Δ₂ = substCtx z t Δ₂}
                 (subst (λ D → substCtx z t Γ ⊢ D) path Π')
      wf-inner = WellFormed-substR path Π' ih
  in WellFormed-substR (sym path2) raw wf-inner
WellFormed-substTokenToPosProof z t (¬⊢ {Γ} {A} {s} {Δ} Π) ec nc wf =
  let Π' = substTokenToPosProof z t Π ec nc
      ih = WellFormed-substTokenToPosProof z t Π ec nc wf
      inner = subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ A ^ s ] Δ) Π'
      wf-inner = WellFormed-substR (substCtx-++ z t [ A ^ s ] Δ) Π' ih
  in WellFormed-substL (sym (substCtx-++ z t Γ [ (¬ A) ^ s ])) (¬⊢ inner) wf-inner
WellFormed-substTokenToPosProof z t (⊢¬ {Γ} {A} {s} {Δ} Π) ec nc wf =
  let Π' = substTokenToPosProof z t Π ec nc
      ih = WellFormed-substTokenToPosProof z t Π ec nc wf
      inner = subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ A ^ s ]) Π'
      wf-inner = WellFormed-substL (substCtx-++ z t Γ [ A ^ s ]) Π' ih
  in WellFormed-substR (sym (substCtx-++ z t [ (¬ A) ^ s ] Δ)) (⊢¬ inner) wf-inner
WellFormed-substTokenToPosProof z t (∧₁⊢ {Γ} {A} {s} {Δ} {B} Π) ec nc wf =
  let Π' = substTokenToPosProof z t Π ec nc
      ih = WellFormed-substTokenToPosProof z t Π ec nc wf
      inner = subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ A ^ s ]) Π'
      wf-inner = WellFormed-substL (substCtx-++ z t Γ [ A ^ s ]) Π' ih
  in WellFormed-substL (sym (substCtx-++ z t Γ [ (A and B) ^ s ])) (∧₁⊢ inner) wf-inner
WellFormed-substTokenToPosProof z t (∧₂⊢ {Γ} {B} {s} {Δ} {A} Π) ec nc wf =
  let Π' = substTokenToPosProof z t Π ec nc
      ih = WellFormed-substTokenToPosProof z t Π ec nc wf
      inner = subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ B ^ s ]) Π'
      wf-inner = WellFormed-substL (substCtx-++ z t Γ [ B ^ s ]) Π' ih
  in WellFormed-substL (sym (substCtx-++ z t Γ [ (A and B) ^ s ])) (∧₂⊢ inner) wf-inner
WellFormed-substTokenToPosProof z t (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) (wf₁ , wf₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      ih₁ = WellFormed-substTokenToPosProof z t Π₁ ec₁ nc₁ wf₁
      ih₂ = WellFormed-substTokenToPosProof z t Π₂ ec₂ nc₂ wf₂
      wf₁' = WellFormed-substR (substCtx-++ z t [ A ^ s ] Δ₁) Π₁' ih₁
      wf₂' = WellFormed-substR (substCtx-++ z t [ B ^ s ] Δ₂) Π₂' ih₂
  in WellFormed-subst2 (sym (substCtx-++ z t Γ₁ Γ₂))
       (cong (substCtx z t [ (A and B) ^ s ] ++L_) (sym (substCtx-++ z t Δ₁ Δ₂)) ∙
        sym (substCtx-++ z t [ (A and B) ^ s ] (Δ₁ ++L Δ₂)))
       (⊢∧ (subst (substCtx z t Γ₁ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₁) Π₁')
           (subst (substCtx z t Γ₂ ⊢_) (substCtx-++ z t [ B ^ s ] Δ₂) Π₂'))
       (wf₁' , wf₂')
WellFormed-substTokenToPosProof z t (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) (wf₁ , wf₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      ih₁ = WellFormed-substTokenToPosProof z t Π₁ ec₁ nc₁ wf₁
      ih₂ = WellFormed-substTokenToPosProof z t Π₂ ec₂ nc₂ wf₂
      wf₁' = WellFormed-substL (substCtx-++ z t Γ₁ [ A ^ s ]) Π₁' ih₁
      wf₂' = WellFormed-substL (substCtx-++ z t Γ₂ [ B ^ s ]) Π₂' ih₂
  in WellFormed-subst2
       (cong (substCtx z t Γ₁ ++L_) (sym (substCtx-++ z t Γ₂ [ (A or B) ^ s ]))
        ∙ sym (substCtx-++ z t Γ₁ (Γ₂ ++L [ (A or B) ^ s ])))
       (sym (substCtx-++ z t Δ₁ Δ₂))
       (∨⊢ (subst (_⊢ substCtx z t Δ₁) (substCtx-++ z t Γ₁ [ A ^ s ]) Π₁')
           (subst (_⊢ substCtx z t Δ₂) (substCtx-++ z t Γ₂ [ B ^ s ]) Π₂'))
       (wf₁' , wf₂')
WellFormed-substTokenToPosProof z t (⊢∨₁ {Γ} {A} {s} {Δ} {B} Π) ec nc wf =
  let Π' = substTokenToPosProof z t Π ec nc
      ih = WellFormed-substTokenToPosProof z t Π ec nc wf
      inner = subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ A ^ s ] Δ) Π'
      wf-inner = WellFormed-substR (substCtx-++ z t [ A ^ s ] Δ) Π' ih
  in WellFormed-substR (sym (substCtx-++ z t [ (A or B) ^ s ] Δ)) (⊢∨₁ inner) wf-inner
WellFormed-substTokenToPosProof z t (⊢∨₂ {Γ} {B} {s} {Δ} {A} Π) ec nc wf =
  let Π' = substTokenToPosProof z t Π ec nc
      ih = WellFormed-substTokenToPosProof z t Π ec nc wf
      inner = subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ B ^ s ] Δ) Π'
      wf-inner = WellFormed-substR (substCtx-++ z t [ B ^ s ] Δ) Π' ih
  in WellFormed-substR (sym (substCtx-++ z t [ (A or B) ^ s ] Δ)) (⊢∨₂ inner) wf-inner
WellFormed-substTokenToPosProof z t (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) (wf₁ , wf₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      ih₁ = WellFormed-substTokenToPosProof z t Π₁ ec₁ nc₁ wf₁
      ih₂ = WellFormed-substTokenToPosProof z t Π₂ ec₂ nc₂ wf₂
      wf₁' = WellFormed-substL (substCtx-++ z t Γ₁ [ B ^ s ]) Π₁' ih₁
      wf₂' = WellFormed-substR (substCtx-++ z t [ A ^ s ] Δ₂) Π₂' ih₂
  in WellFormed-subst2
       (cong (substCtx z t Γ₁ ++L_) (sym (substCtx-++ z t Γ₂ [ (A ⇒ B) ^ s ]))
        ∙ sym (substCtx-++ z t Γ₁ (Γ₂ ++L [ (A ⇒ B) ^ s ])))
       (sym (substCtx-++ z t Δ₁ Δ₂))
       (⇒⊢ (subst (_⊢ substCtx z t Δ₁) (substCtx-++ z t Γ₁ [ B ^ s ]) Π₁')
           (subst (substCtx z t Γ₂ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₂) Π₂'))
       (wf₁' , wf₂')
WellFormed-substTokenToPosProof z t (⊢⇒ {Γ} {A} {s} {B} {Δ} Π) ec nc wf =
  let Π' = substTokenToPosProof z t Π ec nc
      ih = WellFormed-substTokenToPosProof z t Π ec nc wf
      inner = subst2 _⊢_ (substCtx-++ z t Γ [ A ^ s ]) (substCtx-++ z t [ B ^ s ] Δ) Π'
      wf-inner = WellFormed-subst2 (substCtx-++ z t Γ [ A ^ s ]) (substCtx-++ z t [ B ^ s ] Δ) Π' ih
  in WellFormed-substR (sym (substCtx-++ z t [ (A ⇒ B) ^ s ] Δ)) (⊢⇒ inner) wf-inner
WellFormed-substTokenToPosProof z t (□⊢ {Γ} {A} {s} {t'} {Δ} Π) ec nc wf =
  let Π' = substTokenToPosProof z t Π ec nc
      ih = WellFormed-substTokenToPosProof z t Π ec nc wf
      ctx-eq = substCtx-++ z t Γ [ A ^ (s ++Pos t') ]
      pos-eq = substPos-++Pos-distr z t s t'
      Π'' = subst (_⊢ substCtx z t Δ) (ctx-eq ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π'
      out-path = sym (substCtx-++ z t Γ [ (□ A) ^ s ])
      wf-inner = WellFormed-substL (ctx-eq ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π' ih
  in WellFormed-substL out-path (□⊢ Π'') wf-inner
-- ⊢□ case: WellFormedProof (⊢□ ...) = (maxEigenposToken Π < x) × WellFormedProof Π
WellFormed-substTokenToPosProof z t (⊢□ {x} {s} {Γ} {Δ} {A} x∉s xFrΓ xFrΔ Π) (z≢x , ec) (x∉t , nc) (maxΠ<x , wf) =
  let Π' = substTokenToPosProof z t Π ec nc
      ih = WellFormed-substTokenToPosProof z t Π ec nc wf
      pos-eq = substPos-insertToken-neq z x s t z≢x
      x∉substs = ∉Pos-substPos z t s x∉s x∉t
      xFrΓ' = TokenFresh-substCtx z x t Γ z≢x x∉t xFrΓ
      xFrΔ' = TokenFresh-substCtx z x t Δ z≢x x∉t xFrΔ
      rhs-path = substCtx-++ z t [ A ^ insertToken x s ] Δ
      Π'' = subst (substCtx z t Γ ⊢_) (rhs-path ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π'
      raw = ⊢□ x∉substs xFrΓ' xFrΔ' Π''
      out-path = sym (substCtx-++ z t [ (□ A) ^ s ] Δ)
      -- Key: maxEigenposToken Π' ≡ maxEigenposToken Π, so maxEigenposToken Π' < x
      maxΠ'-eq : maxEigenposToken Π' ≡ maxEigenposToken Π
      maxΠ'-eq = maxEigenposToken-substTokenToPosProof z t Π ec nc
      maxΠ'<x : maxEigenposToken Π' < x
      maxΠ'<x = subst (_< x) (sym maxΠ'-eq) maxΠ<x
      -- After the subst, the maxEigenposToken is preserved
      maxΠ''-eq : maxEigenposToken Π'' ≡ maxEigenposToken Π'
      maxΠ''-eq = maxEigenposToken-substR (rhs-path ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π'
      maxΠ''<x : maxEigenposToken Π'' < x
      maxΠ''<x = subst (_< x) (sym maxΠ''-eq) maxΠ'<x
      wf'' = WellFormed-substR (rhs-path ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π' ih
  in WellFormed-substR out-path raw (maxΠ''<x , wf'')
-- ♢⊢ case: symmetric to ⊢□
WellFormed-substTokenToPosProof z t (♢⊢ {x} {s} {Γ} {Δ} {A} x∉s xFrΓ xFrΔ Π) (z≢x , ec) (x∉t , nc) (maxΠ<x , wf) =
  let Π' = substTokenToPosProof z t Π ec nc
      ih = WellFormed-substTokenToPosProof z t Π ec nc wf
      pos-eq = substPos-insertToken-neq z x s t z≢x
      x∉substs = ∉Pos-substPos z t s x∉s x∉t
      xFrΓ' = TokenFresh-substCtx z x t Γ z≢x x∉t xFrΓ
      xFrΔ' = TokenFresh-substCtx z x t Δ z≢x x∉t xFrΔ
      lhs-path = substCtx-++ z t Γ [ A ^ insertToken x s ]
      Π'' = subst (_⊢ substCtx z t Δ) (lhs-path ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π'
      raw = ♢⊢ x∉substs xFrΓ' xFrΔ' Π''
      out-path = sym (substCtx-++ z t Γ [ (♢ A) ^ s ])
      maxΠ'-eq = maxEigenposToken-substTokenToPosProof z t Π ec nc
      maxΠ'<x = subst (_< x) (sym maxΠ'-eq) maxΠ<x
      maxΠ''-eq = maxEigenposToken-substL (lhs-path ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π'
      maxΠ''<x = subst (_< x) (sym maxΠ''-eq) maxΠ'<x
      wf'' = WellFormed-substL (lhs-path ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π' ih
  in WellFormed-substL out-path raw (maxΠ''<x , wf'')
WellFormed-substTokenToPosProof z t (⊢♢ {Γ} {A} {s} {t'} {Δ} Π) ec nc wf =
  let Π' = substTokenToPosProof z t Π ec nc
      ih = WellFormed-substTokenToPosProof z t Π ec nc wf
      ctx-eq = substCtx-++ z t [ A ^ (s ++Pos t') ] Δ
      pos-eq = substPos-++Pos-distr z t s t'
      Π'' = subst (substCtx z t Γ ⊢_) (ctx-eq ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π'
      out-path = sym (substCtx-++ z t [ (♢ A) ^ s ] Δ)
      wf-inner = WellFormed-substR (ctx-eq ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π' ih
  in WellFormed-substR out-path (⊢♢ Π'') wf-inner

-- makeWellFormed-go produces well-formed proofs
-- This is the key lemma: each ⊢□/♢⊢ in the result has eigentoken ≥ base > all original eigenpos
-- and all new eigentokens are chosen to be fresh (= counter value)
makeWellFormed-go-WellFormed : (base k : Token) (base≤k : base ≤ k) {Γ Δ : Ctx} (Π : Γ ⊢ Δ)
  → (origMax<base : maxEigenposToken Π < base)
  → (proofMax<base : maxTokenProof Π < base)
  → WellFormedProof (MWFResult.proof (makeWellFormed-go base k base≤k Π origMax<base proofMax<base))
makeWellFormed-go-WellFormed base k base≤k Ax _ _ = tt
makeWellFormed-go-WellFormed base k base≤k (Cut {Γ₁} {A} {s} {Δ₁} {Γ₂} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  ih₁ , ih₂
  where
    max₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxEigenposToken Π₁) _)) origMax<base
    max₂<base = ≤-trans (suc-≤-suc (≤-myMax-r _ (maxEigenposToken Π₂))) origMax<base
    proof₁<base : maxTokenProof Π₁ < base
    proof₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenPos s) (myMax (maxTokenProof Π₁) (maxTokenProof Π₂))))
                           (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenCtx ((Γ₁ ,, Γ₂) ,, (Δ₁ ,, Δ₂))) _)) proofMax<base))
    proof₂<base : maxTokenProof Π₂ < base
    proof₂<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenPos s) (myMax (maxTokenProof Π₁) (maxTokenProof Π₂))))
                           (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenCtx ((Γ₁ ,, Γ₂) ,, (Δ₁ ,, Δ₂))) _)) proofMax<base))
    mwfR₁ = makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
    base≤next₁ = ≤-trans base≤k (MWFResult.k≤next mwfR₁)
    mwfR₂ = makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
    ih₁ = makeWellFormed-go-WellFormed base k base≤k Π₁ max₁<base proof₁<base
    ih₂ = makeWellFormed-go-WellFormed base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
makeWellFormed-go-WellFormed base k base≤k (W⊢ Π) origMax<base proofMax<base =
  makeWellFormed-go-WellFormed base k base≤k Π origMax<base _
makeWellFormed-go-WellFormed base k base≤k (⊢W Π) origMax<base proofMax<base =
  makeWellFormed-go-WellFormed base k base≤k Π origMax<base _
makeWellFormed-go-WellFormed base k base≤k (C⊢ Π) origMax<base proofMax<base =
  makeWellFormed-go-WellFormed base k base≤k Π origMax<base _
makeWellFormed-go-WellFormed base k base≤k (⊢C Π) origMax<base proofMax<base =
  makeWellFormed-go-WellFormed base k base≤k Π origMax<base _
makeWellFormed-go-WellFormed base k base≤k (Exc⊢ Π) origMax<base proofMax<base =
  makeWellFormed-go-WellFormed base k base≤k Π origMax<base _
makeWellFormed-go-WellFormed base k base≤k (⊢Exc Π) origMax<base proofMax<base =
  makeWellFormed-go-WellFormed base k base≤k Π origMax<base _
makeWellFormed-go-WellFormed base k base≤k (¬⊢ Π) origMax<base proofMax<base =
  makeWellFormed-go-WellFormed base k base≤k Π origMax<base _
makeWellFormed-go-WellFormed base k base≤k (⊢¬ Π) origMax<base proofMax<base =
  makeWellFormed-go-WellFormed base k base≤k Π origMax<base _
makeWellFormed-go-WellFormed base k base≤k (∧₁⊢ Π) origMax<base proofMax<base =
  makeWellFormed-go-WellFormed base k base≤k Π origMax<base _
makeWellFormed-go-WellFormed base k base≤k (∧₂⊢ Π) origMax<base proofMax<base =
  makeWellFormed-go-WellFormed base k base≤k Π origMax<base _
makeWellFormed-go-WellFormed base k base≤k (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  ih₁ , ih₂
  where
    ctxMax = maxTokenCtx ((Γ₁ ,, Γ₂) ,, ([ (A and B) ^ s ] ,, Δ₁ ,, Δ₂))
    proofMax = myMax (maxTokenProof Π₁) (maxTokenProof Π₂)
    max₁<base = ≤-trans (suc-≤-suc (≤-myMax-l _ _)) origMax<base
    max₂<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) origMax<base
    proof₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
    proof₂<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
    mwfR₁ = makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
    base≤next₁ = ≤-trans base≤k (MWFResult.k≤next mwfR₁)
    mwfR₂ = makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
    ih₁ = makeWellFormed-go-WellFormed base k base≤k Π₁ max₁<base proof₁<base
    ih₂ = makeWellFormed-go-WellFormed base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
makeWellFormed-go-WellFormed base k base≤k (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  ih₁ , ih₂
  where
    ctxMax = maxTokenCtx ((Γ₁ ,, Γ₂ ,, [ (A or B) ^ s ]) ,, (Δ₁ ,, Δ₂))
    proofMax = myMax (maxTokenProof Π₁) (maxTokenProof Π₂)
    max₁<base = ≤-trans (suc-≤-suc (≤-myMax-l _ _)) origMax<base
    max₂<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) origMax<base
    proof₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
    proof₂<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
    mwfR₁ = makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
    base≤next₁ = ≤-trans base≤k (MWFResult.k≤next mwfR₁)
    mwfR₂ = makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
    ih₁ = makeWellFormed-go-WellFormed base k base≤k Π₁ max₁<base proof₁<base
    ih₂ = makeWellFormed-go-WellFormed base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
makeWellFormed-go-WellFormed base k base≤k (⊢∨₁ Π) origMax<base proofMax<base =
  makeWellFormed-go-WellFormed base k base≤k Π origMax<base _
makeWellFormed-go-WellFormed base k base≤k (⊢∨₂ Π) origMax<base proofMax<base =
  makeWellFormed-go-WellFormed base k base≤k Π origMax<base _
makeWellFormed-go-WellFormed base k base≤k (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  ih₁ , ih₂
  where
    ctxMax = maxTokenCtx ((Γ₁ ,, Γ₂ ,, [ (A ⇒ B) ^ s ]) ,, (Δ₁ ,, Δ₂))
    proofMax = myMax (maxTokenProof Π₁) (maxTokenProof Π₂)
    max₁<base = ≤-trans (suc-≤-suc (≤-myMax-l _ _)) origMax<base
    max₂<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) origMax<base
    proof₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
    proof₂<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenProof Π₁) (maxTokenProof Π₂)))
                  (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
    mwfR₁ = makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
    base≤next₁ = ≤-trans base≤k (MWFResult.k≤next mwfR₁)
    mwfR₂ = makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
    ih₁ = makeWellFormed-go-WellFormed base k base≤k Π₁ max₁<base proof₁<base
    ih₂ = makeWellFormed-go-WellFormed base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
makeWellFormed-go-WellFormed base k base≤k (⊢⇒ Π) origMax<base proofMax<base =
  makeWellFormed-go-WellFormed base k base≤k Π origMax<base _
makeWellFormed-go-WellFormed base k base≤k (□⊢ Π) origMax<base proofMax<base =
  makeWellFormed-go-WellFormed base k base≤k Π origMax<base _
makeWellFormed-go-WellFormed base k base≤k (⊢□ {x} {r} {Γ} {Δ} {A} x∉r xFrΓ xFrΔ Π) origMax<base proofMax<base =
  -- The result proof is: ⊢□ x'∉r x'FrΓ x'FrΔ Π'
  -- where x' = next (counter after processing subproof)
  -- and Π' is derived from Π-wf (well-formed subproof) via substitution and transport
  -- We need: (maxEigenposToken Π' < x') × WellFormedProof Π'
  wf-bound , wf-sub
  where
    x<base = ≤-trans (suc-≤-suc (≤-myMax-l x _)) origMax<base
    subMax<base = ≤-trans (suc-≤-suc (≤-myMax-r x _)) origMax<base
    ctxMax<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenCtx (Γ ,, [ □ A ^ r ] ,, Δ)) (maxTokenProof Π))) proofMax<base
    ctxMax-eq = maxTokenCtx-++ Γ ([ □ A ^ r ] ,, Δ)
    ctxMax<base' = subst (_< base) ctxMax-eq ctxMax<base
    r<base = ≤-trans (suc-≤-suc (≤-trans (≤-myMax-l (maxTokenPos r) (maxTokenCtx Δ))
                                         (≤-myMax-r (maxTokenCtx Γ) (maxTokenCtx ([ □ A ^ r ] ,, Δ)))))
                     ctxMax<base'
    Γ<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenCtx Γ) (maxTokenCtx ([ □ A ^ r ] ,, Δ)))) ctxMax<base'
    Δ<base = ≤-trans (suc-≤-suc (≤-trans (≤-myMax-r (maxTokenPos r) (maxTokenCtx Δ))
                                         (≤-myMax-r (maxTokenCtx Γ) (maxTokenCtx ([ □ A ^ r ] ,, Δ)))))
                     ctxMax<base'
    subProof<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base
    mwfR = makeWellFormed-go base k base≤k Π subMax<base subProof<base
    Π-wf = MWFResult.proof mwfR
    next = MWFResult.next mwfR
    x' = next
    k≤x' = MWFResult.k≤next mwfR
    ec = EigenposCond-from-lt-base x base Π-wf x<base (MWFResult.allEigen≥base mwfR)
    nc = NoEigenposInt-singleton-fresh x' Π-wf (MWFResult.maxEigen<next mwfR)
    Π-subst = substTokenToPosProof x (singleton-pos x') Π-wf ec nc
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ xFrΓ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ xFrΔ
    pos-eq = substPos-insertToken-eq x x' r x∉r
    ctx-eq = substCtx-++ x (singleton-pos x') [ A ^ insertToken x r ] Δ
             ∙ cong₂ _,,_ (cong [_] (cong (A ^_) pos-eq)) Δ-unchanged

    Π' = subst2 _⊢_ Γ-unchanged ctx-eq Π-subst

    -- The key bound: maxEigenposToken Π' < x'
    -- Chain: maxEigenposToken Π' = maxEigenposToken Π-subst = maxEigenposToken Π-wf < next = x'
    maxΠ'-eq : maxEigenposToken Π' ≡ maxEigenposToken Π-wf
    maxΠ'-eq = maxEigenposToken-subst2 Γ-unchanged ctx-eq Π-subst
               ∙ maxEigenposToken-substTokenToPosProof x (singleton-pos x') Π-wf ec nc

    wf-bound : maxEigenposToken Π' < x'
    wf-bound = subst (_< x') (sym maxΠ'-eq) (MWFResult.maxEigen<next mwfR)

    -- Well-formedness of Π' follows from well-formedness of Π-wf
    ih = makeWellFormed-go-WellFormed base k base≤k Π subMax<base subProof<base
    wf-sub : WellFormedProof Π'
    wf-sub = WellFormed-subst2 Γ-unchanged ctx-eq Π-subst (WellFormed-substTokenToPosProof x (singleton-pos x') Π-wf ec nc ih)

makeWellFormed-go-WellFormed base k base≤k (♢⊢ {x} {r} {Γ} {Δ} {A} x∉r xFrΓ xFrΔ Π) origMax<base proofMax<base =
  -- Similar to ⊢□ case
  wf-bound , wf-sub
  where
    x<base = ≤-trans (suc-≤-suc (≤-myMax-l x _)) origMax<base
    subMax<base = ≤-trans (suc-≤-suc (≤-myMax-r x _)) origMax<base
    ctxMax<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenCtx ((Γ ,, [ ♢ A ^ r ]) ,, Δ)) (maxTokenProof Π))) proofMax<base
    ctxMax-eq = maxTokenCtx-++ (Γ ,, [ ♢ A ^ r ]) Δ
    ctxMax<base' = subst (_< base) ctxMax-eq ctxMax<base
    innerCtx-eq = maxTokenCtx-++ Γ [ ♢ A ^ r ] ∙ cong (myMax (maxTokenCtx Γ)) (maxTokenCtx-singleton (♢ A) r)
    Γ≤innerCtx = subst (maxTokenCtx Γ ≤_) (sym innerCtx-eq) (≤-myMax-l (maxTokenCtx Γ) (maxTokenPos r))
    r≤innerCtx = subst (maxTokenPos r ≤_) (sym innerCtx-eq) (≤-myMax-r (maxTokenCtx Γ) (maxTokenPos r))
    Γ<base = ≤-trans (suc-≤-suc (≤-trans Γ≤innerCtx (≤-myMax-l (maxTokenCtx (Γ ,, [ ♢ A ^ r ])) (maxTokenCtx Δ)))) ctxMax<base'
    r<base = ≤-trans (suc-≤-suc (≤-trans r≤innerCtx (≤-myMax-l (maxTokenCtx (Γ ,, [ ♢ A ^ r ])) (maxTokenCtx Δ)))) ctxMax<base'
    Δ<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenCtx (Γ ,, [ ♢ A ^ r ])) (maxTokenCtx Δ))) ctxMax<base'
    subProof<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base
    mwfR = makeWellFormed-go base k base≤k Π subMax<base subProof<base
    Π-wf = MWFResult.proof mwfR
    next = MWFResult.next mwfR
    x' = next
    k≤x' = MWFResult.k≤next mwfR
    ec = EigenposCond-from-lt-base x base Π-wf x<base (MWFResult.allEigen≥base mwfR)
    nc = NoEigenposInt-singleton-fresh x' Π-wf (MWFResult.maxEigen<next mwfR)
    Π-subst = substTokenToPosProof x (singleton-pos x') Π-wf ec nc
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ xFrΓ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ xFrΔ
    pos-eq = substPos-insertToken-eq x x' r x∉r
    ctx-eq = substCtx-++ x (singleton-pos x') Γ [ A ^ insertToken x r ]
             ∙ cong₂ _,,_ Γ-unchanged (cong [_] (cong (A ^_) pos-eq))

    Π' = subst2 _⊢_ ctx-eq Δ-unchanged Π-subst

    maxΠ'-eq : maxEigenposToken Π' ≡ maxEigenposToken Π-wf
    maxΠ'-eq = maxEigenposToken-subst2 ctx-eq Δ-unchanged Π-subst
               ∙ maxEigenposToken-substTokenToPosProof x (singleton-pos x') Π-wf ec nc

    wf-bound : maxEigenposToken Π' < x'
    wf-bound = subst (_< x') (sym maxΠ'-eq) (MWFResult.maxEigen<next mwfR)

    ih = makeWellFormed-go-WellFormed base k base≤k Π subMax<base subProof<base
    wf-sub : WellFormedProof Π'
    wf-sub = WellFormed-subst2 ctx-eq Δ-unchanged Π-subst (WellFormed-substTokenToPosProof x (singleton-pos x') Π-wf ec nc ih)

makeWellFormed-go-WellFormed base k base≤k (⊢♢ Π) origMax<base proofMax<base =
  makeWellFormed-go-WellFormed base k base≤k Π origMax<base _

-- Main theorem: makeWellFormed produces well-formed proofs
makeWellFormed-WellFormed : ∀ {Γ Δ} (Π : Γ ⊢ Δ) → WellFormedProof (makeWellFormed Π)
makeWellFormed-WellFormed {Γ} {Δ} Π = makeWellFormed-go-WellFormed base base ≤-refl Π origMax<base proofMax<base
  where
    base = makeWellFormed-base Π
    origMax<base = suc-≤-suc (≤-myMax-l _ _)
    proofMax<base = suc-≤-suc (≤-myMax-r _ _)

-- =============================================================================
-- EC-based renaming functions (take EigenposCond directly)
-- These work with well-formed proofs from makeWellFormed where x < base
-- =============================================================================

-- Eigenposition renaming for ♢⊢ premise (takes EigenposCond directly)
renameEigenpos-♢⊢-premise-gen-ec : ∀ {r t : Position} {x : Token} {Γ Δ : Ctx} {A : Formula}
  → (Π : (Γ ,, [ A ^ t ]) ⊢ Δ)
  → (ext : IsSingleTokenExt r t x)
  → (freshΓ : TokenFresh x Γ)
  → (freshΔ : TokenFresh x Δ)
  → (ec : EigenposCond x Π)  -- takes EigenposCond directly
  → (x' : Token)
  → (x'-eigenpos : maxEigenposToken Π < x')
  → (x'∉r : x' ∉Pos r)
  → Σ ((Γ ,, [ A ^ substPos x (singleton-pos x') t ]) ⊢ Δ)
      (λ Π' → IsSingleTokenExt r (substPos x (singleton-pos x') t) x')
renameEigenpos-♢⊢-premise-gen-ec {r} {t} {x} {Γ} {Δ} {A} Π ext freshΓ freshΔ ec x' x'-eigenpos x'∉r =
  Π' , ext'
  where
    nc : NoEigenposInt (singleton-pos x') Π
    nc = NoEigenposInt-singleton-fresh x' Π x'-eigenpos

    Π-subst : substCtx x (singleton-pos x') (Γ ,, [ A ^ t ]) ⊢ substCtx x (singleton-pos x') Δ
    Π-subst = substTokenToPosProof x (singleton-pos x') Π ec nc

    Δ-unchanged : substCtx x (singleton-pos x') Δ ≡ Δ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ freshΔ

    Γ-unchanged : substCtx x (singleton-pos x') Γ ≡ Γ
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ freshΓ

    ctx-eq : substCtx x (singleton-pos x') (Γ ,, [ A ^ t ]) ≡ Γ ,, [ A ^ substPos x (singleton-pos x') t ]
    ctx-eq = substCtx-++ x (singleton-pos x') Γ [ A ^ t ] ∙ cong (_++L [ A ^ substPos x (singleton-pos x') t ]) Γ-unchanged

    Π' : (Γ ,, [ A ^ substPos x (singleton-pos x') t ]) ⊢ Δ
    Π' = subst2 _⊢_ ctx-eq Δ-unchanged Π-subst

    ext' : IsSingleTokenExt r (substPos x (singleton-pos x') t) x'
    ext' = singleTokenExt-rename ext x'∉r

-- Eigenposition renaming for ⊢□ premise (takes EigenposCond directly)
renameEigenpos-⊢□-premise-gen-ec : ∀ {r t : Position} {x : Token} {Γ Δ : Ctx} {A : Formula}
  → (Π : Γ ⊢ ([ A ^ t ] ,, Δ))
  → (ext : IsSingleTokenExt r t x)
  → (freshΓ : TokenFresh x Γ)
  → (freshΔ : TokenFresh x Δ)
  → (ec : EigenposCond x Π)  -- takes EigenposCond directly
  → (x' : Token)
  → (x'-eigenpos : maxEigenposToken Π < x')
  → (x'∉r : x' ∉Pos r)
  → Σ (Γ ⊢ ([ A ^ substPos x (singleton-pos x') t ] ,, Δ))
      (λ Π' → IsSingleTokenExt r (substPos x (singleton-pos x') t) x')
renameEigenpos-⊢□-premise-gen-ec {r} {t} {x} {Γ} {Δ} {A} Π ext freshΓ freshΔ ec x' x'-eigenpos x'∉r =
  Π' , ext'
  where
    nc : NoEigenposInt (singleton-pos x') Π
    nc = NoEigenposInt-singleton-fresh x' Π x'-eigenpos

    Π-subst : substCtx x (singleton-pos x') Γ ⊢ substCtx x (singleton-pos x') ([ A ^ t ] ,, Δ)
    Π-subst = substTokenToPosProof x (singleton-pos x') Π ec nc

    Γ-unchanged : substCtx x (singleton-pos x') Γ ≡ Γ
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ freshΓ

    Δ-unchanged : substCtx x (singleton-pos x') Δ ≡ Δ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ freshΔ

    ctx-eq : substCtx x (singleton-pos x') ([ A ^ t ] ,, Δ) ≡ [ A ^ substPos x (singleton-pos x') t ] ,, Δ
    ctx-eq = substCtx-++ x (singleton-pos x') [ A ^ t ] Δ ∙ cong ([ A ^ substPos x (singleton-pos x') t ] ++L_) Δ-unchanged

    Π' : Γ ⊢ ([ A ^ substPos x (singleton-pos x') t ] ,, Δ)
    Π' = subst2 _⊢_ Γ-unchanged ctx-eq Π-subst

    ext' : IsSingleTokenExt r (substPos x (singleton-pos x') t) x'
    ext' = singleTokenExt-rename ext x'∉r

-- Degree preservation for renameEigenpos-♢⊢-premise-gen-ec
δ-renameEigenpos-♢⊢-premise-gen-ec : ∀ {r t : Position} {x : Token} {Γ Δ : Ctx} {A : Formula}
  → (Π : (Γ ,, [ A ^ t ]) ⊢ Δ)
  → (ext : IsSingleTokenExt r t x)
  → (freshΓ : TokenFresh x Γ)
  → (freshΔ : TokenFresh x Δ)
  → (ec : EigenposCond x Π)
  → (x' : Token)
  → (x'-eigenpos : maxEigenposToken Π < x')
  → (x'∉r : x' ∉Pos r)
  → δ (fst (renameEigenpos-♢⊢-premise-gen-ec Π ext freshΓ freshΔ ec x' x'-eigenpos x'∉r)) ≡ δ Π
δ-renameEigenpos-♢⊢-premise-gen-ec {r} {t} {x} {Γ} {Δ} {A} Π ext freshΓ freshΔ ec x' x'-eigenpos x'∉r =
  δ-subst2 ctx-eq Δ-unchanged Π-subst ∙ δ-substTokenToPosProof x (singleton-pos x') Π ec nc
  where
    nc : NoEigenposInt (singleton-pos x') Π
    nc = NoEigenposInt-singleton-fresh x' Π x'-eigenpos
    Π-subst = substTokenToPosProof x (singleton-pos x') Π ec nc
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ freshΓ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ freshΔ
    ctx-eq = substCtx-++ x (singleton-pos x') Γ [ A ^ t ] ∙ cong (_++L [ A ^ substPos x (singleton-pos x') t ]) Γ-unchanged

-- Degree preservation for renameEigenpos-⊢□-premise-gen-ec
δ-renameEigenpos-⊢□-premise-gen-ec : ∀ {r t : Position} {x : Token} {Γ Δ : Ctx} {A : Formula}
  → (Π : Γ ⊢ ([ A ^ t ] ,, Δ))
  → (ext : IsSingleTokenExt r t x)
  → (freshΓ : TokenFresh x Γ)
  → (freshΔ : TokenFresh x Δ)
  → (ec : EigenposCond x Π)
  → (x' : Token)
  → (x'-eigenpos : maxEigenposToken Π < x')
  → (x'∉r : x' ∉Pos r)
  → δ (fst (renameEigenpos-⊢□-premise-gen-ec Π ext freshΓ freshΔ ec x' x'-eigenpos x'∉r)) ≡ δ Π
δ-renameEigenpos-⊢□-premise-gen-ec {r} {t} {x} {Γ} {Δ} {A} Π ext freshΓ freshΔ ec x' x'-eigenpos x'∉r =
  δ-subst2 Γ-unchanged ctx-eq Π-subst ∙ δ-substTokenToPosProof x (singleton-pos x') Π ec nc
  where
    nc : NoEigenposInt (singleton-pos x') Π
    nc = NoEigenposInt-singleton-fresh x' Π x'-eigenpos
    Π-subst = substTokenToPosProof x (singleton-pos x') Π ec nc
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ freshΓ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ freshΔ
    ctx-eq = substCtx-++ x (singleton-pos x') [ A ^ t ] Δ ∙ cong ([ A ^ substPos x (singleton-pos x') t ] ++L_) Δ-unchanged


-- =============================================================================
-- Height Preservation Lemmas
-- =============================================================================

-- Lemma: height is preserved by subst2 (trivial - type-level transport doesn't change proof structure)
height-subst2 : ∀ {Γ Γ' Δ Δ'} (p : Γ ≡ Γ') (q : Δ ≡ Δ') (Π : Γ ⊢ Δ)
  → height (subst2 _⊢_ p q Π) ≡ height Π
height-subst2 {Γ} {Γ'} {Δ} {Δ'} p q Π =
  J (λ Γ' p → ∀ Δ' (q : Δ ≡ Δ') → height (subst2 _⊢_ p q Π) ≡ height Π)
    (λ Δ' q → J (λ Δ' q → height (subst2 _⊢_ refl q Π) ≡ height Π)
                (cong height (substRefl {B = Γ ⊢_} Π)) q)
    p Δ' q

-- Helpers for single-argument subst
height-substR : ∀ {Γ Δ Δ'} (p : Δ ≡ Δ') (Π : Γ ⊢ Δ)
  → height (subst (Γ ⊢_) p Π) ≡ height Π
height-substR p Π = height-subst2 refl p Π

height-substL : ∀ {Γ Γ' Δ} (p : Γ ≡ Γ') (Π : Γ ⊢ Δ)
  → height (subst (_⊢ Δ) p Π) ≡ height Π
height-substL p Π = height-subst2 p refl Π

-- Main lemma by induction on Π: height is preserved by substTokenToPosProof
height-substTokenToPosProof : (z : Token) (t : Position) {Γ Δ : Ctx}
  → (Π : Γ ⊢ Δ) → (ec : EigenposCond z Π) → (nc : NoEigenposInt t Π)
  → height (substTokenToPosProof z t Π ec nc) ≡ height Π
height-substTokenToPosProof z t Ax _ _ = refl
height-substTokenToPosProof z t (Cut {Γ₁} {A} {s} {Δ₁} {Γ₂} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      outer-eq = height-subst2 (sym (substCtx-++ z t Γ₁ Γ₂)) (sym (substCtx-++ z t Δ₁ Δ₂))
                   (Cut (subst (substCtx z t Γ₁ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₁) Π₁')
                        (subst (_⊢ substCtx z t Δ₂) (substCtx-++ z t Γ₂ [ A ^ s ]) Π₂'))
      inner₁-eq = height-substR (substCtx-++ z t [ A ^ s ] Δ₁) Π₁'
      inner₂-eq = height-substL (substCtx-++ z t Γ₂ [ A ^ s ]) Π₂'
      ih₁ = height-substTokenToPosProof z t Π₁ ec₁ nc₁
      ih₂ = height-substTokenToPosProof z t Π₂ ec₂ nc₂
  in outer-eq ∙ cong (_+ 1) (cong₂ max (inner₁-eq ∙ ih₁) (inner₂-eq ∙ ih₂))
height-substTokenToPosProof z t (W⊢ {Γ} {Δ} {A} {s} Π) ec nc =
  height-substL (sym (substCtx-++ z t Γ [ A ^ s ])) (W⊢ (substTokenToPosProof z t Π ec nc))
  ∙ cong (_+ 1) (height-substTokenToPosProof z t Π ec nc)
height-substTokenToPosProof z t (⊢W {Γ} {Δ} {A} {s} Π) ec nc =
  height-substR (sym (substCtx-++ z t [ A ^ s ] Δ)) (⊢W (substTokenToPosProof z t Π ec nc))
  ∙ cong (_+ 1) (height-substTokenToPosProof z t Π ec nc)
height-substTokenToPosProof z t (C⊢ {Γ} {A} {s} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ)
                (substCtx-++ z t (Γ ++L [ A ^ s ]) [ A ^ s ] ∙
                 cong (_++L substCtx z t [ A ^ s ]) (substCtx-++ z t Γ [ A ^ s ])) Π'
  in height-substL (sym (substCtx-++ z t Γ [ A ^ s ])) (C⊢ inner)
     ∙ cong (_+ 1) (height-substL (substCtx-++ z t (Γ ++L [ A ^ s ]) [ A ^ s ] ∙
                 cong (_++L substCtx z t [ A ^ s ]) (substCtx-++ z t Γ [ A ^ s ])) Π')
     ∙ cong (_+ 1) (height-substTokenToPosProof z t Π ec nc)
height-substTokenToPosProof z t (⊢C {Γ} {A} {s} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_)
                (substCtx-++ z t ([ A ^ s ] ++L [ A ^ s ]) Δ ∙
                 cong (_++L substCtx z t Δ) (substCtx-++ z t [ A ^ s ] [ A ^ s ])) Π'
  in height-substR (sym (substCtx-++ z t [ A ^ s ] Δ)) (⊢C inner)
     ∙ cong (_+ 1) (height-substR (substCtx-++ z t ([ A ^ s ] ++L [ A ^ s ]) Δ ∙
                 cong (_++L substCtx z t Δ) (substCtx-++ z t [ A ^ s ] [ A ^ s ])) Π')
     ∙ cong (_+ 1) (height-substTokenToPosProof z t Π ec nc)
height-substTokenToPosProof z t (Exc⊢ {Γ₁} {A} {s} {B} {t'} {Γ₂} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      step0' = cong (substCtx z t) (++L-assoc (Γ₁ ++L [ B ^ t' ]) [ A ^ s ] Γ₂)
      step1' = substCtx-++ z t (Γ₁ ++L [ B ^ t' ]) (A ^ s ∷ Γ₂)
      step2' = cong (_++L substCtx z t (A ^ s ∷ Γ₂)) (substCtx-++ z t Γ₁ [ B ^ t' ])
      step3' = cong ((substCtx z t Γ₁ ++L substCtx z t [ B ^ t' ]) ++L_) (substCtx-++ z t [ A ^ s ] Γ₂)
      step4' = sym (++L-assoc (substCtx z t Γ₁ ++L substCtx z t [ B ^ t' ]) (substCtx z t [ A ^ s ]) (substCtx z t Γ₂))
      path2 = step0' ∙ step1' ∙ step2' ∙ step3' ∙ step4'
      step0 = cong (substCtx z t) (++L-assoc (Γ₁ ++L [ A ^ s ]) [ B ^ t' ] Γ₂)
      step1 = substCtx-++ z t (Γ₁ ++L [ A ^ s ]) (B ^ t' ∷ Γ₂)
      step2 = cong (_++L substCtx z t (B ^ t' ∷ Γ₂)) (substCtx-++ z t Γ₁ [ A ^ s ])
      step3 = cong ((substCtx z t Γ₁ ++L substCtx z t [ A ^ s ]) ++L_) (substCtx-++ z t [ B ^ t' ] Γ₂)
      step4 = sym (++L-assoc (substCtx z t Γ₁ ++L substCtx z t [ A ^ s ]) (substCtx z t [ B ^ t' ]) (substCtx z t Γ₂))
      path = step0 ∙ step1 ∙ step2 ∙ step3 ∙ step4
      raw = Exc⊢ {Γ₁ = substCtx z t Γ₁} {A = A} {B = B} {Γ₂ = substCtx z t Γ₂}
                 (subst (λ G → G ⊢ substCtx z t Δ) path Π')
  in height-substL (sym path2) raw
     ∙ cong (_+ 1) (height-substL path Π')
     ∙ cong (_+ 1) (height-substTokenToPosProof z t Π ec nc)
height-substTokenToPosProof z t (⊢Exc {Γ} {Δ₁} {A} {s} {B} {t'} {Δ₂} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      step0' = cong (substCtx z t) (++L-assoc (Δ₁ ++L [ B ^ t' ]) [ A ^ s ] Δ₂)
      step1' = substCtx-++ z t (Δ₁ ++L [ B ^ t' ]) (A ^ s ∷ Δ₂)
      step2' = cong (_++L substCtx z t (A ^ s ∷ Δ₂)) (substCtx-++ z t Δ₁ [ B ^ t' ])
      step3' = cong ((substCtx z t Δ₁ ++L substCtx z t [ B ^ t' ]) ++L_) (substCtx-++ z t [ A ^ s ] Δ₂)
      step4' = sym (++L-assoc (substCtx z t Δ₁ ++L substCtx z t [ B ^ t' ]) (substCtx z t [ A ^ s ]) (substCtx z t Δ₂))
      path2 = step0' ∙ step1' ∙ step2' ∙ step3' ∙ step4'
      step0 = cong (substCtx z t) (++L-assoc (Δ₁ ++L [ A ^ s ]) [ B ^ t' ] Δ₂)
      step1 = substCtx-++ z t (Δ₁ ++L [ A ^ s ]) (B ^ t' ∷ Δ₂)
      step2 = cong (_++L substCtx z t (B ^ t' ∷ Δ₂)) (substCtx-++ z t Δ₁ [ A ^ s ])
      step3 = cong ((substCtx z t Δ₁ ++L substCtx z t [ A ^ s ]) ++L_) (substCtx-++ z t [ B ^ t' ] Δ₂)
      step4 = sym (++L-assoc (substCtx z t Δ₁ ++L substCtx z t [ A ^ s ]) (substCtx z t [ B ^ t' ]) (substCtx z t Δ₂))
      path = step0 ∙ step1 ∙ step2 ∙ step3 ∙ step4
      raw = ⊢Exc {Δ₁ = substCtx z t Δ₁} {A = A} {B = B} {Δ₂ = substCtx z t Δ₂}
                 (subst (λ D → substCtx z t Γ ⊢ D) path Π')
  in height-substR (sym path2) raw
     ∙ cong (_+ 1) (height-substR path Π')
     ∙ cong (_+ 1) (height-substTokenToPosProof z t Π ec nc)
height-substTokenToPosProof z t (¬⊢ {Γ} {A} {s} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ A ^ s ] Δ) Π'
  in height-substL (sym (substCtx-++ z t Γ [ (¬ A) ^ s ])) (¬⊢ inner)
     ∙ cong (_+ 1) (height-substR (substCtx-++ z t [ A ^ s ] Δ) Π')
     ∙ cong (_+ 1) (height-substTokenToPosProof z t Π ec nc)
height-substTokenToPosProof z t (⊢¬ {Γ} {A} {s} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ A ^ s ]) Π'
  in height-substR (sym (substCtx-++ z t [ (¬ A) ^ s ] Δ)) (⊢¬ inner)
     ∙ cong (_+ 1) (height-substL (substCtx-++ z t Γ [ A ^ s ]) Π')
     ∙ cong (_+ 1) (height-substTokenToPosProof z t Π ec nc)
height-substTokenToPosProof z t (∧₁⊢ {Γ} {A} {s} {Δ} {B} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ A ^ s ]) Π'
  in height-substL (sym (substCtx-++ z t Γ [ (A and B) ^ s ])) (∧₁⊢ inner)
     ∙ cong (_+ 1) (height-substL (substCtx-++ z t Γ [ A ^ s ]) Π')
     ∙ cong (_+ 1) (height-substTokenToPosProof z t Π ec nc)
height-substTokenToPosProof z t (∧₂⊢ {Γ} {B} {s} {Δ} {A} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (_⊢ substCtx z t Δ) (substCtx-++ z t Γ [ B ^ s ]) Π'
  in height-substL (sym (substCtx-++ z t Γ [ (A and B) ^ s ])) (∧₂⊢ inner)
     ∙ cong (_+ 1) (height-substL (substCtx-++ z t Γ [ B ^ s ]) Π')
     ∙ cong (_+ 1) (height-substTokenToPosProof z t Π ec nc)
height-substTokenToPosProof z t (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      outer-eq = height-subst2 (sym (substCtx-++ z t Γ₁ Γ₂))
                   (cong (substCtx z t [ (A and B) ^ s ] ++L_) (sym (substCtx-++ z t Δ₁ Δ₂)) ∙
                    sym (substCtx-++ z t [ (A and B) ^ s ] (Δ₁ ++L Δ₂)))
                   (⊢∧ (subst (substCtx z t Γ₁ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₁) Π₁')
                       (subst (substCtx z t Γ₂ ⊢_) (substCtx-++ z t [ B ^ s ] Δ₂) Π₂'))
      inner₁-eq = height-substR (substCtx-++ z t [ A ^ s ] Δ₁) Π₁'
      inner₂-eq = height-substR (substCtx-++ z t [ B ^ s ] Δ₂) Π₂'
      ih₁ = height-substTokenToPosProof z t Π₁ ec₁ nc₁
      ih₂ = height-substTokenToPosProof z t Π₂ ec₂ nc₂
  in outer-eq ∙ cong (_+ 1) (cong₂ max (inner₁-eq ∙ ih₁) (inner₂-eq ∙ ih₂))
height-substTokenToPosProof z t (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      outer-eq = height-subst2
                   (cong (substCtx z t Γ₁ ++L_) (sym (substCtx-++ z t Γ₂ [ (A or B) ^ s ]))
                    ∙ sym (substCtx-++ z t Γ₁ (Γ₂ ++L [ (A or B) ^ s ])))
                   (sym (substCtx-++ z t Δ₁ Δ₂))
                   (∨⊢ (subst (_⊢ substCtx z t Δ₁) (substCtx-++ z t Γ₁ [ A ^ s ]) Π₁')
                       (subst (_⊢ substCtx z t Δ₂) (substCtx-++ z t Γ₂ [ B ^ s ]) Π₂'))
      inner₁-eq = height-substL (substCtx-++ z t Γ₁ [ A ^ s ]) Π₁'
      inner₂-eq = height-substL (substCtx-++ z t Γ₂ [ B ^ s ]) Π₂'
      ih₁ = height-substTokenToPosProof z t Π₁ ec₁ nc₁
      ih₂ = height-substTokenToPosProof z t Π₂ ec₂ nc₂
  in outer-eq ∙ cong (_+ 1) (cong₂ max (inner₁-eq ∙ ih₁) (inner₂-eq ∙ ih₂))
height-substTokenToPosProof z t (⊢∨₁ {Γ} {A} {s} {Δ} {B} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ A ^ s ] Δ) Π'
  in height-substR (sym (substCtx-++ z t [ (A or B) ^ s ] Δ)) (⊢∨₁ inner)
     ∙ cong (_+ 1) (height-substR (substCtx-++ z t [ A ^ s ] Δ) Π')
     ∙ cong (_+ 1) (height-substTokenToPosProof z t Π ec nc)
height-substTokenToPosProof z t (⊢∨₂ {Γ} {B} {s} {Δ} {A} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst (substCtx z t Γ ⊢_) (substCtx-++ z t [ B ^ s ] Δ) Π'
  in height-substR (sym (substCtx-++ z t [ (A or B) ^ s ] Δ)) (⊢∨₂ inner)
     ∙ cong (_+ 1) (height-substR (substCtx-++ z t [ B ^ s ] Δ) Π')
     ∙ cong (_+ 1) (height-substTokenToPosProof z t Π ec nc)
height-substTokenToPosProof z t (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} Π₁ Π₂) (ec₁ , ec₂) (nc₁ , nc₂) =
  let Π₁' = substTokenToPosProof z t Π₁ ec₁ nc₁
      Π₂' = substTokenToPosProof z t Π₂ ec₂ nc₂
      outer-eq = height-subst2
                   (cong (substCtx z t Γ₁ ++L_) (sym (substCtx-++ z t Γ₂ [ (A ⇒ B) ^ s ]))
                    ∙ sym (substCtx-++ z t Γ₁ (Γ₂ ++L [ (A ⇒ B) ^ s ])))
                   (sym (substCtx-++ z t Δ₁ Δ₂))
                   (⇒⊢ (subst (_⊢ substCtx z t Δ₁) (substCtx-++ z t Γ₁ [ B ^ s ]) Π₁')
                       (subst (substCtx z t Γ₂ ⊢_) (substCtx-++ z t [ A ^ s ] Δ₂) Π₂'))
      inner₁-eq = height-substL (substCtx-++ z t Γ₁ [ B ^ s ]) Π₁'
      inner₂-eq = height-substR (substCtx-++ z t [ A ^ s ] Δ₂) Π₂'
      ih₁ = height-substTokenToPosProof z t Π₁ ec₁ nc₁
      ih₂ = height-substTokenToPosProof z t Π₂ ec₂ nc₂
  in outer-eq ∙ cong (_+ 1) (cong₂ max (inner₁-eq ∙ ih₁) (inner₂-eq ∙ ih₂))
height-substTokenToPosProof z t (⊢⇒ {Γ} {A} {s} {B} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      inner = subst2 _⊢_ (substCtx-++ z t Γ [ A ^ s ]) (substCtx-++ z t [ B ^ s ] Δ) Π'
  in height-substR (sym (substCtx-++ z t [ (A ⇒ B) ^ s ] Δ)) (⊢⇒ inner)
     ∙ cong (_+ 1) (height-subst2 (substCtx-++ z t Γ [ A ^ s ]) (substCtx-++ z t [ B ^ s ] Δ) Π')
     ∙ cong (_+ 1) (height-substTokenToPosProof z t Π ec nc)
height-substTokenToPosProof z t (□⊢ {Γ} {A} {s} {t'} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      ctx-eq = substCtx-++ z t Γ [ A ^ (s ++Pos t') ]
      pos-eq = substPos-++Pos-distr z t s t'
      Π'' = subst (_⊢ substCtx z t Δ) (ctx-eq ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π'
      out-path = sym (substCtx-++ z t Γ [ (□ A) ^ s ])
  in height-substL out-path (□⊢ Π'')
     ∙ cong (_+ 1) (height-substL (ctx-eq ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π')
     ∙ cong (_+ 1) (height-substTokenToPosProof z t Π ec nc)
height-substTokenToPosProof z t (⊢□ {x} {s} {Γ} {Δ} {A} x∉s xFrΓ xFrΔ Π) (z≢x , ec) (x∉t , nc) =
  let Π' = substTokenToPosProof z t Π ec nc
      pos-eq = substPos-insertToken-neq z x s t z≢x
      x∉substs = ∉Pos-substPos z t s x∉s x∉t
      xFrΓ' = TokenFresh-substCtx z x t Γ z≢x x∉t xFrΓ
      xFrΔ' = TokenFresh-substCtx z x t Δ z≢x x∉t xFrΔ
      rhs-path = substCtx-++ z t [ A ^ insertToken x s ] Δ
      Π'' = subst (substCtx z t Γ ⊢_) (rhs-path ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π'
      raw = ⊢□ x∉substs xFrΓ' xFrΔ' Π''
      out-path = sym (substCtx-++ z t [ (□ A) ^ s ] Δ)
      ih = height-substTokenToPosProof z t Π ec nc
  in height-substR out-path raw
     ∙ cong (_+ 1) (height-substR (rhs-path ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π')
     ∙ cong (_+ 1) ih
height-substTokenToPosProof z t (♢⊢ {x} {s} {Γ} {Δ} {A} x∉s xFrΓ xFrΔ Π) (z≢x , ec) (x∉t , nc) =
  let Π' = substTokenToPosProof z t Π ec nc
      pos-eq = substPos-insertToken-neq z x s t z≢x
      x∉substs = ∉Pos-substPos z t s x∉s x∉t
      xFrΓ' = TokenFresh-substCtx z x t Γ z≢x x∉t xFrΓ
      xFrΔ' = TokenFresh-substCtx z x t Δ z≢x x∉t xFrΔ
      lhs-path = substCtx-++ z t Γ [ A ^ insertToken x s ]
      Π'' = subst (_⊢ substCtx z t Δ) (lhs-path ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π'
      raw = ♢⊢ x∉substs xFrΓ' xFrΔ' Π''
      out-path = sym (substCtx-++ z t Γ [ (♢ A) ^ s ])
      ih = height-substTokenToPosProof z t Π ec nc
  in height-substL out-path raw
     ∙ cong (_+ 1) (height-substL (lhs-path ∙ cong (λ p → substCtx z t Γ ,, [ A ^ p ]) pos-eq) Π')
     ∙ cong (_+ 1) ih
height-substTokenToPosProof z t (⊢♢ {Γ} {A} {s} {t'} {Δ} Π) ec nc =
  let Π' = substTokenToPosProof z t Π ec nc
      ctx-eq = substCtx-++ z t [ A ^ (s ++Pos t') ] Δ
      pos-eq = substPos-++Pos-distr z t s t'
      Π'' = subst (substCtx z t Γ ⊢_) (ctx-eq ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π'
      out-path = sym (substCtx-++ z t [ (♢ A) ^ s ] Δ)
  in height-substR out-path (⊢♢ Π'')
     ∙ cong (_+ 1) (height-substR (ctx-eq ∙ cong (λ p → [ A ^ p ] ,, substCtx z t Δ) pos-eq) Π')
     ∙ cong (_+ 1) (height-substTokenToPosProof z t Π ec nc)

-- Height preservation for renameEigenpos-♢⊢-premise-gen
height-renameEigenpos-♢⊢-premise-gen : ∀ {r t : Position} {x : Token} {Γ Δ : Ctx} {A : Formula}
  → (Π : (Γ ,, [ A ^ t ]) ⊢ Δ)
  → (ext : IsSingleTokenExt r t x)
  → (freshΓ : TokenFresh x Γ)
  → (freshΔ : TokenFresh x Δ)
  → (wf : maxEigenposToken Π < x)
  → (x' : Token)
  → (x'-eigenpos : maxEigenposToken Π < x')
  → (x'∉r : x' ∉Pos r)
  → height (fst (renameEigenpos-♢⊢-premise-gen Π ext freshΓ freshΔ wf x' x'-eigenpos x'∉r)) ≡ height Π
height-renameEigenpos-♢⊢-premise-gen {r} {t} {x} {Γ} {Δ} {A} Π ext freshΓ freshΔ wf x' x'-eigenpos x'∉r =
  height-subst2 ctx-eq Δ-unchanged Π-subst ∙ height-substTokenToPosProof x (singleton-pos x') Π ec nc
  where
    ec : EigenposCond x Π
    ec = EigenposCond-from-wf x Π wf
    nc : NoEigenposInt (singleton-pos x') Π
    nc = NoEigenposInt-singleton-fresh x' Π x'-eigenpos
    Π-subst = substTokenToPosProof x (singleton-pos x') Π ec nc
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ freshΓ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ freshΔ
    ctx-eq = substCtx-++ x (singleton-pos x') Γ [ A ^ t ] ∙ cong (_++L [ A ^ substPos x (singleton-pos x') t ]) Γ-unchanged

-- Height preservation for renameEigenpos-⊢□-premise-gen
height-renameEigenpos-⊢□-premise-gen : ∀ {r t : Position} {x : Token} {Γ Δ : Ctx} {A : Formula}
  → (Π : Γ ⊢ ([ A ^ t ] ,, Δ))
  → (ext : IsSingleTokenExt r t x)
  → (freshΓ : TokenFresh x Γ)
  → (freshΔ : TokenFresh x Δ)
  → (wf : maxEigenposToken Π < x)
  → (x' : Token)
  → (x'-eigenpos : maxEigenposToken Π < x')
  → (x'∉r : x' ∉Pos r)
  → height (fst (renameEigenpos-⊢□-premise-gen Π ext freshΓ freshΔ wf x' x'-eigenpos x'∉r)) ≡ height Π
height-renameEigenpos-⊢□-premise-gen {r} {t} {x} {Γ} {Δ} {A} Π ext freshΓ freshΔ wf x' x'-eigenpos x'∉r =
  height-subst2 Γ-unchanged ctx-eq Π-subst ∙ height-substTokenToPosProof x (singleton-pos x') Π ec nc
  where
    ec : EigenposCond x Π
    ec = EigenposCond-from-wf x Π wf
    nc : NoEigenposInt (singleton-pos x') Π
    nc = NoEigenposInt-singleton-fresh x' Π x'-eigenpos
    Π-subst = substTokenToPosProof x (singleton-pos x') Π ec nc
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ freshΓ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ freshΔ
    ctx-eq = substCtx-++ x (singleton-pos x') [ A ^ t ] Δ ∙ cong ([ A ^ substPos x (singleton-pos x') t ] ++L_) Δ-unchanged

-- WellFormedProof preservation under eigenposition renaming (♢⊢ case)
WellFormed-renameEigenpos-♢⊢-premise-gen : ∀ {r t : Position} {x : Token} {Γ Δ : Ctx} {A : Formula}
  → (Π : (Γ ,, [ A ^ t ]) ⊢ Δ)
  → (ext : IsSingleTokenExt r t x)
  → (freshΓ : TokenFresh x Γ)
  → (freshΔ : TokenFresh x Δ)
  → (wf : maxEigenposToken Π < x)
  → (x' : Token)
  → (x'-eigenpos : maxEigenposToken Π < x')
  → (x'∉r : x' ∉Pos r)
  → WellFormedProof Π
  → WellFormedProof (fst (renameEigenpos-♢⊢-premise-gen Π ext freshΓ freshΔ wf x' x'-eigenpos x'∉r))
WellFormed-renameEigenpos-♢⊢-premise-gen {r} {t} {x} {Γ} {Δ} {A} Π ext freshΓ freshΔ wf x' x'-eigenpos x'∉r wfΠ =
  WellFormed-subst2 ctx-eq Δ-unchanged Π-subst (WellFormed-substTokenToPosProof x (singleton-pos x') Π ec nc wfΠ)
  where
    ec : EigenposCond x Π
    ec = EigenposCond-from-wf x Π wf
    nc : NoEigenposInt (singleton-pos x') Π
    nc = NoEigenposInt-singleton-fresh x' Π x'-eigenpos
    Π-subst = substTokenToPosProof x (singleton-pos x') Π ec nc
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ freshΓ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ freshΔ
    ctx-eq = substCtx-++ x (singleton-pos x') Γ [ A ^ t ] ∙ cong (_++L [ A ^ substPos x (singleton-pos x') t ]) Γ-unchanged

-- WellFormedProof preservation under eigenposition renaming (⊢□ case)
WellFormed-renameEigenpos-⊢□-premise-gen : ∀ {r t : Position} {x : Token} {Γ Δ : Ctx} {A : Formula}
  → (Π : Γ ⊢ ([ A ^ t ] ,, Δ))
  → (ext : IsSingleTokenExt r t x)
  → (freshΓ : TokenFresh x Γ)
  → (freshΔ : TokenFresh x Δ)
  → (wf : maxEigenposToken Π < x)
  → (x' : Token)
  → (x'-eigenpos : maxEigenposToken Π < x')
  → (x'∉r : x' ∉Pos r)
  → WellFormedProof Π
  → WellFormedProof (fst (renameEigenpos-⊢□-premise-gen Π ext freshΓ freshΔ wf x' x'-eigenpos x'∉r))
WellFormed-renameEigenpos-⊢□-premise-gen {r} {t} {x} {Γ} {Δ} {A} Π ext freshΓ freshΔ wf x' x'-eigenpos x'∉r wfΠ =
  WellFormed-subst2 Γ-unchanged ctx-eq Π-subst (WellFormed-substTokenToPosProof x (singleton-pos x') Π ec nc wfΠ)
  where
    ec : EigenposCond x Π
    ec = EigenposCond-from-wf x Π wf
    nc : NoEigenposInt (singleton-pos x') Π
    nc = NoEigenposInt-singleton-fresh x' Π x'-eigenpos
    Π-subst = substTokenToPosProof x (singleton-pos x') Π ec nc
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ freshΓ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ freshΔ
    ctx-eq = substCtx-++ x (singleton-pos x') [ A ^ t ] Δ ∙ cong ([ A ^ substPos x (singleton-pos x') t ] ++L_) Δ-unchanged

-- =============================================================================
-- Height Preservation for makeWellFormed
-- =============================================================================

-- Lemma: makeWellFormed-go preserves height
height-makeWellFormed-go : (base k : Token) (base≤k : base ≤ k) {Γ Δ : Ctx}
  → (Π : Γ ⊢ Δ)
  → (origMax<base : maxEigenposToken Π < base)
  → (proofMax<base : maxTokenProof Π < base)
  → height (MWFResult.proof (makeWellFormed-go base k base≤k Π origMax<base proofMax<base)) ≡ height Π
height-makeWellFormed-go base k base≤k Ax _ _ = refl
height-makeWellFormed-go base k base≤k (Cut {Γ₁} {A} {s} {Δ₁} {Γ₂} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  let max₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxEigenposToken Π₁) _)) origMax<base
      max₂<base = ≤-trans (suc-≤-suc (≤-myMax-r _ (maxEigenposToken Π₂))) origMax<base
      proof₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenProof Π₁) (maxTokenProof Π₂)))
                    (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenPos s) (myMax (maxTokenProof Π₁) (maxTokenProof Π₂))))
                             (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenCtx ((Γ₁ ,, Γ₂) ,, (Δ₁ ,, Δ₂))) _)) proofMax<base))
      proof₂<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenProof Π₁) (maxTokenProof Π₂)))
                    (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenPos s) (myMax (maxTokenProof Π₁) (maxTokenProof Π₂))))
                             (≤-trans (suc-≤-suc (≤-myMax-r (maxTokenCtx ((Γ₁ ,, Γ₂) ,, (Δ₁ ,, Δ₂))) _)) proofMax<base))
      mwfR₁ = makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
      base≤next₁ = ≤-trans base≤k (MWFResult.k≤next mwfR₁)
      mwfR₂ = makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
      ih₁ = height-makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
      ih₂ = height-makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
  in cong (_+ 1) (cong₂ max ih₁ ih₂)
height-makeWellFormed-go base k base≤k (W⊢ Π) origMax<base proofMax<base =
  cong (_+ 1) (height-makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base))
height-makeWellFormed-go base k base≤k (⊢W Π) origMax<base proofMax<base =
  cong (_+ 1) (height-makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base))
height-makeWellFormed-go base k base≤k (C⊢ Π) origMax<base proofMax<base =
  cong (_+ 1) (height-makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base))
height-makeWellFormed-go base k base≤k (⊢C Π) origMax<base proofMax<base =
  cong (_+ 1) (height-makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base))
height-makeWellFormed-go base k base≤k (Exc⊢ {Γ₁} {A} {s} {B} {t} {Γ₂} {Δ} Π) origMax<base proofMax<base =
  cong (_+ 1) (height-makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base))
height-makeWellFormed-go base k base≤k (⊢Exc {Γ} {Δ₁} {A} {s} {B} {t} {Δ₂} Π) origMax<base proofMax<base =
  cong (_+ 1) (height-makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base))
height-makeWellFormed-go base k base≤k (¬⊢ Π) origMax<base proofMax<base =
  cong (_+ 1) (height-makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base))
height-makeWellFormed-go base k base≤k (⊢¬ Π) origMax<base proofMax<base =
  cong (_+ 1) (height-makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base))
height-makeWellFormed-go base k base≤k (∧₁⊢ Π) origMax<base proofMax<base =
  cong (_+ 1) (height-makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base))
height-makeWellFormed-go base k base≤k (∧₂⊢ Π) origMax<base proofMax<base =
  cong (_+ 1) (height-makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base))
height-makeWellFormed-go base k base≤k (⊢∨₁ Π) origMax<base proofMax<base =
  cong (_+ 1) (height-makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base))
height-makeWellFormed-go base k base≤k (⊢∨₂ Π) origMax<base proofMax<base =
  cong (_+ 1) (height-makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base))
height-makeWellFormed-go base k base≤k (⊢⇒ Π) origMax<base proofMax<base =
  cong (_+ 1) (height-makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base))
height-makeWellFormed-go base k base≤k (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  let ctxMax = maxTokenCtx ((Γ₁ ,, Γ₂) ,, ([ (A and B) ^ s ] ,, Δ₁ ,, Δ₂))
      proofMax = myMax (maxTokenProof Π₁) (maxTokenProof Π₂)
      max₁<base = ≤-trans (suc-≤-suc (≤-myMax-l _ _)) origMax<base
      max₂<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) origMax<base
      proof₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenProof Π₁) (maxTokenProof Π₂)))
                    (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
      proof₂<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenProof Π₁) (maxTokenProof Π₂)))
                    (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
      mwfR₁ = makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
      base≤next₁ = ≤-trans base≤k (MWFResult.k≤next mwfR₁)
      mwfR₂ = makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
      ih₁ = height-makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
      ih₂ = height-makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
  in cong (_+ 1) (cong₂ max ih₁ ih₂)
height-makeWellFormed-go base k base≤k (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  let ctxMax = maxTokenCtx ((Γ₁ ,, Γ₂ ,, [ (A or B) ^ s ]) ,, (Δ₁ ,, Δ₂))
      proofMax = myMax (maxTokenProof Π₁) (maxTokenProof Π₂)
      max₁<base = ≤-trans (suc-≤-suc (≤-myMax-l _ _)) origMax<base
      max₂<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) origMax<base
      proof₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenProof Π₁) (maxTokenProof Π₂)))
                    (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
      proof₂<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenProof Π₁) (maxTokenProof Π₂)))
                    (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
      mwfR₁ = makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
      base≤next₁ = ≤-trans base≤k (MWFResult.k≤next mwfR₁)
      mwfR₂ = makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
      ih₁ = height-makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
      ih₂ = height-makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
  in cong (_+ 1) (cong₂ max ih₁ ih₂)
height-makeWellFormed-go base k base≤k (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} Π₁ Π₂) origMax<base proofMax<base =
  let ctxMax = maxTokenCtx ((Γ₁ ,, Γ₂ ,, [ (A ⇒ B) ^ s ]) ,, (Δ₁ ,, Δ₂))
      proofMax = myMax (maxTokenProof Π₁) (maxTokenProof Π₂)
      max₁<base = ≤-trans (suc-≤-suc (≤-myMax-l _ _)) origMax<base
      max₂<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) origMax<base
      proof₁<base = ≤-trans (suc-≤-suc (≤-myMax-l (maxTokenProof Π₁) (maxTokenProof Π₂)))
                    (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
      proof₂<base = ≤-trans (suc-≤-suc (≤-myMax-r (maxTokenProof Π₁) (maxTokenProof Π₂)))
                    (≤-trans (suc-≤-suc (≤-myMax-r ctxMax proofMax)) proofMax<base)
      mwfR₁ = makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
      base≤next₁ = ≤-trans base≤k (MWFResult.k≤next mwfR₁)
      mwfR₂ = makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
      ih₁ = height-makeWellFormed-go base k base≤k Π₁ max₁<base proof₁<base
      ih₂ = height-makeWellFormed-go base (MWFResult.next mwfR₁) base≤next₁ Π₂ max₂<base proof₂<base
  in cong (_+ 1) (cong₂ max ih₁ ih₂)
height-makeWellFormed-go base k base≤k (□⊢ Π) origMax<base proofMax<base =
  cong (_+ 1) (height-makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base))
height-makeWellFormed-go base k base≤k (⊢♢ Π) origMax<base proofMax<base =
  cong (_+ 1) (height-makeWellFormed-go base k base≤k Π origMax<base (≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base))
-- For modal cases with eigentokens (⊢□, ♢⊢), we need to use height-substTokenToPosProof and height-subst2
height-makeWellFormed-go base k base≤k (⊢□ {x} {r} {Γ} {Δ} {A} x∉r xFrΓ xFrΔ Π) origMax<base proofMax<base =
  -- Using same bounds pattern as δ-makeWellFormed-go
  cong (_+ 1) (h-subst2 ∙ h-subst ∙ ih)
  where
    x<base = ≤-trans (suc-≤-suc (≤-myMax-l x _)) origMax<base
    subMax<base = ≤-trans (suc-≤-suc (≤-myMax-r x _)) origMax<base
    subProof<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base
    mwfR = makeWellFormed-go base k base≤k Π subMax<base subProof<base
    Π-wf = MWFResult.proof mwfR
    next = MWFResult.next mwfR
    x' = next
    k≤x' = MWFResult.k≤next mwfR
    ec = EigenposCond-from-lt-base x base Π-wf x<base (MWFResult.allEigen≥base mwfR)
    nc = NoEigenposInt-singleton-fresh x' Π-wf (MWFResult.maxEigen<next mwfR)
    Π-subst = substTokenToPosProof x (singleton-pos x') Π-wf ec nc
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ xFrΓ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ xFrΔ
    pos-eq = substPos-insertToken-eq x x' r x∉r
    ctx-eq = substCtx-++ x (singleton-pos x') [ A ^ insertToken x r ] Δ
             ∙ cong₂ _,,_ (cong [_] (cong (A ^_) pos-eq)) Δ-unchanged
    ih = height-makeWellFormed-go base k base≤k Π subMax<base subProof<base
    h-subst = height-substTokenToPosProof x (singleton-pos x') Π-wf ec nc
    h-subst2 = height-subst2 Γ-unchanged ctx-eq Π-subst
height-makeWellFormed-go base k base≤k (♢⊢ {x} {r} {Γ} {Δ} {A} x∉r xFrΓ xFrΔ Π) origMax<base proofMax<base =
  -- Using same bounds pattern as δ-makeWellFormed-go
  cong (_+ 1) (h-subst2 ∙ h-subst ∙ ih)
  where
    x<base = ≤-trans (suc-≤-suc (≤-myMax-l x _)) origMax<base
    subMax<base = ≤-trans (suc-≤-suc (≤-myMax-r x _)) origMax<base
    subProof<base = ≤-trans (suc-≤-suc (≤-myMax-r _ _)) proofMax<base
    mwfR = makeWellFormed-go base k base≤k Π subMax<base subProof<base
    Π-wf = MWFResult.proof mwfR
    next = MWFResult.next mwfR
    x' = next
    k≤x' = MWFResult.k≤next mwfR
    ec = EigenposCond-from-lt-base x base Π-wf x<base (MWFResult.allEigen≥base mwfR)
    nc = NoEigenposInt-singleton-fresh x' Π-wf (MWFResult.maxEigen<next mwfR)
    Π-subst = substTokenToPosProof x (singleton-pos x') Π-wf ec nc
    Γ-unchanged = substCtx-id x (singleton-pos x') Γ xFrΓ
    Δ-unchanged = substCtx-id x (singleton-pos x') Δ xFrΔ
    pos-eq = substPos-insertToken-eq x x' r x∉r
    ctx-eq = substCtx-++ x (singleton-pos x') Γ [ A ^ insertToken x r ] ∙ cong₂ _,,_ Γ-unchanged (cong [_] (cong (A ^_) pos-eq))
    ih = height-makeWellFormed-go base k base≤k Π subMax<base subProof<base
    h-subst = height-substTokenToPosProof x (singleton-pos x') Π-wf ec nc
    h-subst2 = height-subst2 ctx-eq Δ-unchanged Π-subst

-- Main theorem: makeWellFormed preserves height
height-makeWellFormed : ∀ {Γ Δ} (Π : Γ ⊢ Δ) → height (makeWellFormed Π) ≡ height Π
height-makeWellFormed {Γ} {Δ} Π = height-makeWellFormed-go base base ≤-refl Π origMax<base proofMax<base
  where
    base = makeWellFormed-base Π
    origMax<base = suc-≤-suc (≤-myMax-l _ _)
    proofMax<base = suc-≤-suc (≤-myMax-r _ _)

-- =============================================================================
-- General eigenposition substitution
-- =============================================================================
-- Replaces token x with arbitrary position t in a proof,
-- given that maxEigenposToken Π < x (i.e., x is not an eigentoken of Π).
-- Returns the substituted proof with preserved height and δ.

substEigenposInProof : (x : Token) (t : Position) {Γ Δ : Ctx}
  → (Π : Γ ⊢ Δ)
  → maxEigenposToken Π < x
  → Σ (substCtx x t Γ ⊢ substCtx x t Δ)
      (λ Π' → (height Π' ≡ height Π) × (δ Π' ≡ δ Π))
substEigenposInProof x t {Γ} {Δ} Π wf = (Π-subst , h-pres , δ-pres)
  where
    -- Choose base above everything relevant
    innerMax1 = myMax (maxEigenposToken Π) (maxTokenProof Π)
    innerMax2 = myMax x (maxTokenPos t)
    base = suc (myMax innerMax1 innerMax2)

    -- Base conditions
    origMax<base : maxEigenposToken Π < base
    origMax<base = suc-≤-suc (≤-trans (≤-myMax-l (maxEigenposToken Π) (maxTokenProof Π)) (≤-myMax-l innerMax1 innerMax2))

    proofMax<base : maxTokenProof Π < base
    proofMax<base = suc-≤-suc (≤-trans (≤-myMax-r (maxEigenposToken Π) (maxTokenProof Π)) (≤-myMax-l innerMax1 innerMax2))

    x<base : x < base
    x<base = suc-≤-suc (≤-trans (≤-myMax-l x (maxTokenPos t)) (≤-myMax-r innerMax1 innerMax2))

    t<base : maxTokenPos t < base
    t<base = suc-≤-suc (≤-trans (≤-myMax-r x (maxTokenPos t)) (≤-myMax-r innerMax1 innerMax2))

    -- Rename eigentokens to be ≥ base
    mwfR = makeWellFormed-go base base ≤-refl Π origMax<base proofMax<base
    Π-wf = MWFResult.proof mwfR

    -- EigenposCond x Π-wf: x < base ≤ all eigentokens
    ec : EigenposCond x Π-wf
    ec = EigenposCond-from-lt-base x base Π-wf x<base (MWFResult.allEigen≥base mwfR)

    -- NoEigenposInt t Π-wf: maxTokenPos t < base ≤ all eigentokens
    nc : NoEigenposInt t Π-wf
    nc = NoEigenposInt-from-allGe t base Π-wf t<base (MWFResult.allEigen≥base mwfR)

    -- Apply substitution
    Π-subst = substTokenToPosProof x t Π-wf ec nc

    -- Height preservation: height(Π-subst) = height(Π-wf) = height(Π)
    h-pres : height Π-subst ≡ height Π
    h-pres = height-substTokenToPosProof x t Π-wf ec nc
           ∙ height-makeWellFormed-go base base ≤-refl Π origMax<base proofMax<base

    -- δ preservation: δ(Π-subst) = δ(Π-wf) = δ(Π)
    δ-pres : δ Π-subst ≡ δ Π
    δ-pres = δ-substTokenToPosProof x t Π-wf ec nc
           ∙ δ-makeWellFormed-go base base ≤-refl Π origMax<base proofMax<base
