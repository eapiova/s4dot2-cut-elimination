{-# OPTIONS --cubical --safe --lossy-unification #-}

-- Option 4: Restructured Mix Lemma following the reference proof structure
-- from references/Sequenti/2sequents.tex
--
-- Key insight: The reference proof uses induction on <h(Π), h(Π')> with NO mode switching.
-- Every non-base case recurses on subproofs with height decrease.
--
-- Cases:
-- 1. Left is Ax           → base case
-- 2. Right is Ax          → base case
-- 3. Left is structural   → recurse <Π_sub, Π'>
-- 4. Right is structural  → recurse <Π, Π'_sub>
-- 5. Left doesn't intro A to right → recurse <Π_sub, Π'>
-- 6. Right doesn't intro A to left → recurse <Π, Π'_sub>
-- 7. BOTH intro A (principal)      → special handling

module S4dot2.CutElimination.MixNew where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.Nat using (ℕ; suc; zero; _+_; max; snotz)
open import Cubical.Data.Nat.Properties using (maxComm)
open import Cubical.Data.Nat.Order using (_≤_; _<_; ≤-refl; ≤-trans; left-≤-max; right-≤-max)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Sigma using (_×_; _,_; fst; snd; Σ)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Relation.Nullary using (Dec; yes; no)
open import Cubical.Induction.WellFounded using (Acc; acc)
open import Cubical.Data.List using (List; _∷_; []; _++_; ++-assoc)
open import Cubical.Data.List.Properties using (++-unit-r)

-- Max inequality solver for degree bounds
open import S4dot2.Solver.Semilattice.Expression using (Expr; ∣_; ε∨; _∨ₑ_)
open import S4dot2.Solver.Semilattice.NatMax
open NatMaxSolver using (solve≤ℕ)
open import Cubical.Data.FinData using () renaming (zero to fzero; suc to fsuc)
open import Cubical.Data.Vec using () renaming (_∷_ to _∷v_; [] to []v)

open import S4dot2.Syntax hiding (_⊢_; _≢_)
open import S4dot2.System using (Ctx; _,,_; _⊢_; Ax; Cut; W⊢; ⊢W; C⊢; ⊢C; Exc⊢; ⊢Exc;
                                 ¬⊢; ⊢¬; ∧₁⊢; ∧₂⊢; ⊢∧; ∨⊢; ⊢∨₁; ⊢∨₂;
                                 ⇒⊢; ⊢⇒; □⊢; ⊢□; ♢⊢; ⊢♢;
                                 discretePFormula; structural)
open import S4dot2.CutElimination.Base hiding (Env; var; elm; solve; _++ₑ_; rem)
open import S4dot2.CutElimination.ProofSubst using (WellFormedProof; makeWellFormed; makeWellFormed-WellFormed; δ-makeWellFormed;
  maxEigenposToken; freshTokenForRename; freshTokenForRename-fresh; freshTokenForRename-eigenpos; freshTokenForRename-∉r;
  renameEigenpos-♢⊢-premise-gen; δ-renameEigenpos-♢⊢-premise-gen; height-renameEigenpos-♢⊢-premise-gen;
  WellFormed-renameEigenpos-♢⊢-premise-gen;
  renameEigenpos-⊢□-premise-gen; δ-renameEigenpos-⊢□-premise-gen; height-renameEigenpos-⊢□-premise-gen;
  WellFormed-renameEigenpos-⊢□-premise-gen;
  TokenFresh-split; substPos; substPos-insertToken-eq; substPos-insertToken-gen;
  substEigenposInProof; substCtx; substCtx-id; substCtx-++;
  height-makeWellFormed)
open import S4dot2.CutElimination.MixHelpers using (mkSingleTokenExt;
  lemma-removeAll-cons-eq; lemma-removeAll-head-eq; lemma-removeAll-cons-neq; lemma-removeAll-head-neq)
open import S4dot2.ListExt using (mem-++-l; mem-++-r)
open import S4dot2.CutElimination.Base using (mem-++-split)

-- Subset helper lemmas (defined locally to avoid importing CutElimination which imports Mix)
private
  -- removeAll produces a subset
  removeAll-⊆ : {A : PFormula} {Γ : Ctx} → (Γ - A) ⊆ Γ
  removeAll-⊆ y yIn = mem-removeAll-subset yIn

  -- Subset lemmas for combining with removeAll
  subset-remove-left : (Γ₁ Γ₂ : Ctx) (A : PFormula) → (Γ₁ ,, (Γ₂ - A)) ⊆ (Γ₁ ,, Γ₂)
  subset-remove-left Γ₁ Γ₂ A y yIn with mem-++-split {xs = Γ₁} yIn
  ... | inl yInΓ₁ = mem-++-l yInΓ₁
  ... | inr yInΓ₂-A = mem-++-r Γ₁ (removeAll-⊆ y yInΓ₂-A)

  subset-remove-right : (Δ₁ Δ₂ : Ctx) (A : PFormula) → ((Δ₁ - A) ,, Δ₂) ⊆ (Δ₁ ,, Δ₂)
  subset-remove-right Δ₁ Δ₂ A y yIn with mem-++-split {xs = Δ₁ - A} yIn
  ... | inl yInΔ₁-A = mem-++-l (removeAll-⊆ y yInΔ₁-A)
  ... | inr yInΔ₂ = mem-++-r Δ₁ yInΔ₂

  -- Principal case subset helpers:
  -- After Mix on subformula B, we need to weaken from goal contexts to mix result contexts.
  -- Mix on B gives: (Γ1 ,, [B]) ,, (Γ2 - B) ⊢ (Δ1 - B) ,, ([B] ,, Δ2)
  -- Goal: Γ1 ,, (Γ2 - A) ⊢ (Δ1 - A) ,, Δ2  where A ≠ B
  -- structural needs: goal ⊆ mix-result

  -- Antecedent: Γ1 ,, (Γ2 - A) ⊆ (Γ1 ,, [B]) ,, (Γ2 - B)
  -- Each y ∈ Γ1 goes to left; each y ∈ Γ2-A: if y=B then in [B], if y≠B then in Γ2-B
  principal-ant-sub : (Γ1 Γ2 : Ctx) (A B : PFormula)
    → (Γ1 ,, (Γ2 - A)) ⊆ ((Γ1 ,, [ B ]) ,, (Γ2 - B))
  principal-ant-sub Γ1 Γ2 A B y yIn with mem-++-split {xs = Γ1} yIn
  ... | inl yInΓ1 = mem-++-l (mem-++-l yInΓ1)
  ... | inr yInΓ2-A with discretePFormula y B
  ...   | yes y≡B = mem-++-l (mem-++-r Γ1 (subst (_∈ [ B ]) (sym y≡B) here))
  ...   | no y≢B = mem-++-r (Γ1 ,, [ B ]) (mem-removeAll (mem-removeAll-subset yInΓ2-A) (λ eq → y≢B (sym eq)))

  -- Succedent: (Δ1 - A) ,, Δ2 ⊆ (Δ1 - B) ,, ([B] ,, Δ2)
  -- Each y ∈ Δ1-A: if y=B then in [B], if y≠B then in Δ1-B; each y ∈ Δ2 goes to right
  principal-succ-sub : (Δ1 Δ2 : Ctx) (A B : PFormula)
    → ((Δ1 - A) ,, Δ2) ⊆ ((Δ1 - B) ,, ([ B ] ,, Δ2))
  principal-succ-sub Δ1 Δ2 A B y yIn with mem-++-split {xs = Δ1 - A} yIn
  ... | inl yInΔ1-A with discretePFormula y B
  ...   | yes y≡B = mem-++-r (Δ1 - B) (mem-++-l (subst (_∈ [ B ]) (sym y≡B) here))
  ...   | no y≢B = mem-++-l (mem-removeAll (mem-removeAll-subset yInΔ1-A) (λ eq → y≢B (sym eq)))
  principal-succ-sub Δ1 Δ2 A B y yIn | inr yInΔ2 = mem-++-r (Δ1 - B) (mem-++-r [ B ] yInΔ2)

  -- General contraction: (G ,, G') ⊆ G when G' ⊆ G
  contraction-++ˡ : {G G' : Ctx} → G' ⊆ G → (G ,, G') ⊆ G
  contraction-++ˡ {G} sub y yIn with mem-++-split {xs = G} yIn
  contraction-++ˡ {G} sub y yIn | inl yInG = yInG
  contraction-++ˡ {G} sub y yIn | inr yInG' = sub y yInG'

  -- General contraction: (G' ,, G) ⊆ G when G' ⊆ G
  contraction-++ʳ : {G G' : Ctx} → G' ⊆ G → (G' ,, G) ⊆ G
  contraction-++ʳ {G} sub y yIn with mem-++-split yIn
  contraction-++ʳ {G} sub y yIn | inl yInG' = sub y yInG'
  contraction-++ʳ {G} sub y yIn | inr yInG = yInG

  -- Removing singleton from left position: ((Γ1 ,, [ B ]) ,, Γ2) - B ⊆ Γ1 ,, Γ2
  removeAll-drop-singleton-l : (Γ1 Γ2 : Ctx) (B : PFormula)
    → (((Γ1 ,, [ B ]) ,, Γ2) - B) ⊆ (Γ1 ,, Γ2)
  removeAll-drop-singleton-l Γ1 Γ2 B y yIn with removeAll-mem yIn
  removeAll-drop-singleton-l Γ1 Γ2 B y yIn | (yIn' , neqB) with mem-++-split {xs = Γ1 ,, [ B ]} yIn'
  removeAll-drop-singleton-l Γ1 Γ2 B y yIn | (yIn' , neqB) | inl yInΓ1B with mem-++-split {xs = Γ1} yInΓ1B
  removeAll-drop-singleton-l Γ1 Γ2 B y yIn | (yIn' , neqB) | inl yInΓ1B | inl yInΓ1 = mem-++-l yInΓ1
  removeAll-drop-singleton-l Γ1 Γ2 B y yIn | (yIn' , neqB) | inl yInΓ1B | inr here = ⊥-rec (neqB refl)
  removeAll-drop-singleton-l Γ1 Γ2 B y yIn | (yIn' , neqB) | inl yInΓ1B | inr (there ())
  removeAll-drop-singleton-l Γ1 Γ2 B y yIn | (yIn' , neqB) | inr yInΓ2 = mem-++-r Γ1 yInΓ2

  -- Removing singleton from middle position: (Γ1 ,, ([ B ] ,, Γ2)) - B ⊆ Γ1 ,, Γ2
  removeAll-drop-singleton-r : (Γ1 Γ2 : Ctx) (B : PFormula)
    → ((Γ1 ,, ([ B ] ,, Γ2)) - B) ⊆ (Γ1 ,, Γ2)
  removeAll-drop-singleton-r Γ1 Γ2 B y yIn with removeAll-mem yIn
  removeAll-drop-singleton-r Γ1 Γ2 B y yIn | (yIn' , neqB) with mem-++-split {xs = Γ1} yIn'
  removeAll-drop-singleton-r Γ1 Γ2 B y yIn | (yIn' , neqB) | inl yInΓ1 = mem-++-l yInΓ1
  removeAll-drop-singleton-r Γ1 Γ2 B y yIn | (yIn' , neqB) | inr yInBΓ2 with mem-++-split {xs = [ B ]} yInBΓ2
  removeAll-drop-singleton-r Γ1 Γ2 B y yIn | (yIn' , neqB) | inr yInBΓ2 | inl here = ⊥-rec (neqB refl)
  removeAll-drop-singleton-r Γ1 Γ2 B y yIn | (yIn' , neqB) | inr yInBΓ2 | inl (there ())
  removeAll-drop-singleton-r Γ1 Γ2 B y yIn | (yIn' , neqB) | inr yInBΓ2 | inr yInΓ2 = mem-++-r Γ1 yInΓ2

  -- Combine two subsets into one: G1 ⊆ G → G2 ⊆ G → (G1 ,, G2) ⊆ G
  subset-concat : {G G1 G2 : Ctx} → G1 ⊆ G → G2 ⊆ G → (G1 ,, G2) ⊆ G
  subset-concat {G} sub1 sub2 y yIn with mem-++-split {xs = _} yIn
  subset-concat {G} sub1 sub2 y yIn | inl yIn1 = sub1 y yIn1
  subset-concat {G} sub1 sub2 y yIn | inr yIn2 = sub2 y yIn2

  -- Remove trailing singleton: (G ,, [ B ]) - B ⊆ G
  removeAll-append-singleton-⊆ : (G : Ctx) (B : PFormula) → ((G ,, [ B ]) - B) ⊆ G
  removeAll-append-singleton-⊆ G B y yIn with removeAll-mem yIn
  removeAll-append-singleton-⊆ G B y yIn | (yIn' , neqB) with mem-++-split {xs = G} yIn'
  removeAll-append-singleton-⊆ G B y yIn | (yIn' , neqB) | inl yInG = yInG
  removeAll-append-singleton-⊆ G B y yIn | (yIn' , neqB) | inr here = ⊥-rec (neqB refl)
  removeAll-append-singleton-⊆ G B y yIn | (yIn' , neqB) | inr (there ())

  -- Max inequality composed lemmas (replace ~50 manual ≤-trans chains)
  left-left-≤-max : ∀ {a b c : ℕ} → a ≤ max (max a b) c
  left-left-≤-max = ≤-trans left-≤-max left-≤-max

  right-left-≤-max : ∀ {a b c : ℕ} → b ≤ max (max a b) c
  right-left-≤-max = ≤-trans right-≤-max left-≤-max

  left-right-≤-max : ∀ {a b c : ℕ} → a ≤ max c (max a b)
  left-right-≤-max = ≤-trans left-≤-max right-≤-max

  right-right-≤-max : ∀ {a b c : ℕ} → b ≤ max c (max a b)
  right-right-≤-max = ≤-trans right-≤-max right-≤-max

-- Subset transitivity (inline definition)
subset-trans : ∀ {ℓ} {A : Type ℓ} {l1 l2 l3 : List A} → l1 ⊆ l2 → l2 ⊆ l3 → l1 ⊆ l3
subset-trans f g x xIn = g x (f x xIn)

-- Import solver
open import S4dot2.Solver.Subset hiding (_≢_)
open Solver discretePFormula hiding (removeAll-++)

-- =============================================================================
-- Classification of proofs relative to a cut formula A
-- =============================================================================

-- A left proof either:
-- 1. Is Ax
-- 2. Is structural (W⊢, ⊢W, C⊢, ⊢C, Exc⊢, ⊢Exc, Cut)
-- 3. Is a right-intro rule that introduces A to the right
-- 4. Is a right-intro rule that introduces some B ≠ A to the right
-- 5. Is a left-intro rule (never introduces to the right)

data LeftClass : Type where
  L-Ax       : LeftClass
  L-Struct   : LeftClass
  L-IntroA   : LeftClass  -- introduces A to the right (potential principal)
  L-IntroOther : LeftClass  -- introduces B ≠ A to the right
  L-LeftIntro : LeftClass  -- left-intro rule (doesn't introduce to right)

-- A right proof either:
-- 1. Is Ax
-- 2. Is structural
-- 3. Is a left-intro rule that introduces A to the left
-- 4. Is a left-intro rule that introduces some B ≠ A to the left
-- 5. Is a right-intro rule (never introduces to the left)

data RightClass : Type where
  R-Ax        : RightClass
  R-Struct    : RightClass
  R-IntroA    : RightClass  -- introduces A to the left (potential principal)
  R-IntroOther : RightClass  -- introduces B ≠ A to the left
  R-RightIntro : RightClass  -- right-intro rule (doesn't introduce to left)

-- =============================================================================
-- Helper: Get the formula introduced by a right-intro rule (if any)
-- =============================================================================

-- Returns the positioned formula introduced to the RIGHT by this proof (if any)
introducedRight : ∀ {Γ Δ} → Γ ⊢ Δ → Maybe PFormula
introducedRight (⊢¬ {A = A} {s = s} _) = just ((¬ A) ^ s)
introducedRight (⊢∧ {A = A} {s = s} {B = B} _ _) = just ((A ∧ B) ^ s)
introducedRight (⊢∨₁ {A = A} {s = s} {B = B} _) = just ((A ∨ B) ^ s)
introducedRight (⊢∨₂ {B = B} {s = s} {A = A} _) = just ((A ∨ B) ^ s)
introducedRight (⊢⇒ {A = A} {s = s} {B = B} _) = just ((A ⇒ B) ^ s)
introducedRight (⊢□ {_} {s} {_} {_} {A} _ _ _ _) = just ((□ A) ^ s)
introducedRight (⊢♢ {_} {A} {s} {_} {_} _) = just ((♢ A) ^ s)
introducedRight _ = nothing

-- Returns the positioned formula introduced to the LEFT by this proof (if any)
introducedLeft : ∀ {Γ Δ} → Γ ⊢ Δ → Maybe PFormula
introducedLeft (¬⊢ {A = A} {s = s} _) = just ((¬ A) ^ s)
introducedLeft (∧₁⊢ {A = A} {s = s} {B = B} _) = just ((A ∧ B) ^ s)
introducedLeft (∧₂⊢ {B = B} {s = s} {A = A} _) = just ((A ∧ B) ^ s)
introducedLeft (∨⊢ {A = A} {s = s} {B = B} _ _) = just ((A ∨ B) ^ s)
introducedLeft (⇒⊢ {B = B} {s = s} {A = A} _ _) = just ((A ⇒ B) ^ s)
introducedLeft (□⊢ {_} {A} {s} {_} {_} _) = just ((□ A) ^ s)
introducedLeft (♢⊢ {_} {s} {_} {_} {A} _ _ _ _) = just ((♢ A) ^ s)
introducedLeft _ = nothing

-- =============================================================================
-- Classify left proof relative to cut formula A
-- =============================================================================

classifyLeft : ∀ {Γ Δ} → (Π : Γ ⊢ Δ) → (A : PFormula) → LeftClass
classifyLeft Ax _ = L-Ax
-- Structural rules
classifyLeft (W⊢ _) _ = L-Struct
classifyLeft (⊢W _) _ = L-Struct
classifyLeft (C⊢ _) _ = L-Struct
classifyLeft (⊢C _) _ = L-Struct
classifyLeft (Exc⊢ _) _ = L-Struct
classifyLeft (⊢Exc _) _ = L-Struct
classifyLeft (Cut _ _) _ = L-Struct
-- Left-intro rules (don't introduce to the right)
classifyLeft (¬⊢ _) _ = L-LeftIntro
classifyLeft (∧₁⊢ _) _ = L-LeftIntro
classifyLeft (∧₂⊢ _) _ = L-LeftIntro
classifyLeft (∨⊢ _ _) _ = L-LeftIntro
classifyLeft (⇒⊢ _ _) _ = L-LeftIntro
classifyLeft (□⊢ _) _ = L-LeftIntro
classifyLeft (♢⊢ _ _ _ _) _ = L-LeftIntro
-- Right-intro rules (introduce to the right)
classifyLeft (⊢¬ {A = A'} {s = s'} _) A with discretePFormula A ((¬ A') ^ s')
... | yes _ = L-IntroA
... | no _  = L-IntroOther
classifyLeft (⊢∧ {A = A'} {s = s'} {B = B'} _ _) A with discretePFormula A ((A' ∧ B') ^ s')
... | yes _ = L-IntroA
... | no _  = L-IntroOther
classifyLeft (⊢∨₁ {A = A'} {s = s'} {B = B'} _) A with discretePFormula A ((A' ∨ B') ^ s')
... | yes _ = L-IntroA
... | no _  = L-IntroOther
classifyLeft (⊢∨₂ {B = B'} {s = s'} {A = A'} _) A with discretePFormula A ((A' ∨ B') ^ s')
... | yes _ = L-IntroA
... | no _  = L-IntroOther
classifyLeft (⊢⇒ {A = A'} {s = s'} {B = B'} _) A with discretePFormula A ((A' ⇒ B') ^ s')
... | yes _ = L-IntroA
... | no _  = L-IntroOther
classifyLeft (⊢□ {_} {s'} {_} {_} {A'} _ _ _ _) A with discretePFormula A ((□ A') ^ s')
... | yes _ = L-IntroA
... | no _  = L-IntroOther
classifyLeft (⊢♢ {_} {A'} {s'} {_} {_} _) A with discretePFormula A ((♢ A') ^ s')
... | yes _ = L-IntroA
... | no _  = L-IntroOther

-- =============================================================================
-- Classify right proof relative to cut formula A
-- =============================================================================

classifyRight : ∀ {Γ Δ} → (Π : Γ ⊢ Δ) → (A : PFormula) → RightClass
classifyRight Ax _ = R-Ax
-- Structural rules
classifyRight (W⊢ _) _ = R-Struct
classifyRight (⊢W _) _ = R-Struct
classifyRight (C⊢ _) _ = R-Struct
classifyRight (⊢C _) _ = R-Struct
classifyRight (Exc⊢ _) _ = R-Struct
classifyRight (⊢Exc _) _ = R-Struct
classifyRight (Cut _ _) _ = R-Struct
-- Right-intro rules (don't introduce to the left)
classifyRight (⊢¬ _) _ = R-RightIntro
classifyRight (⊢∧ _ _) _ = R-RightIntro
classifyRight (⊢∨₁ _) _ = R-RightIntro
classifyRight (⊢∨₂ _) _ = R-RightIntro
classifyRight (⊢⇒ _) _ = R-RightIntro
classifyRight (⊢□ _ _ _ _) _ = R-RightIntro
classifyRight (⊢♢ _) _ = R-RightIntro
-- Left-intro rules (introduce to the left)
classifyRight (¬⊢ {A = A'} {s = s'} _) A with discretePFormula A ((¬ A') ^ s')
... | yes _ = R-IntroA
... | no _  = R-IntroOther
classifyRight (∧₁⊢ {A = A'} {s = s'} {B = B'} _) A with discretePFormula A ((A' ∧ B') ^ s')
... | yes _ = R-IntroA
... | no _  = R-IntroOther
classifyRight (∧₂⊢ {B = B'} {s = s'} {A = A'} _) A with discretePFormula A ((A' ∧ B') ^ s')
... | yes _ = R-IntroA
... | no _  = R-IntroOther
classifyRight (∨⊢ {A = A'} {s = s'} {B = B'} _ _) A with discretePFormula A ((A' ∨ B') ^ s')
... | yes _ = R-IntroA
... | no _  = R-IntroOther
classifyRight (⇒⊢ {B = B'} {s = s'} {A = A'} _ _) A with discretePFormula A ((A' ⇒ B') ^ s')
... | yes _ = R-IntroA
... | no _  = R-IntroOther
classifyRight (□⊢ {_} {A'} {s'} {_} {_} _) A with discretePFormula A ((□ A') ^ s')
... | yes _ = R-IntroA
... | no _  = R-IntroOther
classifyRight (♢⊢ {_} {s'} {_} {_} {A'} _ _ _ _) A with discretePFormula A ((♢ A') ^ s')
... | yes _ = R-IntroA
... | no _  = R-IntroOther

-- =============================================================================
-- Type alias for Mix function type
-- =============================================================================

MixFn : Type
MixFn = ∀ {n} {Γ Δ Γ' Δ' : Ctx} {A : Formula} {s : Position}
      → degree A ≡ n
      → (Π : Γ ⊢ Δ)
      → (Π' : Γ' ⊢ Δ')
      → (wfp : WellFormedProof Π)
      → (wfp' : WellFormedProof Π')
      → (acc : Acc _<Lex_ (n , mixHeight Π Π'))
      → Σ (Γ ,, Γ' - (A ^ s) ⊢ Δ - (A ^ s) ,, Δ') (λ p → δ p ≤ max (δ Π) (δ Π'))

-- =============================================================================
-- The Mix function - skeleton showing structure
-- =============================================================================
--
-- Key insight: NO mode switching! Every non-base case recurses on subproofs
-- with strict height decrease.
--
-- This is a placeholder showing the intended structure.
-- The full implementation follows the existing Mix.agda pattern but
-- avoids the catch-all delegation that causes mode-switching cycles.

handleNegNoEq :
  ∀ {n Γ_sub B t Δ_sub Γ' Δ' A s}
  → (degEq : degree A ≡ n)
  → (Π_sub : Γ_sub ,, [ B ^ t ] ⊢ Δ_sub)
  → (Π' : Γ' ⊢ Δ')
  → WellFormedProof (⊢¬ Π_sub)
  → WellFormedProof Π'
  → (∀ m' → m' <Lex (n , mixHeight (⊢¬ Π_sub) Π') → Acc _<Lex_ m')
  → (A ^ s) ≢ ((¬ B) ^ t)
  → Σ (Γ_sub ,, (Γ' - (A ^ s)) ⊢ ([ (¬ B) ^ t ] ,, (Δ_sub - (A ^ s))) ,, Δ')
      (λ p → δ p ≤ max (δ (⊢¬ Π_sub)) (δ Π'))

handleDisj1NoEq :
  ∀ {n Γ_sub B t Δ_sub C Γ' Δ' A s}
  → (degEq : degree A ≡ n)
  → (Π_sub : Γ_sub ⊢ [ B ^ t ] ,, Δ_sub)
  → (Π' : Γ' ⊢ Δ')
  → WellFormedProof (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)
  → WellFormedProof Π'
  → (∀ m' → m' <Lex (n , mixHeight (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) Π') → Acc _<Lex_ m')
  → (A ^ s) ≢ ((B ∨ C) ^ t)
  → Σ (Γ_sub ,, (Γ' - (A ^ s)) ⊢ ([ (B ∨ C) ^ t ] ,, (Δ_sub - (A ^ s))) ,, Δ')
      (λ p → δ p ≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ Π'))

handleDisj2NoEq :
  ∀ {n Γ_sub C t Δ_sub B Γ' Δ' A s}
  → (degEq : degree A ≡ n)
  → (Π_sub : Γ_sub ⊢ [ C ^ t ] ,, Δ_sub)
  → (Π' : Γ' ⊢ Δ')
  → WellFormedProof (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)
  → WellFormedProof Π'
  → (∀ m' → m' <Lex (n , mixHeight (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) Π') → Acc _<Lex_ m')
  → (A ^ s) ≢ ((B ∨ C) ^ t)
  → Σ (Γ_sub ,, (Γ' - (A ^ s)) ⊢ ([ (B ∨ C) ^ t ] ,, (Δ_sub - (A ^ s))) ,, Δ')
      (λ p → δ p ≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ Π'))

handleDiaNoEq :
  ∀ {n Γ_sub B_l r_l t_l Δ_sub Γ' Δ' A s}
  → (degEq : degree A ≡ n)
  → (Π_sub : Γ_sub ⊢ [ B_l ^ (r_l ∘ t_l) ] ,, Δ_sub)
  → (Π' : Γ' ⊢ Δ')
  → WellFormedProof (⊢♢ {Γ = Γ_sub} {A = B_l} {s = r_l} {t = t_l} {Δ = Δ_sub} Π_sub)
  → WellFormedProof Π'
  → (∀ m' → m' <Lex (n , mixHeight (⊢♢ Π_sub) Π') → Acc _<Lex_ m')
  → (A ^ s) ≢ ((♢ B_l) ^ r_l)
  → Σ (Γ_sub ,, (Γ' - (A ^ s)) ⊢ ([ (♢ B_l) ^ r_l ] ,, (Δ_sub - (A ^ s))) ,, Δ')
      (λ p → δ p ≤ max (δ (⊢♢ Π_sub)) (δ Π'))

handleConjNoEq :
  ∀ {n Γ_sub₁ Γ_sub₂ B_l C_l t Δ_sub₁ Δ_sub₂ Γ' Δ' A s}
  → (degEq : degree A ≡ n)
  → (Π₁ : Γ_sub₁ ⊢ [ B_l ^ t ] ,, Δ_sub₁)
  → (Π₂ : Γ_sub₂ ⊢ [ C_l ^ t ] ,, Δ_sub₂)
  → (Π' : Γ' ⊢ Δ')
  → WellFormedProof (⊢∧ {Γ₁ = Γ_sub₁} {A = B_l} {s = t} {Δ₁ = Δ_sub₁} {Γ₂ = Γ_sub₂} {B = C_l} {Δ₂ = Δ_sub₂} Π₁ Π₂)
  → WellFormedProof Π'
  → (∀ m' → m' <Lex (n , mixHeight (⊢∧ Π₁ Π₂) Π') → Acc _<Lex_ m')
  → (A ^ s) ≢ ((B_l ∧ C_l) ^ t)
  → Σ ((Γ_sub₁ ,, Γ_sub₂) ,, (Γ' - (A ^ s)) ⊢ [ (B_l ∧ C_l) ^ t ] ,, ((Δ_sub₁ - (A ^ s)) ,, (Δ_sub₂ - (A ^ s))) ,, Δ')
      (λ p → δ p ≤ max (δ (⊢∧ Π₁ Π₂)) (δ Π'))

handleImplNoEq :
  ∀ {n Γ_sub B_l t C_l Δ_sub Γ' Δ' A s}
  → (degEq : degree A ≡ n)
  → (Π_sub : Γ_sub ,, [ B_l ^ t ] ⊢ [ C_l ^ t ] ,, Δ_sub)
  → (Π' : Γ' ⊢ Δ')
  → WellFormedProof (⊢⇒ {Γ = Γ_sub} {A = B_l} {s = t} {B = C_l} {Δ = Δ_sub} Π_sub)
  → WellFormedProof Π'
  → (∀ m' → m' <Lex (n , mixHeight (⊢⇒ Π_sub) Π') → Acc _<Lex_ m')
  → (A ^ s) ≢ ((B_l ⇒ C_l) ^ t)
  → Σ (Γ_sub ,, (Γ' - (A ^ s)) ⊢ (([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ')
      (λ p → δ p ≤ max (δ (⊢⇒ Π_sub)) (δ Π'))

handleBoxNoEq :
  ∀ {n x_l r_l Γ_sub Δ_sub B_l Γ' Δ' A s}
  → (degEq : degree A ≡ n)
  → (ext_l : x_l ∉Pos r_l)
  → (freshΓ_l : TokenFresh x_l Γ_sub)
  → (freshΔ_l : TokenFresh x_l Δ_sub)
  → (Π_sub : Γ_sub ⊢ [ B_l ^ insertToken x_l r_l ] ,, Δ_sub)
  → (Π' : Γ' ⊢ Δ')
  → WellFormedProof (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)
  → WellFormedProof Π'
  → (∀ m' → m' <Lex (n , mixHeight (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π') → Acc _<Lex_ m')
  → (A ^ s) ≢ ((□ B_l) ^ r_l)
  → Σ (Γ_sub ,, (Γ' - (A ^ s)) ⊢ (([ (□ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, Δ')
      (λ p → δ p ≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ Π'))

Mix : MixFn

-- =============================================================================
-- Case 1: Left is Ax
-- =============================================================================

-- Ax {B} {t} : [B^t] ⊢ [B^t]
-- Goal: ([B^t] ,, Γ') - A ⊢ ([B^t] - A) ,, Δ'
Mix {Γ = .([ B ^ t ])} {Δ = .([ B ^ t ])} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq (Ax {B} {t}) Π' wfp wfp' _ with discretePFormula (A ^ s) (B ^ t)
-- Subcase: A = B (cut formula is the axiom formula)
-- Goal simplifies using Π' with structural rules
... | yes eq =
    let
        -- Γ' ⊆ [A] ,, (Γ' - A)
        sub_left_A : Γ' ⊆ ([ A ^ s ] ,, (Γ' - (A ^ s)))
        sub_left_A = subset-elem-or-removeAll

        sub_left : Γ' ⊆ ([ B ^ t ] ,, (Γ' - (A ^ s)))
        sub_left = subst (λ pf → Γ' ⊆ ([ pf ] ,, (Γ' - (A ^ s)))) eq sub_left_A

        p_struct : [ B ^ t ] ,, (Γ' - (A ^ s)) ⊢ Δ'
        p_struct = structural sub_left subset-refl Π'

        d_final : δ p_struct ≤ max (δ (Ax {B} {t})) (δ Π')
        d_final = subst (λ k → k ≤ max 0 (δ Π'))
                        (sym (structural-preserves-δ sub_left subset-refl Π'))
                        (right-≤-max {δ Π'} {0})
    in (p_struct , d_final)

-- Subcase: A ≠ B
... | no neq =
    let
        env : Env
        env = (Γ' ∷ Δ' ∷ []) , (A ^ s ∷ B ^ t ∷ [])

        sub_left : [ B ^ t ] ⊆ ([ B ^ t ] ,, (Γ' - (A ^ s)))
        sub_left = solve (elm 1) (elm 1 ++ₑ rem (var 0) 0) env {refl}

        sub_right : [ B ^ t ] ⊆ ([ B ^ t ] ,, Δ')
        sub_right = solve (elm 1) (elm 1 ++ₑ var 1) env {refl}

        p_weak : [ B ^ t ] ,, (Γ' - (A ^ s)) ⊢ [ B ^ t ] ,, Δ'
        p_weak = structural sub_left sub_right (Ax {B} {t})

        d_final : δ p_weak ≤ max (δ (Ax {B} {t})) (δ Π')
        d_final = subst (λ k → k ≤ max 0 (δ Π'))
                        (sym (structural-preserves-δ sub_left sub_right (Ax {B} {t})))
                        z≤
    in (p_weak , d_final)

-- =============================================================================
-- Case 2: Right is Ax
-- =============================================================================

Mix {Γ = Γ} {Δ = Δ} {Γ' = .([ B ^ t ])} {Δ' = .([ B ^ t ])} {A = A} {s = s}
    degEq Π (Ax {B} {t}) wfp wfp' _ with discretePFormula (A ^ s) (B ^ t)
-- Subcase: A = B
... | yes eq =
    let
        sub_right_A : Δ ⊆ ((Δ - (A ^ s)) ,, [ A ^ s ])
        sub_right_A = subset-removeAll-or-elem

        sub_right : Δ ⊆ ((Δ - (A ^ s)) ,, [ B ^ t ])
        sub_right = subst (λ pf → Δ ⊆ ((Δ - (A ^ s)) ,, [ pf ])) eq sub_right_A

        p_struct : Γ ⊢ (Δ - (A ^ s)) ,, [ B ^ t ]
        p_struct = structural subset-refl sub_right Π

        p_final : Γ ,, [] ⊢ (Δ - (A ^ s)) ,, [ B ^ t ]
        p_final = subst (λ G → G ⊢ (Δ - (A ^ s)) ,, [ B ^ t ]) (sym (++-unit-r Γ)) p_struct

        d_final : δ p_final ≤ max (δ Π) (δ (Ax {B} {t}))
        d_final = subst (λ k → k ≤ max (δ Π) 0)
                        (sym (subst-preserves-δ-ctx (sym (++-unit-r Γ)) p_struct ∙
                              structural-preserves-δ subset-refl sub_right Π))
                        (left-≤-max {n = 0})
    in (p_final , d_final)

-- Subcase: A ≠ B
... | no neq =
    let
        sub_left : [ B ^ t ] ⊆ (Γ ,, [ B ^ t ])
        sub_left = solve (elm 0) (var 0 ++ₑ elm 0) ((Γ ∷ []) , (B ^ t ∷ [])) {refl}

        sub_right : [ B ^ t ] ⊆ ((Δ - (A ^ s)) ,, [ B ^ t ])
        sub_right = solve (elm 0) (var 0 ++ₑ elm 0) (((Δ - (A ^ s)) ∷ []) , (B ^ t ∷ [])) {refl}

        p_weak : Γ ,, [ B ^ t ] ⊢ (Δ - (A ^ s)) ,, [ B ^ t ]
        p_weak = structural sub_left sub_right (Ax {B} {t})

        d_final : δ p_weak ≤ max (δ Π) (δ (Ax {B} {t}))
        d_final = subst (λ k → k ≤ max (δ Π) 0)
                        (sym (structural-preserves-δ sub_left sub_right (Ax {B} {t})))
                        z≤
    in (p_weak , d_final)

-- =============================================================================
-- Case 3: Left is W⊢ (structural - left weakening)
-- =============================================================================

Mix {n = n} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq (W⊢ {Γ₁} {Δ₁} {B} {t} Π) Π' wfp wfp' (acc accRec) =
    let
        h-dec = mixHeight-dec-l (W⊢ Π) Π Π' (height-subproof-1 Π)
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {n = n} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s} degEq Π Π' wfp wfp' acc'

        -- mix : Γ₁ ,, (Γ' - A) ⊢ (Δ₁ - A) ,, Δ'
        -- Goal : (Γ₁ ,, [B]) ,, (Γ' - A) ⊢ (Δ₁ - A) ,, Δ'
        -- solver: Γ₁ ++ (Γ' - A) ⊆ Γ₁ ++ [B] ++ (Γ' - A)
        sub : (Γ₁ ++ (Γ' - (A ^ s))) ⊆ (Γ₁ ++ [ B ^ t ] ++ (Γ' - (A ^ s)))
        sub = solve (var 0 ++ₑ var 1) (var 0 ++ₑ elm 0 ++ₑ var 1)
                    ((Γ₁ ∷ (Γ' - (A ^ s)) ∷ []) , (B ^ t ∷ [])) {refl}

        p_temp = structural sub subset-refl mix

        -- Transport to correct associativity
        eqAssoc : (Γ₁ ,, ([ B ^ t ] ,, (Γ' - (A ^ s)))) ≡ ((Γ₁ ,, [ B ^ t ]) ,, (Γ' - (A ^ s)))
        eqAssoc = sym (++-assoc Γ₁ [ B ^ t ] (Γ' - (A ^ s)))

        p' = subst (λ G → G ⊢ Δ₁ - (A ^ s) ,, Δ') eqAssoc p_temp

        d_p_temp : δ p_temp ≡ δ mix
        d_p_temp = structural-preserves-δ sub subset-refl mix

        d_p' : δ p' ≡ δ p_temp
        d_p' = subst-preserves-δ-ctx eqAssoc p_temp

        -- dmix : δ mix ≤ max (δ Π) (δ Π')
        -- Since δ (W⊢ Π) = δ Π, we have max (δ (W⊢ Π)) (δ Π') = max (δ Π) (δ Π')
        d_final : δ p' ≤ max (δ (W⊢ Π)) (δ Π')
        d_final = subst (λ k → k ≤ max (δ Π) (δ Π')) (sym (d_p' ∙ d_p_temp)) dmix
    in (p' , d_final)

-- =============================================================================
-- Case 4: Left is ⊢W (structural - right weakening)
-- =============================================================================

-- ⊢W Π : Γ₁ ⊢ [B^t] ,, Δ_sub where Π : Γ₁ ⊢ Δ_sub
-- Goal: Γ₁ ,, (Γ' - A) ⊢ (([B^t] ,, Δ_sub) - A) ,, Δ'
-- IH gives: mix : Γ₁ ,, (Γ' - A) ⊢ (Δ_sub - A) ,, Δ'
Mix {n = n} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq (⊢W {Γ₁} {Δ_sub} {B} {t} Π) Π' wfp wfp' (acc accRec) =
    let
        h-dec = mixHeight-dec-l (⊢W Π) Π Π' (height-subproof-1 Π)
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {n = n} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s} degEq Π Π' wfp wfp' acc'

        -- mix : Γ₁ ,, (Γ' - A) ⊢ (Δ_sub - A) ,, Δ'
        -- Goal: Γ₁ ,, (Γ' - A) ⊢ (([B^t] ,, Δ_sub) - A) ,, Δ'
        -- solver: (Δ_sub - A) ++ Δ' ⊆ ([B] ++ Δ_sub) - A ++ Δ'
        sub_right : ((Δ_sub - (A ^ s)) ,, Δ') ⊆ (([ B ^ t ] ,, Δ_sub) - (A ^ s) ,, Δ')
        sub_right = solve (rem (var 0) 0 ++ₑ var 1) (rem (elm 1 ++ₑ var 0) 0 ++ₑ var 1)
                          ((Δ_sub ∷ Δ' ∷ []) , (A ^ s ∷ B ^ t ∷ [])) {refl}

        p' = structural subset-refl sub_right mix

        -- δ (⊢W Π) = δ Π, so max (δ (⊢W Π)) (δ Π') = max (δ Π) (δ Π')
        d_p' = structural-preserves-δ subset-refl sub_right mix
        d_final : δ p' ≤ max (δ (⊢W Π)) (δ Π')
        d_final = subst (λ k → k ≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- =============================================================================
-- Case 5: Left is C⊢ (structural - left contraction)
-- =============================================================================

-- C⊢ Π : Γ₁ ,, [B^t] ⊢ Δ₁  where Π : (Γ₁ ,, [B^t]) ,, [B^t] ⊢ Δ₁
-- Goal: (Γ₁ ,, [B^t]) ,, (Γ' - A) ⊢ (Δ₁ - A) ,, Δ'
Mix {n = n} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq (C⊢ {Γ = Γ₁} {A = B} {s = t} {Δ = Δ₁} Π) Π' wfp wfp' (acc accRec) =
    let
        h-dec = mixHeight-dec-l (C⊢ Π) Π Π' (height-subproof-1 Π)
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {n = n} {Γ = (Γ₁ ,, [ B ^ t ]) ,, [ B ^ t ]} {Δ = Δ₁} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s} degEq Π Π' wfp wfp' acc'

        -- solver: Γ₁ ++ [B] ++ [B] ++ (Γ' - A) ⊆ Γ₁ ++ [B] ++ (Γ' - A)
        sub : (Γ₁ ++ [ B ^ t ] ++ [ B ^ t ] ++ (Γ' - (A ^ s))) ⊆ (Γ₁ ++ [ B ^ t ] ++ (Γ' - (A ^ s)))
        sub = solve (var 0 ++ₑ elm 0 ++ₑ elm 0 ++ₑ var 1) (var 0 ++ₑ elm 0 ++ₑ var 1)
                    ((Γ₁ ∷ (Γ' - (A ^ s)) ∷ []) , (B ^ t ∷ [])) {refl}

        -- mix has type ((Γ₁ ,, [ B ]) ,, [ B ]) ,, (Γ' - A) ⊢ ...
        -- Need to reassociate
        eqAssoc1 : ((Γ₁ ,, [ B ^ t ]) ,, [ B ^ t ]) ≡ (Γ₁ ,, ([ B ^ t ] ,, [ B ^ t ]))
        eqAssoc1 = ++-assoc Γ₁ [ B ^ t ] [ B ^ t ]

        eqAssoc2 : ((Γ₁ ,, ([ B ^ t ] ,, [ B ^ t ])) ,, (Γ' - (A ^ s))) ≡ (Γ₁ ,, (([ B ^ t ] ,, [ B ^ t ]) ,, (Γ' - (A ^ s))))
        eqAssoc2 = ++-assoc Γ₁ ([ B ^ t ] ,, [ B ^ t ]) (Γ' - (A ^ s))

        eqTotal : (((Γ₁ ,, [ B ^ t ]) ,, [ B ^ t ]) ,, (Γ' - (A ^ s))) ≡ (Γ₁ ,, (([ B ^ t ] ,, [ B ^ t ]) ,, (Γ' - (A ^ s))))
        eqTotal = cong (λ G → G ,, (Γ' - (A ^ s))) eqAssoc1 ∙ eqAssoc2

        mix_assoc = subst (λ G → G ⊢ (Δ₁ - (A ^ s)) ,, Δ') eqTotal mix

        p_temp = structural sub subset-refl mix_assoc

        -- p_temp : Γ₁ ,, [ B ] ,, (Γ' - A) ⊢ ...
        -- Goal : (Γ₁ ,, [ B ]) ,, (Γ' - A) ⊢ ...
        eqAssocBack : (Γ₁ ,, ([ B ^ t ] ,, (Γ' - (A ^ s)))) ≡ ((Γ₁ ,, [ B ^ t ]) ,, (Γ' - (A ^ s)))
        eqAssocBack = sym (++-assoc Γ₁ [ B ^ t ] (Γ' - (A ^ s)))

        p' = subst (λ G → G ⊢ (Δ₁ - (A ^ s)) ,, Δ') eqAssocBack p_temp

        d_p_temp : δ p_temp ≡ δ mix
        d_p_temp = structural-preserves-δ sub subset-refl mix_assoc ∙ subst-preserves-δ-ctx eqTotal mix

        d_p' : δ p' ≡ δ p_temp
        d_p' = subst-preserves-δ-ctx eqAssocBack p_temp

        -- dmix : δ mix ≤ max (δ Π) (δ Π'), and δ (C⊢ Π) = δ Π
        d_final : δ p' ≤ max (δ (C⊢ Π)) (δ Π')
        d_final = subst (λ k → k ≤ max (δ Π) (δ Π')) (sym (d_p' ∙ d_p_temp)) dmix
    in (p' , d_final)

-- =============================================================================
-- Case 6: Left is ⊢C (structural - right contraction)
-- =============================================================================

-- ⊢C Π : Γ₁ ⊢ [B^t] ,, Δ_sub  where Π : Γ₁ ⊢ [B^t] ,, [B^t] ,, Δ_sub
Mix {n = n} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq (⊢C {Γ₁} {B} {t} {Δ_sub} Π) Π' wfp wfp' (acc accRec) =
    let
        h-dec = mixHeight-dec-l (⊢C Π) Π Π' (height-subproof-1 Π)
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {n = n} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s} degEq Π Π' wfp wfp' acc'

        -- mix : Γ₁ ,, (Γ' - A) ⊢ ([B^t] ,, [B^t] ,, Δ_sub - A) ,, Δ'
        -- Goal: Γ₁ ,, (Γ' - A) ⊢ ([B^t] ,, Δ_sub - A) ,, Δ'
        sub_right : (([ B ^ t ] ,, [ B ^ t ] ,, Δ_sub) - (A ^ s) ,, Δ') ⊆ (([ B ^ t ] ,, Δ_sub) - (A ^ s) ,, Δ')
        sub_right = solve (rem (elm 1 ++ₑ elm 1 ++ₑ var 0) 0 ++ₑ var 1) (rem (elm 1 ++ₑ var 0) 0 ++ₑ var 1)
                          ((Δ_sub ∷ Δ' ∷ []) , (A ^ s ∷ B ^ t ∷ [])) {refl}

        p' = structural subset-refl sub_right mix
        d_p' = structural-preserves-δ subset-refl sub_right mix

        d_final : δ p' ≤ max (δ (⊢C Π)) (δ Π')
        d_final = subst (λ k → k ≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- =============================================================================
-- Case 7: Left is Exc⊢ (structural - left exchange)
-- =============================================================================

-- Exc⊢ Π : ((Γ₁ ,, [C]) ,, [B]) ,, Γ₂ ⊢ Δ_sub  where Π : ((Γ₁ ,, [B]) ,, [C]) ,, Γ₂ ⊢ Δ_sub
Mix {n = n} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq theProof@(Exc⊢ {Γ₁} {B} {t} {C} {r} {Γ₂} {Δ_sub} Π) Π' wfp wfp' (acc accRec) =
    let
        h-dec = mixHeight-dec-l theProof Π Π' (height-subproof-1 Π)
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {n = n} {Γ = (((Γ₁ ,, [ B ^ t ]) ,, [ C ^ r ]) ,, Γ₂)} {Δ = Δ_sub} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s} degEq Π Π' wfp wfp' acc'

        eq1 : ((((Γ₁ ,, [ B ^ t ]) ,, [ C ^ r ]) ,, Γ₂) ,, (Γ' - (A ^ s))) ≡ (((Γ₁ ,, [ B ^ t ]) ,, [ C ^ r ]) ,, (Γ₂ ,, (Γ' - (A ^ s))))
        eq1 = ++-assoc ((Γ₁ ,, [ B ^ t ]) ,, [ C ^ r ]) Γ₂ (Γ' - (A ^ s))

        mix_assoc = subst (λ G → G ⊢ (Δ_sub - (A ^ s)) ,, Δ') eq1 mix

        p_swapped = Exc⊢ {Γ₁} {B} {t} {C} {r} {Γ₂ ,, (Γ' - (A ^ s))} {Δ_sub - (A ^ s) ,, Δ'} mix_assoc

        eq2 : (((Γ₁ ,, [ C ^ r ]) ,, [ B ^ t ]) ,, (Γ₂ ,, (Γ' - (A ^ s)))) ≡ ((((Γ₁ ,, [ C ^ r ]) ,, [ B ^ t ]) ,, Γ₂) ,, (Γ' - (A ^ s)))
        eq2 = sym (++-assoc ((Γ₁ ,, [ C ^ r ]) ,, [ B ^ t ]) Γ₂ (Γ' - (A ^ s)))

        p' = subst (λ G → G ⊢ (Δ_sub - (A ^ s)) ,, Δ') eq2 p_swapped

        d_p_swapped : δ p_swapped ≡ δ mix
        d_p_swapped = subst-preserves-δ-ctx eq1 mix

        d_p' : δ p' ≡ δ p_swapped
        d_p' = subst-preserves-δ-ctx eq2 p_swapped

        d_final : δ p' ≤ max (δ theProof) (δ Π')
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym (d_p' ∙ d_p_swapped)) dmix
    in (p' , d_final)

-- =============================================================================
-- Case 8: Left is ⊢Exc (structural - right exchange)
-- =============================================================================

-- ⊢Exc Π : Γ_sub ⊢ ((Δ₁ ,, [C]) ,, [B]) ,, Δ₂  where Π : Γ_sub ⊢ ((Δ₁ ,, [B]) ,, [C]) ,, Δ₂
Mix {n = n} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq theProof@(⊢Exc {Γ_sub} {Δ₁} {B} {t} {C} {r} {Δ₂} Π) Π' wfp wfp' (acc accRec) =
    let
        h-dec = mixHeight-dec-l theProof Π Π' (height-subproof-1 Π)
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {n = n} {Γ = Γ_sub} {Δ = (((Δ₁ ,, [ B ^ t ]) ,, [ C ^ r ]) ,, Δ₂)} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s} degEq Π Π' wfp wfp' acc'

        -- Use solver-style approach: prove via structural
        sub_right : (((((Δ₁ ,, [ B ^ t ]) ,, [ C ^ r ]) ,, Δ₂) - (A ^ s)) ,, Δ') ⊆ (((((Δ₁ ,, [ C ^ r ]) ,, [ B ^ t ]) ,, Δ₂) - (A ^ s)) ,, Δ')
        sub_right = solve (rem (((var 0 ++ₑ elm 1) ++ₑ elm 2) ++ₑ var 1) 0 ++ₑ var 2)
                          (rem (((var 0 ++ₑ elm 2) ++ₑ elm 1) ++ₑ var 1) 0 ++ₑ var 2)
                          ((Δ₁ ∷ Δ₂ ∷ Δ' ∷ []) , (A ^ s ∷ B ^ t ∷ C ^ r ∷ [])) {refl}

        p' = structural subset-refl sub_right mix

        d_p' : δ p' ≡ δ mix
        d_p' = structural-preserves-δ subset-refl sub_right mix

        d_final : δ p' ≤ max (δ theProof) (δ Π')
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- =============================================================================
-- Right structural cases: when Π' is structural
-- =============================================================================

-- Case 9: Right is W⊢ (structural - left weakening on right proof)
Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = .(Γ₁' ,, [ B ^ t ])} {Δ' = Δ₁'} {A = A} {s = s}
    degEq Π (W⊢ {Γ₁'} {.Δ₁'} {B} {t} Π') wfp wfp' (acc accRec) =
    let
        h-dec = mixHeight-dec-r Π (W⊢ Π') Π' (height-subproof-1 Π')
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = Γ₁'} {Δ' = Δ₁'} {A = A} {s = s} degEq Π Π' wfp wfp' acc'

        sub_left : (Γ ,, (Γ₁' - (A ^ s))) ⊆ (Γ ,, ((Γ₁' ,, [ B ^ t ]) - (A ^ s)))
        sub_left = solve (var 0 ++ₑ rem (var 1) 0) (var 0 ++ₑ rem (var 1 ++ₑ elm 1) 0)
                         ((Γ ∷ Γ₁' ∷ []) , (A ^ s ∷ B ^ t ∷ [])) {refl}

        p' = structural sub_left subset-refl mix
        d_p' = structural-preserves-δ sub_left subset-refl mix

        d_final : δ p' ≤ max (δ Π) (δ (W⊢ Π'))
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- Case 10: Right is ⊢W (structural - right weakening on right proof)
Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = Γ₁'} {Δ' = .([ B ^ t ] ,, Δ_sub)} {A = A} {s = s}
    degEq Π (⊢W {.Γ₁'} {Δ_sub} {B} {t} Π') wfp wfp' (acc accRec) =
    let
        h-dec = mixHeight-dec-r Π (⊢W Π') Π' (height-subproof-1 Π')
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = Γ₁'} {Δ' = Δ_sub} {A = A} {s = s} degEq Π Π' wfp wfp' acc'

        sub_right : ((Δ - (A ^ s)) ,, Δ_sub) ⊆ ((Δ - (A ^ s)) ,, ([ B ^ t ] ,, Δ_sub))
        sub_right = solve (rem (var 0) 0 ++ₑ var 1) (rem (var 0) 0 ++ₑ elm 1 ++ₑ var 1)
                          ((Δ ∷ Δ_sub ∷ []) , (A ^ s ∷ B ^ t ∷ [])) {refl}

        p' = structural subset-refl sub_right mix
        d_p' = structural-preserves-δ subset-refl sub_right mix

        d_final : δ p' ≤ max (δ Π) (δ (⊢W Π'))
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- Case 11: Right is C⊢ (structural - left contraction on right proof)
-- Π' : (Γ1 ,, [B]) ,, [B] ⊢ Δ1
-- C⊢ Π' : Γ1 ,, [B] ⊢ Δ1
-- IH: mix : Γ ,, ((Γ1 ,, [B] ,, [B]) - A) ⊢ (Δ - A) ,, Δ1
-- Goal: Γ ,, ((Γ1 ,, [B]) - A) ⊢ (Δ - A) ,, Δ1
-- Key: Γ ,, ((Γ1 ,, [B] ,, [B]) - A) ⊆ Γ ,, ((Γ1 ,, [B]) - A) always holds
Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = .(Γ1 ,, [ B ^ t ])} {Δ' = Δ1} {A = A} {s = s}
    degEq Π theProof@(C⊢ {Γ1} {B} {t} {Δ1} Π') wfp wfp' (acc accRec) =
    let
        h-dec = mixHeight-dec-r Π theProof Π' (height-subproof-1 Π')
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = ((Γ1 ,, [ B ^ t ]) ,, [ B ^ t ])} {Δ' = Δ1} {A = A} {s = s} degEq Π Π' wfp wfp' acc'

        sub_left : (Γ ,, (((Γ1 ,, [ B ^ t ]) ,, [ B ^ t ]) - (A ^ s))) ⊆ (Γ ,, ((Γ1 ,, [ B ^ t ]) - (A ^ s)))
        sub_left = solve (var 0 ++ₑ rem ((var 1 ++ₑ elm 1) ++ₑ elm 1) 0)
                         (var 0 ++ₑ rem (var 1 ++ₑ elm 1) 0)
                         ((Γ ∷ Γ1 ∷ []) , (A ^ s ∷ B ^ t ∷ [])) {refl}

        p' = structural sub_left subset-refl mix
        d_p' = structural-preserves-δ sub_left subset-refl mix

        d_final : δ p' ≤ max (δ Π) (δ theProof)
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- Case 12: Right is ⊢C (structural - right contraction on right proof)
Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = Γ₁'} {Δ' = .([ B ^ t ] ,, Δ_sub)} {A = A} {s = s}
    degEq Π (⊢C {.Γ₁'} {B} {t} {Δ_sub} Π') wfp wfp' (acc accRec) =
    let
        h-dec = mixHeight-dec-r Π (⊢C Π') Π' (height-subproof-1 Π')
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = Γ₁'} {Δ' = [ B ^ t ] ,, [ B ^ t ] ,, Δ_sub} {A = A} {s = s} degEq Π Π' wfp wfp' acc'

        -- (Δ - A) ,, ([B] ,, [B] ,, Δ_sub) ⊆ (Δ - A) ,, ([B] ,, Δ_sub)
        sub_right : ((Δ - (A ^ s)) ,, ([ B ^ t ] ,, [ B ^ t ] ,, Δ_sub)) ⊆ ((Δ - (A ^ s)) ,, ([ B ^ t ] ,, Δ_sub))
        sub_right = solve (rem (var 0) 0 ++ₑ elm 1 ++ₑ elm 1 ++ₑ var 1) (rem (var 0) 0 ++ₑ elm 1 ++ₑ var 1)
                          ((Δ ∷ Δ_sub ∷ []) , (A ^ s ∷ B ^ t ∷ [])) {refl}

        p' = structural subset-refl sub_right mix
        d_p' = structural-preserves-δ subset-refl sub_right mix

        d_final : δ p' ≤ max (δ Π) (δ (⊢C Π'))
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- Case 13: Right is Exc⊢ (structural - left exchange on right proof)
Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = .((((Γ₁' ,, [ C ^ r ]) ,, [ B ^ t ]) ,, Γ₂'))} {Δ' = Δ_sub'} {A = A} {s = s}
    degEq Π theProof'@(Exc⊢ {Γ₁'} {B} {t} {C} {r} {Γ₂'} {.Δ_sub'} Π') wfp wfp' (acc accRec) =
    let
        h-dec = mixHeight-dec-r Π theProof' Π' (height-subproof-1 Π')
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = (((Γ₁' ,, [ B ^ t ]) ,, [ C ^ r ]) ,, Γ₂')} {Δ' = Δ_sub'} {A = A} {s = s} degEq Π Π' wfp wfp' acc'

        -- Use solver: Γ ,, (((Γ₁' ,, [B] ,, [C]) ,, Γ₂') - A) ⊆ Γ ,, (((Γ₁' ,, [C] ,, [B]) ,, Γ₂') - A)
        sub_left : (Γ ,, (((((Γ₁' ,, [ B ^ t ]) ,, [ C ^ r ]) ,, Γ₂')) - (A ^ s))) ⊆ (Γ ,, (((((Γ₁' ,, [ C ^ r ]) ,, [ B ^ t ]) ,, Γ₂')) - (A ^ s)))
        sub_left = solve (var 0 ++ₑ rem (((var 1 ++ₑ elm 1) ++ₑ elm 2) ++ₑ var 2) 0)
                         (var 0 ++ₑ rem (((var 1 ++ₑ elm 2) ++ₑ elm 1) ++ₑ var 2) 0)
                         ((Γ ∷ Γ₁' ∷ Γ₂' ∷ []) , (A ^ s ∷ B ^ t ∷ C ^ r ∷ [])) {refl}

        p' = structural sub_left subset-refl mix
        d_p' = structural-preserves-δ sub_left subset-refl mix

        d_final : δ p' ≤ max (δ Π) (δ theProof')
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- Case 14: Right is ⊢Exc (structural - right exchange on right proof)
Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = Γ_sub'} {Δ' = .((((Δ₁' ,, [ C ^ r ]) ,, [ B ^ t ]) ,, Δ₂'))} {A = A} {s = s}
    degEq Π theProof'@(⊢Exc {.Γ_sub'} {Δ₁'} {B} {t} {C} {r} {Δ₂'} Π') wfp wfp' (acc accRec) =
    let
        h-dec = mixHeight-dec-r Π theProof' Π' (height-subproof-1 Π')
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = Γ_sub'} {Δ' = (((Δ₁' ,, [ B ^ t ]) ,, [ C ^ r ]) ,, Δ₂')} {A = A} {s = s} degEq Π Π' wfp wfp' acc'

        -- (Δ - A) ,, (((Δ₁' ,, [B]) ,, [C]) ,, Δ₂') ⊆ (Δ - A) ,, (((Δ₁' ,, [C]) ,, [B]) ,, Δ₂')
        sub_right : ((Δ - (A ^ s)) ,, ((((Δ₁' ,, [ B ^ t ]) ,, [ C ^ r ]) ,, Δ₂'))) ⊆ ((Δ - (A ^ s)) ,, ((((Δ₁' ,, [ C ^ r ]) ,, [ B ^ t ]) ,, Δ₂')))
        sub_right = solve (rem (var 0) 0 ++ₑ (((var 1 ++ₑ elm 1) ++ₑ elm 2) ++ₑ var 2))
                          (rem (var 0) 0 ++ₑ (((var 1 ++ₑ elm 2) ++ₑ elm 1) ++ₑ var 2))
                          ((Δ ∷ Δ₁' ∷ Δ₂' ∷ []) , (A ^ s ∷ B ^ t ∷ C ^ r ∷ [])) {refl}

        p' = structural subset-refl sub_right mix
        d_p' = structural-preserves-δ subset-refl sub_right mix

        d_final : δ p' ≤ max (δ Π) (δ theProof')
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- =============================================================================
-- Case 15: Left is Cut (structural - two premises)
-- =============================================================================

-- Cut Π1 Π2 : (Γ1 ,, Γ2) ⊢ (Δ1 ,, Δ2)
-- where Π1 : Γ1 ⊢ [ C ^ t ] ,, Δ1
--       Π2 : Γ2 ,, [ C ^ t ] ⊢ Δ2
Mix {n = n} {Γ = .(Γ1 ,, Γ2)} {Δ = .(Δ1 ,, Δ2)} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq (Cut {Γ₁ = Γ1} {A = C} {s = t} {Δ₁ = Δ1} {Γ₂ = Γ2} {Δ₂ = Δ2} Π1 Π2) Π' wfp wfp' (acc accRec) =
    let
        -- Height decrease for two premises
        h-dec1 = mixHeight-dec-l (Cut Π1 Π2) Π1 Π' (height-subproof-2-l Π1 Π2)
        h-dec2 = mixHeight-dec-l (Cut Π1 Π2) Π2 Π' (height-subproof-2-r Π1 Π2)
        acc1 = accRec _ (inr (refl , h-dec1))
        acc2 = accRec _ (inr (refl , h-dec2))

        -- WellFormedProof (Cut Π1 Π2) = WellFormedProof Π1 × WellFormedProof Π2
        wfp1 = fst wfp
        wfp2 = snd wfp

        -- Recursive calls
        (mix1 , dmix1) = Mix {n = n} {Γ = Γ1} {Δ = [ C ^ t ] ,, Δ1} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s} degEq Π1 Π' wfp1 wfp' acc1
        (mix2 , dmix2) = Mix {n = n} {Γ = Γ2 ,, [ C ^ t ]} {Δ = Δ2} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s} degEq Π2 Π' wfp2 wfp' acc2
        -- mix1 : Γ1 ,, (Γ' - A) ⊢ (([ C ^ t ] ,, Δ1) - A) ,, Δ'
        -- mix2 : (Γ2 ,, [ C ^ t ]) ,, (Γ' - A) ⊢ (Δ2 - A) ,, Δ'
        -- Goal: (Γ1 ,, Γ2) ,, (Γ' - A) ⊢ ((Δ1 ,, Δ2) - A) ,, Δ'

        Γ'-rem = Γ' - (A ^ s)
        Δ1-rem = Δ1 - (A ^ s)
        Δ2-rem = Δ2 - (A ^ s)

        -- For mix1: reorder succedent to get [ C ^ t ] at front
        -- mix1 : Γ1 ,, Γ'-rem ⊢ (([ C ^ t ] ,, Δ1) - A) ,, Δ'
        -- need: Γ1 ,, Γ'-rem ⊢ [ C ^ t ] ,, (Δ1-rem ,, Δ')
        sub_delta1 : ((([ C ^ t ] ,, Δ1) - (A ^ s)) ,, Δ') ⊆ ([ C ^ t ] ,, (Δ1-rem ,, Δ'))
        sub_delta1 = solve (rem (elm 0 ++ₑ var 0) 1 ++ₑ var 1)
                           (elm 0 ++ₑ (rem (var 0) 1 ++ₑ var 1))
                           ((Δ1 ∷ Δ' ∷ []) , (C ^ t ∷ A ^ s ∷ [])) {refl}

        mix1_reordered = structural subset-refl sub_delta1 mix1
        -- mix1_reordered : Γ1 ,, Γ'-rem ⊢ [ C ^ t ] ,, (Δ1-rem ,, Δ')

        -- For mix2: reorder antecedent to get [ C ^ t ] at end
        -- mix2 : (Γ2 ,, [ C ^ t ]) ,, Γ'-rem ⊢ (Δ2 - A) ,, Δ'
        -- need: (Γ2 ,, Γ'-rem) ,, [ C ^ t ] ⊢ Δ2-rem ,, Δ'
        sub_gamma2 : (((Γ2 ,, [ C ^ t ]) ,, Γ'-rem)) ⊆ ((Γ2 ,, Γ'-rem) ,, [ C ^ t ])
        sub_gamma2 = solve ((var 0 ++ₑ elm 0) ++ₑ var 1) ((var 0 ++ₑ var 1) ++ₑ elm 0) ((Γ2 ∷ Γ'-rem ∷ []) , (C ^ t ∷ [])) {refl}

        mix2_reordered = structural sub_gamma2 subset-refl mix2
        -- mix2_reordered : (Γ2 ,, Γ'-rem) ,, [ C ^ t ] ⊢ Δ2-rem ,, Δ'

        -- Apply Cut rule
        p_cut = Cut {Γ₁ = Γ1 ,, Γ'-rem} {A = C} {s = t} {Δ₁ = Δ1-rem ,, Δ'} {Γ₂ = Γ2 ,, Γ'-rem} {Δ₂ = Δ2-rem ,, Δ'} mix1_reordered mix2_reordered
        -- p_cut : (Γ1 ,, Γ'-rem) ,, (Γ2 ,, Γ'-rem) ⊢ (Δ1-rem ,, Δ') ,, (Δ2-rem ,, Δ')

        -- Contract Γ'-rem and Δ' which appear twice
        sub_left : ((Γ1 ,, Γ'-rem) ,, (Γ2 ,, Γ'-rem)) ⊆ ((Γ1 ,, Γ2) ,, Γ'-rem)
        sub_left = solve ((var 0 ++ₑ var 2) ++ₑ (var 1 ++ₑ var 2)) ((var 0 ++ₑ var 1) ++ₑ var 2) ((Γ1 ∷ Γ2 ∷ Γ'-rem ∷ []) , []) {refl}

        sub_right : ((Δ1-rem ,, Δ') ,, (Δ2-rem ,, Δ')) ⊆ ((Δ1-rem ,, Δ2-rem) ,, Δ')
        sub_right = solve ((var 0 ++ₑ var 2) ++ₑ (var 1 ++ₑ var 2)) ((var 0 ++ₑ var 1) ++ₑ var 2) ((Δ1-rem ∷ Δ2-rem ∷ Δ' ∷ []) , []) {refl}

        p_contracted = structural sub_left sub_right p_cut
        -- p_contracted : (Γ1 ,, Γ2) ,, Γ'-rem ⊢ (Δ1-rem ,, Δ2-rem) ,, Δ'

        -- Rewrite to match goal: (Δ1 ,, Δ2) - A ≡ Δ1-rem ,, Δ2-rem
        eqDelta : ((Δ1 ,, Δ2) - (A ^ s)) ≡ (Δ1-rem ,, Δ2-rem)
        eqDelta = S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Δ1 Δ2

        p' = subst (λ D → (Γ1 ,, Γ2) ,, Γ'-rem ⊢ D ,, Δ') (sym eqDelta) p_contracted

        -- Degree preservation
        cutBound = max (δ (Cut Π1 Π2)) (δ Π')

        d_structural1 : δ mix1_reordered ≡ δ mix1
        d_structural1 = structural-preserves-δ subset-refl sub_delta1 mix1
        d_structural2 : δ mix2_reordered ≡ δ mix2
        d_structural2 = structural-preserves-δ sub_gamma2 subset-refl mix2
        d_contracted = structural-preserves-δ sub_left sub_right p_cut
        d_p' = trans (subst-preserves-δ (cong (_,, Δ') (sym eqDelta)) p_contracted) d_contracted

        -- Solver env: 0=δΠ1, 1=δΠ2, 2=suc(degree C), 3=δΠ'
        -- cutBound = max (max 2 (max 0 1)) 3
        maxEnv = δ Π1 ∷v δ Π2 ∷v suc (degree C) ∷v δ Π' ∷v []v
        cutRHS = (∣ fsuc (fsuc fzero) ∨ₑ (∣ fzero ∨ₑ ∣ fsuc fzero)) ∨ₑ ∣ fsuc (fsuc (fsuc fzero))

        dmix1' : δ mix1 ≤ cutBound
        dmix1' = ≤-trans dmix1
          (solve≤ℕ (∣ fzero ∨ₑ ∣ fsuc (fsuc (fsuc fzero))) cutRHS maxEnv {refl})

        dmix2' : δ mix2 ≤ cutBound
        dmix2' = ≤-trans dmix2
          (solve≤ℕ (∣ fsuc fzero ∨ₑ ∣ fsuc (fsuc (fsuc fzero))) cutRHS maxEnv {refl})

        dmix1_reordered : δ mix1_reordered ≤ cutBound
        dmix1_reordered = subst (λ k → k ≤ cutBound) (sym d_structural1) dmix1'
        dmix2_reordered : δ mix2_reordered ≤ cutBound
        dmix2_reordered = subst (λ k → k ≤ cutBound) (sym d_structural2) dmix2'

        degC_bound : suc (degree C) ≤ cutBound
        degC_bound = solve≤ℕ (∣ fsuc (fsuc fzero)) cutRHS maxEnv {refl}

        d_cut_bound : δ p_cut ≤ cutBound
        d_cut_bound = max-least degC_bound (max-least dmix1_reordered dmix2_reordered)

        d_final : δ p' ≤ max (δ (Cut Π1 Π2)) (δ Π')
        d_final = subst (λ k → k ≤ cutBound) (sym d_p') d_cut_bound
    in (p' , d_final)

-- =============================================================================
-- Case 16: Right is Cut (structural - two premises on right proof)
-- =============================================================================

Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq Π (Cut {Γ₁ = Γ'1} {A = C} {s = t} {Δ₁ = Δ'1} {Γ₂ = Γ'2} {Δ₂ = Δ'2} Π'1 Π'2) wfp wfp' (acc accRec) =
    let
        wfp'1 = fst wfp'
        wfp'2 = snd wfp'

        -- Height decrease proofs for both premises
        h-dec1 = mixHeight-dec-r Π (Cut Π'1 Π'2) Π'1 (height-subproof-2-l Π'1 Π'2)
        h-dec2 = mixHeight-dec-r Π (Cut Π'1 Π'2) Π'2 (height-subproof-2-r Π'1 Π'2)
        acc1 = accRec _ (inr (refl , h-dec1))
        acc2 = accRec _ (inr (refl , h-dec2))

        (mix1 , dmix1) = Mix {Γ' = Γ'1} {Δ' = [ C ^ t ] ,, Δ'1} {A = A} {s = s} degEq Π Π'1 wfp wfp'1 acc1
        (mix2 , dmix2) = Mix {Γ' = Γ'2 ,, [ C ^ t ]} {Δ' = Δ'2} {A = A} {s = s} degEq Π Π'2 wfp wfp'2 acc2
        -- mix1 : Γ ,, (Γ'1 - A) ⊢ (Δ - A) ,, ([ C ^ t ] ,, Δ'1)
        -- mix2 : Γ ,, ((Γ'2 ,, [ C ^ t ]) - A) ⊢ (Δ - A) ,, Δ'2
        -- Goal: Γ ,, ((Γ'1 ,, Γ'2) - A) ⊢ (Δ - A) ,, (Δ'1 ,, Δ'2)

        Γ'1-rem = Γ'1 - (A ^ s)
        Γ'2-rem = Γ'2 - (A ^ s)
        Δ-rem = Δ - (A ^ s)

        -- For mix1: reorder succedent to get [ C ^ t ] at front
        sub_reorder1 : (Δ-rem ,, ([ C ^ t ] ,, Δ'1)) ⊆ ([ C ^ t ] ,, (Δ-rem ,, Δ'1))
        sub_reorder1 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ'1 ∷ []) , (C ^ t ∷ [])) {refl}

        mix1_reordered = structural subset-refl sub_reorder1 mix1
        -- mix1_reordered : Γ ,, Γ'1-rem ⊢ [ C ^ t ] ,, (Δ-rem ,, Δ'1)

        -- For mix2: ((Γ'2 ,, [ C ^ t ]) - A) needs to be subset of Γ'2-rem ,, [ C ^ t ]
        sub_gamma2 : (((Γ'2 ,, [ C ^ t ]) - (A ^ s))) ⊆ (Γ'2-rem ,, [ C ^ t ])
        sub_gamma2 = solve (rem (var 0 ++ₑ elm 0) 1) (rem (var 0) 1 ++ₑ elm 0) ((Γ'2 ∷ []) , (C ^ t ∷ A ^ s ∷ [])) {refl}

        sub_left2 : (Γ ,, ((Γ'2 ,, [ C ^ t ]) - (A ^ s))) ⊆ ((Γ ,, Γ'2-rem) ,, [ C ^ t ])
        sub_left2 = solve (var 1 ++ₑ rem (var 0 ++ₑ elm 0) 1) ((var 1 ++ₑ rem (var 0) 1) ++ₑ elm 0) ((Γ'2 ∷ Γ ∷ []) , (C ^ t ∷ A ^ s ∷ [])) {refl}

        mix2_reordered = structural sub_left2 subset-refl mix2
        -- mix2_reordered : (Γ ,, Γ'2-rem) ,, [ C ^ t ] ⊢ Δ-rem ,, Δ'2

        -- Apply Cut rule
        p_cut = Cut {Γ₁ = Γ ,, Γ'1-rem} {A = C} {s = t} {Δ₁ = Δ-rem ,, Δ'1}
                    {Γ₂ = Γ ,, Γ'2-rem} {Δ₂ = Δ-rem ,, Δ'2} mix1_reordered mix2_reordered
        -- p_cut : (Γ ,, Γ'1-rem) ,, (Γ ,, Γ'2-rem) ⊢ (Δ-rem ,, Δ'1) ,, (Δ-rem ,, Δ'2)

        -- Contract contexts using solver
        sub_left : ((Γ ,, Γ'1-rem) ,, (Γ ,, Γ'2-rem)) ⊆ (Γ ,, (Γ'1-rem ,, Γ'2-rem))
        sub_left = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Γ ∷ Γ'1-rem ∷ Γ'2-rem ∷ []) , []) {refl}

        sub_right : ((Δ-rem ,, Δ'1) ,, (Δ-rem ,, Δ'2)) ⊆ (Δ-rem ,, (Δ'1 ,, Δ'2))
        sub_right = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Δ-rem ∷ Δ'1 ∷ Δ'2 ∷ []) , []) {refl}

        p_contracted = structural sub_left sub_right p_cut

        -- Rewrite using removeAll distribution
        eqGamma : ((Γ'1 ,, Γ'2) - (A ^ s)) ≡ (Γ'1-rem ,, Γ'2-rem)
        eqGamma = S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ'1 Γ'2

        p' = subst (λ G → Γ ,, G ⊢ Δ-rem ,, (Δ'1 ,, Δ'2)) (sym eqGamma) p_contracted

        d_mix1_reordered = structural-preserves-δ subset-refl sub_reorder1 mix1
        d_mix2_reordered = structural-preserves-δ sub_left2 subset-refl mix2

        -- Degree bound
        cutBound = max (δ Π) (δ (Cut Π'1 Π'2))

        -- Lift dmix1 to cutBound
        dmix1' : δ mix1 ≤ cutBound
        dmix1' = ≤-trans dmix1 (max-least
          (left-≤-max {m = δ Π})
          (≤-trans (≤-trans (left-≤-max {m = δ Π'1}) (right-≤-max {m = suc (degree C)})) (right-≤-max {m = δ Π})))

        dmix2' : δ mix2 ≤ cutBound
        dmix2' = ≤-trans dmix2 (max-least
          (left-≤-max {m = δ Π})
          (≤-trans (≤-trans (right-≤-max {m = δ Π'1}) (right-≤-max {m = suc (degree C)})) (right-≤-max {m = δ Π})))

        dmix1r' : δ mix1_reordered ≤ cutBound
        dmix1r' = subst (_≤ cutBound) (sym d_mix1_reordered) dmix1'

        dmix2r' : δ mix2_reordered ≤ cutBound
        dmix2r' = subst (_≤ cutBound) (sym d_mix2_reordered) dmix2'

        -- δ p_cut = max (suc (degree C)) (max (δ mix1_reordered) (δ mix2_reordered))
        deg_C_bound : suc (degree C) ≤ cutBound
        deg_C_bound = ≤-trans (left-≤-max {suc (degree C)} {max (δ Π'1) (δ Π'2)}) (right-≤-max {m = δ Π})

        dp_cut : δ p_cut ≤ cutBound
        dp_cut = max-least deg_C_bound (max-least dmix1r' dmix2r')

        d_contracted = structural-preserves-δ sub_left sub_right p_cut
        dp_contracted : δ p_contracted ≤ cutBound
        dp_contracted = subst (_≤ cutBound) (sym d_contracted) dp_cut

        d_p'_eq = subst-preserves-δ-ctx (cong (λ G → Γ ,, G) (sym eqGamma)) p_contracted

        d_final : δ p' ≤ max (δ Π) (δ (Cut Π'1 Π'2))
        d_final = subst (_≤ cutBound) (sym d_p'_eq) dp_contracted
    in (p' , d_final)

-- =============================================================================
-- Left-intro rules on left proof (don't introduce to the right)
-- These are never principal when the left proof has them
-- =============================================================================

-- Case 17: Left proof is ¬⊢
-- ¬⊢ Π : Γ1 ,, [ (¬ B) ^ t ] ⊢ Δ1  where Π : Γ1 ⊢ [ B ^ t ] ,, Δ1
-- This introduces (¬ B) to the LEFT (antecedent), not to the right
Mix {n = n} {Γ = .(Γ1 ,, [ (¬ B) ^ t ])} {Δ = Δ1} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq (¬⊢ {Γ1} {B} {t} {.Δ1} Π) Π' wfp wfp' (acc accRec) with discretePFormula (A ^ s) (B ^ t)
-- Subcase: A = B (B disappears after removeAll)
... | yes eq =
    let h-dec = mixHeight-dec-l (¬⊢ Π) Π Π' (height-subproof-1 Π)
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ = Γ1} {Δ = [ B ^ t ] ,, Δ1} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s} degEq Π Π' wfp wfp' acc'

        eqSucc : ([ B ^ t ] ,, Δ1) - (A ^ s) ≡ Δ1 - (A ^ s)
        eqSucc = removeAll-yes (A ^ s) (B ^ t) Δ1 eq

        mix_fixed : Γ1 ,, (Γ' - (A ^ s)) ⊢ (Δ1 - (A ^ s)) ,, Δ'
        mix_fixed = subst (λ D → Γ1 ,, (Γ' - (A ^ s)) ⊢ D ,, Δ') eqSucc mix

        sub : (Γ1 ++ (Γ' - (A ^ s))) ⊆ (Γ1 ++ [ (¬ B) ^ t ] ++ (Γ' - (A ^ s)))
        sub = solve (var 0 ++ₑ var 1) (var 0 ++ₑ elm 0 ++ₑ var 1) ((Γ1 ∷ (Γ' - (A ^ s)) ∷ []) , ((¬ B) ^ t ∷ [])) {refl}

        p_weak = structural sub subset-refl mix_fixed

        eqCtx : (Γ1 ++ [ (¬ B) ^ t ] ++ (Γ' - (A ^ s))) ≡ ((Γ1 ++ [ (¬ B) ^ t ]) ++ (Γ' - (A ^ s)))
        eqCtx = sym (++-assoc Γ1 [ (¬ B) ^ t ] (Γ' - (A ^ s)))

        p' = subst (λ G → G ⊢ (Δ1 - (A ^ s)) ,, Δ') eqCtx p_weak

        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx eqCtx p_weak) (trans (structural-preserves-δ sub subset-refl mix_fixed) (subst-preserves-δ (cong (λ D → D ,, Δ') eqSucc) mix))

        d_final : δ p' ≤ max (δ (¬⊢ Π)) (δ Π')
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- Subcase: A ≠ B (B stays after removeAll)
... | no neq =
    let h-dec = mixHeight-dec-l (¬⊢ Π) Π Π' (height-subproof-1 Π)
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ = Γ1} {Δ = [ B ^ t ] ,, Δ1} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s} degEq Π Π' wfp wfp' acc'

        eqSucc = removeAll-no (A ^ s) (B ^ t) Δ1 neq

        mix_fixed : Γ1 ,, (Γ' - (A ^ s)) ⊢ [ B ^ t ] ,, (Δ1 - (A ^ s)) ,, Δ'
        mix_fixed = subst (λ D → Γ1 ,, (Γ' - (A ^ s)) ⊢ D ,, Δ') eqSucc mix

        p_raw : (Γ1 ,, (Γ' - (A ^ s))) ,, [ (¬ B) ^ t ] ⊢ (Δ1 - (A ^ s)) ++ Δ'
        p_raw = ¬⊢ mix_fixed

        sub : (Γ1 ++ (Γ' - (A ^ s)) ++ [ (¬ B) ^ t ]) ⊆ (Γ1 ++ [ (¬ B) ^ t ] ++ (Γ' - (A ^ s)))
        sub = solve (var 0 ++ₑ var 1 ++ₑ elm 0) (var 0 ++ₑ elm 0 ++ₑ var 1) ((Γ1 ∷ (Γ' - (A ^ s)) ∷ []) , ((¬ B) ^ t ∷ [])) {refl}

        eqAssoc : ((Γ1 ,, (Γ' - (A ^ s))) ,, [ (¬ B) ^ t ]) ≡ (Γ1 ++ (Γ' - (A ^ s)) ++ [ (¬ B) ^ t ])
        eqAssoc = ++-assoc Γ1 (Γ' - (A ^ s)) [ (¬ B) ^ t ]

        p_raw_casted : Γ1 ++ (Γ' - (A ^ s)) ++ [ (¬ B) ^ t ] ⊢ (Δ1 - (A ^ s)) ++ Δ'
        p_raw_casted = subst (λ G → G ⊢ (Δ1 - (A ^ s)) ++ Δ') eqAssoc p_raw

        p_weak = structural sub subset-refl p_raw_casted

        eqCtx' : (Γ1 ++ [ (¬ B) ^ t ] ++ (Γ' - (A ^ s))) ≡ ((Γ1 ++ [ (¬ B) ^ t ]) ++ (Γ' - (A ^ s)))
        eqCtx' = sym (++-assoc Γ1 [ (¬ B) ^ t ] (Γ' - (A ^ s)))

        p' : (Γ1 ++ [ (¬ B) ^ t ]) ++ (Γ' - (A ^ s)) ⊢ (Δ1 - (A ^ s)) ++ Δ'
        p' = subst (λ G → G ⊢ (Δ1 - (A ^ s)) ++ Δ') eqCtx' p_weak

        d_p_raw : δ p_raw ≡ δ mix
        d_p_raw = trans refl (subst-preserves-δ (cong (_,, Δ') eqSucc) mix)

        d_p_raw_casted : δ p_raw_casted ≡ δ mix
        d_p_raw_casted = trans (subst-preserves-δ-ctx eqAssoc p_raw) d_p_raw

        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx eqCtx' p_weak) (trans (structural-preserves-δ sub subset-refl p_raw_casted) d_p_raw_casted)

        d_final : δ p' ≤ max (δ (¬⊢ Π)) (δ Π')
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- Case 18: Left proof is ∧₁⊢
-- ∧₁⊢ Π : Γ1 ,, [ (B ∧ C) ^ t ] ⊢ Δ1  where Π : Γ1 ,, [ B ^ t ] ⊢ Δ1
Mix {n = n} {Γ = .(Γ1 ,, [ (B ∧ C) ^ t ])} {Δ = Δ1} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq (∧₁⊢ {Γ = Γ1} {A = B} {s = t} {Δ = .Δ1} {B = C} Π) Π' wfp wfp' (acc accRec) =
    let h-dec = mixHeight-dec-l (∧₁⊢ Π) Π Π' (height-subproof-1 Π)
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix degEq Π Π' wfp wfp' acc'
        -- mix : (Γ1 ,, [ B ^ t ]) ,, (Γ' - A) ⊢ (Δ1 - A) ,, Δ'
        -- Goal: (Γ1 ,, [ (B ∧ C) ^ t ]) ,, (Γ' - A) ⊢ (Δ1 - A) ,, Δ'

        Γ'-rem = Γ' - (A ^ s)
        Δ1-rem = Δ1 - (A ^ s)

        -- Step 1: Move [ B ^ t ] to the end using solver
        subL1 : ((Γ1 ,, [ B ^ t ]) ,, Γ'-rem) ⊆ ((Γ1 ,, Γ'-rem) ,, [ B ^ t ])
        subL1 = solve ((var 0 ++ₑ elm 0) ++ₑ var 1) ((var 0 ++ₑ var 1) ++ₑ elm 0) ((Γ1 ∷ Γ'-rem ∷ []) , (B ^ t ∷ [])) {refl}
        mix1 = structural subL1 subset-refl mix

        -- Step 2: Apply ∧₁⊢
        mix2 = ∧₁⊢ {Γ = Γ1 ,, Γ'-rem} {A = B} {s = t} {Δ = Δ1-rem ,, Δ'} {B = C} mix1

        -- Step 3: Move [ (B ∧ C) ^ t ] back to the front using solver
        subL2 : ((Γ1 ,, Γ'-rem) ,, [ (B ∧ C) ^ t ]) ⊆ ((Γ1 ,, [ (B ∧ C) ^ t ]) ,, Γ'-rem)
        subL2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) ((var 0 ++ₑ elm 0) ++ₑ var 1) ((Γ1 ∷ Γ'-rem ∷ []) , ((B ∧ C) ^ t ∷ [])) {refl}
        p' = structural subL2 subset-refl mix2

        -- Degree preservation
        d_p' : δ p' ≡ δ mix
        d_p' = trans (structural-preserves-δ subL2 subset-refl mix2)
               (trans refl (structural-preserves-δ subL1 subset-refl mix))

        d_final : δ p' ≤ max (δ (∧₁⊢ Π)) (δ Π')
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- Case 19: Left proof is ∧₂⊢
-- ∧₂⊢ {B = B} {A = C} Π : Γ1 ,, [ (C ∧ B) ^ t ] ⊢ Δ1  where Π : Γ1 ,, [ B ^ t ] ⊢ Δ1
Mix {n = n} {Γ = .(Γ1 ,, [ (C ∧ B) ^ t ])} {Δ = Δ1} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq (∧₂⊢ {Γ = Γ1} {B = B} {s = t} {Δ = .Δ1} {A = C} Π) Π' wfp wfp' (acc accRec) =
    let h-dec = mixHeight-dec-l (∧₂⊢ Π) Π Π' (height-subproof-1 Π)
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix degEq Π Π' wfp wfp' acc'
        -- mix : (Γ1 ,, [ B ^ t ]) ,, (Γ' - A) ⊢ (Δ1 - A) ,, Δ'

        Γ'-rem = Γ' - (A ^ s)
        Δ1-rem = Δ1 - (A ^ s)

        -- Step 1: Move [ B ^ t ] to the end
        subL1 : ((Γ1 ,, [ B ^ t ]) ,, Γ'-rem) ⊆ ((Γ1 ,, Γ'-rem) ,, [ B ^ t ])
        subL1 = solve ((var 0 ++ₑ elm 0) ++ₑ var 1) ((var 0 ++ₑ var 1) ++ₑ elm 0) ((Γ1 ∷ Γ'-rem ∷ []) , (B ^ t ∷ [])) {refl}
        mix1 = structural subL1 subset-refl mix

        -- Step 2: Apply ∧₂⊢
        mix2 = ∧₂⊢ {Γ = Γ1 ,, Γ'-rem} {B = B} {s = t} {Δ = Δ1-rem ,, Δ'} {A = C} mix1

        -- Step 3: Move [ (C ∧ B) ^ t ] back to the front
        subL2 : ((Γ1 ,, Γ'-rem) ,, [ (C ∧ B) ^ t ]) ⊆ ((Γ1 ,, [ (C ∧ B) ^ t ]) ,, Γ'-rem)
        subL2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) ((var 0 ++ₑ elm 0) ++ₑ var 1) ((Γ1 ∷ Γ'-rem ∷ []) , ((C ∧ B) ^ t ∷ [])) {refl}
        p' = structural subL2 subset-refl mix2

        d_p' : δ p' ≡ δ mix
        d_p' = trans (structural-preserves-δ subL2 subset-refl mix2)
               (trans refl (structural-preserves-δ subL1 subset-refl mix))

        d_final : δ p' ≤ max (δ (∧₂⊢ Π)) (δ Π')
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- Case 20: Left proof is ∨⊢ (two premises)
-- ∨⊢ Π1 Π2 : Γ1 ,, Γ2 ,, [ (B ∨ C) ^ t ] ⊢ Δ1 ,, Δ2
-- where Π1 : Γ1 ,, [ B ^ t ] ⊢ Δ1, Π2 : Γ2 ,, [ C ^ t ] ⊢ Δ2
-- Note: Type uses right-associativity: Γ1 ,, (Γ2 ,, [ (B ∨ C) ^ t ])
Mix {n = n} {Γ = .(Γ1 ,, Γ2 ,, [ (B ∨ C) ^ t ])} {Δ = .(Δ1 ,, Δ2)} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq (∨⊢ {Γ₁ = Γ1} {A = B} {s = t} {Δ₁ = Δ1} {Γ₂ = Γ2} {B = C} {Δ₂ = Δ2} Π1 Π2) Π' wfp wfp' (acc accRec) =
    let h-dec1 = mixHeight-dec-l (∨⊢ Π1 Π2) Π1 Π' (height-subproof-2-l Π1 Π2)
        h-dec2 = mixHeight-dec-l (∨⊢ Π1 Π2) Π2 Π' (height-subproof-2-r Π1 Π2)
        acc1 = accRec _ (inr (refl , h-dec1))
        acc2 = accRec _ (inr (refl , h-dec2))

        wfp1 = fst wfp
        wfp2 = snd wfp

        (mix1 , dmix1) = Mix {Γ = Γ1 ,, [ B ^ t ]} {Δ = Δ1} degEq Π1 Π' wfp1 wfp' acc1
        (mix2 , dmix2) = Mix {Γ = Γ2 ,, [ C ^ t ]} {Δ = Δ2} degEq Π2 Π' wfp2 wfp' acc2
        -- mix1 : (Γ1 ,, [ B ^ t ]) ,, (Γ' - A) ⊢ (Δ1 - A) ,, Δ'
        -- mix2 : (Γ2 ,, [ C ^ t ]) ,, (Γ' - A) ⊢ (Δ2 - A) ,, Δ'

        Γ'-rem = Γ' - (A ^ s)
        Δ1-rem = Δ1 - (A ^ s)
        Δ2-rem = Δ2 - (A ^ s)

        -- Reorder mix1: move [ B ^ t ] to end
        subL1 : ((Γ1 ,, [ B ^ t ]) ,, Γ'-rem) ⊆ ((Γ1 ,, Γ'-rem) ,, [ B ^ t ])
        subL1 = solve ((var 0 ++ₑ elm 0) ++ₑ var 1) ((var 0 ++ₑ var 1) ++ₑ elm 0) ((Γ1 ∷ Γ'-rem ∷ []) , (B ^ t ∷ [])) {refl}
        mix1_r = structural subL1 subset-refl mix1

        -- Reorder mix2: move [ C ^ t ] to end
        subL2 : ((Γ2 ,, [ C ^ t ]) ,, Γ'-rem) ⊆ ((Γ2 ,, Γ'-rem) ,, [ C ^ t ])
        subL2 = solve ((var 0 ++ₑ elm 0) ++ₑ var 1) ((var 0 ++ₑ var 1) ++ₑ elm 0) ((Γ2 ∷ Γ'-rem ∷ []) , (C ^ t ∷ [])) {refl}
        mix2_r = structural subL2 subset-refl mix2

        -- Apply ∨⊢
        p_disj = ∨⊢ {Γ₁ = Γ1 ,, Γ'-rem} {A = B} {s = t} {Δ₁ = Δ1-rem ,, Δ'} {Γ₂ = Γ2 ,, Γ'-rem} {B = C} {Δ₂ = Δ2-rem ,, Δ'} mix1_r mix2_r
        -- p_disj type is right-associative: (Γ1 ,, Γ'-rem) ,, ((Γ2 ,, Γ'-rem) ,, [ (B ∨ C) ^ t ])

        -- Reassociate left context to left-associative form
        eqAssocL : ((Γ1 ,, Γ'-rem) ,, (Γ2 ,, Γ'-rem) ,, [ (B ∨ C) ^ t ]) ≡ (((Γ1 ,, Γ'-rem) ,, (Γ2 ,, Γ'-rem)) ,, [ (B ∨ C) ^ t ])
        eqAssocL = sym (++-assoc (Γ1 ,, Γ'-rem) (Γ2 ,, Γ'-rem) [ (B ∨ C) ^ t ])

        p_disj_assoc = subst (λ G → G ⊢ (Δ1-rem ,, Δ') ,, (Δ2-rem ,, Δ')) eqAssocL p_disj

        -- Contract contexts
        subLeft : (((Γ1 ,, Γ'-rem) ,, (Γ2 ,, Γ'-rem)) ,, [ (B ∨ C) ^ t ]) ⊆ ((Γ1 ,, Γ2 ,, [ (B ∨ C) ^ t ]) ,, Γ'-rem)
        subLeft = solve ((((var 0 ++ₑ var 2) ++ₑ (var 1 ++ₑ var 2)) ++ₑ elm 0)) ((var 0 ++ₑ var 1 ++ₑ elm 0) ++ₑ var 2) ((Γ1 ∷ Γ2 ∷ Γ'-rem ∷ []) , ((B ∨ C) ^ t ∷ [])) {refl}

        subRight : ((Δ1-rem ,, Δ') ,, (Δ2-rem ,, Δ')) ⊆ ((Δ1-rem ,, Δ2-rem) ,, Δ')
        subRight = solve ((var 0 ++ₑ var 2) ++ₑ (var 1 ++ₑ var 2)) ((var 0 ++ₑ var 1) ++ₑ var 2) ((Δ1-rem ∷ Δ2-rem ∷ Δ' ∷ []) , []) {refl}

        p_contracted = structural subLeft subRight p_disj_assoc

        -- Rewrite using removeAll distribution
        eqDelta : ((Δ1 ,, Δ2) - (A ^ s)) ≡ (Δ1-rem ,, Δ2-rem)
        eqDelta = S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Δ1 Δ2

        p' = subst (λ D → (Γ1 ,, Γ2 ,, [ (B ∨ C) ^ t ]) ,, Γ'-rem ⊢ D ,, Δ') (sym eqDelta) p_contracted

        -- Degree bound
        d_mix1_r = structural-preserves-δ subL1 subset-refl mix1
        d_mix2_r = structural-preserves-δ subL2 subset-refl mix2
        d_disj_assoc = subst-preserves-δ-ctx eqAssocL p_disj
        d_contracted = structural-preserves-δ subLeft subRight p_disj_assoc
        d_p'_eq = subst-preserves-δ (cong (_,, Δ') (sym eqDelta)) p_contracted

        cutBound = max (δ (∨⊢ Π1 Π2)) (δ Π')
        -- δ (∨⊢ Π1 Π2) = max (δ Π1) (δ Π2)
        -- cutBound = max (max (δ Π1) (δ Π2)) (δ Π')

        -- δ Π1 ≤ max (δ Π1) (δ Π2) ≤ cutBound
        dΠ1≤cutBound : δ Π1 ≤ cutBound
        dΠ1≤cutBound = left-left-≤-max

        dΠ'≤cutBound : δ Π' ≤ cutBound
        dΠ'≤cutBound = right-≤-max {δ Π'} {max (δ Π1) (δ Π2)}

        dmix1' : δ mix1 ≤ cutBound
        dmix1' = ≤-trans dmix1 (max-least dΠ1≤cutBound dΠ'≤cutBound)

        -- δ Π2 ≤ max (δ Π1) (δ Π2) ≤ cutBound
        dΠ2≤cutBound : δ Π2 ≤ cutBound
        dΠ2≤cutBound = right-left-≤-max

        dmix2' : δ mix2 ≤ cutBound
        dmix2' = ≤-trans dmix2 (max-least dΠ2≤cutBound dΠ'≤cutBound)

        dmix1r' = subst (_≤ cutBound) (sym d_mix1_r) dmix1'
        dmix2r' = subst (_≤ cutBound) (sym d_mix2_r) dmix2'

        dp_disj : δ p_disj ≤ cutBound
        dp_disj = max-least dmix1r' dmix2r'

        dp_disj_assoc : δ p_disj_assoc ≤ cutBound
        dp_disj_assoc = subst (_≤ cutBound) (sym d_disj_assoc) dp_disj

        dp_contracted = subst (_≤ cutBound) (sym d_contracted) dp_disj_assoc

        d_final : δ p' ≤ cutBound
        d_final = subst (_≤ cutBound) (sym d_p'_eq) dp_contracted
    in (p' , d_final)

-- Case 21: Left proof is ⇒⊢ (two premises)
-- ⇒⊢ Π1 Π2 : Γ1 ,, Γ2 ,, [ (A ⇒ B) ^ t ] ⊢ Δ1 ,, Δ2
-- where Π1 : Γ1 ,, [ B ^ t ] ⊢ Δ1, Π2 : Γ2 ⊢ [ A ^ t ] ,, Δ2
Mix {n = n} {Γ = .(Γ1 ,, Γ2 ,, [ (B₁ ⇒ B₂) ^ t ])} {Δ = .(Δ1 ,, Δ2)} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq (⇒⊢ {Γ₁ = Γ1} {B = B₂} {s = t} {Δ₁ = Δ1} {Γ₂ = Γ2} {A = B₁} {Δ₂ = Δ2} Π1 Π2) Π' wfp wfp' (acc accRec) =
    let h-dec1 = mixHeight-dec-l (⇒⊢ Π1 Π2) Π1 Π' (height-subproof-2-l Π1 Π2)
        h-dec2 = mixHeight-dec-l (⇒⊢ Π1 Π2) Π2 Π' (height-subproof-2-r Π1 Π2)
        acc1 = accRec _ (inr (refl , h-dec1))
        acc2 = accRec _ (inr (refl , h-dec2))

        wfp1 = fst wfp
        wfp2 = snd wfp

        (mix1 , dmix1) = Mix {Γ = Γ1 ,, [ B₂ ^ t ]} {Δ = Δ1} degEq Π1 Π' wfp1 wfp' acc1
        (mix2 , dmix2) = Mix {Γ = Γ2} {Δ = [ B₁ ^ t ] ,, Δ2} degEq Π2 Π' wfp2 wfp' acc2
        -- mix1 : (Γ1 ,, [ B₂ ^ t ]) ,, (Γ' - A) ⊢ (Δ1 - A) ,, Δ'
        -- mix2 : Γ2 ,, (Γ' - A) ⊢ (([ B₁ ^ t ] ,, Δ2) - A) ,, Δ'

        Γ'-rem = Γ' - (A ^ s)
        Δ1-rem = Δ1 - (A ^ s)
        Δ2-rem = Δ2 - (A ^ s)

        -- Reorder mix1: move [ B₂ ^ t ] to end
        subL1 : ((Γ1 ,, [ B₂ ^ t ]) ,, Γ'-rem) ⊆ ((Γ1 ,, Γ'-rem) ,, [ B₂ ^ t ])
        subL1 = solve ((var 0 ++ₑ elm 0) ++ₑ var 1) ((var 0 ++ₑ var 1) ++ₑ elm 0) ((Γ1 ∷ Γ'-rem ∷ []) , (B₂ ^ t ∷ [])) {refl}
        mix1_r = structural subL1 subset-refl mix1

        -- Reorder mix2: move [ B₁ ^ t ] to front of succedent
        subR2 : ((([ B₁ ^ t ] ,, Δ2) - (A ^ s)) ,, Δ') ⊆ ([ B₁ ^ t ] ,, (Δ2-rem ,, Δ'))
        subR2 = solve (rem (elm 0 ++ₑ var 0) 1 ++ₑ var 1) (elm 0 ++ₑ (rem (var 0) 1 ++ₑ var 1)) ((Δ2 ∷ Δ' ∷ []) , (B₁ ^ t ∷ A ^ s ∷ [])) {refl}
        mix2_r = structural subset-refl subR2 mix2

        -- Apply ⇒⊢
        p_impl = ⇒⊢ {Γ₁ = Γ1 ,, Γ'-rem} {B = B₂} {s = t} {Δ₁ = Δ1-rem ,, Δ'} {Γ₂ = Γ2 ,, Γ'-rem} {A = B₁} {Δ₂ = Δ2-rem ,, Δ'} mix1_r mix2_r

        -- Reassociate left context
        eqAssocL : ((Γ1 ,, Γ'-rem) ,, (Γ2 ,, Γ'-rem) ,, [ (B₁ ⇒ B₂) ^ t ]) ≡ (((Γ1 ,, Γ'-rem) ,, (Γ2 ,, Γ'-rem)) ,, [ (B₁ ⇒ B₂) ^ t ])
        eqAssocL = sym (++-assoc (Γ1 ,, Γ'-rem) (Γ2 ,, Γ'-rem) [ (B₁ ⇒ B₂) ^ t ])

        p_impl_assoc = subst (λ G → G ⊢ (Δ1-rem ,, Δ') ,, (Δ2-rem ,, Δ')) eqAssocL p_impl

        -- Contract contexts
        subLeft : (((Γ1 ,, Γ'-rem) ,, (Γ2 ,, Γ'-rem)) ,, [ (B₁ ⇒ B₂) ^ t ]) ⊆ ((Γ1 ,, Γ2 ,, [ (B₁ ⇒ B₂) ^ t ]) ,, Γ'-rem)
        subLeft = solve ((((var 0 ++ₑ var 2) ++ₑ (var 1 ++ₑ var 2)) ++ₑ elm 0)) ((var 0 ++ₑ var 1 ++ₑ elm 0) ++ₑ var 2) ((Γ1 ∷ Γ2 ∷ Γ'-rem ∷ []) , ((B₁ ⇒ B₂) ^ t ∷ [])) {refl}

        subRight : ((Δ1-rem ,, Δ') ,, (Δ2-rem ,, Δ')) ⊆ ((Δ1-rem ,, Δ2-rem) ,, Δ')
        subRight = solve ((var 0 ++ₑ var 2) ++ₑ (var 1 ++ₑ var 2)) ((var 0 ++ₑ var 1) ++ₑ var 2) ((Δ1-rem ∷ Δ2-rem ∷ Δ' ∷ []) , []) {refl}

        p_contracted = structural subLeft subRight p_impl_assoc

        eqDelta : ((Δ1 ,, Δ2) - (A ^ s)) ≡ (Δ1-rem ,, Δ2-rem)
        eqDelta = S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Δ1 Δ2

        p' = subst (λ D → (Γ1 ,, Γ2 ,, [ (B₁ ⇒ B₂) ^ t ]) ,, Γ'-rem ⊢ D ,, Δ') (sym eqDelta) p_contracted

        -- Degree bound
        d_mix1_r = structural-preserves-δ subL1 subset-refl mix1
        d_mix2_r = structural-preserves-δ subset-refl subR2 mix2
        d_impl_assoc = subst-preserves-δ-ctx eqAssocL p_impl
        d_contracted = structural-preserves-δ subLeft subRight p_impl_assoc
        d_p'_eq = subst-preserves-δ (cong (_,, Δ') (sym eqDelta)) p_contracted

        cutBound = max (δ (⇒⊢ Π1 Π2)) (δ Π')

        dΠ1≤cutBound : δ Π1 ≤ cutBound
        dΠ1≤cutBound = left-left-≤-max

        dΠ'≤cutBound : δ Π' ≤ cutBound
        dΠ'≤cutBound = right-≤-max {δ Π'} {max (δ Π1) (δ Π2)}

        dmix1' : δ mix1 ≤ cutBound
        dmix1' = ≤-trans dmix1 (max-least dΠ1≤cutBound dΠ'≤cutBound)

        dΠ2≤cutBound : δ Π2 ≤ cutBound
        dΠ2≤cutBound = right-left-≤-max

        dmix2' : δ mix2 ≤ cutBound
        dmix2' = ≤-trans dmix2 (max-least dΠ2≤cutBound dΠ'≤cutBound)

        dmix1r' = subst (_≤ cutBound) (sym d_mix1_r) dmix1'
        dmix2r' = subst (_≤ cutBound) (sym d_mix2_r) dmix2'

        dp_impl : δ p_impl ≤ cutBound
        dp_impl = max-least dmix1r' dmix2r'

        dp_impl_assoc : δ p_impl_assoc ≤ cutBound
        dp_impl_assoc = subst (_≤ cutBound) (sym d_impl_assoc) dp_impl

        dp_contracted = subst (_≤ cutBound) (sym d_contracted) dp_impl_assoc

        d_final : δ p' ≤ cutBound
        d_final = subst (_≤ cutBound) (sym d_p'_eq) dp_contracted
    in (p' , d_final)

-- Case 22: Left proof is □⊢
-- □⊢ Π : Γ1 ,, [ (□ B) ^ t ] ⊢ Δ1  where Π : Γ1 ,, [ B ^ (t ∘ r) ] ⊢ Δ1
Mix {n = n} {Γ = .(Γ1 ,, [ (□ B) ^ t ])} {Δ = Δ1} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq (□⊢ {Γ = Γ1} {A = B} {s = t} {t = r} {Δ = .Δ1} Π) Π' wfp wfp' (acc accRec) =
    let h-dec = mixHeight-dec-l (□⊢ Π) Π Π' (height-subproof-1 Π)
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix degEq Π Π' wfp wfp' acc'
        -- mix : (Γ1 ,, [ B ^ (t ∘ r) ]) ,, (Γ' - A) ⊢ (Δ1 - A) ,, Δ'

        Γ'-rem = Γ' - (A ^ s)
        Δ1-rem = Δ1 - (A ^ s)

        -- Step 1: Move [ B ^ (t ∘ r) ] to the end
        subL1 : ((Γ1 ,, [ B ^ (t ∘ r) ]) ,, Γ'-rem) ⊆ ((Γ1 ,, Γ'-rem) ,, [ B ^ (t ∘ r) ])
        subL1 = solve ((var 0 ++ₑ elm 0) ++ₑ var 1) ((var 0 ++ₑ var 1) ++ₑ elm 0) ((Γ1 ∷ Γ'-rem ∷ []) , (B ^ (t ∘ r) ∷ [])) {refl}
        mix1 = structural subL1 subset-refl mix

        -- Step 2: Apply □⊢
        mix2 = □⊢ {Γ = Γ1 ,, Γ'-rem} {A = B} {s = t} {t = r} {Δ = Δ1-rem ,, Δ'} mix1

        -- Step 3: Move [ (□ B) ^ t ] back to the front
        subL2 : ((Γ1 ,, Γ'-rem) ,, [ (□ B) ^ t ]) ⊆ ((Γ1 ,, [ (□ B) ^ t ]) ,, Γ'-rem)
        subL2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) ((var 0 ++ₑ elm 0) ++ₑ var 1) ((Γ1 ∷ Γ'-rem ∷ []) , ((□ B) ^ t ∷ [])) {refl}
        p' = structural subL2 subset-refl mix2

        d_p' : δ p' ≡ δ mix
        d_p' = trans (structural-preserves-δ subL2 subset-refl mix2)
               (trans refl (structural-preserves-δ subL1 subset-refl mix))

        d_final : δ p' ≤ max (δ (□⊢ Π)) (δ Π')
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- Case 23: Left proof is ♢⊢ (complex with eigenposition renaming)
-- ♢⊢ Π : Γ1 ,, [ (♢ B) ^ r ] ⊢ Δ1  where Π : Γ1 ,, [ B ^ insertToken x r ] ⊢ Δ1
Mix {n = n} {Γ = .(Γ1 ,, [ (♢ B) ^ r ])} {Δ = Δ1} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
    degEq (♢⊢ {x} {r} {Γ1} {Δ_sub} {B} ext freshΓ_sub freshΔ_sub Π) Π' wfp wfp' (acc accRec) = (p' , d_final)
    where
      -- Combined contexts after mixing
      Γ'-rem = Γ' - (A ^ s)
      Δ-rem = Δ1 - (A ^ s)
      combined = (Γ1 ,, Γ'-rem) ,, (Δ-rem ,, Δ')

      -- Compute fresh eigenposition token for combined contexts
      x' : Token
      x' = freshTokenForRename r combined Π

      -- Get well-formedness: maxEigenposToken Π < x (extracted from WellFormedProof)
      wf : maxEigenposToken Π < x
      wf = fst wfp

      -- Properties of x'
      x'-fresh-combined : TokenFresh x' combined
      x'-fresh-combined = freshTokenForRename-fresh r combined Π

      x'-eigenpos : maxEigenposToken Π < x'
      x'-eigenpos = freshTokenForRename-eigenpos r combined Π

      x'∉r : x' ∉Pos r
      x'∉r = freshTokenForRename-∉r r combined Π

      -- In the new API, the extended position is insertToken x r
      eigent : Position
      eigent = insertToken x r

      -- New eigenposition t' = substTokenToPos x [x'] eigent
      t' : Position
      t' = substPos x (singleton-pos x') eigent

      -- Rename eigenposition using the generalized function (works with abstract eigent)
      -- Use mkSingleTokenExt to construct IsSingleTokenExt from x ∉Pos r
      extSTE : IsSingleTokenExt r eigent x
      extSTE = mkSingleTokenExt r x ext
      rename-result = renameEigenpos-♢⊢-premise-gen {r = r} {t = eigent} {x = x} {Γ = Γ1} {Δ = Δ_sub} {A = B} Π extSTE freshΓ_sub freshΔ_sub wf x' x'-eigenpos x'∉r
      Π-renamed : (Γ1 ,, [ B ^ t' ]) ⊢ Δ_sub
      Π-renamed = fst rename-result
      ext' : IsSingleTokenExt r t' x'
      ext' = snd rename-result

      -- Transport degree bound (proven in ProofSubst)
      δ-eq-renamed : δ Π-renamed ≡ δ Π
      δ-eq-renamed = δ-renameEigenpos-♢⊢-premise-gen Π extSTE freshΓ_sub freshΔ_sub wf x' x'-eigenpos x'∉r

      -- Height preservation for eigenposition renaming
      height-eq-renamed : height Π-renamed ≡ height Π
      height-eq-renamed = height-renameEigenpos-♢⊢-premise-gen Π extSTE freshΓ_sub freshΔ_sub wf x' x'-eigenpos x'∉r

      -- WellFormedProof preservation for renamed proof
      wfp-sub : WellFormedProof Π
      wfp-sub = snd wfp
      wfp-renamed : WellFormedProof Π-renamed
      wfp-renamed = WellFormed-renameEigenpos-♢⊢-premise-gen Π extSTE freshΓ_sub freshΔ_sub wf x' x'-eigenpos x'∉r wfp-sub

      -- Height decrease: mixHeight Π-renamed Π' = mixHeight Π Π' < mixHeight (♢⊢ ... Π) Π'
      h-dec-raw = mixHeight-dec-l (♢⊢ ext freshΓ_sub freshΔ_sub Π) Π Π' (height-subproof-1 Π)

      -- Transport to Π-renamed using height equality
      mixHeight-eq = cong (λ h → h + height Π') height-eq-renamed

      h-dec = subst (_< mixHeight (♢⊢ ext freshΓ_sub freshΔ_sub Π) Π') (sym mixHeight-eq) h-dec-raw

      -- Mix the renamed proof with Π'
      mix-result = Mix {Γ = Γ1 ,, [ B ^ t' ]} {Δ = Δ_sub} {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s} degEq Π-renamed Π' wfp-renamed wfp' (accRec _ (inr (refl , h-dec)))
      mix = fst mix-result
      dmix = snd mix-result
      -- mix : (Γ1 ,, [ B ^ t' ]) ,, Γ'-rem ⊢ Δ-rem ,, Δ'

      -- Move B^t' to the end
      sub_reorder : ((Γ1 ,, [ B ^ t' ]) ,, Γ'-rem) ⊆ ((Γ1 ,, Γ'-rem) ,, [ B ^ t' ])
      sub_reorder = solve ((var 0 ++ₑ elm 0) ++ₑ var 1) ((var 0 ++ₑ var 1) ++ₑ elm 0) ((Γ1 ∷ Γ'-rem ∷ []) , (B ^ t' ∷ [])) {refl}

      mix_reordered = structural sub_reorder subset-refl mix
      -- mix_reordered : (Γ1 ,, Γ'-rem) ,, [ B ^ t' ] ⊢ Δ-rem ,, Δ'

      -- Freshness of x' for combined contexts (split from x'-fresh-combined)
      fresh-split = TokenFresh-split (Γ1 ,, Γ'-rem) (Δ-rem ,, Δ') x' x'-fresh-combined
      freshΓ' : TokenFresh x' (Γ1 ,, Γ'-rem)
      freshΓ' = fst fresh-split
      freshΔ' : TokenFresh x' (Δ-rem ,, Δ')
      freshΔ' = snd fresh-split

      -- Apply ♢⊢ with the fresh token x'
      -- Need to transport mix_reordered from t' to insertToken x' r
      t'-eq : t' ≡ insertToken x' r
      t'-eq = substPos-insertToken-eq x x' r ext

      mix_transported : (Γ1 ,, Γ'-rem) ,, [ B ^ insertToken x' r ] ⊢ Δ-rem ,, Δ'
      mix_transported = subst (λ (p : Position) → (Γ1 ,, Γ'-rem) ,, [ B ^ p ] ⊢ Δ-rem ,, Δ') t'-eq mix_reordered

      p_diamond = ♢⊢ {x'} {r} {Γ1 ,, Γ'-rem} {Δ-rem ,, Δ'} {B} x'∉r freshΓ' freshΔ' mix_transported
      -- p_diamond : (Γ1 ,, Γ'-rem) ,, [ (♢ B) ^ r ] ⊢ Δ-rem ,, Δ'

      -- Move (♢B)^r back to its proper position
      sub_reorder_back : ((Γ1 ,, Γ'-rem) ,, [ (♢ B) ^ r ]) ⊆ ((Γ1 ,, [ (♢ B) ^ r ]) ,, Γ'-rem)
      sub_reorder_back = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) ((var 0 ++ₑ elm 0) ++ₑ var 1) ((Γ1 ∷ Γ'-rem ∷ []) , ((♢ B) ^ r ∷ [])) {refl}

      p' = structural sub_reorder_back subset-refl p_diamond

      -- Build degree proof chain: δ p' = δ p_diamond = δ mix_transported = δ mix_reordered = δ mix
      d_step1 : δ p' ≡ δ p_diamond
      d_step1 = structural-preserves-δ sub_reorder_back subset-refl p_diamond
      -- δ (♢⊢ _ _ _ p) = δ p by definition, so δ p_diamond = δ mix_transported
      d_step2 : δ p_diamond ≡ δ mix_transported
      d_step2 = refl
      -- Transport preserves degree
      d_step3 : δ mix_transported ≡ δ mix_reordered
      d_step3 = subst-preserves-δ-ctx (cong {A = Position} (λ (p : Position) → (Γ1 ,, Γ'-rem) ,, [ B ^ p ]) t'-eq) mix_reordered
      d_step4 : δ mix_reordered ≡ δ mix
      d_step4 = structural-preserves-δ sub_reorder subset-refl mix

      d_p' : δ p' ≡ δ mix
      d_p' = d_step1 ∙ d_step2 ∙ d_step3 ∙ d_step4

      -- Bound: dmix : δ mix ≤ max (δ Π-renamed) (δ Π')
      -- Since δ Π-renamed = δ Π (via δ-eq-renamed) and δ (♢⊢ ... Π) = δ Π
      -- We have: max (δ Π-renamed) (δ Π') = max (δ (♢⊢ ...)) (δ Π')
      diamondBound = max (δ (♢⊢ ext freshΓ_sub freshΔ_sub Π)) (δ Π')

      -- δ (♢⊢ ... Π) = δ Π by definition
      δ-♢⊢-eq : δ (♢⊢ ext freshΓ_sub freshΔ_sub Π) ≡ δ Π
      δ-♢⊢-eq = refl

      -- Transport the bound from max (δ Π-renamed) (δ Π') to diamondBound
      bound-eq : max (δ Π-renamed) (δ Π') ≡ diamondBound
      bound-eq = cong (λ k → max k (δ Π')) (δ-eq-renamed ∙ sym δ-♢⊢-eq)

      dmix' : δ mix ≤ diamondBound
      dmix' = subst (δ mix ≤_) bound-eq dmix

      d_final : δ p' ≤ max (δ (♢⊢ ext freshΓ_sub freshΔ_sub Π)) (δ Π')
      d_final = subst (λ k → k ≤ diamondBound) (sym d_p') dmix'


-- =============================================================================
-- RIGHT-INTRO RULES (on right proof Π')
-- These introduce formulas to the RIGHT (succedent), so they don't introduce
-- to the left where A might appear
-- =============================================================================

-- Case 24: Right proof is ⊢¬
-- ⊢¬ Π' : Γ1 ⊢ [ (¬ B) ^ t ] ,, Δ1  where Π' : Γ1 ,, [ B ^ t ] ⊢ Δ1
-- Note: The conclusion's antecedent is Γ1, not Γ1 ,, [ B ^ t ]
Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = Γ1} {Δ' = .([ (¬ B) ^ t ] ,, Δ1)} {A = A} {s = s}
    degEq Π (⊢¬ {.Γ1} {B} {t} {Δ1} Π') wfp wfp' (acc accRec) =
    let h-dec = mixHeight-dec-r Π (⊢¬ Π') Π' (height-subproof-1 Π')
        acc' = accRec _ (inr (refl , h-dec))
        -- Recurse on premise Π' which has Γ1 ,, [ B ^ t ] as antecedent
        (mix , dmix) = Mix {Γ' = Γ1 ,, [ B ^ t ]} {Δ' = Δ1} {A = A} {s = s} degEq Π Π' wfp wfp' acc'
        -- mix : Γ ,, ((Γ1 ,, [ B ^ t ]) - A) ⊢ (Δ - A) ,, Δ1
        -- Goal: Γ ,, (Γ1 - A) ⊢ (Δ - A) ,, ([ (¬ B) ^ t ] ,, Δ1)

        Γ1-rem = Γ1 - (A ^ s)
        Δ-rem = Δ - (A ^ s)

        -- ((Γ1 ,, [ B ^ t ]) - A) needs to be subset of Γ1-rem ,, [ B ^ t ]
        sub_gamma : (((Γ1 ,, [ B ^ t ]) - (A ^ s))) ⊆ (Γ1-rem ,, [ B ^ t ])
        sub_gamma = solve (rem (var 0 ++ₑ elm 0) 1) (rem (var 0) 1 ++ₑ elm 0) ((Γ1 ∷ []) , (B ^ t ∷ A ^ s ∷ [])) {refl}

        sub_left : (Γ ,, ((Γ1 ,, [ B ^ t ]) - (A ^ s))) ⊆ ((Γ ,, Γ1-rem) ,, [ B ^ t ])
        sub_left = solve (var 1 ++ₑ rem (var 0 ++ₑ elm 0) 1) ((var 1 ++ₑ rem (var 0) 1) ++ₑ elm 0) ((Γ1 ∷ Γ ∷ []) , (B ^ t ∷ A ^ s ∷ [])) {refl}

        mix_reordered = structural sub_left subset-refl mix
        -- mix_reordered : (Γ ,, Γ1-rem) ,, [ B ^ t ] ⊢ Δ-rem ,, Δ1

        -- Apply ⊢¬ rule
        p_neg = ⊢¬ {Γ = Γ ,, Γ1-rem} {A = B} {s = t} {Δ = Δ-rem ,, Δ1} mix_reordered
        -- p_neg : Γ ,, Γ1-rem ⊢ [ (¬ B) ^ t ] ,, (Δ-rem ,, Δ1)

        -- Reorder succedent to match goal: Δ-rem ,, ([ (¬ B) ^ t ] ,, Δ1)
        sub_right : ([ (¬ B) ^ t ] ,, (Δ-rem ,, Δ1)) ⊆ (Δ-rem ,, ([ (¬ B) ^ t ] ,, Δ1))
        sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) (var 0 ++ₑ (elm 0 ++ₑ var 1)) ((Δ-rem ∷ Δ1 ∷ []) , ((¬ B) ^ t ∷ [])) {refl}

        p' = structural subset-refl sub_right p_neg

        d_mix_reordered = structural-preserves-δ sub_left subset-refl mix

        d_p' : δ p' ≡ δ mix
        d_p' = trans (structural-preserves-δ subset-refl sub_right p_neg) d_mix_reordered

        d_final : δ p' ≤ max (δ Π) (δ Π')
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- Case 25: Right proof is ⊢∧ (two-premise)
-- ⊢∧ Π'1 Π'2 : Γ1 ,, Γ2 ⊢ [ (B ∧ C) ^ t ] ,, Δ1 ,, Δ2
-- where Π'1 : Γ1 ⊢ [ B ^ t ] ,, Δ1  and  Π'2 : Γ2 ⊢ [ C ^ t ] ,, Δ2
Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = .(Γ1 ,, Γ2)} {Δ' = .([ (B ∧ C) ^ t ] ,, Δ1 ,, Δ2)} {A = A} {s = s}
    degEq Π (⊢∧ {Γ₁ = Γ1} {A = B} {s = t} {Δ₁ = Δ1} {Γ₂ = Γ2} {B = C} {Δ₂ = Δ2} Π'1 Π'2) wfp wfp' (acc accRec) =
    let wfp'1 = fst wfp'
        wfp'2 = snd wfp'

        -- Height decrease proofs for both premises
        h-dec1 = mixHeight-dec-r Π (⊢∧ Π'1 Π'2) Π'1 (height-subproof-2-l Π'1 Π'2)
        h-dec2 = mixHeight-dec-r Π (⊢∧ Π'1 Π'2) Π'2 (height-subproof-2-r Π'1 Π'2)
        acc1 = accRec _ (inr (refl , h-dec1))
        acc2 = accRec _ (inr (refl , h-dec2))

        (mix1 , dmix1) = Mix {Γ' = Γ1} {Δ' = [ B ^ t ] ,, Δ1} {A = A} {s = s} degEq Π Π'1 wfp wfp'1 acc1
        (mix2 , dmix2) = Mix {Γ' = Γ2} {Δ' = [ C ^ t ] ,, Δ2} {A = A} {s = s} degEq Π Π'2 wfp wfp'2 acc2
        -- mix1 : Γ ,, (Γ1 - A) ⊢ (Δ - A) ,, ([ B ^ t ] ,, Δ1)
        -- mix2 : Γ ,, (Γ2 - A) ⊢ (Δ - A) ,, ([ C ^ t ] ,, Δ2)
        -- Goal: Γ ,, ((Γ1 ,, Γ2) - A) ⊢ (Δ - A) ,, ([ (B ∧ C) ^ t ] ,, Δ1 ,, Δ2)

        Γ1-rem = Γ1 - (A ^ s)
        Γ2-rem = Γ2 - (A ^ s)
        Δ-rem = Δ - (A ^ s)

        -- Reorder mix1 to get [ B ^ t ] at front for ⊢∧
        sub_delta1 : (Δ-rem ,, ([ B ^ t ] ,, Δ1)) ⊆ ([ B ^ t ] ,, (Δ-rem ,, Δ1))
        sub_delta1 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ1 ∷ []) , (B ^ t ∷ [])) {refl}
        mix1_r = structural subset-refl sub_delta1 mix1
        -- mix1_r : Γ ,, Γ1-rem ⊢ [ B ^ t ] ,, (Δ-rem ,, Δ1)

        -- Reorder mix2 to get [ C ^ t ] at front for ⊢∧
        sub_delta2 : (Δ-rem ,, ([ C ^ t ] ,, Δ2)) ⊆ ([ C ^ t ] ,, (Δ-rem ,, Δ2))
        sub_delta2 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ2 ∷ []) , (C ^ t ∷ [])) {refl}
        mix2_r = structural subset-refl sub_delta2 mix2
        -- mix2_r : Γ ,, Γ2-rem ⊢ [ C ^ t ] ,, (Δ-rem ,, Δ2)

        -- Apply ⊢∧
        p_conj = ⊢∧ {Γ₁ = Γ ,, Γ1-rem} {A = B} {s = t} {Δ₁ = Δ-rem ,, Δ1} {Γ₂ = Γ ,, Γ2-rem} {B = C} {Δ₂ = Δ-rem ,, Δ2} mix1_r mix2_r
        -- p_conj : (Γ ,, Γ1-rem) ,, (Γ ,, Γ2-rem) ⊢ [ (B ∧ C) ^ t ] ,, (Δ-rem ,, Δ1) ,, (Δ-rem ,, Δ2)

        -- Contract contexts
        subLeft : ((Γ ,, Γ1-rem) ,, (Γ ,, Γ2-rem)) ⊆ (Γ ,, (Γ1-rem ,, Γ2-rem))
        subLeft = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Γ ∷ Γ1-rem ∷ Γ2-rem ∷ []) , []) {refl}

        subRight : (([ (B ∧ C) ^ t ] ,, (Δ-rem ,, Δ1)) ,, (Δ-rem ,, Δ2)) ⊆ (Δ-rem ,, ([ (B ∧ C) ^ t ] ,, Δ1 ,, Δ2))
        subRight = solve (((elm 0 ++ₑ (var 0 ++ₑ var 1)) ++ₑ (var 0 ++ₑ var 2))) (var 0 ++ₑ (elm 0 ++ₑ var 1 ++ₑ var 2)) ((Δ-rem ∷ Δ1 ∷ Δ2 ∷ []) , ((B ∧ C) ^ t ∷ [])) {refl}

        p_contracted = structural subLeft subRight p_conj

        eqGamma : ((Γ1 ,, Γ2) - (A ^ s)) ≡ (Γ1-rem ,, Γ2-rem)
        eqGamma = S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ1 Γ2

        p' = subst (λ G → Γ ,, G ⊢ Δ-rem ,, ([ (B ∧ C) ^ t ] ,, Δ1 ,, Δ2)) (sym eqGamma) p_contracted

        -- Degree bounds
        d_mix1_r = structural-preserves-δ subset-refl sub_delta1 mix1
        d_mix2_r = structural-preserves-δ subset-refl sub_delta2 mix2
        d_contracted = structural-preserves-δ subLeft subRight p_conj
        d_p'_eq = subst-preserves-δ-ctx (cong (Γ ,,_) (sym eqGamma)) p_contracted

        -- cutBound = max (max (δ Π'1) (δ Π'2)) (δ Π) since δ (⊢∧ Π'1 Π'2) = max (δ Π'1) (δ Π'2)
        cutBound = max (δ (⊢∧ Π'1 Π'2)) (δ Π)

        dΠ'1≤cutBound : δ Π'1 ≤ cutBound
        dΠ'1≤cutBound = left-left-≤-max

        dΠ'2≤cutBound : δ Π'2 ≤ cutBound
        dΠ'2≤cutBound = right-left-≤-max

        dΠ≤cutBound : δ Π ≤ cutBound
        dΠ≤cutBound = right-≤-max {δ Π} {max (δ Π'1) (δ Π'2)}

        dmix1' : δ mix1 ≤ cutBound
        dmix1' = ≤-trans dmix1 (max-least dΠ≤cutBound dΠ'1≤cutBound)

        dmix2' : δ mix2 ≤ cutBound
        dmix2' = ≤-trans dmix2 (max-least dΠ≤cutBound dΠ'2≤cutBound)

        dmix1r' = subst (_≤ cutBound) (sym d_mix1_r) dmix1'
        dmix2r' = subst (_≤ cutBound) (sym d_mix2_r) dmix2'

        dp_conj : δ p_conj ≤ cutBound
        dp_conj = max-least dmix1r' dmix2r'

        dp_contracted = subst (_≤ cutBound) (sym d_contracted) dp_conj

        dp'_cutBound : δ p' ≤ cutBound
        dp'_cutBound = subst (_≤ cutBound) (sym d_p'_eq) dp_contracted

        -- cutBound = max (δ (⊢∧ Π'1 Π'2)) (δ Π) ≡ max (δ Π) (δ (⊢∧ Π'1 Π'2)) by commutativity
        cutBound-eq : cutBound ≡ max (δ Π) (δ (⊢∧ Π'1 Π'2))
        cutBound-eq = maxComm (δ (⊢∧ Π'1 Π'2)) (δ Π)

        d_final : δ p' ≤ max (δ Π) (δ (⊢∧ Π'1 Π'2))
        d_final = subst (δ p' ≤_) cutBound-eq dp'_cutBound
    in (p' , d_final)

-- Case 26: Right proof is ⊢∨₁
-- ⊢∨₁ Π' : Γ1 ⊢ [ (B ∨ C) ^ t ] ,, Δ1  where Π' : Γ1 ⊢ [ B ^ t ] ,, Δ1
Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = Γ1} {Δ' = .([ (B ∨ C) ^ t ] ,, Δ1)} {A = A} {s = s}
    degEq Π (⊢∨₁ {.Γ1} {B} {t} {Δ1} {C} Π') wfp wfp' (acc accRec) =
    let h-dec = mixHeight-dec-r Π (⊢∨₁ Π') Π' (height-subproof-1 Π')
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ1} {Δ' = [ B ^ t ] ,, Δ1} {A = A} {s = s} degEq Π Π' wfp wfp' acc'
        -- mix : Γ ,, (Γ1 - A) ⊢ (Δ - A) ,, ([ B ^ t ] ,, Δ1)
        -- Goal: Γ ,, (Γ1 - A) ⊢ (Δ - A) ,, ([ (B ∨ C) ^ t ] ,, Δ1)

        Γ1-rem = Γ1 - (A ^ s)
        Δ-rem = Δ - (A ^ s)

        -- Move [ B ^ t ] to front
        sub_delta : (Δ-rem ,, ([ B ^ t ] ,, Δ1)) ⊆ ([ B ^ t ] ,, (Δ-rem ,, Δ1))
        sub_delta = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ1 ∷ []) , (B ^ t ∷ [])) {refl}
        mix_r = structural subset-refl sub_delta mix
        -- mix_r : Γ ,, Γ1-rem ⊢ [ B ^ t ] ,, (Δ-rem ,, Δ1)

        -- Apply ⊢∨₁
        p_disj = ⊢∨₁ {Γ = Γ ,, Γ1-rem} {A = B} {s = t} {Δ = Δ-rem ,, Δ1} {B = C} mix_r
        -- p_disj : Γ ,, Γ1-rem ⊢ [ (B ∨ C) ^ t ] ,, (Δ-rem ,, Δ1)

        -- Move [ (B ∨ C) ^ t ] back
        sub_right : ([ (B ∨ C) ^ t ] ,, (Δ-rem ,, Δ1)) ⊆ (Δ-rem ,, ([ (B ∨ C) ^ t ] ,, Δ1))
        sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) (var 0 ++ₑ (elm 0 ++ₑ var 1)) ((Δ-rem ∷ Δ1 ∷ []) , ((B ∨ C) ^ t ∷ [])) {refl}

        p' = structural subset-refl sub_right p_disj

        d_mix_r = structural-preserves-δ subset-refl sub_delta mix
        d_p' : δ p' ≡ δ mix
        d_p' = trans (structural-preserves-δ subset-refl sub_right p_disj) d_mix_r

        d_final : δ p' ≤ max (δ Π) (δ Π')
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- Case 27: Right proof is ⊢∨₂
-- ⊢∨₂ Π' : Γ1 ⊢ [ (B ∨ C) ^ t ] ,, Δ1  where Π' : Γ1 ⊢ [ C ^ t ] ,, Δ1
Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = Γ1} {Δ' = .([ (B ∨ C) ^ t ] ,, Δ1)} {A = A} {s = s}
    degEq Π (⊢∨₂ {.Γ1} {C} {t} {Δ1} {B} Π') wfp wfp' (acc accRec) =
    let h-dec = mixHeight-dec-r Π (⊢∨₂ Π') Π' (height-subproof-1 Π')
        acc' = accRec _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ1} {Δ' = [ C ^ t ] ,, Δ1} {A = A} {s = s} degEq Π Π' wfp wfp' acc'
        -- mix : Γ ,, (Γ1 - A) ⊢ (Δ - A) ,, ([ C ^ t ] ,, Δ1)
        -- Goal: Γ ,, (Γ1 - A) ⊢ (Δ - A) ,, ([ (B ∨ C) ^ t ] ,, Δ1)

        Γ1-rem = Γ1 - (A ^ s)
        Δ-rem = Δ - (A ^ s)

        -- Move [ C ^ t ] to front
        sub_delta : (Δ-rem ,, ([ C ^ t ] ,, Δ1)) ⊆ ([ C ^ t ] ,, (Δ-rem ,, Δ1))
        sub_delta = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ1 ∷ []) , (C ^ t ∷ [])) {refl}
        mix_r = structural subset-refl sub_delta mix
        -- mix_r : Γ ,, Γ1-rem ⊢ [ C ^ t ] ,, (Δ-rem ,, Δ1)

        -- Apply ⊢∨₂
        p_disj = ⊢∨₂ {Γ = Γ ,, Γ1-rem} {B = C} {s = t} {Δ = Δ-rem ,, Δ1} {A = B} mix_r
        -- p_disj : Γ ,, Γ1-rem ⊢ [ (B ∨ C) ^ t ] ,, (Δ-rem ,, Δ1)

        -- Move [ (B ∨ C) ^ t ] back
        sub_right : ([ (B ∨ C) ^ t ] ,, (Δ-rem ,, Δ1)) ⊆ (Δ-rem ,, ([ (B ∨ C) ^ t ] ,, Δ1))
        sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) (var 0 ++ₑ (elm 0 ++ₑ var 1)) ((Δ-rem ∷ Δ1 ∷ []) , ((B ∨ C) ^ t ∷ [])) {refl}

        p' = structural subset-refl sub_right p_disj

        d_mix_r = structural-preserves-δ subset-refl sub_delta mix
        d_p' : δ p' ≡ δ mix
        d_p' = trans (structural-preserves-δ subset-refl sub_right p_disj) d_mix_r

        d_final : δ p' ≤ max (δ Π) (δ Π')
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- Case 28: Right proof is ⊢⇒
-- ⊢⇒ Π' : Γ1 ⊢ [ (B ⇒ C) ^ t ] ,, Δ1  where Π' : Γ1 ,, [ B ^ t ] ⊢ [ C ^ t ] ,, Δ1
Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = Γ1} {Δ' = .([ (B ⇒ C) ^ t ] ,, Δ1)} {A = A} {s = s}
    degEq Π (⊢⇒ {.Γ1} {B} {t} {C} {Δ1} Π') wfp wfp' (acc accRec) =
    let h-dec = mixHeight-dec-r Π (⊢⇒ Π') Π' (height-subproof-1 Π')
        acc' = accRec _ (inr (refl , h-dec))
        -- Recurse on premise which has Γ1 ,, [ B ^ t ] as antecedent and [ C ^ t ] ,, Δ1 as succedent
        (mix , dmix) = Mix {Γ' = Γ1 ,, [ B ^ t ]} {Δ' = [ C ^ t ] ,, Δ1} {A = A} {s = s} degEq Π Π' wfp wfp' acc'
        -- mix : Γ ,, ((Γ1 ,, [ B ^ t ]) - A) ⊢ (Δ - A) ,, ([ C ^ t ] ,, Δ1)
        -- Goal: Γ ,, (Γ1 - A) ⊢ (Δ - A) ,, ([ (B ⇒ C) ^ t ] ,, Δ1)

        Γ1-rem = Γ1 - (A ^ s)
        Δ-rem = Δ - (A ^ s)

        -- ((Γ1 ,, [ B ^ t ]) - A) needs to be subset of Γ1-rem ,, [ B ^ t ]
        sub_left : (Γ ,, ((Γ1 ,, [ B ^ t ]) - (A ^ s))) ⊆ ((Γ ,, Γ1-rem) ,, [ B ^ t ])
        sub_left = solve (var 1 ++ₑ rem (var 0 ++ₑ elm 0) 1) ((var 1 ++ₑ rem (var 0) 1) ++ₑ elm 0) ((Γ1 ∷ Γ ∷ []) , (B ^ t ∷ A ^ s ∷ [])) {refl}

        -- For succedent: Δ-rem ,, ([ C ^ t ] ,, Δ1) needs to be reordered
        sub_delta : (Δ-rem ,, ([ C ^ t ] ,, Δ1)) ⊆ ([ C ^ t ] ,, (Δ-rem ,, Δ1))
        sub_delta = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ1 ∷ []) , (C ^ t ∷ [])) {refl}

        mix_reordered = structural sub_left sub_delta mix
        -- mix_reordered : (Γ ,, Γ1-rem) ,, [ B ^ t ] ⊢ [ C ^ t ] ,, (Δ-rem ,, Δ1)

        -- Apply ⊢⇒ rule
        p_impl = ⊢⇒ {Γ = Γ ,, Γ1-rem} {A = B} {s = t} {B = C} {Δ = Δ-rem ,, Δ1} mix_reordered
        -- p_impl : Γ ,, Γ1-rem ⊢ [ (B ⇒ C) ^ t ] ,, (Δ-rem ,, Δ1)

        -- Reorder succedent to match goal: Δ-rem ,, ([ (B ⇒ C) ^ t ] ,, Δ1)
        sub_right : ([ (B ⇒ C) ^ t ] ,, (Δ-rem ,, Δ1)) ⊆ (Δ-rem ,, ([ (B ⇒ C) ^ t ] ,, Δ1))
        sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) (var 0 ++ₑ (elm 0 ++ₑ var 1)) ((Δ-rem ∷ Δ1 ∷ []) , ((B ⇒ C) ^ t ∷ [])) {refl}

        p' = structural subset-refl sub_right p_impl

        d_mix_reordered = structural-preserves-δ sub_left sub_delta mix
        d_p' = trans (structural-preserves-δ subset-refl sub_right p_impl) d_mix_reordered
        d_final : δ p' ≤ max (δ Π) (δ Π')
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- Case 29: Right proof is ⊢□ (with eigenposition renaming)
-- ⊢□ Π' : Γ_sub ⊢ [ (□ B) ^ r ] ,, Δ_sub  where Π' : Γ_sub ⊢ [ B ^ insertToken x r ] ,, Δ_sub
Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = Γ_sub} {Δ' = .([ (□ B) ^ r ] ,, Δ_sub)} {A = A} {s = s}
    degEq Π (⊢□ {x} {r} {.Γ_sub} {Δ_sub} {B} ext freshΓ_sub freshΔ_sub Π') wfp wfp' (acc accRec) = (p' , d_final)
    where
      -- Combined contexts after mixing
      Γ_sub-rem = Γ_sub - (A ^ s)
      Δ-rem = Δ - (A ^ s)
      combined = (Γ ,, Γ_sub-rem) ,, (Δ-rem ,, Δ_sub)

      -- Compute fresh eigenposition token for combined contexts
      x' : Token
      x' = freshTokenForRename r combined Π'

      -- In the new API, the extended position is insertToken x r
      eigent : Position
      eigent = insertToken x r

      -- Get well-formedness: maxEigenposToken Π' < x (extracted from WellFormedProof)
      wf : maxEigenposToken Π' < x
      wf = fst wfp'

      wfp'-sub : WellFormedProof Π'
      wfp'-sub = snd wfp'

      -- Properties of x'
      x'-fresh-combined : TokenFresh x' combined
      x'-fresh-combined = freshTokenForRename-fresh r combined Π'

      x'-eigenpos : maxEigenposToken Π' < x'
      x'-eigenpos = freshTokenForRename-eigenpos r combined Π'

      x'∉r : x' ∉Pos r
      x'∉r = freshTokenForRename-∉r r combined Π'

      -- New eigenposition t' = substTokenToPos x [x'] eigent
      t' : Position
      t' = substPos x (singleton-pos x') eigent

      -- Use mkSingleTokenExt to construct IsSingleTokenExt from x ∉Pos r
      extSTE : IsSingleTokenExt r eigent x
      extSTE = mkSingleTokenExt r x ext

      -- Rename eigenposition using the generalized function
      rename-result = renameEigenpos-⊢□-premise-gen {r = r} {t = eigent} {x = x} {Γ = Γ_sub} {Δ = Δ_sub} {A = B} Π' extSTE freshΓ_sub freshΔ_sub wf x' x'-eigenpos x'∉r
      Π'-renamed : Γ_sub ⊢ ([ B ^ t' ] ,, Δ_sub)
      Π'-renamed = fst rename-result
      ext' : IsSingleTokenExt r t' x'
      ext' = snd rename-result

      -- Transport degree bound (proven in ProofSubst)
      δ-eq-renamed : δ Π'-renamed ≡ δ Π'
      δ-eq-renamed = δ-renameEigenpos-⊢□-premise-gen Π' extSTE freshΓ_sub freshΔ_sub wf x' x'-eigenpos x'∉r

      -- Height preservation for eigenposition renaming
      height-eq-renamed : height Π'-renamed ≡ height Π'
      height-eq-renamed = height-renameEigenpos-⊢□-premise-gen Π' extSTE freshΓ_sub freshΔ_sub wf x' x'-eigenpos x'∉r

      -- WellFormedProof for renamed proof (preserved under renaming)
      wfp'-renamed : WellFormedProof Π'-renamed
      wfp'-renamed = WellFormed-renameEigenpos-⊢□-premise-gen Π' extSTE freshΓ_sub freshΔ_sub wf x' x'-eigenpos x'∉r wfp'-sub

      -- Height decrease: mixHeight Π Π'-renamed = mixHeight Π Π' < mixHeight Π (⊢□ Π')
      h-dec-raw = mixHeight-dec-r Π (⊢□ ext freshΓ_sub freshΔ_sub Π') Π' (height-subproof-1 Π')

      -- Transport to Π'-renamed using height equality
      mixHeight-eq = cong (λ h → height Π + h) height-eq-renamed

      h-dec = subst (_< mixHeight Π (⊢□ ext freshΓ_sub freshΔ_sub Π')) (sym mixHeight-eq) h-dec-raw

      -- Mix with the renamed proof
      mix-result = Mix {Γ' = Γ_sub} {Δ' = [ B ^ t' ] ,, Δ_sub} {A = A} {s = s} degEq Π Π'-renamed wfp wfp'-renamed (accRec _ (inr (refl , h-dec)))
      mix = fst mix-result
      dmix = snd mix-result
      -- mix : Γ ,, (Γ_sub - A) ⊢ (Δ - A) ,, ([ B ^ t' ] ,, Δ_sub)

      -- Reorder to get [ B ^ t' ] at front of succedent
      sub_delta : (Δ-rem ,, ([ B ^ t' ] ,, Δ_sub)) ⊆ ([ B ^ t' ] ,, (Δ-rem ,, Δ_sub))
      sub_delta = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ_sub ∷ []) , (B ^ t' ∷ [])) {refl}

      mix_reordered = structural subset-refl sub_delta mix
      -- mix_reordered : Γ ,, Γ_sub-rem ⊢ [ B ^ t' ] ,, (Δ-rem ,, Δ_sub)

      -- Freshness of x' for combined contexts
      fresh-split = TokenFresh-split (Γ ,, Γ_sub-rem) (Δ-rem ,, Δ_sub) x' x'-fresh-combined
      freshΓ' : TokenFresh x' (Γ ,, Γ_sub-rem)
      freshΓ' = fst fresh-split
      freshΔ' : TokenFresh x' (Δ-rem ,, Δ_sub)
      freshΔ' = snd fresh-split

      -- Apply ⊢□ rule with fresh token x'
      -- Need to transport mix_reordered from t' to insertToken x' r
      t'-eq : t' ≡ insertToken x' r
      t'-eq = substPos-insertToken-eq x x' r ext

      mix_transported : Γ ,, Γ_sub-rem ⊢ [ B ^ insertToken x' r ] ,, (Δ-rem ,, Δ_sub)
      mix_transported = subst (λ (p : Position) → Γ ,, Γ_sub-rem ⊢ [ B ^ p ] ,, (Δ-rem ,, Δ_sub)) t'-eq mix_reordered

      p_boxed = ⊢□ {x'} {r} {Γ ,, Γ_sub-rem} {Δ-rem ,, Δ_sub} {B} x'∉r freshΓ' freshΔ' mix_transported
      -- p_boxed : Γ ,, Γ_sub-rem ⊢ [ (□ B) ^ r ] ,, (Δ-rem ,, Δ_sub)

      -- Reorder succedent to match goal: Δ-rem ,, ([ (□ B) ^ r ] ,, Δ_sub)
      sub_right : ([ (□ B) ^ r ] ,, (Δ-rem ,, Δ_sub)) ⊆ (Δ-rem ,, ([ (□ B) ^ r ] ,, Δ_sub))
      sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) (var 0 ++ₑ (elm 0 ++ₑ var 1)) ((Δ-rem ∷ Δ_sub ∷ []) , ((□ B) ^ r ∷ [])) {refl}

      p' = structural subset-refl sub_right p_boxed

      -- Degree preservation
      d_mix_transported : δ mix_transported ≡ δ mix_reordered
      d_mix_transported = subst-preserves-δ (cong {A = Position} (λ (p : Position) → [ B ^ p ] ,, (Δ-rem ,, Δ_sub)) t'-eq) mix_reordered
      d_mix_reordered = structural-preserves-δ subset-refl sub_delta mix
      d_p' = trans (structural-preserves-δ subset-refl sub_right p_boxed) (d_mix_transported ∙ d_mix_reordered)

      -- Transport dmix from Π'-renamed bound to Π' bound
      bound-eq : max (δ Π) (δ Π'-renamed) ≡ max (δ Π) (δ Π')
      bound-eq = cong (λ d → max (δ Π) d) δ-eq-renamed
      dmix' : δ mix ≤ max (δ Π) (δ Π')
      dmix' = subst (δ mix ≤_) bound-eq dmix

      d_final : δ p' ≤ max (δ Π) (δ Π')
      d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix'

-- Case 30: Right proof is ⊢♢
-- ⊢♢ Π' : Γ_sub ⊢ [ (♢ B) ^ r ] ,, Δ_sub  where Π' : Γ_sub ⊢ [ B ^ (r ∘ t) ] ,, Δ_sub
Mix {n = n} {Γ = Γ} {Δ = Δ} {Γ' = Γ_sub} {Δ' = .([ (♢ B) ^ r ] ,, Δ_sub)} {A = A} {s = s}
    degEq Π theProof@(⊢♢ {.Γ_sub} {B} {r} {t} {Δ_sub} Π') wfp wfp' (acc accRec) =
    let -- Full position is r ∘ t in the new API
        fullPos = r ∘ t

        -- Height decrease proof
        h-dec = mixHeight-dec-r Π theProof Π' (height-subproof-1 Π')
        acc' = accRec _ (inr (refl , h-dec))

        (mix , dmix) = Mix {Γ' = Γ_sub} {Δ' = [ B ^ fullPos ] ,, Δ_sub} {A = A} {s = s} degEq Π Π' wfp wfp' acc'
        -- mix : Γ ,, (Γ_sub - A) ⊢ (Δ - A) ,, ([ B ^ fullPos ] ,, Δ_sub)
        -- Goal: Γ ,, (Γ_sub - A) ⊢ (Δ - A) ,, ([ (♢ B) ^ r ] ,, Δ_sub)

        Γ_sub-rem = Γ_sub - (A ^ s)
        Δ-rem = Δ - (A ^ s)

        -- Reorder to get [ B ^ fullPos ] at front of succedent
        sub_delta : (Δ-rem ,, ([ B ^ fullPos ] ,, Δ_sub)) ⊆ ([ B ^ fullPos ] ,, (Δ-rem ,, Δ_sub))
        sub_delta = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ_sub ∷ []) , (B ^ fullPos ∷ [])) {refl}

        mix_reordered = structural subset-refl sub_delta mix
        -- mix_reordered : Γ ,, Γ_sub-rem ⊢ [ B ^ fullPos ] ,, (Δ-rem ,, Δ_sub)

        -- Apply ⊢♢ rule (in new API, just takes the proof)
        p_dia = ⊢♢ {Γ ,, Γ_sub-rem} {B} {r} {t} {Δ-rem ,, Δ_sub} mix_reordered
        -- p_dia : Γ ,, Γ_sub-rem ⊢ [ (♢ B) ^ r ] ,, (Δ-rem ,, Δ_sub)

        -- Reorder succedent to match goal: Δ-rem ,, ([ (♢ B) ^ r ] ,, Δ_sub)
        sub_right : ([ (♢ B) ^ r ] ,, (Δ-rem ,, Δ_sub)) ⊆ (Δ-rem ,, ([ (♢ B) ^ r ] ,, Δ_sub))
        sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) (var 0 ++ₑ (elm 0 ++ₑ var 1)) ((Δ-rem ∷ Δ_sub ∷ []) , ((♢ B) ^ r ∷ [])) {refl}

        p' = structural subset-refl sub_right p_dia

        d_mix_reordered = structural-preserves-δ subset-refl sub_delta mix
        d_p' = trans (structural-preserves-δ subset-refl sub_right p_dia) d_mix_reordered
        d_final : δ p' ≤ max (δ Π) (δ Π')
        d_final = subst (_≤ max (δ Π) (δ Π')) (sym d_p') dmix
    in (p' , d_final)

-- =============================================================================
-- Principal Cases: Both proofs introduce the cut formula
-- =============================================================================

-- Principal Case 1: ⊢¬ vs ¬⊢
-- Left: ⊢¬ Π1 : Γ1 ⊢ [ (¬ B) ^ t ] ,, Δ1  (Π1 : Γ1 ,, [ B ^ t ] ⊢ Δ1)
-- Right: ¬⊢ Π2 : Γ2 ,, [ (¬ B') ^ t' ] ⊢ Δ2'  (Π2 : Γ2 ⊢ [ B' ^ t' ] ,, Δ2)
-- Cut formula A = ¬ B
-- Three cases:
-- 1. A^s = (¬B)^t AND A^s = (¬B')^t' → Principal: cut on B with degree decrease
-- 2. A^s ≠ (¬B)^t → Recurse on Π1 with height decrease
-- 3. A^s = (¬B)^t BUT A^s ≠ (¬B')^t' → Recurse on Π2 with height decrease
Mix {n = n} {Γ = Γ1} {Δ = .([ (¬ B) ^ t ] ,, Δ1)} {Γ' = .(Γ2 ,, [ (¬ B') ^ t' ])} {Δ' = Δ2'} {A = A} {s = s}
    degEq (⊢¬ {.Γ1} {B} {t} {Δ1} Π1) (¬⊢ {Γ2} {B'} {t'} {Δ2} Π2) wfp wfp' (acc accRec) =
    handleNegCase accRec (discretePFormula (A ^ s) ((¬ B) ^ t)) (discretePFormula (A ^ s) ((¬ B') ^ t'))
  where
    GoalCtx = Γ1 ,, ((Γ2 ,, [ (¬ B') ^ t' ]) - (A ^ s))
    GoalSucc = (([ (¬ B) ^ t ] ,, Δ1) - (A ^ s)) ,, Δ2'
    GoalType = GoalCtx ⊢ GoalSucc
    GoalBound = max (δ (⊢¬ Π1)) (δ (¬⊢ Π2))
    Result = Σ GoalType (λ p → δ p ≤ GoalBound)

    handleNegCase : (∀ m' → m' <Lex (n , mixHeight (⊢¬ Π1) (¬⊢ Π2)) → Acc _<Lex_ m')
                  → Dec ((A ^ s) ≡ ((¬ B) ^ t)) → Dec ((A ^ s) ≡ ((¬ B') ^ t')) → Result
    -- Non-principal: A ≠ (¬B)^t → recurse on Π1 with height decrease
    handleNegCase accR (no neq1) _ =
      let h-dec = mixHeight-dec-l (⊢¬ Π1) Π1 (¬⊢ Π2) (height-subproof-1 Π1)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ = Γ1 ,, [ B ^ t ]} {Δ = Δ1} degEq Π1 (¬⊢ Π2) wfp wfp' acc'
          Γ'-rem = (Γ2 ,, [ (¬ B') ^ t' ]) - (A ^ s)
          Δ1-rem = Δ1 - (A ^ s)
          sub_left : ((Γ1 ,, [ B ^ t ]) ,, Γ'-rem) ⊆ ((Γ1 ,, Γ'-rem) ,, [ B ^ t ])
          sub_left = solve ((var 0 ++ₑ elm 0) ++ₑ var 1) ((var 0 ++ₑ var 1) ++ₑ elm 0) ((Γ1 ∷ Γ'-rem ∷ []) , (B ^ t ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          p_neg = ⊢¬ {Γ = Γ1 ,, Γ'-rem} {A = B} {s = t} {Δ = Δ1-rem ,, Δ2'} mix_r
          sub_right : ([ (¬ B) ^ t ] ,, (Δ1-rem ,, Δ2')) ⊆ (([ (¬ B) ^ t ] ,, Δ1-rem) ,, Δ2')
          sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((elm 0 ++ₑ var 0) ++ₑ var 1) ((Δ1-rem ∷ Δ2' ∷ []) , ((¬ B) ^ t ∷ [])) {refl}
          p_reorder = structural subset-refl sub_right p_neg
          succ-eq : ([ (¬ B) ^ t ] ,, Δ1) - (A ^ s) ≡ [ (¬ B) ^ t ] ,, Δ1-rem
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (¬ B) ^ t} {Γ = Δ1} neq1
          p' : GoalType
          p' = subst (GoalCtx ⊢_) (cong (_,, Δ2') (sym succ-eq)) p_reorder
          d_mix_r = structural-preserves-δ sub_left subset-refl mix
          d_p_reorder = structural-preserves-δ subset-refl sub_right p_neg
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ (cong (_,, Δ2') (sym succ-eq)) p_reorder) (trans d_p_reorder d_mix_r)
          d_final : δ p' ≤ GoalBound
          d_final = subst (_≤ GoalBound) (sym d_p') dmix
      in (p' , d_final)
    -- Non-principal: A = (¬B)^t, A ≠ (¬B')^t' → recurse on Π2 with height decrease
    handleNegCase accR (yes eq1) (no neq2) =
      let h-dec = mixHeight-dec-r (⊢¬ Π1) (¬⊢ Π2) Π2 (height-subproof-1 Π2)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ2} {Δ' = [ B' ^ t' ] ,, Δ2} degEq (⊢¬ Π1) Π2 wfp wfp' acc'
          Γ2-rem = Γ2 - (A ^ s)
          Δ-rem = ([ (¬ B) ^ t ] ,, Δ1) - (A ^ s)
          succ-simp : Δ-rem ≡ Δ1 - (A ^ s)
          succ-simp = lemma-removeAll-head-eq {A = A ^ s} {B = (¬ B) ^ t} {Γ = Δ1} eq1
          Δ1-rem = Δ1 - (A ^ s)
          sub_right : (Δ-rem ,, ([ B' ^ t' ] ,, Δ2)) ⊆ ([ B' ^ t' ] ,, (Δ-rem ,, Δ2))
          sub_right = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ2 ∷ []) , (B' ^ t' ∷ [])) {refl}
          mix_r = structural subset-refl sub_right mix
          p_neg = ¬⊢ {Γ = Γ1 ,, Γ2-rem} {A = B'} {s = t'} {Δ = Δ-rem ,, Δ2} mix_r
          sub_left : ((Γ1 ,, Γ2-rem) ,, [ (¬ B') ^ t' ]) ⊆ (Γ1 ,, (Γ2-rem ,, [ (¬ B') ^ t' ]))
          sub_left = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ1 ∷ Γ2-rem ∷ []) , ((¬ B') ^ t' ∷ [])) {refl}
          p_reorder = structural sub_left subset-refl p_neg
          ant-eq : (Γ2 ,, [ (¬ B') ^ t' ]) - (A ^ s) ≡ Γ2-rem ,, [ (¬ B') ^ t' ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (¬ B') ^ t'} {Γ = Γ2} neq2
          p' : GoalType
          p' = subst (λ G → Γ1 ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          d_mix_r = structural-preserves-δ subset-refl sub_right mix
          d_p_reorder = structural-preserves-δ sub_left subset-refl p_neg
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong (Γ1 ,,_) (sym ant-eq)) p_reorder) (trans d_p_reorder d_mix_r)
          d_final : δ p' ≤ GoalBound
          d_final = subst (_≤ GoalBound) (sym d_p') dmix
      in (p' , d_final)
    -- Principal: A = (¬B)^t AND A = (¬B')^t' → cross-cuts on A, then final mix on B
    handleNegCase accR (yes eq1) (yes eq2) =
      let
        -- Formula equalities
        negB-eq-negB' : (¬ B) ^ t ≡ (¬ B') ^ t'
        negB-eq-negB' = sym eq1 ∙ eq2
        B-eq-B' : B ≡ B'
        B-eq-B' = ¬-inj (cong PFormula.form negB-eq-negB')
        t-eq-t' : t ≡ t'
        t-eq-t' = cong PFormula.pos negB-eq-negB'
        Bt-eq-B't' : B ^ t ≡ B' ^ t'
        Bt-eq-B't' = cong₂ _^_ B-eq-B' t-eq-t'

        -- Degree decrease: degree B < n
        degA-eq : degree A ≡ suc (degree B)
        degA-eq = cong degree (cong PFormula.form eq1)
        degB-lt-n : degree B < n
        degB-lt-n = subst (degree B <_) (sym degA-eq ∙ degEq) (0 , refl)

        -- Abbreviations
        Γ2-A = Γ2 - (A ^ s)
        Δ1-A = Δ1 - (A ^ s)

        -- CROSS-CUT 1: Mix Π1 with (¬⊢ Π2) on A — height decrease left
        h-dec-1 = mixHeight-dec-l (⊢¬ Π1) Π1 (¬⊢ Π2) (height-subproof-1 Π1)
        acc1 = accR _ (inr (refl , h-dec-1))
        res1-pair = Mix {Γ = Γ1 ,, [ B ^ t ]} {Δ = Δ1} degEq Π1 (¬⊢ Π2) wfp wfp' acc1
        res1 = fst res1-pair
        d-res1 = snd res1-pair

        ant-simp-1 : (Γ2 ,, [ (¬ B') ^ t' ]) - (A ^ s) ≡ Γ2-A
        ant-simp-1 = lemma-removeAll-cons-eq {A = A ^ s} {B = (¬ B') ^ t'} {Γ = Γ2} eq2
        res1-cast : (Γ1 ,, [ B ^ t ]) ,, Γ2-A ⊢ Δ1-A ,, Δ2
        res1-cast = subst (λ G → (Γ1 ,, [ B ^ t ]) ,, G ⊢ Δ1-A ,, Δ2) ant-simp-1 res1

        -- CROSS-CUT 2: Mix (⊢¬ Π1) with Π2 on A — height decrease right
        h-dec-2 = mixHeight-dec-r (⊢¬ Π1) (¬⊢ Π2) Π2 (height-subproof-1 Π2)
        acc2 = accR _ (inr (refl , h-dec-2))
        res2-pair = Mix {Γ' = Γ2} {Δ' = [ B' ^ t' ] ,, Δ2} degEq (⊢¬ Π1) Π2 wfp wfp' acc2
        res2 = fst res2-pair
        d-res2 = snd res2-pair

        succ-simp-2 : ([ (¬ B) ^ t ] ,, Δ1) - (A ^ s) ≡ Δ1-A
        succ-simp-2 = lemma-removeAll-head-eq {A = A ^ s} {B = (¬ B) ^ t} {Γ = Δ1} eq1
        res2-succ : Γ1 ,, Γ2-A ⊢ Δ1-A ,, ([ B' ^ t' ] ,, Δ2)
        res2-succ = subst (λ D → Γ1 ,, Γ2-A ⊢ D ,, ([ B' ^ t' ] ,, Δ2)) succ-simp-2 res2
        res2-cast : Γ1 ,, Γ2-A ⊢ Δ1-A ,, ([ B ^ t ] ,, Δ2)
        res2-cast = subst (λ pf → Γ1 ,, Γ2-A ⊢ Δ1-A ,, ([ pf ] ,, Δ2)) (sym Bt-eq-B't') res2-succ

        -- FINAL MIX ON B: degree decrease
        res2-wf = makeWellFormed res2-cast
        res1-wf = makeWellFormed res1-cast
        acc3 = accR (degree B , mixHeight res2-wf res1-wf) (inl degB-lt-n)
        mix3-pair = Mix {n = degree B} {A = B} {s = t} refl
                       res2-wf res1-wf
                       (makeWellFormed-WellFormed res2-cast) (makeWellFormed-WellFormed res1-cast) acc3
        mix3 = fst mix3-pair
        d-mix3 = snd mix3-pair

        -- STRUCTURAL WEAKENING
        sub-ant = contraction-++ˡ (removeAll-drop-singleton-l Γ1 Γ2-A (B ^ t))
        sub-succ = contraction-++ʳ (removeAll-drop-singleton-r Δ1-A Δ2 (B ^ t))
        p_struct = structural sub-ant sub-succ mix3

        -- TRANSPORT TO FULL GOAL TYPE
        ant-eq : (Γ2 ,, [ (¬ B') ^ t' ]) - (A ^ s) ≡ Γ2-A
        ant-eq = ant-simp-1
        succ-eq : ([ (¬ B) ^ t ] ,, Δ1) - (A ^ s) ≡ Δ1-A
        succ-eq = succ-simp-2
        p_ctx : GoalCtx ⊢ Δ1-A ,, Δ2
        p_ctx = subst (λ G → Γ1 ,, G ⊢ Δ1-A ,, Δ2) (sym ant-eq) p_struct
        p' : GoalType
        p' = subst (GoalCtx ⊢_) (cong (_,, Δ2) (sym succ-eq)) p_ctx

        -- DEGREE BOUND
        δ-res1-cast-eq : δ res1-cast ≡ δ res1
        δ-res1-cast-eq = subst-preserves-δ-ctx (cong ((Γ1 ,, [ B ^ t ]) ,,_) ant-simp-1) res1
        δ-res1-wf-eq : δ res1-wf ≡ δ res1
        δ-res1-wf-eq = trans (δ-makeWellFormed res1-cast) δ-res1-cast-eq
        res1-bound : δ res1-wf ≤ GoalBound
        res1-bound = subst (_≤ GoalBound) (sym δ-res1-wf-eq) d-res1

        δ-res2-succ-eq : δ res2-succ ≡ δ res2
        δ-res2-succ-eq = subst-preserves-δ (cong (_,, ([ B' ^ t' ] ,, Δ2)) succ-simp-2) res2
        δ-res2-cast-eq : δ res2-cast ≡ δ res2
        δ-res2-cast-eq = trans (subst-preserves-δ (cong (λ pf → Δ1-A ,, ([ pf ] ,, Δ2)) (sym Bt-eq-B't')) res2-succ) δ-res2-succ-eq
        δ-res2-wf-eq : δ res2-wf ≡ δ res2
        δ-res2-wf-eq = trans (δ-makeWellFormed res2-cast) δ-res2-cast-eq
        res2-bound : δ res2-wf ≤ GoalBound
        res2-bound = subst (_≤ GoalBound) (sym δ-res2-wf-eq) d-res2

        max-res-bound : max (δ res2-wf) (δ res1-wf) ≤ GoalBound
        max-res-bound = max-least res2-bound res1-bound
        mix3-bound : δ mix3 ≤ GoalBound
        mix3-bound = ≤-trans d-mix3 max-res-bound

        δ-p-struct : δ p_struct ≡ δ mix3
        δ-p-struct = structural-preserves-δ sub-ant sub-succ mix3
        δ-p-ctx : δ p_ctx ≡ δ p_struct
        δ-p-ctx = subst-preserves-δ-ctx (cong (Γ1 ,,_) (sym ant-eq)) p_struct
        δ-p' : δ p' ≡ δ p_ctx
        δ-p' = subst-preserves-δ (cong (_,, Δ2) (sym succ-eq)) p_ctx
        d_final : δ p' ≤ GoalBound
        d_final = subst (_≤ GoalBound) (sym (δ-p' ∙ δ-p-ctx ∙ δ-p-struct)) mix3-bound
      in (p' , d_final)

-- Principal Case 2: ⊢∧ vs ∧₁⊢
-- Left: ⊢∧ Π1 Π2 : (Γ1 ,, Γ2) ⊢ [ (B ∧ C) ^ t ] ,, (Δ1 ,, Δ2)
--   where Π1 : Γ1 ⊢ [ B ^ t ] ,, Δ1  and  Π2 : Γ2 ⊢ [ C ^ t ] ,, Δ2
-- Right: ∧₁⊢ Π1' : (Γ' ,, [ (B' ∧ C') ^ t' ]) ⊢ Δ''
--   where Π1' : Γ' ,, [ B' ^ t' ] ⊢ Δ''
Mix {n = n} {Γ = .(Γ1 ,, Γ2)} {Δ = .([ (B ∧ C) ^ t ] ,, Δ1 ,, Δ2)}
    {Γ' = .(Γ' ,, [ (B' ∧ C') ^ t' ])} {Δ' = Δ''} {A = A} {s = s}
    degEq (⊢∧ {Γ₁ = Γ1} {A = B} {s = t} {Δ₁ = Δ1} {Γ₂ = Γ2} {B = C} {Δ₂ = Δ2} Π1 Π2)
          (∧₁⊢ {Γ = Γ'} {A = B'} {s = t'} {Δ = Δ''} {B = C'} Π1') wfp wfp' (acc accRec) =
    handleAndCase1 accRec (discretePFormula (A ^ s) ((B ∧ C) ^ t)) (discretePFormula (A ^ s) ((B' ∧ C') ^ t'))
  where
    GoalCtx = (Γ1 ,, Γ2) ,, ((Γ' ,, [ (B' ∧ C') ^ t' ]) - (A ^ s))
    GoalSucc = (([ (B ∧ C) ^ t ] ,, Δ1 ,, Δ2) - (A ^ s)) ,, Δ''
    GoalType = GoalCtx ⊢ GoalSucc
    GoalBound = max (δ (⊢∧ Π1 Π2)) (δ (∧₁⊢ Π1'))
    Result = Σ GoalType (λ p → δ p ≤ GoalBound)

    handleAndCase1 : (∀ m' → m' <Lex (n , mixHeight (⊢∧ Π1 Π2) (∧₁⊢ Π1')) → Acc _<Lex_ m')
                   → Dec ((A ^ s) ≡ ((B ∧ C) ^ t)) → Dec ((A ^ s) ≡ ((B' ∧ C') ^ t')) → Result
    -- Non-principal on left: A ≠ (B∧C)^t
    handleAndCase1 accR (no neq1) _ =
      let h-dec1 = mixHeight-dec-l (⊢∧ Π1 Π2) Π1 (∧₁⊢ Π1') (height-subproof-2-l Π1 Π2)
          h-dec2 = mixHeight-dec-l (⊢∧ Π1 Π2) Π2 (∧₁⊢ Π1') (height-subproof-2-r Π1 Π2)
          acc1 = accR _ (inr (refl , h-dec1))
          acc2 = accR _ (inr (refl , h-dec2))
          (mix1 , dmix1) = Mix {Γ = Γ1} {Δ = [ B ^ t ] ,, Δ1} degEq Π1 (∧₁⊢ Π1') (fst wfp) wfp' acc1
          (mix2 , dmix2) = Mix {Γ = Γ2} {Δ = [ C ^ t ] ,, Δ2} degEq Π2 (∧₁⊢ Π1') (snd wfp) wfp' acc2
          Γ'-rem = (Γ' ,, [ (B' ∧ C') ^ t' ]) - (A ^ s)
          Δ1-rem = Δ1 - (A ^ s)
          Δ2-rem = Δ2 - (A ^ s)
          -- Reorder succedents to get [B^t] and [C^t] at front
          sub_delta1 : ((([ B ^ t ] ,, Δ1) - (A ^ s)) ,, Δ'') ⊆ ([ B ^ t ] ,, (Δ1-rem ,, Δ''))
          sub_delta1 = solve (rem (elm 0 ++ₑ var 0) 1 ++ₑ var 1) (elm 0 ++ₑ (rem (var 0) 1 ++ₑ var 1)) ((Δ1 ∷ Δ'' ∷ []) , (B ^ t ∷ A ^ s ∷ [])) {refl}
          mix1_r = structural subset-refl sub_delta1 mix1
          sub_delta2 : ((([ C ^ t ] ,, Δ2) - (A ^ s)) ,, Δ'') ⊆ ([ C ^ t ] ,, (Δ2-rem ,, Δ''))
          sub_delta2 = solve (rem (elm 0 ++ₑ var 0) 1 ++ₑ var 1) (elm 0 ++ₑ (rem (var 0) 1 ++ₑ var 1)) ((Δ2 ∷ Δ'' ∷ []) , (C ^ t ∷ A ^ s ∷ [])) {refl}
          mix2_r = structural subset-refl sub_delta2 mix2
          -- Apply ⊢∧
          p_conj = ⊢∧ {Γ₁ = Γ1 ,, Γ'-rem} {A = B} {s = t} {Δ₁ = Δ1-rem ,, Δ''} {Γ₂ = Γ2 ,, Γ'-rem} {B = C} {Δ₂ = Δ2-rem ,, Δ''} mix1_r mix2_r
          -- Contract
          subLeft : ((Γ1 ,, Γ'-rem) ,, (Γ2 ,, Γ'-rem)) ⊆ ((Γ1 ,, Γ2) ,, Γ'-rem)
          subLeft = solve ((var 0 ++ₑ var 2) ++ₑ (var 1 ++ₑ var 2)) ((var 0 ++ₑ var 1) ++ₑ var 2) ((Γ1 ∷ Γ2 ∷ Γ'-rem ∷ []) , []) {refl}
          subRight : (([ (B ∧ C) ^ t ] ,, (Δ1-rem ,, Δ'')) ,, (Δ2-rem ,, Δ'')) ⊆ (([ (B ∧ C) ^ t ] ,, Δ1-rem ,, Δ2-rem) ,, Δ'')
          subRight = solve ((elm 0 ++ₑ (var 0 ++ₑ var 2)) ++ₑ (var 1 ++ₑ var 2)) ((elm 0 ++ₑ var 0 ++ₑ var 1) ++ₑ var 2) ((Δ1-rem ∷ Δ2-rem ∷ Δ'' ∷ []) , ((B ∧ C) ^ t ∷ [])) {refl}
          p_contracted = structural subLeft subRight p_conj
          -- Transport succedent
          succ-eq : ([ (B ∧ C) ^ t ] ,, Δ1 ,, Δ2) - (A ^ s) ≡ [ (B ∧ C) ^ t ] ,, Δ1-rem ,, Δ2-rem
          succ-eq = trans (lemma-removeAll-head-neq neq1) (cong ([ (B ∧ C) ^ t ] ,,_) (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Δ1 Δ2))
          p' : GoalType
          p' = subst (λ D → GoalCtx ⊢ D ,, Δ'') (sym succ-eq) p_contracted
          -- Degree bounds
          d_mix1_r = structural-preserves-δ subset-refl sub_delta1 mix1
          d_mix2_r = structural-preserves-δ subset-refl sub_delta2 mix2
          d_contracted = structural-preserves-δ subLeft subRight p_conj
          d_p'_eq = subst-preserves-δ (cong (_,, Δ'') (sym succ-eq)) p_contracted
          -- δ (⊢∧ Π1 Π2) = max (δ Π1) (δ Π2) by definition
          dΠ1≤G : δ Π1 ≤ GoalBound
          dΠ1≤G = left-left-≤-max
          dΠ'≤G : δ (∧₁⊢ Π1') ≤ GoalBound
          dΠ'≤G = right-≤-max {δ (∧₁⊢ Π1')} {δ (⊢∧ Π1 Π2)}
          dmix1' = subst (_≤ GoalBound) (sym d_mix1_r) (≤-trans dmix1 (max-least dΠ1≤G dΠ'≤G))
          dΠ2≤G : δ Π2 ≤ GoalBound
          dΠ2≤G = right-left-≤-max
          dmix2' = subst (_≤ GoalBound) (sym d_mix2_r) (≤-trans dmix2 (max-least dΠ2≤G dΠ'≤G))
          dpConj = max-least dmix1' dmix2'
          d_final : δ p' ≤ GoalBound
          d_final = subst (_≤ GoalBound) (sym (d_p'_eq ∙ d_contracted)) dpConj
      in (p' , d_final)
    -- Non-principal on right: A = (B∧C)^t, A ≠ (B'∧C')^t'
    handleAndCase1 accR (yes eq1) (no neq2) =
      let h-dec = mixHeight-dec-r (⊢∧ Π1 Π2) (∧₁⊢ Π1') Π1' (height-subproof-1 Π1')
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ' ,, [ B' ^ t' ]} {Δ' = Δ''} degEq (⊢∧ Π1 Π2) Π1' wfp wfp' acc'
          Γ'-A = Γ' - (A ^ s)
          sub_left : ((Γ1 ,, Γ2) ,, ((Γ' ,, [ B' ^ t' ]) - (A ^ s))) ⊆ (((Γ1 ,, Γ2) ,, Γ'-A) ,, [ B' ^ t' ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) (((Γ1 ,, Γ2) ∷ Γ' ∷ []) , (B' ^ t' ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          p_and = ∧₁⊢ {(Γ1 ,, Γ2) ,, Γ'-A} {B'} {t'} {GoalSucc} {C'} mix_r
          sub_left2 : (((Γ1 ,, Γ2) ,, Γ'-A) ,, [ (B' ∧ C') ^ t' ]) ⊆ ((Γ1 ,, Γ2) ,, (Γ'-A ,, [ (B' ∧ C') ^ t' ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) (((Γ1 ,, Γ2) ∷ Γ'-A ∷ []) , ((B' ∧ C') ^ t' ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_and
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (B' ∧ C') ^ t'} {Γ = Γ'} neq2
          p' : GoalType
          p' = subst (λ G → (Γ1 ,, Γ2) ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong ((Γ1 ,, Γ2) ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_and) (structural-preserves-δ sub_left subset-refl mix))
          d_final : δ p' ≤ GoalBound
          d_final = subst (_≤ GoalBound) (sym d_p') dmix
      in (p' , d_final)
    -- Principal: A = (B∧C)^t AND A = (B'∧C')^t'
    handleAndCase1 accR (yes eq1) (yes eq2) =
      let
        -- Formula equalities
        BC-eq-B'C' : (B ∧ C) ^ t ≡ (B' ∧ C') ^ t'
        BC-eq-B'C' = sym eq1 ∙ eq2
        B-eq-B' : B ≡ B'
        B-eq-B' = ∧-inj-l (cong PFormula.form BC-eq-B'C')
        C-eq-C' : C ≡ C'
        C-eq-C' = ∧-inj-r (cong PFormula.form BC-eq-B'C')
        t-eq-t' : t ≡ t'
        t-eq-t' = cong PFormula.pos BC-eq-B'C'
        Bt-eq-B't' : B ^ t ≡ B' ^ t'
        Bt-eq-B't' = cong₂ _^_ B-eq-B' t-eq-t'

        -- Degree decrease: degree B < n
        degA-eq : degree A ≡ suc (max (degree B) (degree C))
        degA-eq = cong degree (cong PFormula.form eq1)
        degB-lt-n : degree B < n
        degB-lt-n = subst (degree B <_) (sym degA-eq ∙ degEq) (degree-∧-l B C)

        -- B^t ≠ A^s (subformula)
        B-neq-A : (B ^ t) ≢ (A ^ s)
        B-neq-A eq = subformula-neq-∧-l {B = B} {C = C} {s = t} {t = s}
                     (subst (λ X → B ^ t ≡ X ^ s) (cong PFormula.form eq1) eq)

        -- Abbreviations
        Γ'-A = Γ' - (A ^ s)
        Δ1-A = Δ1 - (A ^ s)
        Δ2-A = Δ2 - (A ^ s)

        -- CROSS-CUT 1: Mix Π1 with (∧₁⊢ Π1') on A — height decrease left
        h-dec-1 = mixHeight-dec-l (⊢∧ Π1 Π2) Π1 (∧₁⊢ Π1') (height-subproof-2-l Π1 Π2)
        acc1 = accR _ (inr (refl , h-dec-1))
        res1-pair = Mix {Γ = Γ1} {Δ = [ B ^ t ] ,, Δ1} degEq Π1 (∧₁⊢ Π1') (fst wfp) wfp' acc1
        res1 = fst res1-pair
        d-res1 = snd res1-pair
        -- res1 : Γ1 ,, ((Γ' ,, [(B'∧C')^t']) - A) ⊢ ([B^t] ,, Δ1) - A ,, Δ''

        -- Simplify res1 antecedent: (Γ' ,, [(B'∧C')^t']) - A = Γ'-A
        ant-simp-1 : (Γ' ,, [ (B' ∧ C') ^ t' ]) - (A ^ s) ≡ Γ'-A
        ant-simp-1 = lemma-removeAll-cons-eq {A = A ^ s} {B = (B' ∧ C') ^ t'} {Γ = Γ'} eq2

        -- Simplify res1 succedent: ([B^t] ,, Δ1) - A = [B^t] ,, Δ1-A
        succ-simp-1 : ([ B ^ t ] ,, Δ1) - (A ^ s) ≡ [ B ^ t ] ,, Δ1-A
        succ-simp-1 = removeAll-prepend-pf-neq (λ eq → B-neq-A (sym eq))

        res1-cast : Γ1 ,, Γ'-A ⊢ ([ B ^ t ] ,, Δ1-A) ,, Δ''
        res1-cast = subst2 (λ G D → Γ1 ,, G ⊢ D ,, Δ'') ant-simp-1 succ-simp-1 res1

        -- CROSS-CUT 2: Mix (⊢∧ Π1 Π2) with Π1' on A — height decrease right
        h-dec-2 = mixHeight-dec-r (⊢∧ Π1 Π2) (∧₁⊢ Π1') Π1' (height-subproof-1 Π1')
        acc2 = accR _ (inr (refl , h-dec-2))
        res2-pair = Mix {Γ' = Γ' ,, [ B' ^ t' ]} {Δ' = Δ''} degEq (⊢∧ Π1 Π2) Π1' wfp wfp' acc2
        res2 = fst res2-pair
        d-res2 = snd res2-pair
        -- res2 : (Γ1 ,, Γ2) ,, ((Γ' ,, [B'^t']) - A) ⊢ ([(B∧C)^t] ,, Δ1 ,, Δ2) - A ,, Δ''

        -- Simplify res2 succedent: ([(B∧C)^t] ,, Δ1 ,, Δ2) - A = (Δ1 ,, Δ2) - A
        succ-simp-2 : ([ (B ∧ C) ^ t ] ,, (Δ1 ,, Δ2)) - (A ^ s) ≡ (Δ1 ,, Δ2) - (A ^ s)
        succ-simp-2 = lemma-removeAll-head-eq {A = A ^ s} {B = (B ∧ C) ^ t} {Γ = Δ1 ,, Δ2} eq1
        res2-succ : (Γ1 ,, Γ2) ,, ((Γ' ,, [ B' ^ t' ]) - (A ^ s)) ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ''
        res2-succ = subst (λ D → (Γ1 ,, Γ2) ,, ((Γ' ,, [ B' ^ t' ]) - (A ^ s)) ⊢ D ,, Δ'') succ-simp-2 res2

        -- Simplify res2 antecedent: (Γ' ,, [B'^t']) - A = Γ'-A ,, [B'^t'] (since B'^t' ≠ A)
        B'-neq-A : (B' ^ t') ≢ (A ^ s)
        B'-neq-A eq = subformula-neq-∧-l {B = B'} {C = C'} {s = t'} {t = s}
                      (subst (λ X → B' ^ t' ≡ X ^ s) (cong PFormula.form eq2) eq)
        ant-simp-2 : (Γ' ,, [ B' ^ t' ]) - (A ^ s) ≡ Γ'-A ,, [ B' ^ t' ]
        ant-simp-2 = removeAll-++-r-pf-neq (λ eq → B'-neq-A (sym eq))
        -- Cast B'^t' to B^t
        res2-ant-cast : (Γ1 ,, Γ2) ,, (Γ'-A ,, [ B ^ t ]) ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ''
        res2-ant-cast = subst (λ pf → (Γ1 ,, Γ2) ,, (Γ'-A ,, [ pf ]) ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ'')
                              (sym Bt-eq-B't')
                              (subst (λ G → (Γ1 ,, Γ2) ,, G ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ'') ant-simp-2 res2-succ)
        -- Reassociate antecedent
        ant-assoc : (Γ1 ,, Γ2) ,, (Γ'-A ,, [ B ^ t ]) ≡ ((Γ1 ,, Γ2) ,, Γ'-A) ,, [ B ^ t ]
        ant-assoc = sym (++-assoc (Γ1 ,, Γ2) Γ'-A [ B ^ t ])
        res2-cast : ((Γ1 ,, Γ2) ,, Γ'-A) ,, [ B ^ t ] ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ''
        res2-cast = subst (_⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ'') ant-assoc res2-ant-cast

        -- FINAL MIX ON B: degree decrease
        res1-wf = makeWellFormed res1-cast
        res2-wf = makeWellFormed res2-cast
        acc3 = accR (degree B , mixHeight res1-wf res2-wf) (inl degB-lt-n)
        mix3-pair = Mix {n = degree B} {A = B} {s = t} refl
                       res1-wf res2-wf
                       (makeWellFormed-WellFormed res1-cast) (makeWellFormed-WellFormed res2-cast) acc3
        mix3 = fst mix3-pair
        d-mix3 = snd mix3-pair
        -- mix3 : (Γ1 ,, Γ'-A) ,, ((((Γ1,,Γ2) ,, Γ'-A) ,, [B^t]) - B^t)
        --      ⊢ (([B^t] ,, Δ1-A ,, Δ'') - B^t) ,, (((Δ1,,Δ2)-A) ,, Δ'')

        -- STRUCTURAL CONTRACTION
        -- Goal ant: (Γ1 ,, Γ2) ,, Γ'-A
        -- Goal succ: ((Δ1 ,, Δ2) - A) ,, Δ''

        -- sub-ant: mix3-ant ⊆ goal-ant
        sub-ant = subset-concat {G = (Γ1 ,, Γ2) ,, Γ'-A}
          (subset-concat (λ y yIn → mem-++-l (mem-++-l yIn)) (λ y yIn → mem-++-r (Γ1 ,, Γ2) yIn))
          (removeAll-append-singleton-⊆ ((Γ1 ,, Γ2) ,, Γ'-A) (B ^ t))

        -- sub-succ: mix3-succ ⊆ goal-succ
        succ-left-sub = subset-trans {l2 = Δ1-A ,, Δ''}
          (removeAll-drop-singleton-r [] (Δ1-A ,, Δ'') (B ^ t))
          (subset-concat
            (λ y yIn → mem-++-l (let (yInΔ1 , y≠A) = removeAll-mem yIn in mem-removeAll (mem-++-l yInΔ1) y≠A))
            (λ y yIn → mem-++-r ((Δ1 ,, Δ2) - (A ^ s)) yIn))

        sub-succ = subset-concat succ-left-sub (λ y yIn → yIn)

        p_struct = structural sub-ant sub-succ mix3

        -- TRANSPORT TO FULL GOAL TYPE
        ant-eq-full : (Γ' ,, [ (B' ∧ C') ^ t' ]) - (A ^ s) ≡ Γ'-A
        ant-eq-full = ant-simp-1
        succ-eq-full : ([ (B ∧ C) ^ t ] ,, Δ1 ,, Δ2) - (A ^ s) ≡ (Δ1 ,, Δ2) - (A ^ s)
        succ-eq-full = succ-simp-2
        p_ctx : GoalCtx ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ''
        p_ctx = subst (λ G → (Γ1 ,, Γ2) ,, G ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ'') (sym ant-eq-full) p_struct
        p' : GoalType
        p' = subst (GoalCtx ⊢_) (cong (_,, Δ'') (sym succ-eq-full)) p_ctx

        -- DEGREE BOUND
        -- d-res1 : δ res1 ≤ max (δ Π1) (δ (∧₁⊢ Π1'))
        -- GoalBound = max (δ (⊢∧ Π1 Π2)) (δ (∧₁⊢ Π1'))
        -- Need: max (δ Π1) (δ (∧₁⊢ Π1')) ≤ GoalBound
        δ-res1-cast-eq : δ res1-cast ≡ δ res1
        δ-res1-cast-eq = subst2-preserves-δ (Γ1 ,,_) (_,, Δ'') ant-simp-1 succ-simp-1 res1
        δ-res1-wf-eq : δ res1-wf ≡ δ res1
        δ-res1-wf-eq = trans (δ-makeWellFormed res1-cast) δ-res1-cast-eq
        res1-intermediate : max (δ Π1) (δ (∧₁⊢ Π1')) ≤ GoalBound
        res1-intermediate = max-least
          (left-left-≤-max)
          (right-≤-max {δ (∧₁⊢ Π1')} {δ (⊢∧ Π1 Π2)})
        res1-bound : δ res1-wf ≤ GoalBound
        res1-bound = subst (_≤ GoalBound) (sym δ-res1-wf-eq) (≤-trans d-res1 res1-intermediate)

        -- d-res2 : δ res2 ≤ max (δ (⊢∧ Π1 Π2)) (δ Π1')
        -- δ (∧₁⊢ Π1') = δ Π1', so GoalBound = max (δ (⊢∧ Π1 Π2)) (δ Π1')
        δ-res2-succ-eq : δ res2-succ ≡ δ res2
        δ-res2-succ-eq = subst-preserves-δ (cong (_,, Δ'') succ-simp-2) res2
        δ-res2-ant-eq : δ res2-ant-cast ≡ δ res2
        δ-res2-ant-eq = trans
          (subst-preserves-δ-ctx (cong (λ pf → (Γ1 ,, Γ2) ,, (Γ'-A ,, [ pf ])) (sym Bt-eq-B't'))
            (subst (λ G → (Γ1 ,, Γ2) ,, G ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ'') ant-simp-2 res2-succ))
          (trans (subst-preserves-δ-ctx (cong ((Γ1 ,, Γ2) ,,_) ant-simp-2) res2-succ) δ-res2-succ-eq)
        δ-res2-cast-eq : δ res2-cast ≡ δ res2
        δ-res2-cast-eq = trans (subst-preserves-δ-ctx ant-assoc res2-ant-cast) δ-res2-ant-eq
        δ-res2-wf-eq : δ res2-wf ≡ δ res2
        δ-res2-wf-eq = trans (δ-makeWellFormed res2-cast) δ-res2-cast-eq
        res2-bound : δ res2-wf ≤ GoalBound
        res2-bound = subst (_≤ GoalBound) (sym δ-res2-wf-eq) d-res2

        max-res-bound : max (δ res1-wf) (δ res2-wf) ≤ GoalBound
        max-res-bound = max-least res1-bound res2-bound
        mix3-bound : δ mix3 ≤ GoalBound
        mix3-bound = ≤-trans d-mix3 max-res-bound

        δ-p-struct : δ p_struct ≡ δ mix3
        δ-p-struct = structural-preserves-δ sub-ant sub-succ mix3
        δ-p-ctx : δ p_ctx ≡ δ p_struct
        δ-p-ctx = subst-preserves-δ-ctx (cong ((Γ1 ,, Γ2) ,,_) (sym ant-eq-full)) p_struct
        δ-p' : δ p' ≡ δ p_ctx
        δ-p' = subst-preserves-δ (cong (_,, Δ'') (sym succ-eq-full)) p_ctx
        d_final : δ p' ≤ GoalBound
        d_final = subst (_≤ GoalBound) (sym (δ-p' ∙ δ-p-ctx ∙ δ-p-struct)) mix3-bound
      in (p' , d_final)

-- Principal Case 3: ⊢∧ vs ∧₂⊢
-- Left: ⊢∧ Π1 Π2 : (Γ1 ,, Γ2) ⊢ [ (B ∧ C) ^ t ] ,, (Δ1 ,, Δ2)
-- Right: ∧₂⊢ Π1' : (Γ' ,, [ (C' ∧ B') ^ t' ]) ⊢ Δ''  where Π1' : Γ' ,, [ B' ^ t' ] ⊢ Δ''
-- Note: ∧₂⊢ extracts the SECOND conjunct B' from (C' ∧ B')
Mix {n = n} {Γ = .(Γ1 ,, Γ2)} {Δ = .([ (B ∧ C) ^ t ] ,, Δ1 ,, Δ2)}
    {Γ' = .(Γ' ,, [ (C' ∧ B') ^ t' ])} {Δ' = Δ''} {A = A} {s = s}
    degEq (⊢∧ {Γ₁ = Γ1} {A = B} {s = t} {Δ₁ = Δ1} {Γ₂ = Γ2} {B = C} {Δ₂ = Δ2} Π1 Π2)
          (∧₂⊢ {Γ = Γ'} {B = B'} {s = t'} {Δ = Δ''} {A = C'} Π1') wfp wfp' (acc accRec) =
    handleAndCase2 accRec (discretePFormula (A ^ s) ((B ∧ C) ^ t)) (discretePFormula (A ^ s) ((C' ∧ B') ^ t'))
  where
    GoalCtx = (Γ1 ,, Γ2) ,, ((Γ' ,, [ (C' ∧ B') ^ t' ]) - (A ^ s))
    GoalSucc = (([ (B ∧ C) ^ t ] ,, Δ1 ,, Δ2) - (A ^ s)) ,, Δ''
    GoalType = GoalCtx ⊢ GoalSucc
    GoalBound = max (δ (⊢∧ Π1 Π2)) (δ (∧₂⊢ Π1'))
    Result = Σ GoalType (λ p → δ p ≤ GoalBound)

    handleAndCase2 : (∀ m' → m' <Lex (n , mixHeight (⊢∧ Π1 Π2) (∧₂⊢ Π1')) → Acc _<Lex_ m')
                   → Dec ((A ^ s) ≡ ((B ∧ C) ^ t)) → Dec ((A ^ s) ≡ ((C' ∧ B') ^ t')) → Result
    handleAndCase2 accR (no neq1) _ =
      let h-dec1 = mixHeight-dec-l (⊢∧ Π1 Π2) Π1 (∧₂⊢ Π1') (height-subproof-2-l Π1 Π2)
          h-dec2 = mixHeight-dec-l (⊢∧ Π1 Π2) Π2 (∧₂⊢ Π1') (height-subproof-2-r Π1 Π2)
          acc1 = accR _ (inr (refl , h-dec1))
          acc2 = accR _ (inr (refl , h-dec2))
          (mix1 , dmix1) = Mix {Γ = Γ1} {Δ = [ B ^ t ] ,, Δ1} degEq Π1 (∧₂⊢ Π1') (fst wfp) wfp' acc1
          (mix2 , dmix2) = Mix {Γ = Γ2} {Δ = [ C ^ t ] ,, Δ2} degEq Π2 (∧₂⊢ Π1') (snd wfp) wfp' acc2
          Γ'-rem = (Γ' ,, [ (C' ∧ B') ^ t' ]) - (A ^ s)
          Δ1-rem = Δ1 - (A ^ s)
          Δ2-rem = Δ2 - (A ^ s)
          sub_delta1 : ((([ B ^ t ] ,, Δ1) - (A ^ s)) ,, Δ'') ⊆ ([ B ^ t ] ,, (Δ1-rem ,, Δ''))
          sub_delta1 = solve (rem (elm 0 ++ₑ var 0) 1 ++ₑ var 1) (elm 0 ++ₑ (rem (var 0) 1 ++ₑ var 1)) ((Δ1 ∷ Δ'' ∷ []) , (B ^ t ∷ A ^ s ∷ [])) {refl}
          mix1_r = structural subset-refl sub_delta1 mix1
          sub_delta2 : ((([ C ^ t ] ,, Δ2) - (A ^ s)) ,, Δ'') ⊆ ([ C ^ t ] ,, (Δ2-rem ,, Δ''))
          sub_delta2 = solve (rem (elm 0 ++ₑ var 0) 1 ++ₑ var 1) (elm 0 ++ₑ (rem (var 0) 1 ++ₑ var 1)) ((Δ2 ∷ Δ'' ∷ []) , (C ^ t ∷ A ^ s ∷ [])) {refl}
          mix2_r = structural subset-refl sub_delta2 mix2
          p_conj = ⊢∧ {Γ₁ = Γ1 ,, Γ'-rem} {A = B} {s = t} {Δ₁ = Δ1-rem ,, Δ''} {Γ₂ = Γ2 ,, Γ'-rem} {B = C} {Δ₂ = Δ2-rem ,, Δ''} mix1_r mix2_r
          subLeft : ((Γ1 ,, Γ'-rem) ,, (Γ2 ,, Γ'-rem)) ⊆ ((Γ1 ,, Γ2) ,, Γ'-rem)
          subLeft = solve ((var 0 ++ₑ var 2) ++ₑ (var 1 ++ₑ var 2)) ((var 0 ++ₑ var 1) ++ₑ var 2) ((Γ1 ∷ Γ2 ∷ Γ'-rem ∷ []) , []) {refl}
          subRight : (([ (B ∧ C) ^ t ] ,, (Δ1-rem ,, Δ'')) ,, (Δ2-rem ,, Δ'')) ⊆ (([ (B ∧ C) ^ t ] ,, Δ1-rem ,, Δ2-rem) ,, Δ'')
          subRight = solve ((elm 0 ++ₑ (var 0 ++ₑ var 2)) ++ₑ (var 1 ++ₑ var 2)) ((elm 0 ++ₑ var 0 ++ₑ var 1) ++ₑ var 2) ((Δ1-rem ∷ Δ2-rem ∷ Δ'' ∷ []) , ((B ∧ C) ^ t ∷ [])) {refl}
          p_contracted = structural subLeft subRight p_conj
          succ-eq : ([ (B ∧ C) ^ t ] ,, Δ1 ,, Δ2) - (A ^ s) ≡ [ (B ∧ C) ^ t ] ,, Δ1-rem ,, Δ2-rem
          succ-eq = trans (lemma-removeAll-head-neq neq1) (cong ([ (B ∧ C) ^ t ] ,,_) (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Δ1 Δ2))
          p' : GoalType
          p' = subst (λ D → GoalCtx ⊢ D ,, Δ'') (sym succ-eq) p_contracted
          d_mix1_r = structural-preserves-δ subset-refl sub_delta1 mix1
          d_mix2_r = structural-preserves-δ subset-refl sub_delta2 mix2
          d_contracted = structural-preserves-δ subLeft subRight p_conj
          d_p'_eq = subst-preserves-δ (cong (_,, Δ'') (sym succ-eq)) p_contracted
          -- δ (⊢∧ Π1 Π2) = max (δ Π1) (δ Π2) by definition
          dΠ1≤G : δ Π1 ≤ GoalBound
          dΠ1≤G = left-left-≤-max
          dΠ'≤G : δ (∧₂⊢ Π1') ≤ GoalBound
          dΠ'≤G = right-≤-max {δ (∧₂⊢ Π1')} {δ (⊢∧ Π1 Π2)}
          dmix1' = subst (_≤ GoalBound) (sym d_mix1_r) (≤-trans dmix1 (max-least dΠ1≤G dΠ'≤G))
          dΠ2≤G : δ Π2 ≤ GoalBound
          dΠ2≤G = right-left-≤-max
          dmix2' = subst (_≤ GoalBound) (sym d_mix2_r) (≤-trans dmix2 (max-least dΠ2≤G dΠ'≤G))
          dpConj = max-least dmix1' dmix2'
          d_final : δ p' ≤ GoalBound
          d_final = subst (_≤ GoalBound) (sym (d_p'_eq ∙ d_contracted)) dpConj
      in (p' , d_final)
    handleAndCase2 accR (yes eq1) (no neq2) =
      let h-dec = mixHeight-dec-r (⊢∧ Π1 Π2) (∧₂⊢ Π1') Π1' (height-subproof-1 Π1')
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ' ,, [ B' ^ t' ]} {Δ' = Δ''} degEq (⊢∧ Π1 Π2) Π1' wfp wfp' acc'
          Γ'-A = Γ' - (A ^ s)
          sub_left : ((Γ1 ,, Γ2) ,, ((Γ' ,, [ B' ^ t' ]) - (A ^ s))) ⊆ (((Γ1 ,, Γ2) ,, Γ'-A) ,, [ B' ^ t' ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) (((Γ1 ,, Γ2) ∷ Γ' ∷ []) , (B' ^ t' ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          p_and = ∧₂⊢ {(Γ1 ,, Γ2) ,, Γ'-A} {B'} {t'} {GoalSucc} {C'} mix_r
          sub_left2 : (((Γ1 ,, Γ2) ,, Γ'-A) ,, [ (C' ∧ B') ^ t' ]) ⊆ ((Γ1 ,, Γ2) ,, (Γ'-A ,, [ (C' ∧ B') ^ t' ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) (((Γ1 ,, Γ2) ∷ Γ'-A ∷ []) , ((C' ∧ B') ^ t' ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_and
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (C' ∧ B') ^ t'} {Γ = Γ'} neq2
          p' : GoalType
          p' = subst (λ G → (Γ1 ,, Γ2) ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong ((Γ1 ,, Γ2) ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_and) (structural-preserves-δ sub_left subset-refl mix))
          d_final : δ p' ≤ GoalBound
          d_final = subst (_≤ GoalBound) (sym d_p') dmix
      in (p' , d_final)
    -- Principal: A = (B∧C)^t AND A = (C'∧B')^t' → B=C', C=B', final mix on C
    handleAndCase2 accR (yes eq1) (yes eq2) =
      let
        -- Formula equalities: (B∧C)^t ≡ (C'∧B')^t'
        BC-eq-C'B' : (B ∧ C) ^ t ≡ (C' ∧ B') ^ t'
        BC-eq-C'B' = sym eq1 ∙ eq2
        B-eq-C' : B ≡ C'
        B-eq-C' = ∧-inj-l (cong PFormula.form BC-eq-C'B')
        C-eq-B' : C ≡ B'
        C-eq-B' = ∧-inj-r (cong PFormula.form BC-eq-C'B')
        t-eq-t' : t ≡ t'
        t-eq-t' = cong PFormula.pos BC-eq-C'B'
        Ct-eq-B't' : C ^ t ≡ B' ^ t'
        Ct-eq-B't' = cong₂ _^_ C-eq-B' t-eq-t'

        -- Degree decrease: degree C < n
        degA-eq : degree A ≡ suc (max (degree B) (degree C))
        degA-eq = cong degree (cong PFormula.form eq1)
        degC-lt-n : degree C < n
        degC-lt-n = subst (degree C <_) (sym degA-eq ∙ degEq) (degree-∧-r B C)

        -- C^t ≠ A^s (subformula)
        C-neq-A : (C ^ t) ≢ (A ^ s)
        C-neq-A eq = subformula-neq-∧-r {B = B} {C = C} {s = t} {t = s}
                     (subst (λ X → C ^ t ≡ X ^ s) (cong PFormula.form eq1) eq)

        -- B'^t' ≠ A^s
        B'-neq-A : (B' ^ t') ≢ (A ^ s)
        B'-neq-A eq = subformula-neq-∧-r {B = C'} {C = B'} {s = t'} {t = s}
                      (subst (λ X → B' ^ t' ≡ X ^ s) (cong PFormula.form eq2) eq)

        -- Abbreviations
        Γ'-A = Γ' - (A ^ s)
        Δ1-A = Δ1 - (A ^ s)
        Δ2-A = Δ2 - (A ^ s)

        -- CROSS-CUT 1: Mix Π2 with (∧₂⊢ Π1') on A — height decrease left
        h-dec-1 = mixHeight-dec-l (⊢∧ Π1 Π2) Π2 (∧₂⊢ Π1') (height-subproof-2-r Π1 Π2)
        acc1 = accR _ (inr (refl , h-dec-1))
        res1-pair = Mix {Γ = Γ2} {Δ = [ C ^ t ] ,, Δ2} degEq Π2 (∧₂⊢ Π1') (snd wfp) wfp' acc1
        res1 = fst res1-pair
        d-res1 = snd res1-pair

        -- Simplify res1
        ant-simp-1 : (Γ' ,, [ (C' ∧ B') ^ t' ]) - (A ^ s) ≡ Γ'-A
        ant-simp-1 = lemma-removeAll-cons-eq {A = A ^ s} {B = (C' ∧ B') ^ t'} {Γ = Γ'} eq2
        succ-simp-1 : ([ C ^ t ] ,, Δ2) - (A ^ s) ≡ [ C ^ t ] ,, Δ2-A
        succ-simp-1 = removeAll-prepend-pf-neq (λ eq → C-neq-A (sym eq))
        res1-cast : Γ2 ,, Γ'-A ⊢ ([ C ^ t ] ,, Δ2-A) ,, Δ''
        res1-cast = subst2 (λ G D → Γ2 ,, G ⊢ D ,, Δ'') ant-simp-1 succ-simp-1 res1

        -- CROSS-CUT 2: Mix (⊢∧ Π1 Π2) with Π1' on A — height decrease right
        h-dec-2 = mixHeight-dec-r (⊢∧ Π1 Π2) (∧₂⊢ Π1') Π1' (height-subproof-1 Π1')
        acc2 = accR _ (inr (refl , h-dec-2))
        res2-pair = Mix {Γ' = Γ' ,, [ B' ^ t' ]} {Δ' = Δ''} degEq (⊢∧ Π1 Π2) Π1' wfp wfp' acc2
        res2 = fst res2-pair
        d-res2 = snd res2-pair

        -- Simplify res2
        succ-simp-2 : ([ (B ∧ C) ^ t ] ,, (Δ1 ,, Δ2)) - (A ^ s) ≡ (Δ1 ,, Δ2) - (A ^ s)
        succ-simp-2 = lemma-removeAll-head-eq {A = A ^ s} {B = (B ∧ C) ^ t} {Γ = Δ1 ,, Δ2} eq1
        res2-succ : (Γ1 ,, Γ2) ,, ((Γ' ,, [ B' ^ t' ]) - (A ^ s)) ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ''
        res2-succ = subst (λ D → (Γ1 ,, Γ2) ,, ((Γ' ,, [ B' ^ t' ]) - (A ^ s)) ⊢ D ,, Δ'') succ-simp-2 res2

        ant-simp-2 : (Γ' ,, [ B' ^ t' ]) - (A ^ s) ≡ Γ'-A ,, [ B' ^ t' ]
        ant-simp-2 = removeAll-++-r-pf-neq (λ eq → B'-neq-A (sym eq))
        res2-ant-cast : (Γ1 ,, Γ2) ,, (Γ'-A ,, [ C ^ t ]) ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ''
        res2-ant-cast = subst (λ pf → (Γ1 ,, Γ2) ,, (Γ'-A ,, [ pf ]) ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ'')
                              (sym Ct-eq-B't')
                              (subst (λ G → (Γ1 ,, Γ2) ,, G ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ'') ant-simp-2 res2-succ)
        ant-assoc : (Γ1 ,, Γ2) ,, (Γ'-A ,, [ C ^ t ]) ≡ ((Γ1 ,, Γ2) ,, Γ'-A) ,, [ C ^ t ]
        ant-assoc = sym (++-assoc (Γ1 ,, Γ2) Γ'-A [ C ^ t ])
        res2-cast : ((Γ1 ,, Γ2) ,, Γ'-A) ,, [ C ^ t ] ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ''
        res2-cast = subst (_⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ'') ant-assoc res2-ant-cast

        -- FINAL MIX ON C: degree decrease
        res1-wf = makeWellFormed res1-cast
        res2-wf = makeWellFormed res2-cast
        acc3 = accR (degree C , mixHeight res1-wf res2-wf) (inl degC-lt-n)
        mix3-pair = Mix {n = degree C} {A = C} {s = t} refl
                       res1-wf res2-wf
                       (makeWellFormed-WellFormed res1-cast) (makeWellFormed-WellFormed res2-cast) acc3
        mix3 = fst mix3-pair
        d-mix3 = snd mix3-pair

        -- STRUCTURAL CONTRACTION
        sub-ant = subset-concat {G = (Γ1 ,, Γ2) ,, Γ'-A}
          (subset-concat (λ y yIn → mem-++-l (mem-++-r Γ1 yIn)) (λ y yIn → mem-++-r (Γ1 ,, Γ2) yIn))
          (removeAll-append-singleton-⊆ ((Γ1 ,, Γ2) ,, Γ'-A) (C ^ t))

        succ-left-sub = subset-trans {l2 = Δ2-A ,, Δ''}
          (removeAll-drop-singleton-r [] (Δ2-A ,, Δ'') (C ^ t))
          (subset-concat
            (λ y yIn → mem-++-l (let (yInΔ2 , y≠A) = removeAll-mem yIn in mem-removeAll (mem-++-r Δ1 yInΔ2) y≠A))
            (λ y yIn → mem-++-r ((Δ1 ,, Δ2) - (A ^ s)) yIn))

        sub-succ = subset-concat succ-left-sub (λ y yIn → yIn)

        p_struct = structural sub-ant sub-succ mix3

        -- TRANSPORT TO FULL GOAL TYPE
        p_ctx : GoalCtx ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ''
        p_ctx = subst (λ G → (Γ1 ,, Γ2) ,, G ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ'') (sym ant-simp-1) p_struct
        p' : GoalType
        p' = subst (GoalCtx ⊢_) (cong (_,, Δ'') (sym succ-simp-2)) p_ctx

        -- DEGREE BOUND
        δ-res1-cast-eq : δ res1-cast ≡ δ res1
        δ-res1-cast-eq = subst2-preserves-δ (Γ2 ,,_) (_,, Δ'') ant-simp-1 succ-simp-1 res1
        δ-res1-wf-eq : δ res1-wf ≡ δ res1
        δ-res1-wf-eq = trans (δ-makeWellFormed res1-cast) δ-res1-cast-eq
        res1-intermediate : max (δ Π2) (δ (∧₂⊢ Π1')) ≤ GoalBound
        res1-intermediate = max-least
          (right-left-≤-max)
          (right-≤-max {δ (∧₂⊢ Π1')} {δ (⊢∧ Π1 Π2)})
        res1-bound : δ res1-wf ≤ GoalBound
        res1-bound = subst (_≤ GoalBound) (sym δ-res1-wf-eq) (≤-trans d-res1 res1-intermediate)

        δ-res2-succ-eq : δ res2-succ ≡ δ res2
        δ-res2-succ-eq = subst-preserves-δ (cong (_,, Δ'') succ-simp-2) res2
        δ-res2-ant-eq : δ res2-ant-cast ≡ δ res2
        δ-res2-ant-eq = trans
          (subst-preserves-δ-ctx (cong (λ pf → (Γ1 ,, Γ2) ,, (Γ'-A ,, [ pf ])) (sym Ct-eq-B't'))
            (subst (λ G → (Γ1 ,, Γ2) ,, G ⊢ ((Δ1 ,, Δ2) - (A ^ s)) ,, Δ'') ant-simp-2 res2-succ))
          (trans (subst-preserves-δ-ctx (cong ((Γ1 ,, Γ2) ,,_) ant-simp-2) res2-succ) δ-res2-succ-eq)
        δ-res2-cast-eq : δ res2-cast ≡ δ res2
        δ-res2-cast-eq = trans (subst-preserves-δ-ctx ant-assoc res2-ant-cast) δ-res2-ant-eq
        δ-res2-wf-eq : δ res2-wf ≡ δ res2
        δ-res2-wf-eq = trans (δ-makeWellFormed res2-cast) δ-res2-cast-eq
        res2-bound : δ res2-wf ≤ GoalBound
        res2-bound = subst (_≤ GoalBound) (sym δ-res2-wf-eq) d-res2

        max-res-bound : max (δ res1-wf) (δ res2-wf) ≤ GoalBound
        max-res-bound = max-least res1-bound res2-bound
        mix3-bound : δ mix3 ≤ GoalBound
        mix3-bound = ≤-trans d-mix3 max-res-bound

        δ-p-struct = structural-preserves-δ sub-ant sub-succ mix3
        δ-p-ctx = subst-preserves-δ-ctx (cong ((Γ1 ,, Γ2) ,,_) (sym ant-simp-1)) p_struct
        δ-p' = subst-preserves-δ (cong (_,, Δ'') (sym succ-simp-2)) p_ctx
        d_final : δ p' ≤ GoalBound
        d_final = subst (_≤ GoalBound) (sym (δ-p' ∙ δ-p-ctx ∙ δ-p-struct)) mix3-bound
      in (p' , d_final)

-- Principal Case 4: ⊢∨₁ vs ∨⊢
-- Left: ⊢∨₁ Π1 : Γ ⊢ [(B ∨ C) ^ t] ,, Δ1  where Π1 : Γ ⊢ [B ^ t] ,, Δ1
-- Right: ∨⊢ Π1' Π2' : Γ'₁ ,, Γ'₂ ,, [(B' ∨ C') ^ t'] ⊢ Δ'₁ ,, Δ'₂
Mix {n = n} {Γ = Γ} {Δ = .([ (B ∨ C) ^ t ] ,, Δ1)}
    {Γ' = .(Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ])} {Δ' = .(Δ'₁ ,, Δ'₂)} {A = A} {s = s}
    degEq (⊢∨₁ {.Γ} {B} {t} {Δ1} {C} Π1)
          (∨⊢ {Γ₁ = Γ'₁} {A = B'} {s = t'} {Δ₁ = Δ'₁} {Γ₂ = Γ'₂} {B = C'} {Δ₂ = Δ'₂} Π1' Π2') wfp wfp' (acc accRec) =
    handleDisjCase1 accRec (discretePFormula (A ^ s) ((B ∨ C) ^ t)) (discretePFormula (A ^ s) ((B' ∨ C') ^ t'))
  where
    GoalBound = max (δ (⊢∨₁ {B = C} Π1)) (δ (∨⊢ Π1' Π2'))
    Result = Σ (Γ ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ]) - (A ^ s)) ⊢
                 (([ (B ∨ C) ^ t ] ,, Δ1) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂))
               (λ p → δ p ≤ GoalBound)

    handleDisjCase1 : (∀ m' → m' <Lex (n , mixHeight (⊢∨₁ {B = C} Π1) (∨⊢ Π1' Π2')) → Acc _<Lex_ m')
                    → Dec ((A ^ s) ≡ ((B ∨ C) ^ t)) → Dec ((A ^ s) ≡ ((B' ∨ C') ^ t')) → Result
    handleDisjCase1 accR (no neq1) _ =
      let h-dec = mixHeight-dec-l (⊢∨₁ {B = C} Π1) Π1 (∨⊢ Π1' Π2') (height-subproof-1 Π1)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ = Γ} {Δ = [ B ^ t ] ,, Δ1} degEq Π1 (∨⊢ Π1' Π2') wfp wfp' acc'
          Γ'-rem = (Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ]) - (A ^ s)
          Δ1-rem = Δ1 - (A ^ s)
          sub_delta : ((([ B ^ t ] ,, Δ1) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂)) ⊆ ([ B ^ t ] ,, (Δ1-rem ,, (Δ'₁ ,, Δ'₂)))
          sub_delta = solve (rem (elm 0 ++ₑ var 0) 1 ++ₑ var 1) (elm 0 ++ₑ (rem (var 0) 1 ++ₑ var 1)) ((Δ1 ∷ (Δ'₁ ,, Δ'₂) ∷ []) , (B ^ t ∷ A ^ s ∷ [])) {refl}
          mix_r = structural subset-refl sub_delta mix
          p_disj = ⊢∨₁ {Γ = Γ ,, Γ'-rem} {A = B} {s = t} {Δ = Δ1-rem ,, (Δ'₁ ,, Δ'₂)} {B = C} mix_r
          sub_right : ([ (B ∨ C) ^ t ] ,, (Δ1-rem ,, (Δ'₁ ,, Δ'₂))) ⊆ (([ (B ∨ C) ^ t ] ,, Δ1-rem) ,, (Δ'₁ ,, Δ'₂))
          sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((elm 0 ++ₑ var 0) ++ₑ var 1) ((Δ1-rem ∷ (Δ'₁ ,, Δ'₂) ∷ []) , ((B ∨ C) ^ t ∷ [])) {refl}
          p_reorder = structural subset-refl sub_right p_disj
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ1} neq1
          p' = subst (λ D → Γ ,, Γ'-rem ⊢ D ,, (Δ'₁ ,, Δ'₂)) (sym succ-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-eq)) p_reorder)
                 (trans (structural-preserves-δ subset-refl sub_right p_disj) (structural-preserves-δ subset-refl sub_delta mix))
          d_final : δ p' ≤ GoalBound
          d_final = subst (_≤ GoalBound) (sym d_p') dmix
      in (p' , d_final)
    handleDisjCase1 accR (yes eq1) (no neq2) =
      let h-dec1 = mixHeight-dec-r (⊢∨₁ {B = C} Π1) (∨⊢ Π1' Π2') Π1' (height-subproof-2-l Π1' Π2')
          h-dec2 = mixHeight-dec-r (⊢∨₁ {B = C} Π1) (∨⊢ Π1' Π2') Π2' (height-subproof-2-r Π1' Π2')
          acc1 = accR _ (inr (refl , h-dec1))
          acc2 = accR _ (inr (refl , h-dec2))
          (mix1 , dmix1) = Mix {Γ' = Γ'₁ ,, [ B' ^ t' ]} {Δ' = Δ'₁} degEq (⊢∨₁ {B = C} Π1) Π1' wfp (fst wfp') acc1
          (mix2 , dmix2) = Mix {Γ' = Γ'₂ ,, [ C' ^ t' ]} {Δ' = Δ'₂} degEq (⊢∨₁ {B = C} Π1) Π2' wfp (snd wfp') acc2
          Γ'₁-A = Γ'₁ - (A ^ s)
          Γ'₂-A = Γ'₂ - (A ^ s)
          Succ-rem = (([ (B ∨ C) ^ t ] ,, Δ1) - (A ^ s))
          -- Reorder antecedents to move subformulas to end
          sub_left1 : (Γ ,, ((Γ'₁ ,, [ B' ^ t' ]) - (A ^ s))) ⊆ ((Γ ,, Γ'₁-A) ,, [ B' ^ t' ])
          sub_left1 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ ∷ Γ'₁ ∷ []) , (B' ^ t' ∷ A ^ s ∷ [])) {refl}
          mix1_r = structural sub_left1 subset-refl mix1
          sub_left2 : (Γ ,, ((Γ'₂ ,, [ C' ^ t' ]) - (A ^ s))) ⊆ ((Γ ,, Γ'₂-A) ,, [ C' ^ t' ])
          sub_left2 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ ∷ Γ'₂ ∷ []) , (C' ^ t' ∷ A ^ s ∷ [])) {refl}
          mix2_r = structural sub_left2 subset-refl mix2
          -- Apply ∨⊢
          p_disj = ∨⊢ {Γ₁ = Γ ,, Γ'₁-A} {A = B'} {s = t'} {Δ₁ = Succ-rem ,, Δ'₁} {Γ₂ = Γ ,, Γ'₂-A} {B = C'} {Δ₂ = Succ-rem ,, Δ'₂} mix1_r mix2_r
          -- Contract — ∨⊢ result type: Γ₁ ,, (Γ₂ ,, [formula]) (right-assoc ,,)
          subLeft : ((Γ ,, Γ'₁-A) ,, ((Γ ,, Γ'₂-A) ,, [ (B' ∨ C') ^ t' ])) ⊆ (Γ ,, ((Γ'₁-A ,, Γ'₂-A) ,, [ (B' ∨ C') ^ t' ]))
          subLeft = solve ((var 0 ++ₑ var 1) ++ₑ ((var 0 ++ₑ var 2) ++ₑ elm 0)) (var 0 ++ₑ ((var 1 ++ₑ var 2) ++ₑ elm 0)) ((Γ ∷ Γ'₁-A ∷ Γ'₂-A ∷ []) , ((B' ∨ C') ^ t' ∷ [])) {refl}
          subRight : ((Succ-rem ,, Δ'₁) ,, (Succ-rem ,, Δ'₂)) ⊆ (Succ-rem ,, (Δ'₁ ,, Δ'₂))
          subRight = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Succ-rem ∷ Δ'₁ ∷ Δ'₂ ∷ []) , []) {refl}
          p_contracted = structural subLeft subRight p_disj
          -- Transport antecedent
          ant-eq : (Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ]) - (A ^ s) ≡ (Γ'₁-A ,, Γ'₂-A) ,, [ (B' ∨ C') ^ t' ]
          ant-eq = cong (_- (A ^ s)) (sym (++-assoc Γ'₁ Γ'₂ [ (B' ∨ C') ^ t' ]))
                 ∙ trans (lemma-removeAll-cons-neq {Γ = Γ'₁ ,, Γ'₂} neq2)
                         (cong (_,, [ (B' ∨ C') ^ t' ]) (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ'₁ Γ'₂))
          p' = subst (λ G → Γ ,, G ⊢ Succ-rem ,, (Δ'₁ ,, Δ'₂)) (sym ant-eq) p_contracted
          -- Degree bounds
          d_mix1_r = structural-preserves-δ sub_left1 subset-refl mix1
          d_mix2_r = structural-preserves-δ sub_left2 subset-refl mix2
          d_contracted = structural-preserves-δ subLeft subRight p_disj
          d_p'_eq = subst-preserves-δ-ctx (cong (Γ ,,_) (sym ant-eq)) p_contracted
          dLeft≤G : δ (⊢∨₁ {B = C} Π1) ≤ GoalBound
          dLeft≤G = left-≤-max {δ (⊢∨₁ {B = C} Π1)} {δ (∨⊢ Π1' Π2')}
          -- δ (∨⊢ Π1' Π2') = max (δ Π1') (δ Π2') by definition
          dΠ1'≤G : δ Π1' ≤ GoalBound
          dΠ1'≤G = left-right-≤-max
          dmix1' = subst (_≤ GoalBound) (sym d_mix1_r) (≤-trans dmix1 (max-least dLeft≤G dΠ1'≤G))
          dΠ2'≤G : δ Π2' ≤ GoalBound
          dΠ2'≤G = right-right-≤-max
          dmix2' = subst (_≤ GoalBound) (sym d_mix2_r) (≤-trans dmix2 (max-least dLeft≤G dΠ2'≤G))
          dpDisj = max-least dmix1' dmix2'
          d_final : δ p' ≤ GoalBound
          d_final = subst (_≤ GoalBound) (sym (d_p'_eq ∙ d_contracted)) dpDisj
      in (p' , d_final)
    -- Principal: A = (B∨C)^t AND A = (B'∨C')^t' → B=B', C=C', final mix on B
    handleDisjCase1 accR (yes eq1) (yes eq2) =
      let
        -- Formula equalities
        BC-eq-B'C' : (B ∨ C) ^ t ≡ (B' ∨ C') ^ t'
        BC-eq-B'C' = sym eq1 ∙ eq2
        B-eq-B' : B ≡ B'
        B-eq-B' = ∨-inj-l (cong PFormula.form BC-eq-B'C')
        t-eq-t' : t ≡ t'
        t-eq-t' = cong PFormula.pos BC-eq-B'C'
        Bt-eq-B't' : B ^ t ≡ B' ^ t'
        Bt-eq-B't' = cong₂ _^_ B-eq-B' t-eq-t'

        -- Degree decrease
        degA-eq : degree A ≡ suc (max (degree B) (degree C))
        degA-eq = cong degree (cong PFormula.form eq1)
        degB-lt-n : degree B < n
        degB-lt-n = subst (degree B <_) (sym degA-eq ∙ degEq) (degree-∨-l B C)

        -- Subformula inequalities
        B-neq-A : (B ^ t) ≢ (A ^ s)
        B-neq-A eq = subformula-neq-∨-l {B = B} {C = C} {s = t} {t = s}
                     (subst (λ X → B ^ t ≡ X ^ s) (cong PFormula.form eq1) eq)
        B'-neq-A : (B' ^ t') ≢ (A ^ s)
        B'-neq-A eq = subformula-neq-∨-l {B = B'} {C = C'} {s = t'} {t = s}
                      (subst (λ X → B' ^ t' ≡ X ^ s) (cong PFormula.form eq2) eq)

        -- Abbreviations
        Δ1-A = Δ1 - (A ^ s)
        Γ'₁-A = Γ'₁ - (A ^ s)

        -- CROSS-CUT 1: Mix Π1 with (∨⊢ Π1' Π2') on A — height decrease left
        h-dec-1 = mixHeight-dec-l (⊢∨₁ {B = C} Π1) Π1 (∨⊢ Π1' Π2') (height-subproof-1 Π1)
        acc1 = accR _ (inr (refl , h-dec-1))
        res1-pair = Mix {Γ = Γ} {Δ = [ B ^ t ] ,, Δ1} degEq Π1 (∨⊢ Π1' Π2') wfp wfp' acc1
        res1 = fst res1-pair
        d-res1 = snd res1-pair

        succ-simp-1 : ([ B ^ t ] ,, Δ1) - (A ^ s) ≡ [ B ^ t ] ,, Δ1-A
        succ-simp-1 = removeAll-prepend-pf-neq (λ eq → B-neq-A (sym eq))
        res1-cast : Γ ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ]) - (A ^ s)) ⊢ ([ B ^ t ] ,, Δ1-A) ,, (Δ'₁ ,, Δ'₂)
        res1-cast = subst (λ D → Γ ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ]) - (A ^ s)) ⊢ D ,, (Δ'₁ ,, Δ'₂)) succ-simp-1 res1

        -- CROSS-CUT 2: Mix (⊢∨₁ Π1) with Π1' on A — height decrease right
        h-dec-2 = mixHeight-dec-r (⊢∨₁ {B = C} Π1) (∨⊢ Π1' Π2') Π1' (height-subproof-2-l Π1' Π2')
        acc2 = accR _ (inr (refl , h-dec-2))
        res2-pair = Mix {Γ' = Γ'₁ ,, [ B' ^ t' ]} {Δ' = Δ'₁} degEq (⊢∨₁ {B = C} Π1) Π1' wfp (fst wfp') acc2
        res2 = fst res2-pair
        d-res2 = snd res2-pair

        -- Simplify res2 succedent
        succ-simp-2 : ([ (B ∨ C) ^ t ] ,, Δ1) - (A ^ s) ≡ Δ1-A
        succ-simp-2 = lemma-removeAll-head-eq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ1} eq1
        res2-succ : Γ ,, ((Γ'₁ ,, [ B' ^ t' ]) - (A ^ s)) ⊢ Δ1-A ,, Δ'₁
        res2-succ = subst (λ D → Γ ,, ((Γ'₁ ,, [ B' ^ t' ]) - (A ^ s)) ⊢ D ,, Δ'₁) succ-simp-2 res2

        -- Simplify res2 antecedent
        ant-simp-2 : (Γ'₁ ,, [ B' ^ t' ]) - (A ^ s) ≡ Γ'₁-A ,, [ B' ^ t' ]
        ant-simp-2 = removeAll-++-r-pf-neq (λ eq → B'-neq-A (sym eq))
        res2-ant-cast : Γ ,, (Γ'₁-A ,, [ B ^ t ]) ⊢ Δ1-A ,, Δ'₁
        res2-ant-cast = subst (λ pf → Γ ,, (Γ'₁-A ,, [ pf ]) ⊢ Δ1-A ,, Δ'₁)
                              (sym Bt-eq-B't')
                              (subst (λ G → Γ ,, G ⊢ Δ1-A ,, Δ'₁) ant-simp-2 res2-succ)
        ant-assoc : Γ ,, (Γ'₁-A ,, [ B ^ t ]) ≡ (Γ ,, Γ'₁-A) ,, [ B ^ t ]
        ant-assoc = sym (++-assoc Γ Γ'₁-A [ B ^ t ])
        res2-cast : (Γ ,, Γ'₁-A) ,, [ B ^ t ] ⊢ Δ1-A ,, Δ'₁
        res2-cast = subst (_⊢ Δ1-A ,, Δ'₁) ant-assoc res2-ant-cast

        -- FINAL MIX ON B: degree decrease
        res1-wf = makeWellFormed res1-cast
        res2-wf = makeWellFormed res2-cast
        acc3 = accR (degree B , mixHeight res1-wf res2-wf) (inl degB-lt-n)
        mix3-pair = Mix {n = degree B} {A = B} {s = t} refl
                       res1-wf res2-wf
                       (makeWellFormed-WellFormed res1-cast) (makeWellFormed-WellFormed res2-cast) acc3
        mix3 = fst mix3-pair
        d-mix3 = snd mix3-pair

        -- STRUCTURAL CONTRACTION
        sub-ant = subset-concat {G = Γ ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ]) - (A ^ s))}
          subset-refl
          (subset-trans
            (removeAll-append-singleton-⊆ (Γ ,, Γ'₁-A) (B ^ t))
            (subset-concat (λ y yIn → mem-++-l yIn)
              (λ y yIn → mem-++-r Γ (let (yInΓ'₁ , y≠A) = removeAll-mem yIn in mem-removeAll (mem-++-l yInΓ'₁) y≠A))))

        sub-succ = subset-concat {G = Δ1-A ,, (Δ'₁ ,, Δ'₂)}
          (removeAll-drop-singleton-r [] (Δ1-A ,, (Δ'₁ ,, Δ'₂)) (B ^ t))
          (subset-concat (λ y yIn → mem-++-l yIn)
            (λ y yIn → mem-++-r Δ1-A (mem-++-l yIn)))

        p_struct = structural sub-ant sub-succ mix3

        -- TRANSPORT TO GOAL TYPE
        p' = subst (Γ ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ]) - (A ^ s)) ⊢_)
                   (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-simp-2)) p_struct

        -- DEGREE BOUND
        δ-res1-cast-eq : δ res1-cast ≡ δ res1
        δ-res1-cast-eq = subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) succ-simp-1) res1
        δ-res1-wf-eq : δ res1-wf ≡ δ res1
        δ-res1-wf-eq = trans (δ-makeWellFormed res1-cast) δ-res1-cast-eq
        res1-bound : δ res1-wf ≤ GoalBound
        res1-bound = subst (_≤ GoalBound) (sym δ-res1-wf-eq) d-res1

        δ-res2-succ-eq : δ res2-succ ≡ δ res2
        δ-res2-succ-eq = subst-preserves-δ (cong (_,, Δ'₁) succ-simp-2) res2
        δ-res2-ant-eq : δ res2-ant-cast ≡ δ res2
        δ-res2-ant-eq = trans
          (subst-preserves-δ-ctx (cong (λ pf → Γ ,, (Γ'₁-A ,, [ pf ])) (sym Bt-eq-B't'))
            (subst (λ G → Γ ,, G ⊢ Δ1-A ,, Δ'₁) ant-simp-2 res2-succ))
          (trans (subst-preserves-δ-ctx (cong (Γ ,,_) ant-simp-2) res2-succ) δ-res2-succ-eq)
        δ-res2-cast-eq : δ res2-cast ≡ δ res2
        δ-res2-cast-eq = trans (subst-preserves-δ-ctx ant-assoc res2-ant-cast) δ-res2-ant-eq
        δ-res2-wf-eq : δ res2-wf ≡ δ res2
        δ-res2-wf-eq = trans (δ-makeWellFormed res2-cast) δ-res2-cast-eq
        res2-intermediate : max (δ (⊢∨₁ {B = C} Π1)) (δ Π1') ≤ GoalBound
        res2-intermediate = max-least
          (left-≤-max {δ (⊢∨₁ {B = C} Π1)} {δ (∨⊢ Π1' Π2')})
          (left-right-≤-max)
        res2-bound : δ res2-wf ≤ GoalBound
        res2-bound = subst (_≤ GoalBound) (sym δ-res2-wf-eq) (≤-trans d-res2 res2-intermediate)

        max-res-bound = max-least res1-bound res2-bound
        mix3-bound : δ mix3 ≤ GoalBound
        mix3-bound = ≤-trans d-mix3 max-res-bound

        δ-p-struct = structural-preserves-δ sub-ant sub-succ mix3
        δ-p' = subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-simp-2)) p_struct
        d_final : δ p' ≤ GoalBound
        d_final = subst (_≤ GoalBound) (sym (δ-p' ∙ δ-p-struct)) mix3-bound
      in (p' , d_final)

-- =============================================================================
-- Principal Case: ⊢∨₂ vs ∨⊢
-- Left: ⊢∨₂ Π1 : Γ ⊢ [(B ∨ C) ^ t] ,, Δ1  where Π1 : Γ ⊢ [C ^ t] ,, Δ1
-- Right: ∨⊢ Π1' Π2' : Γ'₁ ,, Γ'₂ ,, [(B' ∨ C') ^ t'] ⊢ Δ'₁ ,, Δ'₂
-- Note: ⊢∨₂ proves second disjunct C; ∨⊢'s Π2' uses second disjunct C'
-- =============================================================================
Mix {n = n} {Γ = Γ} {Δ = .([ (B ∨ C) ^ t ] ,, Δ1)}
    {Γ' = .(Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ])} {Δ' = .(Δ'₁ ,, Δ'₂)} {A = A} {s = s}
    degEq (⊢∨₂ {.Γ} {C} {t} {Δ1} {B} Π1)
          (∨⊢ {Γ₁ = Γ'₁} {A = B'} {s = t'} {Δ₁ = Δ'₁} {Γ₂ = Γ'₂} {B = C'} {Δ₂ = Δ'₂} Π1' Π2') wfp wfp' (acc accRec) =
    handleDisjCase2 accRec (discretePFormula (A ^ s) ((B ∨ C) ^ t)) (discretePFormula (A ^ s) ((B' ∨ C') ^ t'))
  where
    GoalBound = max (δ (⊢∨₂ {A = B} Π1)) (δ (∨⊢ Π1' Π2'))
    Result = Σ (Γ ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ]) - (A ^ s)) ⊢
                 (([ (B ∨ C) ^ t ] ,, Δ1) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂))
               (λ p → δ p ≤ GoalBound)

    handleDisjCase2 : (∀ m' → m' <Lex (n , mixHeight (⊢∨₂ {A = B} Π1) (∨⊢ Π1' Π2')) → Acc _<Lex_ m')
                    → Dec ((A ^ s) ≡ ((B ∨ C) ^ t)) → Dec ((A ^ s) ≡ ((B' ∨ C') ^ t')) → Result
    handleDisjCase2 accR (no neq1) _ =
      let h-dec = mixHeight-dec-l (⊢∨₂ {A = B} Π1) Π1 (∨⊢ Π1' Π2') (height-subproof-1 Π1)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ = Γ} {Δ = [ C ^ t ] ,, Δ1} degEq Π1 (∨⊢ Π1' Π2') wfp wfp' acc'
          Γ'-rem = (Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ]) - (A ^ s)
          Δ1-rem = Δ1 - (A ^ s)
          sub_delta : ((([ C ^ t ] ,, Δ1) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂)) ⊆ ([ C ^ t ] ,, (Δ1-rem ,, (Δ'₁ ,, Δ'₂)))
          sub_delta = solve (rem (elm 0 ++ₑ var 0) 1 ++ₑ var 1) (elm 0 ++ₑ (rem (var 0) 1 ++ₑ var 1)) ((Δ1 ∷ (Δ'₁ ,, Δ'₂) ∷ []) , (C ^ t ∷ A ^ s ∷ [])) {refl}
          mix_r = structural subset-refl sub_delta mix
          p_disj = ⊢∨₂ {Γ = Γ ,, Γ'-rem} {B = C} {s = t} {Δ = Δ1-rem ,, (Δ'₁ ,, Δ'₂)} {A = B} mix_r
          sub_right : ([ (B ∨ C) ^ t ] ,, (Δ1-rem ,, (Δ'₁ ,, Δ'₂))) ⊆ (([ (B ∨ C) ^ t ] ,, Δ1-rem) ,, (Δ'₁ ,, Δ'₂))
          sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((elm 0 ++ₑ var 0) ++ₑ var 1) ((Δ1-rem ∷ (Δ'₁ ,, Δ'₂) ∷ []) , ((B ∨ C) ^ t ∷ [])) {refl}
          p_reorder = structural subset-refl sub_right p_disj
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ1} neq1
          p' = subst (λ D → Γ ,, Γ'-rem ⊢ D ,, (Δ'₁ ,, Δ'₂)) (sym succ-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-eq)) p_reorder)
                 (trans (structural-preserves-δ subset-refl sub_right p_disj) (structural-preserves-δ subset-refl sub_delta mix))
          d_final : δ p' ≤ GoalBound
          d_final = subst (_≤ GoalBound) (sym d_p') dmix
      in (p' , d_final)
    handleDisjCase2 accR (yes eq1) (no neq2) =
      let h-dec1 = mixHeight-dec-r (⊢∨₂ {A = B} Π1) (∨⊢ Π1' Π2') Π1' (height-subproof-2-l Π1' Π2')
          h-dec2 = mixHeight-dec-r (⊢∨₂ {A = B} Π1) (∨⊢ Π1' Π2') Π2' (height-subproof-2-r Π1' Π2')
          acc1 = accR _ (inr (refl , h-dec1))
          acc2 = accR _ (inr (refl , h-dec2))
          (mix1 , dmix1) = Mix {Γ' = Γ'₁ ,, [ B' ^ t' ]} {Δ' = Δ'₁} degEq (⊢∨₂ {A = B} Π1) Π1' wfp (fst wfp') acc1
          (mix2 , dmix2) = Mix {Γ' = Γ'₂ ,, [ C' ^ t' ]} {Δ' = Δ'₂} degEq (⊢∨₂ {A = B} Π1) Π2' wfp (snd wfp') acc2
          Γ'₁-A = Γ'₁ - (A ^ s)
          Γ'₂-A = Γ'₂ - (A ^ s)
          Succ-rem = (([ (B ∨ C) ^ t ] ,, Δ1) - (A ^ s))
          sub_left1 : (Γ ,, ((Γ'₁ ,, [ B' ^ t' ]) - (A ^ s))) ⊆ ((Γ ,, Γ'₁-A) ,, [ B' ^ t' ])
          sub_left1 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ ∷ Γ'₁ ∷ []) , (B' ^ t' ∷ A ^ s ∷ [])) {refl}
          mix1_r = structural sub_left1 subset-refl mix1
          sub_left2 : (Γ ,, ((Γ'₂ ,, [ C' ^ t' ]) - (A ^ s))) ⊆ ((Γ ,, Γ'₂-A) ,, [ C' ^ t' ])
          sub_left2 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ ∷ Γ'₂ ∷ []) , (C' ^ t' ∷ A ^ s ∷ [])) {refl}
          mix2_r = structural sub_left2 subset-refl mix2
          p_disj = ∨⊢ {Γ₁ = Γ ,, Γ'₁-A} {A = B'} {s = t'} {Δ₁ = Succ-rem ,, Δ'₁} {Γ₂ = Γ ,, Γ'₂-A} {B = C'} {Δ₂ = Succ-rem ,, Δ'₂} mix1_r mix2_r
          -- ∨⊢ result type: Γ₁ ,, (Γ₂ ,, [formula]) (right-assoc ,,)
          subLeft : ((Γ ,, Γ'₁-A) ,, ((Γ ,, Γ'₂-A) ,, [ (B' ∨ C') ^ t' ])) ⊆ (Γ ,, ((Γ'₁-A ,, Γ'₂-A) ,, [ (B' ∨ C') ^ t' ]))
          subLeft = solve ((var 0 ++ₑ var 1) ++ₑ ((var 0 ++ₑ var 2) ++ₑ elm 0)) (var 0 ++ₑ ((var 1 ++ₑ var 2) ++ₑ elm 0)) ((Γ ∷ Γ'₁-A ∷ Γ'₂-A ∷ []) , ((B' ∨ C') ^ t' ∷ [])) {refl}
          subRight : ((Succ-rem ,, Δ'₁) ,, (Succ-rem ,, Δ'₂)) ⊆ (Succ-rem ,, (Δ'₁ ,, Δ'₂))
          subRight = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Succ-rem ∷ Δ'₁ ∷ Δ'₂ ∷ []) , []) {refl}
          p_contracted = structural subLeft subRight p_disj
          ant-eq : (Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ]) - (A ^ s) ≡ (Γ'₁-A ,, Γ'₂-A) ,, [ (B' ∨ C') ^ t' ]
          ant-eq = cong (_- (A ^ s)) (sym (++-assoc Γ'₁ Γ'₂ [ (B' ∨ C') ^ t' ]))
                 ∙ trans (lemma-removeAll-cons-neq {Γ = Γ'₁ ,, Γ'₂} neq2)
                         (cong (_,, [ (B' ∨ C') ^ t' ]) (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ'₁ Γ'₂))
          p' = subst (λ G → Γ ,, G ⊢ Succ-rem ,, (Δ'₁ ,, Δ'₂)) (sym ant-eq) p_contracted
          d_mix1_r = structural-preserves-δ sub_left1 subset-refl mix1
          d_mix2_r = structural-preserves-δ sub_left2 subset-refl mix2
          d_contracted = structural-preserves-δ subLeft subRight p_disj
          d_p'_eq = subst-preserves-δ-ctx (cong (Γ ,,_) (sym ant-eq)) p_contracted
          dLeft≤G : δ (⊢∨₂ {A = B} Π1) ≤ GoalBound
          dLeft≤G = left-≤-max {δ (⊢∨₂ {A = B} Π1)} {δ (∨⊢ Π1' Π2')}
          -- δ (∨⊢ Π1' Π2') = max (δ Π1') (δ Π2') by definition
          dΠ1'≤G : δ Π1' ≤ GoalBound
          dΠ1'≤G = left-right-≤-max
          dmix1' = subst (_≤ GoalBound) (sym d_mix1_r) (≤-trans dmix1 (max-least dLeft≤G dΠ1'≤G))
          dΠ2'≤G : δ Π2' ≤ GoalBound
          dΠ2'≤G = right-right-≤-max
          dmix2' = subst (_≤ GoalBound) (sym d_mix2_r) (≤-trans dmix2 (max-least dLeft≤G dΠ2'≤G))
          dpDisj = max-least dmix1' dmix2'
          d_final : δ p' ≤ GoalBound
          d_final = subst (_≤ GoalBound) (sym (d_p'_eq ∙ d_contracted)) dpDisj
      in (p' , d_final)
    -- Principal: A = (B∨C)^t AND A = (B'∨C')^t' → B=B', C=C', final mix on C
    handleDisjCase2 accR (yes eq1) (yes eq2) =
      let
        -- Formula equalities
        BC-eq-B'C' : (B ∨ C) ^ t ≡ (B' ∨ C') ^ t'
        BC-eq-B'C' = sym eq1 ∙ eq2
        C-eq-C' : C ≡ C'
        C-eq-C' = ∨-inj-r (cong PFormula.form BC-eq-B'C')
        t-eq-t' : t ≡ t'
        t-eq-t' = cong PFormula.pos BC-eq-B'C'
        Ct-eq-C't' : C ^ t ≡ C' ^ t'
        Ct-eq-C't' = cong₂ _^_ C-eq-C' t-eq-t'

        -- Degree decrease
        degA-eq : degree A ≡ suc (max (degree B) (degree C))
        degA-eq = cong degree (cong PFormula.form eq1)
        degC-lt-n : degree C < n
        degC-lt-n = subst (degree C <_) (sym degA-eq ∙ degEq) (degree-∨-r B C)

        -- Subformula inequalities
        C-neq-A : (C ^ t) ≢ (A ^ s)
        C-neq-A eq = subformula-neq-∨-r {B = B} {C = C} {s = t} {t = s}
                     (subst (λ X → C ^ t ≡ X ^ s) (cong PFormula.form eq1) eq)
        C'-neq-A : (C' ^ t') ≢ (A ^ s)
        C'-neq-A eq = subformula-neq-∨-r {B = B'} {C = C'} {s = t'} {t = s}
                      (subst (λ X → C' ^ t' ≡ X ^ s) (cong PFormula.form eq2) eq)

        -- Abbreviations
        Δ1-A = Δ1 - (A ^ s)
        Γ'₂-A = Γ'₂ - (A ^ s)

        -- CROSS-CUT 1: Mix Π1 with (∨⊢ Π1' Π2') on A — height decrease left
        h-dec-1 = mixHeight-dec-l (⊢∨₂ {A = B} Π1) Π1 (∨⊢ Π1' Π2') (height-subproof-1 Π1)
        acc1 = accR _ (inr (refl , h-dec-1))
        res1-pair = Mix {Γ = Γ} {Δ = [ C ^ t ] ,, Δ1} degEq Π1 (∨⊢ Π1' Π2') wfp wfp' acc1
        res1 = fst res1-pair
        d-res1 = snd res1-pair

        succ-simp-1 : ([ C ^ t ] ,, Δ1) - (A ^ s) ≡ [ C ^ t ] ,, Δ1-A
        succ-simp-1 = removeAll-prepend-pf-neq (λ eq → C-neq-A (sym eq))
        res1-cast : Γ ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ]) - (A ^ s)) ⊢ ([ C ^ t ] ,, Δ1-A) ,, (Δ'₁ ,, Δ'₂)
        res1-cast = subst (λ D → Γ ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ]) - (A ^ s)) ⊢ D ,, (Δ'₁ ,, Δ'₂)) succ-simp-1 res1

        -- CROSS-CUT 2: Mix (⊢∨₂ Π1) with Π2' on A — height decrease right
        h-dec-2 = mixHeight-dec-r (⊢∨₂ {A = B} Π1) (∨⊢ Π1' Π2') Π2' (height-subproof-2-r Π1' Π2')
        acc2 = accR _ (inr (refl , h-dec-2))
        res2-pair = Mix {Γ' = Γ'₂ ,, [ C' ^ t' ]} {Δ' = Δ'₂} degEq (⊢∨₂ {A = B} Π1) Π2' wfp (snd wfp') acc2
        res2 = fst res2-pair
        d-res2 = snd res2-pair

        -- Simplify res2 succedent
        succ-simp-2 : ([ (B ∨ C) ^ t ] ,, Δ1) - (A ^ s) ≡ Δ1-A
        succ-simp-2 = lemma-removeAll-head-eq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ1} eq1
        res2-succ : Γ ,, ((Γ'₂ ,, [ C' ^ t' ]) - (A ^ s)) ⊢ Δ1-A ,, Δ'₂
        res2-succ = subst (λ D → Γ ,, ((Γ'₂ ,, [ C' ^ t' ]) - (A ^ s)) ⊢ D ,, Δ'₂) succ-simp-2 res2

        -- Simplify res2 antecedent
        ant-simp-2 : (Γ'₂ ,, [ C' ^ t' ]) - (A ^ s) ≡ Γ'₂-A ,, [ C' ^ t' ]
        ant-simp-2 = removeAll-++-r-pf-neq (λ eq → C'-neq-A (sym eq))
        res2-ant-cast : Γ ,, (Γ'₂-A ,, [ C ^ t ]) ⊢ Δ1-A ,, Δ'₂
        res2-ant-cast = subst (λ pf → Γ ,, (Γ'₂-A ,, [ pf ]) ⊢ Δ1-A ,, Δ'₂)
                              (sym Ct-eq-C't')
                              (subst (λ G → Γ ,, G ⊢ Δ1-A ,, Δ'₂) ant-simp-2 res2-succ)
        ant-assoc : Γ ,, (Γ'₂-A ,, [ C ^ t ]) ≡ (Γ ,, Γ'₂-A) ,, [ C ^ t ]
        ant-assoc = sym (++-assoc Γ Γ'₂-A [ C ^ t ])
        res2-cast : (Γ ,, Γ'₂-A) ,, [ C ^ t ] ⊢ Δ1-A ,, Δ'₂
        res2-cast = subst (_⊢ Δ1-A ,, Δ'₂) ant-assoc res2-ant-cast

        -- FINAL MIX ON C: degree decrease
        res1-wf = makeWellFormed res1-cast
        res2-wf = makeWellFormed res2-cast
        acc3 = accR (degree C , mixHeight res1-wf res2-wf) (inl degC-lt-n)
        mix3-pair = Mix {n = degree C} {A = C} {s = t} refl
                       res1-wf res2-wf
                       (makeWellFormed-WellFormed res1-cast) (makeWellFormed-WellFormed res2-cast) acc3
        mix3 = fst mix3-pair
        d-mix3 = snd mix3-pair

        -- STRUCTURAL CONTRACTION
        sub-ant = subset-concat {G = Γ ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ]) - (A ^ s))}
          subset-refl
          (subset-trans
            (removeAll-append-singleton-⊆ (Γ ,, Γ'₂-A) (C ^ t))
            (subset-concat (λ y yIn → mem-++-l yIn)
              (λ y yIn → mem-++-r Γ (let (yInΓ'₂ , y≠A) = removeAll-mem yIn
                                      in mem-removeAll (mem-++-r Γ'₁ (mem-++-l yInΓ'₂)) y≠A))))

        sub-succ = subset-concat {G = Δ1-A ,, (Δ'₁ ,, Δ'₂)}
          (removeAll-drop-singleton-r [] (Δ1-A ,, (Δ'₁ ,, Δ'₂)) (C ^ t))
          (subset-concat (λ y yIn → mem-++-l yIn)
            (λ y yIn → mem-++-r Δ1-A (mem-++-r Δ'₁ yIn)))

        p_struct = structural sub-ant sub-succ mix3

        -- TRANSPORT TO GOAL TYPE
        p' = subst (Γ ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ t' ]) - (A ^ s)) ⊢_)
                   (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-simp-2)) p_struct

        -- DEGREE BOUND
        δ-res1-cast-eq : δ res1-cast ≡ δ res1
        δ-res1-cast-eq = subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) succ-simp-1) res1
        δ-res1-wf-eq : δ res1-wf ≡ δ res1
        δ-res1-wf-eq = trans (δ-makeWellFormed res1-cast) δ-res1-cast-eq
        res1-bound : δ res1-wf ≤ GoalBound
        res1-bound = subst (_≤ GoalBound) (sym δ-res1-wf-eq) d-res1

        δ-res2-succ-eq : δ res2-succ ≡ δ res2
        δ-res2-succ-eq = subst-preserves-δ (cong (_,, Δ'₂) succ-simp-2) res2
        δ-res2-ant-eq : δ res2-ant-cast ≡ δ res2
        δ-res2-ant-eq = trans
          (subst-preserves-δ-ctx (cong (λ pf → Γ ,, (Γ'₂-A ,, [ pf ])) (sym Ct-eq-C't'))
            (subst (λ G → Γ ,, G ⊢ Δ1-A ,, Δ'₂) ant-simp-2 res2-succ))
          (trans (subst-preserves-δ-ctx (cong (Γ ,,_) ant-simp-2) res2-succ) δ-res2-succ-eq)
        δ-res2-cast-eq : δ res2-cast ≡ δ res2
        δ-res2-cast-eq = trans (subst-preserves-δ-ctx ant-assoc res2-ant-cast) δ-res2-ant-eq
        δ-res2-wf-eq : δ res2-wf ≡ δ res2
        δ-res2-wf-eq = trans (δ-makeWellFormed res2-cast) δ-res2-cast-eq
        res2-intermediate : max (δ (⊢∨₂ {A = B} Π1)) (δ Π2') ≤ GoalBound
        res2-intermediate = max-least
          (left-≤-max {δ (⊢∨₂ {A = B} Π1)} {δ (∨⊢ Π1' Π2')})
          (right-right-≤-max)
        res2-bound : δ res2-wf ≤ GoalBound
        res2-bound = subst (_≤ GoalBound) (sym δ-res2-wf-eq) (≤-trans d-res2 res2-intermediate)

        max-res-bound = max-least res1-bound res2-bound
        mix3-bound : δ mix3 ≤ GoalBound
        mix3-bound = ≤-trans d-mix3 max-res-bound

        δ-p-struct = structural-preserves-δ sub-ant sub-succ mix3
        δ-p' = subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-simp-2)) p_struct
        d_final : δ p' ≤ GoalBound
        d_final = subst (_≤ GoalBound) (sym (δ-p' ∙ δ-p-struct)) mix3-bound
      in (p' , d_final)

-- =============================================================================
-- Principal Case: ⊢⇒ vs ⇒⊢
-- Left: ⊢⇒ Π1 : Γ ⊢ [(B ⇒ C) ^ t] ,, Δ1  where Π1 : Γ ,, [B ^ t] ⊢ [C ^ t] ,, Δ1
-- Right: ⇒⊢ Π1' Π2' : Γ'₁ ,, Γ'₂ ,, [(B' ⇒ C') ^ t'] ⊢ Δ'₁ ,, Δ'₂
--   where Π1' : Γ'₁ ,, [C' ^ t'] ⊢ Δ'₁, Π2' : Γ'₂ ⊢ [B' ^ t'] ,, Δ'₂
-- 3 cross-cuts + 2 final mixes (on C then B)
-- =============================================================================
Mix {n = n} {Γ = Γ} {Δ = .([ (B ⇒ C) ^ t ] ,, Δ1)}
    {Γ' = .(Γ'₁ ,, Γ'₂ ,, [ (B' ⇒ C') ^ t' ])} {Δ' = .(Δ'₁ ,, Δ'₂)} {A = A} {s = s}
    degEq (⊢⇒ {.Γ} {B} {t} {C} {Δ1} Π1)
          (⇒⊢ {Γ₁ = Γ'₁} {B = C'} {s = t'} {Δ₁ = Δ'₁} {Γ₂ = Γ'₂} {A = B'} {Δ₂ = Δ'₂} Π1' Π2') wfp wfp' (acc accRec) =
    handleImplCase accRec (discretePFormula (A ^ s) ((B ⇒ C) ^ t)) (discretePFormula (A ^ s) ((B' ⇒ C') ^ t'))
  where
    GoalBound = max (δ (⊢⇒ Π1)) (δ (⇒⊢ Π1' Π2'))
    Result = Σ (Γ ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ⇒ C') ^ t' ]) - (A ^ s)) ⊢
                 (([ (B ⇒ C) ^ t ] ,, Δ1) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂))
               (λ p → δ p ≤ GoalBound)

    handleImplCase : (∀ m' → m' <Lex (n , mixHeight (⊢⇒ Π1) (⇒⊢ Π1' Π2')) → Acc _<Lex_ m')
                   → Dec ((A ^ s) ≡ ((B ⇒ C) ^ t)) → Dec ((A ^ s) ≡ ((B' ⇒ C') ^ t')) → Result
    handleImplCase accR (no neq1) _ =
      let h-dec = mixHeight-dec-l (⊢⇒ Π1) Π1 (⇒⊢ Π1' Π2') (height-subproof-1 Π1)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ = Γ ,, [ B ^ t ]} {Δ = [ C ^ t ] ,, Δ1} degEq Π1 (⇒⊢ Π1' Π2') wfp wfp' acc'
          Γ'-rem = (Γ'₁ ,, Γ'₂ ,, [ (B' ⇒ C') ^ t' ]) - (A ^ s)
          Δ1-rem = Δ1 - (A ^ s)
          -- Reorder antecedent and succedent simultaneously
          sub_left : ((Γ ,, [ B ^ t ]) ,, Γ'-rem) ⊆ ((Γ ,, Γ'-rem) ,, [ B ^ t ])
          sub_left = solve ((var 0 ++ₑ elm 0) ++ₑ var 1) ((var 0 ++ₑ var 1) ++ₑ elm 0) ((Γ ∷ Γ'-rem ∷ []) , (B ^ t ∷ [])) {refl}
          sub_delta : ((([ C ^ t ] ,, Δ1) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂)) ⊆ ([ C ^ t ] ,, (Δ1-rem ,, (Δ'₁ ,, Δ'₂)))
          sub_delta = solve (rem (elm 0 ++ₑ var 0) 1 ++ₑ var 1) (elm 0 ++ₑ (rem (var 0) 1 ++ₑ var 1)) ((Δ1 ∷ (Δ'₁ ,, Δ'₂) ∷ []) , (C ^ t ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left sub_delta mix
          p_impl = ⊢⇒ {Γ = Γ ,, Γ'-rem} {A = B} {s = t} {B = C} {Δ = Δ1-rem ,, (Δ'₁ ,, Δ'₂)} mix_r
          sub_right : ([ (B ⇒ C) ^ t ] ,, (Δ1-rem ,, (Δ'₁ ,, Δ'₂))) ⊆ (([ (B ⇒ C) ^ t ] ,, Δ1-rem) ,, (Δ'₁ ,, Δ'₂))
          sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((elm 0 ++ₑ var 0) ++ₑ var 1) ((Δ1-rem ∷ (Δ'₁ ,, Δ'₂) ∷ []) , ((B ⇒ C) ^ t ∷ [])) {refl}
          p_reorder = structural subset-refl sub_right p_impl
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B ⇒ C) ^ t} {Γ = Δ1} neq1
          p' = subst (λ D → Γ ,, Γ'-rem ⊢ D ,, (Δ'₁ ,, Δ'₂)) (sym succ-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-eq)) p_reorder)
                 (trans (structural-preserves-δ subset-refl sub_right p_impl) (structural-preserves-δ sub_left sub_delta mix))
          d_final : δ p' ≤ GoalBound
          d_final = subst (_≤ GoalBound) (sym d_p') dmix
      in (p' , d_final)
    handleImplCase accR (yes eq1) (no neq2) =
      let h-dec1 = mixHeight-dec-r (⊢⇒ Π1) (⇒⊢ Π1' Π2') Π1' (height-subproof-2-l Π1' Π2')
          h-dec2 = mixHeight-dec-r (⊢⇒ Π1) (⇒⊢ Π1' Π2') Π2' (height-subproof-2-r Π1' Π2')
          acc1 = accR _ (inr (refl , h-dec1))
          acc2 = accR _ (inr (refl , h-dec2))
          (mix1 , dmix1) = Mix {Γ' = Γ'₁ ,, [ C' ^ t' ]} {Δ' = Δ'₁} degEq (⊢⇒ Π1) Π1' wfp (fst wfp') acc1
          (mix2 , dmix2) = Mix {Γ' = Γ'₂} {Δ' = [ B' ^ t' ] ,, Δ'₂} degEq (⊢⇒ Π1) Π2' wfp (snd wfp') acc2
          Γ'₁-A = Γ'₁ - (A ^ s)
          Γ'₂-A = Γ'₂ - (A ^ s)
          Succ-rem = (([ (B ⇒ C) ^ t ] ,, Δ1) - (A ^ s))
          -- Reorder mix1 antecedent: move [C'^t'] to end
          sub_left1 : (Γ ,, ((Γ'₁ ,, [ C' ^ t' ]) - (A ^ s))) ⊆ ((Γ ,, Γ'₁-A) ,, [ C' ^ t' ])
          sub_left1 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ ∷ Γ'₁ ∷ []) , (C' ^ t' ∷ A ^ s ∷ [])) {refl}
          mix1_r = structural sub_left1 subset-refl mix1
          -- Reorder mix2 succedent: move [B'^t'] to front
          sub_delta2 : (Succ-rem ,, ([ B' ^ t' ] ,, Δ'₂)) ⊆ ([ B' ^ t' ] ,, (Succ-rem ,, Δ'₂))
          sub_delta2 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Succ-rem ∷ Δ'₂ ∷ []) , (B' ^ t' ∷ [])) {refl}
          mix2_r = structural subset-refl sub_delta2 mix2
          -- Apply ⇒⊢
          p_impl = ⇒⊢ {Γ₁ = Γ ,, Γ'₁-A} {B = C'} {s = t'} {Δ₁ = Succ-rem ,, Δ'₁} {Γ₂ = Γ ,, Γ'₂-A} {A = B'} {Δ₂ = Succ-rem ,, Δ'₂} mix1_r mix2_r
          -- Contract — ⇒⊢ result type: Γ₁ ,, (Γ₂ ,, [formula]) (right-assoc ,,)
          subLeft : ((Γ ,, Γ'₁-A) ,, ((Γ ,, Γ'₂-A) ,, [ (B' ⇒ C') ^ t' ])) ⊆ (Γ ,, ((Γ'₁-A ,, Γ'₂-A) ,, [ (B' ⇒ C') ^ t' ]))
          subLeft = solve ((var 0 ++ₑ var 1) ++ₑ ((var 0 ++ₑ var 2) ++ₑ elm 0)) (var 0 ++ₑ ((var 1 ++ₑ var 2) ++ₑ elm 0)) ((Γ ∷ Γ'₁-A ∷ Γ'₂-A ∷ []) , ((B' ⇒ C') ^ t' ∷ [])) {refl}
          subRight : ((Succ-rem ,, Δ'₁) ,, (Succ-rem ,, Δ'₂)) ⊆ (Succ-rem ,, (Δ'₁ ,, Δ'₂))
          subRight = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Succ-rem ∷ Δ'₁ ∷ Δ'₂ ∷ []) , []) {refl}
          p_contracted = structural subLeft subRight p_impl
          -- Transport antecedent
          ant-eq : (Γ'₁ ,, Γ'₂ ,, [ (B' ⇒ C') ^ t' ]) - (A ^ s) ≡ (Γ'₁-A ,, Γ'₂-A) ,, [ (B' ⇒ C') ^ t' ]
          ant-eq = cong (_- (A ^ s)) (sym (++-assoc Γ'₁ Γ'₂ [ (B' ⇒ C') ^ t' ]))
                 ∙ trans (lemma-removeAll-cons-neq {Γ = Γ'₁ ,, Γ'₂} neq2)
                         (cong (_,, [ (B' ⇒ C') ^ t' ]) (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ'₁ Γ'₂))
          p' = subst (λ G → Γ ,, G ⊢ Succ-rem ,, (Δ'₁ ,, Δ'₂)) (sym ant-eq) p_contracted
          -- Degree bounds
          d_mix1_r = structural-preserves-δ sub_left1 subset-refl mix1
          d_mix2_r = structural-preserves-δ subset-refl sub_delta2 mix2
          d_contracted = structural-preserves-δ subLeft subRight p_impl
          d_p'_eq = subst-preserves-δ-ctx (cong (Γ ,,_) (sym ant-eq)) p_contracted
          dLeft≤G : δ (⊢⇒ Π1) ≤ GoalBound
          dLeft≤G = left-≤-max {δ (⊢⇒ Π1)} {δ (⇒⊢ Π1' Π2')}
          -- δ (⇒⊢ Π1' Π2') = max (δ Π1') (δ Π2') by definition
          dΠ1'≤G : δ Π1' ≤ GoalBound
          dΠ1'≤G = left-right-≤-max
          dmix1' = subst (_≤ GoalBound) (sym d_mix1_r) (≤-trans dmix1 (max-least dLeft≤G dΠ1'≤G))
          dΠ2'≤G : δ Π2' ≤ GoalBound
          dΠ2'≤G = right-right-≤-max
          dmix2' = subst (_≤ GoalBound) (sym d_mix2_r) (≤-trans dmix2 (max-least dLeft≤G dΠ2'≤G))
          dpImpl = max-least dmix1' dmix2'
          d_final : δ p' ≤ GoalBound
          d_final = subst (_≤ GoalBound) (sym (d_p'_eq ∙ d_contracted)) dpImpl
      in (p' , d_final)
    handleImplCase accR (yes eq1) (yes eq2) =
      let
        BC-eq-B'C' : (B ⇒ C) ^ t ≡ (B' ⇒ C') ^ t'
        BC-eq-B'C' = sym eq1 ∙ eq2
        B-eq-B' : B ≡ B'
        B-eq-B' = ⇒-inj-l (cong PFormula.form BC-eq-B'C')
        C-eq-C' : C ≡ C'
        C-eq-C' = ⇒-inj-r (cong PFormula.form BC-eq-B'C')
        t-eq-t' : t ≡ t'
        t-eq-t' = cong PFormula.pos BC-eq-B'C'
        Bt-eq-B't' : B ^ t ≡ B' ^ t'
        Bt-eq-B't' = cong₂ _^_ B-eq-B' t-eq-t'
        Ct-eq-C't' : C ^ t ≡ C' ^ t'
        Ct-eq-C't' = cong₂ _^_ C-eq-C' t-eq-t'

        degA-eq : degree A ≡ suc (max (degree B) (degree C))
        degA-eq = cong degree (cong PFormula.form eq1)
        degB-lt-n : degree B < n
        degB-lt-n = subst (degree B <_) (sym degA-eq ∙ degEq) (degree-⇒-l B C)
        degC-lt-n : degree C < n
        degC-lt-n = subst (degree C <_) (sym degA-eq ∙ degEq) (degree-⇒-r B C)

        B-neq-A : (B ^ t) ≢ (A ^ s)
        B-neq-A eq = subformula-neq-⇒-l {B = B} {C = C} {s = t} {t = s}
                     (subst (λ X → B ^ t ≡ X ^ s) (cong PFormula.form eq1) eq)
        C-neq-A : (C ^ t) ≢ (A ^ s)
        C-neq-A eq = subformula-neq-⇒-r {B = B} {C = C} {s = t} {t = s}
                     (subst (λ X → C ^ t ≡ X ^ s) (cong PFormula.form eq1) eq)
        C'-neq-A : (C' ^ t') ≢ (A ^ s)
        C'-neq-A eq = subformula-neq-⇒-r {B = B'} {C = C'} {s = t'} {t = s}
                      (subst (λ X → C' ^ t' ≡ X ^ s) (cong PFormula.form eq2) eq)
        B'-neq-A : (B' ^ t') ≢ (A ^ s)
        B'-neq-A eq = subformula-neq-⇒-l {B = B'} {C = C'} {s = t'} {t = s}
                      (subst (λ X → B' ^ t' ≡ X ^ s) (cong PFormula.form eq2) eq)

        Δ1-A = Δ1 - (A ^ s)
        Γ'₁-A = Γ'₁ - (A ^ s)
        Γ'₂-A = Γ'₂ - (A ^ s)
        Γ'-rem = (Γ'₁ ,, Γ'₂ ,, [ (B' ⇒ C') ^ t' ]) - (A ^ s)

        -- CROSS-CUT 1: Mix Π1 with (⇒⊢ Π1' Π2') on A — height decrease left
        h-dec-1 = mixHeight-dec-l (⊢⇒ Π1) Π1 (⇒⊢ Π1' Π2') (height-subproof-1 Π1)
        acc1 = accR _ (inr (refl , h-dec-1))
        res1-pair = Mix {Γ = Γ ,, [ B ^ t ]} {Δ = [ C ^ t ] ,, Δ1} degEq Π1 (⇒⊢ Π1' Π2') wfp wfp' acc1
        res1 = fst res1-pair
        d-res1 = snd res1-pair

        succ-simp-1 : ([ C ^ t ] ,, Δ1) - (A ^ s) ≡ [ C ^ t ] ,, Δ1-A
        succ-simp-1 = removeAll-prepend-pf-neq (λ eq → C-neq-A (sym eq))
        res1-cast : (Γ ,, [ B ^ t ]) ,, Γ'-rem ⊢ ([ C ^ t ] ,, Δ1-A) ,, (Δ'₁ ,, Δ'₂)
        res1-cast = subst (λ D → (Γ ,, [ B ^ t ]) ,, Γ'-rem ⊢ D ,, (Δ'₁ ,, Δ'₂)) succ-simp-1 res1

        -- CROSS-CUT 2: Mix (⊢⇒ Π1) with Π1' on A — height decrease right
        h-dec-2 = mixHeight-dec-r (⊢⇒ Π1) (⇒⊢ Π1' Π2') Π1' (height-subproof-2-l Π1' Π2')
        acc2 = accR _ (inr (refl , h-dec-2))
        res2-pair = Mix {Γ' = Γ'₁ ,, [ C' ^ t' ]} {Δ' = Δ'₁} degEq (⊢⇒ Π1) Π1' wfp (fst wfp') acc2
        res2 = fst res2-pair
        d-res2 = snd res2-pair

        succ-simp-2 : ([ (B ⇒ C) ^ t ] ,, Δ1) - (A ^ s) ≡ Δ1-A
        succ-simp-2 = lemma-removeAll-head-eq {A = A ^ s} {B = (B ⇒ C) ^ t} {Γ = Δ1} eq1
        res2-succ : Γ ,, ((Γ'₁ ,, [ C' ^ t' ]) - (A ^ s)) ⊢ Δ1-A ,, Δ'₁
        res2-succ = subst (λ D → Γ ,, ((Γ'₁ ,, [ C' ^ t' ]) - (A ^ s)) ⊢ D ,, Δ'₁) succ-simp-2 res2

        ant-simp-2 : (Γ'₁ ,, [ C' ^ t' ]) - (A ^ s) ≡ Γ'₁-A ,, [ C' ^ t' ]
        ant-simp-2 = removeAll-++-r-pf-neq (λ eq → C'-neq-A (sym eq))
        res2-ant-cast : Γ ,, (Γ'₁-A ,, [ C ^ t ]) ⊢ Δ1-A ,, Δ'₁
        res2-ant-cast = subst (λ pf → Γ ,, (Γ'₁-A ,, [ pf ]) ⊢ Δ1-A ,, Δ'₁)
                              (sym Ct-eq-C't')
                              (subst (λ G → Γ ,, G ⊢ Δ1-A ,, Δ'₁) ant-simp-2 res2-succ)
        ant-assoc-2 : Γ ,, (Γ'₁-A ,, [ C ^ t ]) ≡ (Γ ,, Γ'₁-A) ,, [ C ^ t ]
        ant-assoc-2 = sym (++-assoc Γ Γ'₁-A [ C ^ t ])
        res2-final : (Γ ,, Γ'₁-A) ,, [ C ^ t ] ⊢ Δ1-A ,, Δ'₁
        res2-final = subst (_⊢ Δ1-A ,, Δ'₁) ant-assoc-2 res2-ant-cast

        -- CROSS-CUT 3: Mix (⊢⇒ Π1) with Π2' on A — height decrease right
        h-dec-3 = mixHeight-dec-r (⊢⇒ Π1) (⇒⊢ Π1' Π2') Π2' (height-subproof-2-r Π1' Π2')
        acc3 = accR _ (inr (refl , h-dec-3))
        res3-pair = Mix {Γ' = Γ'₂} {Δ' = [ B' ^ t' ] ,, Δ'₂} degEq (⊢⇒ Π1) Π2' wfp (snd wfp') acc3
        res3 = fst res3-pair
        d-res3 = snd res3-pair

        res3-succ : Γ ,, Γ'₂-A ⊢ Δ1-A ,, ([ B' ^ t' ] ,, Δ'₂)
        res3-succ = subst (λ D → Γ ,, Γ'₂-A ⊢ D ,, ([ B' ^ t' ] ,, Δ'₂)) succ-simp-2 res3
        res3-cast : Γ ,, Γ'₂-A ⊢ Δ1-A ,, ([ B ^ t ] ,, Δ'₂)
        res3-cast = subst (λ pf → Γ ,, Γ'₂-A ⊢ Δ1-A ,, ([ pf ] ,, Δ'₂)) (sym Bt-eq-B't') res3-succ

        -- Reorder res3 succedent: [B^t] to head
        res3-reorder : (Δ1-A ,, ([ B ^ t ] ,, Δ'₂)) ⊆ ([ B ^ t ] ,, (Δ1-A ,, Δ'₂))
        res3-reorder = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1))
                             ((Δ1-A ∷ Δ'₂ ∷ []) , (B ^ t ∷ [])) {refl}
        res3-reordered : Γ ,, Γ'₂-A ⊢ [ B ^ t ] ,, (Δ1-A ,, Δ'₂)
        res3-reordered = structural subset-refl res3-reorder res3-cast

        -- FINAL MIX 1 ON C: degree decrease
        res1-wf = makeWellFormed res1-cast
        res2-wf = makeWellFormed res2-final
        acc4 = accR (degree C , mixHeight res1-wf res2-wf) (inl degC-lt-n)
        mix4-pair = Mix {n = degree C} {A = C} {s = t} refl
                       res1-wf res2-wf
                       (makeWellFormed-WellFormed res1-cast) (makeWellFormed-WellFormed res2-final) acc4
        mix4 = fst mix4-pair
        d-mix4 = snd mix4-pair

        -- Contract mix4 to Υ
        sub-ant-4 = subset-concat {G = (Γ ,, [ B ^ t ]) ,, Γ'-rem}
          subset-refl
          (subset-trans
            (removeAll-append-singleton-⊆ (Γ ,, Γ'₁-A) (C ^ t))
            (subset-concat (λ y yIn → mem-++-l (mem-++-l yIn))
              (λ y yIn → mem-++-r (Γ ,, [ B ^ t ])
                (let (yInΓ'₁ , y≠A) = removeAll-mem yIn
                 in mem-removeAll (mem-++-l yInΓ'₁) y≠A))))

        sub-succ-4 = subset-concat {G = Δ1-A ,, (Δ'₁ ,, Δ'₂)}
          (removeAll-drop-singleton-r [] (Δ1-A ,, (Δ'₁ ,, Δ'₂)) (C ^ t))
          (subset-concat (λ y yIn → mem-++-l yIn)
            (λ y yIn → mem-++-r Δ1-A (mem-++-l yIn)))

        Υ = structural sub-ant-4 sub-succ-4 mix4
        -- Υ : (Γ ,, [B^t]) ,, Γ'-rem ⊢ Δ1-A ,, (Δ'₁ ,, Δ'₂)

        -- Reorder Υ antecedent: move [B^t] to end
        Υ-reorder = solve ((var 0 ++ₑ elm 0) ++ₑ var 1) ((var 0 ++ₑ var 1) ++ₑ elm 0)
                          ((Γ ∷ Γ'-rem ∷ []) , (B ^ t ∷ [])) {refl}
        Υ-cast : (Γ ,, Γ'-rem) ,, [ B ^ t ] ⊢ Δ1-A ,, (Δ'₁ ,, Δ'₂)
        Υ-cast = structural Υ-reorder subset-refl Υ

        -- FINAL MIX 2 ON B: degree decrease
        res3-wf = makeWellFormed res3-reordered
        Υ-wf = makeWellFormed Υ-cast
        acc5 = accR (degree B , mixHeight res3-wf Υ-wf) (inl degB-lt-n)
        mix5-pair = Mix {n = degree B} {A = B} {s = t} refl
                       res3-wf Υ-wf
                       (makeWellFormed-WellFormed res3-reordered) (makeWellFormed-WellFormed Υ-cast) acc5
        mix5 = fst mix5-pair
        d-mix5 = snd mix5-pair

        -- Contract mix5 to goal
        sub-ant-5 = subset-concat {G = Γ ,, Γ'-rem}
          (subset-concat (λ y yIn → mem-++-l yIn)
            (λ y yIn → mem-++-r Γ (let (yInΓ'₂ , y≠A) = removeAll-mem yIn
                                    in mem-removeAll (mem-++-r Γ'₁ (mem-++-l yInΓ'₂)) y≠A)))
          (removeAll-append-singleton-⊆ (Γ ,, Γ'-rem) (B ^ t))

        sub-succ-5 = subset-concat {G = Δ1-A ,, (Δ'₁ ,, Δ'₂)}
          (subset-trans
            (removeAll-drop-singleton-r [] (Δ1-A ,, Δ'₂) (B ^ t))
            (subset-concat (λ y yIn → mem-++-l yIn)
              (λ y yIn → mem-++-r Δ1-A (mem-++-r Δ'₁ yIn))))
          subset-refl

        p_struct = structural sub-ant-5 sub-succ-5 mix5

        p' = subst (Γ ,, Γ'-rem ⊢_)
                   (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-simp-2)) p_struct

        -- DEGREE BOUND
        δ-res1-cast-eq : δ res1-cast ≡ δ res1
        δ-res1-cast-eq = subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) succ-simp-1) res1
        δ-res1-wf-eq : δ res1-wf ≡ δ res1
        δ-res1-wf-eq = trans (δ-makeWellFormed res1-cast) δ-res1-cast-eq
        res1-bound : δ res1-wf ≤ GoalBound
        res1-bound = subst (_≤ GoalBound) (sym δ-res1-wf-eq) d-res1

        δ-res2-succ-eq : δ res2-succ ≡ δ res2
        δ-res2-succ-eq = subst-preserves-δ (cong (_,, Δ'₁) succ-simp-2) res2
        δ-res2-ant-eq : δ res2-ant-cast ≡ δ res2
        δ-res2-ant-eq = trans
          (subst-preserves-δ-ctx (cong (λ pf → Γ ,, (Γ'₁-A ,, [ pf ])) (sym Ct-eq-C't'))
            (subst (λ G → Γ ,, G ⊢ Δ1-A ,, Δ'₁) ant-simp-2 res2-succ))
          (trans (subst-preserves-δ-ctx (cong (Γ ,,_) ant-simp-2) res2-succ) δ-res2-succ-eq)
        δ-res2-final-eq : δ res2-final ≡ δ res2
        δ-res2-final-eq = trans (subst-preserves-δ-ctx ant-assoc-2 res2-ant-cast) δ-res2-ant-eq
        δ-res2-wf-eq : δ res2-wf ≡ δ res2
        δ-res2-wf-eq = trans (δ-makeWellFormed res2-final) δ-res2-final-eq
        res2-intermediate : max (δ (⊢⇒ Π1)) (δ Π1') ≤ GoalBound
        res2-intermediate = max-least
          (left-≤-max {δ (⊢⇒ Π1)} {δ (⇒⊢ Π1' Π2')})
          (left-right-≤-max)
        res2-bound : δ res2-wf ≤ GoalBound
        res2-bound = subst (_≤ GoalBound) (sym δ-res2-wf-eq) (≤-trans d-res2 res2-intermediate)

        max-res12-bound = max-least res1-bound res2-bound
        mix4-bound : δ mix4 ≤ GoalBound
        mix4-bound = ≤-trans d-mix4 max-res12-bound

        δ-Υ-eq = structural-preserves-δ sub-ant-4 sub-succ-4 mix4
        δ-Υ-cast-eq = structural-preserves-δ Υ-reorder subset-refl Υ
        δ-Υ-wf-eq : δ Υ-wf ≡ δ mix4
        δ-Υ-wf-eq = trans (δ-makeWellFormed Υ-cast) (trans δ-Υ-cast-eq δ-Υ-eq)
        Υ-wf-bound : δ Υ-wf ≤ GoalBound
        Υ-wf-bound = subst (_≤ GoalBound) (sym δ-Υ-wf-eq) mix4-bound

        δ-res3-succ-eq : δ res3-succ ≡ δ res3
        δ-res3-succ-eq = subst-preserves-δ (cong (_,, ([ B' ^ t' ] ,, Δ'₂)) succ-simp-2) res3
        δ-res3-cast-eq : δ res3-cast ≡ δ res3
        δ-res3-cast-eq = trans
          (subst-preserves-δ (cong (λ pf → Δ1-A ,, ([ pf ] ,, Δ'₂)) (sym Bt-eq-B't')) res3-succ)
          δ-res3-succ-eq
        δ-res3-reordered-eq : δ res3-reordered ≡ δ res3
        δ-res3-reordered-eq = trans (structural-preserves-δ subset-refl res3-reorder res3-cast) δ-res3-cast-eq
        δ-res3-wf-eq : δ res3-wf ≡ δ res3
        δ-res3-wf-eq = trans (δ-makeWellFormed res3-reordered) δ-res3-reordered-eq
        res3-intermediate : max (δ (⊢⇒ Π1)) (δ Π2') ≤ GoalBound
        res3-intermediate = max-least
          (left-≤-max {δ (⊢⇒ Π1)} {δ (⇒⊢ Π1' Π2')})
          (right-right-≤-max)
        res3-bound : δ res3-wf ≤ GoalBound
        res3-bound = subst (_≤ GoalBound) (sym δ-res3-wf-eq) (≤-trans d-res3 res3-intermediate)

        max-res35-bound = max-least res3-bound Υ-wf-bound
        mix5-bound : δ mix5 ≤ GoalBound
        mix5-bound = ≤-trans d-mix5 max-res35-bound

        δ-p-struct = structural-preserves-δ sub-ant-5 sub-succ-5 mix5
        δ-p' = subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-simp-2)) p_struct
        d_final : δ p' ≤ GoalBound
        d_final = subst (_≤ GoalBound) (sym (δ-p' ∙ δ-p-struct)) mix5-bound
      in (p' , d_final)

-- =============================================================================
-- Principal Case 7: ⊢□ vs □⊢
-- =============================================================================
-- Left: ⊢□ ext freshΓ freshΔ Π1 : Γ_sub ⊢ [ (□ B) ^ r ] ,, Δ_sub
--   where Π1 : Γ_sub ⊢ [ B ^ insertToken x r ] ,, Δ_sub
-- Right: □⊢ Π1' : Γ'₁ ,, [ (□ B') ^ r' ] ⊢ Δ'₁
--   where Π1' : Γ'₁ ,, [ B' ^ (r' ∘ t_r) ] ⊢ Δ'₁
Mix {n = n} {Γ = Γ_sub} {Δ = .([ (□ B) ^ r ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (□ B') ^ r' ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢□ {x} {r} {.Γ_sub} {Δ_sub} {B} ext freshΓ_sub freshΔ_sub Π1) (□⊢ {Γ'₁} {B'} {r'} {t_r} {Δ'₁} Π1') wfp wfp' (acc accRec) =
    handleBoxCase accRec (discretePFormula (A ^ s) ((□ B) ^ r)) (discretePFormula (A ^ s) ((□ B') ^ r'))
  where
    GoalCtx = Γ_sub ,, ((Γ'₁ ,, [ (□ B') ^ r' ]) - (A ^ s))
    GoalSucc = (([ (□ B) ^ r ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
    GoalType = GoalCtx ⊢ GoalSucc
    GoalBound = max (δ (⊢□ ext freshΓ_sub freshΔ_sub Π1)) (δ (□⊢ Π1'))
    Result = Σ GoalType (λ p → δ p ≤ GoalBound)

    handleBoxCase : (∀ m' → m' <Lex (n , mixHeight (⊢□ ext freshΓ_sub freshΔ_sub Π1) (□⊢ Π1')) → Acc _<Lex_ m')
                  → Dec ((A ^ s) ≡ ((□ B) ^ r)) → Dec ((A ^ s) ≡ ((□ B') ^ r')) → Result
    -- Non-principal cases (to be handled by catch-all)
    handleBoxCase accR (no neq1) _ =
      let -- Well-formedness components
          wf : maxEigenposToken Π1 < x
          wf = fst wfp
          wfp-sub : WellFormedProof Π1
          wfp-sub = snd wfp

          -- Abbreviations
          Γ'₁-rem = (Γ'₁ ,, [ (□ B') ^ r' ]) - (A ^ s)
          Δ_sub-A = Δ_sub - (A ^ s)

          -- Combined context for freshness
          combined = (Γ_sub ,, Γ'₁-rem) ,, (Δ_sub-A ,, Δ'₁)

          -- Fresh eigenposition
          x' = freshTokenForRename r combined Π1
          x'-fresh-combined = freshTokenForRename-fresh r combined Π1
          x'-eigenpos = freshTokenForRename-eigenpos r combined Π1
          x'∉r = freshTokenForRename-∉r r combined Π1

          -- Eigenposition extension
          eigent = insertToken x r
          extSTE = mkSingleTokenExt r x ext

          -- New eigenposition
          t' = substPos x (singleton-pos x') eigent

          -- Rename eigenposition: x → x' in Π1
          rename-result = renameEigenpos-⊢□-premise-gen {r = r} {t = eigent} {x = x} {Γ = Γ_sub} {Δ = Δ_sub} {A = B}
                            Π1 extSTE freshΓ_sub freshΔ_sub wf x' x'-eigenpos x'∉r
          Π1-renamed = fst rename-result
          ext' = snd rename-result

          -- Properties of renamed proof
          δ-eq-renamed = δ-renameEigenpos-⊢□-premise-gen Π1 extSTE freshΓ_sub freshΔ_sub wf x' x'-eigenpos x'∉r
          height-eq-renamed = height-renameEigenpos-⊢□-premise-gen Π1 extSTE freshΓ_sub freshΔ_sub wf x' x'-eigenpos x'∉r
          wfp-renamed = WellFormed-renameEigenpos-⊢□-premise-gen Π1 extSTE freshΓ_sub freshΔ_sub wf x' x'-eigenpos x'∉r wfp-sub

          -- Height decrease: h(Π1-renamed) < h(⊢□ ... Π1)
          h-dec-raw = mixHeight-dec-l (⊢□ ext freshΓ_sub freshΔ_sub Π1) Π1 (□⊢ Π1') (height-subproof-1 Π1)
          mixHeight-eq = cong (λ h → h + height (□⊢ Π1')) height-eq-renamed
          h-dec = subst (_< mixHeight (⊢□ ext freshΓ_sub freshΔ_sub Π1) (□⊢ Π1')) (sym mixHeight-eq) h-dec-raw

          -- Mix renamed proof with right proof
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ = Γ_sub} {Δ = [ B ^ t' ] ,, Δ_sub} degEq Π1-renamed (□⊢ Π1') wfp-renamed wfp' acc'

          -- Reorder succedent: get [B^t'] at front
          sub_delta : ((([ B ^ t' ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁) ⊆ ([ B ^ t' ] ,, (Δ_sub-A ,, Δ'₁))
          sub_delta = solve (rem (elm 0 ++ₑ var 0) 1 ++ₑ var 1) (elm 0 ++ₑ (rem (var 0) 1 ++ₑ var 1)) ((Δ_sub ∷ Δ'₁ ∷ []) , (B ^ t' ∷ A ^ s ∷ [])) {refl}
          mix_reordered = structural subset-refl sub_delta mix

          -- Freshness of x' for combined contexts
          fresh-split = TokenFresh-split (Γ_sub ,, Γ'₁-rem) (Δ_sub-A ,, Δ'₁) x' x'-fresh-combined
          freshΓ_new = fst fresh-split
          freshΔ_new = snd fresh-split

          -- Transport t' to insertToken x' r
          t'-eq : t' ≡ insertToken x' r
          t'-eq = substPos-insertToken-eq x x' r ext
          mix_transported = subst (λ (p : Position) → Γ_sub ,, Γ'₁-rem ⊢ [ B ^ p ] ,, (Δ_sub-A ,, Δ'₁)) t'-eq mix_reordered

          -- Apply ⊢□ rule with fresh token x'
          p_boxed = ⊢□ {x'} {r} {Γ_sub ,, Γ'₁-rem} {Δ_sub-A ,, Δ'₁} {B} x'∉r freshΓ_new freshΔ_new mix_transported

          -- Reorder succedent: [(□B)^r] ,, (Δ_sub-A ,, Δ'₁) → ((□B)^r ,, Δ_sub-A) ,, Δ'₁
          sub_right : ([ (□ B) ^ r ] ,, (Δ_sub-A ,, Δ'₁)) ⊆ (([ (□ B) ^ r ] ,, Δ_sub-A) ,, Δ'₁)
          sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((elm 0 ++ₑ var 0) ++ₑ var 1) ((Δ_sub-A ∷ Δ'₁ ∷ []) , ((□ B) ^ r ∷ [])) {refl}
          p_reorder = structural subset-refl sub_right p_boxed

          -- Transport succedent to goal
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (□ B) ^ r} {Γ = Δ_sub} neq1
          p' : GoalType
          p' = subst (GoalCtx ⊢_) (cong (_,, Δ'₁) (sym succ-eq)) p_reorder

          -- Degree bounds
          d_mix_transported = subst-preserves-δ (cong {A = Position} (λ (p : Position) → [ B ^ p ] ,, (Δ_sub-A ,, Δ'₁)) t'-eq) mix_reordered
          d_mix_reordered = structural-preserves-δ subset-refl sub_delta mix
          d_p_reorder = structural-preserves-δ subset-refl sub_right p_boxed
          d_p'_eq = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = d_p'_eq ∙ d_p_reorder ∙ d_mix_transported ∙ d_mix_reordered

          bound-eq : max (δ Π1-renamed) (δ (□⊢ Π1')) ≡ max (δ Π1) (δ (□⊢ Π1'))
          bound-eq = cong (λ d → max d (δ (□⊢ Π1'))) δ-eq-renamed
          dmix' : δ mix ≤ max (δ Π1) (δ (□⊢ Π1'))
          dmix' = subst (δ mix ≤_) bound-eq dmix

          d_final : δ p' ≤ GoalBound
          d_final = subst (_≤ GoalBound) (sym d_p') dmix'
      in (p' , d_final)
    handleBoxCase accR (yes eq1) (no neq2) =
      let h-dec = mixHeight-dec-r (⊢□ ext freshΓ_sub freshΔ_sub Π1) (□⊢ Π1') Π1' (height-subproof-1 Π1')
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ (r' ∘ t_r) ]} {Δ' = Δ'₁} degEq (⊢□ ext freshΓ_sub freshΔ_sub Π1) Π1' wfp wfp' acc'
          -- mix : Γ_sub ,, ((Γ'₁ ,, [B'^(r'∘t_r)]) - A) ⊢ GoalSucc ,, Δ'₁
          -- (since GoalSucc uses the full ([(□ B)^r] ,, Δ_sub) - A which is the left proof's Δ - A)
          Γ'₁-A = Γ'₁ - (A ^ s)

          -- Reorder antecedent: move [B'^(r'∘t_r)] to end via subset
          sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ (r' ∘ t_r) ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ (r' ∘ t_r) ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ (r' ∘ t_r) ∷ A ^ s ∷ [])) {refl}

          mix_r = structural sub_left subset-refl mix
          -- mix_r : (Γ_sub ,, Γ'₁-A) ,, [B'^(r'∘t_r)] ⊢ GoalSucc ,, Δ'₁

          -- Apply □⊢ to convert [B'^(r'∘t_r)] to [(□ B')^r']
          p_box = □⊢ {Γ_sub ,, Γ'₁-A} {B'} {r'} {t_r} {GoalSucc} mix_r

          -- Reorder antecedent: (Γ_sub ,, Γ'₁-A) ,, [(□ B')^r'] → Γ_sub ,, (Γ'₁-A ,, [(□ B')^r'])
          sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (□ B') ^ r' ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (□ B') ^ r' ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((□ B') ^ r' ∷ [])) {refl}

          p_reorder = structural sub_left2 subset-refl p_box

          -- Transport antecedent: Γ'₁-A ,, [(□ B')^r'] = (Γ'₁ ,, [(□ B')^r']) - A
          ant-eq : (Γ'₁ ,, [ (□ B') ^ r' ]) - (A ^ s) ≡ Γ'₁-A ,, [ (□ B') ^ r' ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (□ B') ^ r'} {Γ = Γ'₁} neq2

          p' : GoalType
          p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder

          -- Degree preservation
          d_mix_r = structural-preserves-δ sub_left subset-refl mix
          d_p_reorder = structural-preserves-δ sub_left2 subset-refl p_box
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder) (trans d_p_reorder d_mix_r)
          d_final : δ p' ≤ GoalBound
          d_final = subst (_≤ GoalBound) (sym d_p') dmix
      in (p' , d_final)
    -- Principal: A = (□B)^r AND A = (□B')^r'
    handleBoxCase accR (yes eq1) (yes eq2) =
      let
        -- Formula equalities
        □B-eq-□B' : (□ B) ^ r ≡ (□ B') ^ r'
        □B-eq-□B' = sym eq1 ∙ eq2
        B-eq-B' : B ≡ B'
        B-eq-B' = □-inj (cong PFormula.form □B-eq-□B')
        r-eq-r' : r ≡ r'
        r-eq-r' = cong PFormula.pos □B-eq-□B'
        Brt-eq-B'r't : B ^ (r ∘ t_r) ≡ B' ^ (r' ∘ t_r)
        Brt-eq-B'r't = cong₂ _^_ B-eq-B' (cong (_∘ t_r) r-eq-r')

        -- Degree decrease: degree B < n
        degA-eq : degree A ≡ suc (degree B)
        degA-eq = cong degree (cong PFormula.form eq1)
        degB-lt-n : degree B < n
        degB-lt-n = subst (degree B <_) (sym degA-eq ∙ degEq) (degree-□ B)

        -- B^(r∘t_r) ≠ A^s (subformula inequality)
        B-neq-A : (B ^ (r ∘ t_r)) ≢ (A ^ s)
        B-neq-A eq = subformula-neq-□ {B = B} {s = r ∘ t_r} {t = s}
                     (subst (λ X → B ^ (r ∘ t_r) ≡ X ^ s) (cong PFormula.form eq1) eq)

        -- Abbreviations
        Γ'₁-A = Γ'₁ - (A ^ s)
        Δ_sub-A = Δ_sub - (A ^ s)

        -- ================================================================
        -- EIGENPOSITION SUBSTITUTION: x → t_r in Π1
        -- Converts B^(insertToken x r) to B^(r ∘ t_r)
        -- ================================================================
        subst-result = substEigenposInProof x t_r Π1 (fst wfp)
        Π1_subst_raw = fst subst-result
        h-Π1-subst-raw = fst (snd subst-result)
        δ-Π1-subst-raw = snd (snd subst-result)
        -- Π1_subst_raw : substCtx x t_r Γ_sub ⊢ substCtx x t_r ([ B ^ insertToken x r ] ,, Δ_sub)

        -- Transport to correct types (two steps for explicit height/δ preservation)
        ctx-eq-l : substCtx x t_r Γ_sub ≡ Γ_sub
        ctx-eq-l = substCtx-id x t_r Γ_sub freshΓ_sub
        succ-eq : substCtx x t_r ([ B ^ insertToken x r ] ,, Δ_sub) ≡ [ B ^ (r ∘ t_r) ] ,, Δ_sub
        succ-eq = substCtx-++ x t_r [ B ^ insertToken x r ] Δ_sub
                ∙ cong₂ _,,_ (cong [_] (cong (B ^_) (substPos-insertToken-gen x t_r r ext)))
                              (substCtx-id x t_r Δ_sub freshΔ_sub)

        Π1_subst_step1 = subst (_⊢ substCtx x t_r ([ B ^ insertToken x r ] ,, Δ_sub)) ctx-eq-l Π1_subst_raw
        Π1_subst = subst (Γ_sub ⊢_) succ-eq Π1_subst_step1
        -- Π1_subst : Γ_sub ⊢ [ B ^ (r ∘ t_r) ] ,, Δ_sub

        -- Height preservation chain
        h-Π1-subst : height Π1_subst ≡ height Π1
        h-Π1-subst = height-subst-Δ succ-eq Π1_subst_step1
                    ∙ height-subst-Γ ctx-eq-l Π1_subst_raw
                    ∙ h-Π1-subst-raw

        -- δ preservation chain
        δ-Π1-subst : δ Π1_subst ≡ δ Π1
        δ-Π1-subst = subst-preserves-δ succ-eq Π1_subst_step1
                    ∙ subst-preserves-δ-ctx ctx-eq-l Π1_subst_raw
                    ∙ δ-Π1-subst-raw

        -- Make well-formed for Mix
        Π1_subst_mwf = makeWellFormed Π1_subst
        wfp1_subst = makeWellFormed-WellFormed Π1_subst

        -- Height and δ of makeWellFormed version
        h-Π1-subst-mwf : height Π1_subst_mwf ≡ height Π1
        h-Π1-subst-mwf = height-makeWellFormed Π1_subst ∙ h-Π1-subst
        δ-Π1-subst-mwf : δ Π1_subst_mwf ≡ δ Π1
        δ-Π1-subst-mwf = δ-makeWellFormed Π1_subst ∙ δ-Π1-subst

        -- ================================================================
        -- CROSS-CUT 1: Mix Π1_subst_mwf with (□⊢ Π1') on A — height decrease left
        -- ================================================================
        h-dec-1-raw : height Π1_subst_mwf < height (⊢□ ext freshΓ_sub freshΔ_sub Π1)
        h-dec-1-raw = subst (_< height (⊢□ ext freshΓ_sub freshΔ_sub Π1)) (sym h-Π1-subst-mwf) (height-subproof-1 Π1)
        h-dec-1 = mixHeight-dec-l (⊢□ ext freshΓ_sub freshΔ_sub Π1) Π1_subst_mwf (□⊢ Π1') h-dec-1-raw
        acc1 = accR _ (inr (refl , h-dec-1))
        res1-pair = Mix {Γ = Γ_sub} {Δ = [ B ^ (r ∘ t_r) ] ,, Δ_sub} degEq Π1_subst_mwf (□⊢ Π1') wfp1_subst wfp' acc1
        res1 = fst res1-pair
        d-res1 = snd res1-pair
        -- res1 : Γ_sub ,, ((Γ'₁ ,, [(□ B')^r']) - A) ⊢ ([B^(r∘t_r)] ,, Δ_sub) - A ,, Δ'₁

        -- Simplify res1 antecedent: (Γ'₁ ,, [(□ B')^r']) - A = Γ'₁-A
        ant-simp-1 : (Γ'₁ ,, [ (□ B') ^ r' ]) - (A ^ s) ≡ Γ'₁-A
        ant-simp-1 = lemma-removeAll-cons-eq {A = A ^ s} {B = (□ B') ^ r'} {Γ = Γ'₁} eq2

        -- Simplify res1 succedent: ([B^(r∘t_r)] ,, Δ_sub) - A = [B^(r∘t_r)] ,, Δ_sub-A
        succ-simp-1 : ([ B ^ (r ∘ t_r) ] ,, Δ_sub) - (A ^ s) ≡ [ B ^ (r ∘ t_r) ] ,, Δ_sub-A
        succ-simp-1 = removeAll-prepend-pf-neq (λ eq → B-neq-A (sym eq))

        res1-cast : Γ_sub ,, Γ'₁-A ⊢ ([ B ^ (r ∘ t_r) ] ,, Δ_sub-A) ,, Δ'₁
        res1-cast = subst2 (λ G D → Γ_sub ,, G ⊢ D ,, Δ'₁) ant-simp-1 succ-simp-1 res1

        -- ================================================================
        -- CROSS-CUT 2: Mix (⊢□ ... Π1) with Π1' on A — height decrease right
        -- ================================================================
        h-dec-2 = mixHeight-dec-r (⊢□ ext freshΓ_sub freshΔ_sub Π1) (□⊢ Π1') Π1' (height-subproof-1 Π1')
        acc2 = accR _ (inr (refl , h-dec-2))
        res2-pair = Mix {Γ' = Γ'₁ ,, [ B' ^ (r' ∘ t_r) ]} {Δ' = Δ'₁} degEq (⊢□ ext freshΓ_sub freshΔ_sub Π1) Π1' wfp wfp' acc2
        res2 = fst res2-pair
        d-res2 = snd res2-pair
        -- res2 : Γ_sub ,, ((Γ'₁ ,, [B'^(r'∘t_r)]) - A) ⊢ ([(□ B)^r] ,, Δ_sub) - A ,, Δ'₁

        -- Simplify res2 succedent: ([(□ B)^r] ,, Δ_sub) - A = Δ_sub-A
        succ-simp-2 : ([ (□ B) ^ r ] ,, Δ_sub) - (A ^ s) ≡ Δ_sub-A
        succ-simp-2 = lemma-removeAll-head-eq {A = A ^ s} {B = (□ B) ^ r} {Γ = Δ_sub} eq1
        res2-succ : Γ_sub ,, ((Γ'₁ ,, [ B' ^ (r' ∘ t_r) ]) - (A ^ s)) ⊢ Δ_sub-A ,, Δ'₁
        res2-succ = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ B' ^ (r' ∘ t_r) ]) - (A ^ s)) ⊢ D ,, Δ'₁) succ-simp-2 res2

        -- Simplify res2 antecedent: (Γ'₁ ,, [B'^(r'∘t_r)]) - A = Γ'₁-A ,, [B'^(r'∘t_r)]
        B'-neq-A : (B' ^ (r' ∘ t_r)) ≢ (A ^ s)
        B'-neq-A eq = subformula-neq-□ {B = B'} {s = r' ∘ t_r} {t = s}
                      (subst (λ X → B' ^ (r' ∘ t_r) ≡ X ^ s) (cong PFormula.form eq2) eq)
        ant-simp-2 : (Γ'₁ ,, [ B' ^ (r' ∘ t_r) ]) - (A ^ s) ≡ Γ'₁-A ,, [ B' ^ (r' ∘ t_r) ]
        ant-simp-2 = removeAll-++-r-pf-neq (λ eq → B'-neq-A (sym eq))

        -- Cast B'^(r'∘t_r) to B^(r∘t_r)
        res2-ant-cast : Γ_sub ,, (Γ'₁-A ,, [ B ^ (r ∘ t_r) ]) ⊢ Δ_sub-A ,, Δ'₁
        res2-ant-cast = subst (λ pf → Γ_sub ,, (Γ'₁-A ,, [ pf ]) ⊢ Δ_sub-A ,, Δ'₁)
                              (sym Brt-eq-B'r't)
                              (subst (λ G → Γ_sub ,, G ⊢ Δ_sub-A ,, Δ'₁) ant-simp-2 res2-succ)

        -- Reassociate antecedent
        ant-assoc : Γ_sub ,, (Γ'₁-A ,, [ B ^ (r ∘ t_r) ]) ≡ (Γ_sub ,, Γ'₁-A) ,, [ B ^ (r ∘ t_r) ]
        ant-assoc = sym (++-assoc Γ_sub Γ'₁-A [ B ^ (r ∘ t_r) ])
        res2-cast : (Γ_sub ,, Γ'₁-A) ,, [ B ^ (r ∘ t_r) ] ⊢ Δ_sub-A ,, Δ'₁
        res2-cast = subst (_⊢ Δ_sub-A ,, Δ'₁) ant-assoc res2-ant-cast

        -- ================================================================
        -- FINAL MIX ON B^(r∘t_r): degree decrease
        -- res1-cast : Γ_sub ,, Γ'₁-A ⊢ [B^(r∘t_r)] ,, Δ_sub-A ,, Δ'₁
        -- res2-cast : (Γ_sub ,, Γ'₁-A) ,, [B^(r∘t_r)] ⊢ Δ_sub-A ,, Δ'₁
        -- ================================================================
        res1-wf = makeWellFormed res1-cast
        res2-wf = makeWellFormed res2-cast
        acc3 = accR (degree B , mixHeight res1-wf res2-wf) (inl degB-lt-n)
        mix3-pair = Mix {n = degree B} {A = B} {s = r ∘ t_r} refl
                       res1-wf res2-wf
                       (makeWellFormed-WellFormed res1-cast) (makeWellFormed-WellFormed res2-cast) acc3
        mix3 = fst mix3-pair
        d-mix3 = snd mix3-pair

        -- ================================================================
        -- STRUCTURAL CONTRACTION
        -- Goal ant: Γ_sub ,, Γ'₁-A
        -- Goal succ: Δ_sub-A ,, Δ'₁
        -- ================================================================
        sub-ant = subset-concat {G = Γ_sub ,, Γ'₁-A}
          (λ y yIn → yIn)
          (removeAll-append-singleton-⊆ (Γ_sub ,, Γ'₁-A) (B ^ (r ∘ t_r)))

        sub-succ = subset-concat {G = Δ_sub-A ,, Δ'₁}
          (removeAll-drop-singleton-r [] (Δ_sub-A ,, Δ'₁) (B ^ (r ∘ t_r)))
          (λ y yIn → yIn)

        p_struct = structural sub-ant sub-succ mix3

        -- TRANSPORT TO FULL GOAL TYPE
        p_ctx : GoalCtx ⊢ Δ_sub-A ,, Δ'₁
        p_ctx = subst (λ G → Γ_sub ,, G ⊢ Δ_sub-A ,, Δ'₁) (sym ant-simp-1) p_struct
        p' : GoalType
        p' = subst (GoalCtx ⊢_) (cong (_,, Δ'₁) (sym succ-simp-2)) p_ctx

        -- ================================================================
        -- DEGREE BOUND
        -- ================================================================
        -- res1 bound: δ res1-wf ≤ GoalBound
        δ-res1-cast-eq : δ res1-cast ≡ δ res1
        δ-res1-cast-eq = subst2-preserves-δ (Γ_sub ,,_) (_,, Δ'₁) ant-simp-1 succ-simp-1 res1
        δ-res1-wf-eq : δ res1-wf ≡ δ res1
        δ-res1-wf-eq = trans (δ-makeWellFormed res1-cast) δ-res1-cast-eq
        res1-intermediate : max (δ Π1_subst_mwf) (δ (□⊢ Π1')) ≤ GoalBound
        res1-intermediate = max-least
          (subst (_≤ GoalBound) (sym δ-Π1-subst-mwf) (left-≤-max {δ (⊢□ ext freshΓ_sub freshΔ_sub Π1)} {δ (□⊢ Π1')}))
          (right-≤-max {δ (□⊢ Π1')} {δ (⊢□ ext freshΓ_sub freshΔ_sub Π1)})
        res1-bound : δ res1-wf ≤ GoalBound
        res1-bound = subst (_≤ GoalBound) (sym δ-res1-wf-eq) (≤-trans d-res1 res1-intermediate)

        -- res2 bound: δ res2-wf ≤ GoalBound
        δ-res2-succ-eq : δ res2-succ ≡ δ res2
        δ-res2-succ-eq = subst-preserves-δ (cong (_,, Δ'₁) succ-simp-2) res2
        δ-res2-ant-eq : δ res2-ant-cast ≡ δ res2
        δ-res2-ant-eq = trans
          (subst-preserves-δ-ctx (cong (λ pf → Γ_sub ,, (Γ'₁-A ,, [ pf ])) (sym Brt-eq-B'r't))
            (subst (λ G → Γ_sub ,, G ⊢ Δ_sub-A ,, Δ'₁) ant-simp-2 res2-succ))
          (trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) ant-simp-2) res2-succ) δ-res2-succ-eq)
        δ-res2-cast-eq : δ res2-cast ≡ δ res2
        δ-res2-cast-eq = trans (subst-preserves-δ-ctx ant-assoc res2-ant-cast) δ-res2-ant-eq
        δ-res2-wf-eq : δ res2-wf ≡ δ res2
        δ-res2-wf-eq = trans (δ-makeWellFormed res2-cast) δ-res2-cast-eq
        res2-bound : δ res2-wf ≤ GoalBound
        res2-bound = subst (_≤ GoalBound) (sym δ-res2-wf-eq) d-res2

        max-res-bound : max (δ res1-wf) (δ res2-wf) ≤ GoalBound
        max-res-bound = max-least res1-bound res2-bound
        mix3-bound : δ mix3 ≤ GoalBound
        mix3-bound = ≤-trans d-mix3 max-res-bound

        δ-p-struct : δ p_struct ≡ δ mix3
        δ-p-struct = structural-preserves-δ sub-ant sub-succ mix3
        δ-p-ctx : δ p_ctx ≡ δ p_struct
        δ-p-ctx = subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-simp-1)) p_struct
        δ-p' : δ p' ≡ δ p_ctx
        δ-p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-simp-2)) p_ctx
        d_final : δ p' ≤ GoalBound
        d_final = subst (_≤ GoalBound) (sym (δ-p' ∙ δ-p-ctx ∙ δ-p-struct)) mix3-bound
      in (p' , d_final)

-- =============================================================================
-- Principal Case 8: ⊢♢ vs ♢⊢
-- =============================================================================
-- Left: ⊢♢ Π1 : Γ_sub ⊢ [ (♢ B) ^ r ] ,, Δ_sub
--   where Π1 : Γ_sub ⊢ [ B ^ (r ∘ t_l) ] ,, Δ_sub
-- Right: ♢⊢ ext freshΓ' freshΔ' Π1' : Γ'₁ ,, [ (♢ B') ^ r' ] ⊢ Δ'₁
--   where Π1' : Γ'₁ ,, [ B' ^ insertToken x r' ] ⊢ Δ'₁
Mix {n = n} {Γ = Γ_sub} {Δ = .([ (♢ B) ^ r ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (♢ B') ^ r' ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢♢ {.Γ_sub} {B} {r} {t_l} {Δ_sub} Π1) (♢⊢ {x} {r'} {Γ'₁} {Δ'₁} {B'} ext freshΓ' freshΔ' Π1') wfp wfp' (acc accRec) =
    handleDiaCase accRec (discretePFormula (A ^ s) ((♢ B) ^ r)) (discretePFormula (A ^ s) ((♢ B') ^ r'))
  where
    GoalCtx = Γ_sub ,, ((Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s))
    GoalSucc = (([ (♢ B) ^ r ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
    GoalType = GoalCtx ⊢ GoalSucc
    GoalBound = max (δ (⊢♢ Π1)) (δ (♢⊢ ext freshΓ' freshΔ' Π1'))
    Result = Σ GoalType (λ p → δ p ≤ GoalBound)

    handleDiaCase : (∀ m' → m' <Lex (n , mixHeight (⊢♢ Π1) (♢⊢ ext freshΓ' freshΔ' Π1')) → Acc _<Lex_ m')
                  → Dec ((A ^ s) ≡ ((♢ B) ^ r)) → Dec ((A ^ s) ≡ ((♢ B') ^ r')) → Result
    -- Non-principal cases (to be handled by catch-all)
    handleDiaCase accR (no neq1) _ =
      let h-dec = mixHeight-dec-l (⊢♢ Π1) Π1 (♢⊢ ext freshΓ' freshΔ' Π1') (height-subproof-1 Π1)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ = Γ_sub} {Δ = [ B ^ (r ∘ t_l) ] ,, Δ_sub} degEq Π1 (♢⊢ ext freshΓ' freshΔ' Π1') wfp wfp' acc'
          Γ'-rem = (Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s)
          Δ_sub-rem = Δ_sub - (A ^ s)
          sub_delta : ((([ B ^ (r ∘ t_l) ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁) ⊆ ([ B ^ (r ∘ t_l) ] ,, (Δ_sub-rem ,, Δ'₁))
          sub_delta = solve (rem (elm 0 ++ₑ var 0) 1 ++ₑ var 1) (elm 0 ++ₑ (rem (var 0) 1 ++ₑ var 1)) ((Δ_sub ∷ Δ'₁ ∷ []) , (B ^ (r ∘ t_l) ∷ A ^ s ∷ [])) {refl}
          mix_r = structural subset-refl sub_delta mix
          p_dia = ⊢♢ {Γ_sub ,, Γ'-rem} {B} {r} {t_l} {Δ_sub-rem ,, Δ'₁} mix_r
          sub_right : ([ (♢ B) ^ r ] ,, (Δ_sub-rem ,, Δ'₁)) ⊆ (([ (♢ B) ^ r ] ,, Δ_sub-rem) ,, Δ'₁)
          sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((elm 0 ++ₑ var 0) ++ₑ var 1) ((Δ_sub-rem ∷ Δ'₁ ∷ []) , ((♢ B) ^ r ∷ [])) {refl}
          p_reorder = structural subset-refl sub_right p_dia
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (♢ B) ^ r} {Γ = Δ_sub} neq1
          p' : GoalType
          p' = subst (λ D → GoalCtx ⊢ D ,, Δ'₁) (sym succ-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_reorder)
                 (trans (structural-preserves-δ subset-refl sub_right p_dia) (structural-preserves-δ subset-refl sub_delta mix))
          d_final : δ p' ≤ GoalBound
          d_final = subst (_≤ GoalBound) (sym d_p') dmix
      in (p' , d_final)
    handleDiaCase accR (yes eq1) (no neq2) =
      let
        -- Abbreviations
        Γ'₁-A = Γ'₁ - (A ^ s)

        -- Combined contexts for freshness (antecedent + succedent of ♢⊢ application)
        combined = (Γ_sub ,, Γ'₁-A) ,, GoalSucc

        -- ================================================================
        -- EIGENPOSITION RENAMING: x → x' in Π1'
        -- Converts B'^(insertToken x r') to B'^t' (then to B'^(insertToken x' r'))
        -- ================================================================
        x' : Token
        x' = freshTokenForRename r' combined Π1'

        -- Well-formedness of right proof
        wf-Π1' : maxEigenposToken Π1' < x
        wf-Π1' = fst wfp'
        wfp-sub' : WellFormedProof Π1'
        wfp-sub' = snd wfp'

        -- Properties of x'
        x'-fresh-combined : TokenFresh x' combined
        x'-fresh-combined = freshTokenForRename-fresh r' combined Π1'
        x'-eigenpos : maxEigenposToken Π1' < x'
        x'-eigenpos = freshTokenForRename-eigenpos r' combined Π1'
        x'∉r' : x' ∉Pos r'
        x'∉r' = freshTokenForRename-∉r r' combined Π1'

        -- Eigenposition structures
        eigent : Position
        eigent = insertToken x r'

        t' : Position
        t' = substPos x (singleton-pos x') eigent

        extSTE : IsSingleTokenExt r' eigent x
        extSTE = mkSingleTokenExt r' x ext

        -- Rename eigenposition in Π1'
        rename-result = renameEigenpos-♢⊢-premise-gen {r = r'} {t = eigent} {x = x} {Γ = Γ'₁} {Δ = Δ'₁} {A = B'} Π1' extSTE freshΓ' freshΔ' wf-Π1' x' x'-eigenpos x'∉r'
        Π1'-renamed : Γ'₁ ,, [ B' ^ t' ] ⊢ Δ'₁
        Π1'-renamed = fst rename-result
        ext' : IsSingleTokenExt r' t' x'
        ext' = snd rename-result

        -- Degree/height preservation
        δ-eq-renamed : δ Π1'-renamed ≡ δ Π1'
        δ-eq-renamed = δ-renameEigenpos-♢⊢-premise-gen Π1' extSTE freshΓ' freshΔ' wf-Π1' x' x'-eigenpos x'∉r'
        height-eq-renamed : height Π1'-renamed ≡ height Π1'
        height-eq-renamed = height-renameEigenpos-♢⊢-premise-gen Π1' extSTE freshΓ' freshΔ' wf-Π1' x' x'-eigenpos x'∉r'

        wfp-renamed : WellFormedProof Π1'-renamed
        wfp-renamed = WellFormed-renameEigenpos-♢⊢-premise-gen Π1' extSTE freshΓ' freshΔ' wf-Π1' x' x'-eigenpos x'∉r' wfp-sub'

        -- ================================================================
        -- HEIGHT DECREASE: mixHeight (⊢♢ Π1) Π1'-renamed < mixHeight (⊢♢ Π1) (♢⊢ ... Π1')
        -- ================================================================
        h-dec-raw = mixHeight-dec-r (⊢♢ Π1) (♢⊢ ext freshΓ' freshΔ' Π1') Π1' (height-subproof-1 Π1')
        mixHeight-eq = cong (height (⊢♢ Π1) +_) height-eq-renamed
        h-dec = subst (_< mixHeight (⊢♢ Π1) (♢⊢ ext freshΓ' freshΔ' Π1')) (sym mixHeight-eq) h-dec-raw
        acc' = accR _ (inr (refl , h-dec))

        -- ================================================================
        -- MIX: (⊢♢ Π1) with Π1'-renamed
        -- ================================================================
        (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ t' ]} {Δ' = Δ'₁} degEq (⊢♢ Π1) Π1'-renamed wfp wfp-renamed acc'
        -- mix : Γ_sub ,, ((Γ'₁ ,, [B'^t']) - (A^s)) ⊢ GoalSucc

        -- ================================================================
        -- REORDER ANTECEDENT: move [B'^t'] to end
        -- ================================================================
        sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ t' ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ t' ])
        sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ t' ∷ A ^ s ∷ [])) {refl}

        mix_r = structural sub_left subset-refl mix
        -- mix_r : (Γ_sub ,, Γ'₁-A) ,, [B'^t'] ⊢ GoalSucc

        -- ================================================================
        -- TRANSPORT t' → insertToken x' r'
        -- ================================================================
        t'-eq : t' ≡ insertToken x' r'
        t'-eq = substPos-insertToken-eq x x' r' ext

        mix_transported : (Γ_sub ,, Γ'₁-A) ,, [ B' ^ insertToken x' r' ] ⊢ GoalSucc
        mix_transported = subst (λ (p : Position) → (Γ_sub ,, Γ'₁-A) ,, [ B' ^ p ] ⊢ GoalSucc) t'-eq mix_r

        -- ================================================================
        -- FRESHNESS for ♢⊢ application
        -- ================================================================
        fresh-split = TokenFresh-split (Γ_sub ,, Γ'₁-A) GoalSucc x' x'-fresh-combined
        freshΓ_new : TokenFresh x' (Γ_sub ,, Γ'₁-A)
        freshΓ_new = fst fresh-split
        freshΔ_new : TokenFresh x' GoalSucc
        freshΔ_new = snd fresh-split

        -- ================================================================
        -- APPLY ♢⊢ with x'
        -- ================================================================
        p_dia = ♢⊢ {x'} {r'} {Γ_sub ,, Γ'₁-A} {GoalSucc} {B'} x'∉r' freshΓ_new freshΔ_new mix_transported
        -- p_dia : (Γ_sub ,, Γ'₁-A) ,, [(♢B')^r'] ⊢ GoalSucc

        -- ================================================================
        -- REORDER: (Γ_sub ,, Γ'₁-A) ,, [(♢B')^r'] → Γ_sub ,, (Γ'₁-A ,, [(♢B')^r'])
        -- ================================================================
        sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (♢ B') ^ r' ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (♢ B') ^ r' ]))
        sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((♢ B') ^ r' ∷ [])) {refl}

        p_reorder = structural sub_left2 subset-refl p_dia

        -- ================================================================
        -- TRANSPORT antecedent: Γ'₁-A ,, [(♢B')^r'] = (Γ'₁ ,, [(♢B')^r']) - (A^s)
        -- ================================================================
        ant-eq : (Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s) ≡ Γ'₁-A ,, [ (♢ B') ^ r' ]
        ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (♢ B') ^ r'} {Γ = Γ'₁} neq2

        p' : GoalType
        p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder

        -- ================================================================
        -- DEGREE BOUND
        -- ================================================================
        d_step1 : δ p' ≡ δ p_reorder
        d_step1 = subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder
        d_step2 : δ p_reorder ≡ δ p_dia
        d_step2 = structural-preserves-δ sub_left2 subset-refl p_dia
        d_step3 : δ p_dia ≡ δ mix_transported
        d_step3 = refl
        d_step4 : δ mix_transported ≡ δ mix_r
        d_step4 = subst-preserves-δ-ctx (cong {A = Position} (λ (p : Position) → (Γ_sub ,, Γ'₁-A) ,, [ B' ^ p ]) t'-eq) mix_r
        d_step5 : δ mix_r ≡ δ mix
        d_step5 = structural-preserves-δ sub_left subset-refl mix

        d_p' : δ p' ≡ δ mix
        d_p' = d_step1 ∙ d_step2 ∙ d_step3 ∙ d_step4 ∙ d_step5

        bound-eq : max (δ (⊢♢ Π1)) (δ Π1'-renamed) ≡ GoalBound
        bound-eq = cong (λ k → max (δ (⊢♢ Π1)) k) δ-eq-renamed
        dmix' : δ mix ≤ GoalBound
        dmix' = subst (δ mix ≤_) bound-eq dmix

        d_final : δ p' ≤ GoalBound
        d_final = subst (_≤ GoalBound) (sym d_p') dmix'
      in (p' , d_final)
    -- Principal: A = (♢B)^r AND A = (♢B')^r'
    handleDiaCase accR (yes eq1) (yes eq2) =
      let
        -- Formula equalities
        ♢B-eq-♢B' : (♢ B) ^ r ≡ (♢ B') ^ r'
        ♢B-eq-♢B' = sym eq1 ∙ eq2
        B-eq-B' : B ≡ B'
        B-eq-B' = ♢-inj (cong PFormula.form ♢B-eq-♢B')
        r-eq-r' : r ≡ r'
        r-eq-r' = cong PFormula.pos ♢B-eq-♢B'
        Brt-eq-B'r't : B ^ (r ∘ t_l) ≡ B' ^ (r' ∘ t_l)
        Brt-eq-B'r't = cong₂ _^_ B-eq-B' (cong (_∘ t_l) r-eq-r')

        -- Degree decrease: degree B < n
        degA-eq : degree A ≡ suc (degree B)
        degA-eq = cong degree (cong PFormula.form eq1)
        degB-lt-n : degree B < n
        degB-lt-n = subst (degree B <_) (sym degA-eq ∙ degEq) (degree-♢ B)

        -- B^(r∘t_l) ≠ A^s (subformula inequality)
        B-neq-A : (B ^ (r ∘ t_l)) ≢ (A ^ s)
        B-neq-A eq = subformula-neq-♢ {B = B} {s = r ∘ t_l} {t = s}
                     (subst (λ X → B ^ (r ∘ t_l) ≡ X ^ s) (cong PFormula.form eq1) eq)

        -- Abbreviations
        Γ'₁-A = Γ'₁ - (A ^ s)
        Δ_sub-A = Δ_sub - (A ^ s)

        -- ================================================================
        -- EIGENPOSITION SUBSTITUTION: x → t_l in Π1' (RIGHT proof)
        -- Converts B'^(insertToken x r') to B'^(r' ∘ t_l)
        -- ================================================================
        subst-result = substEigenposInProof x t_l Π1' (fst wfp')
        Π1'_subst_raw = fst subst-result
        h-Π1'-subst-raw = fst (snd subst-result)
        δ-Π1'-subst-raw = snd (snd subst-result)

        -- Transport to correct types (two steps)
        -- Antecedent: substCtx x t_l (Γ'₁ ,, [B'^insertToken x r']) = Γ'₁ ,, [B'^(r'∘t_l)]
        ant-eq : substCtx x t_l (Γ'₁ ,, [ B' ^ insertToken x r' ]) ≡ Γ'₁ ,, [ B' ^ (r' ∘ t_l) ]
        ant-eq = substCtx-++ x t_l Γ'₁ [ B' ^ insertToken x r' ]
               ∙ cong₂ _,,_ (substCtx-id x t_l Γ'₁ freshΓ')
                             (cong [_] (cong (B' ^_) (substPos-insertToken-gen x t_l r' ext)))
        -- Succedent: substCtx x t_l Δ'₁ = Δ'₁
        succ-eq-raw : substCtx x t_l Δ'₁ ≡ Δ'₁
        succ-eq-raw = substCtx-id x t_l Δ'₁ freshΔ'

        Π1'_subst_step1 = subst (_⊢ substCtx x t_l Δ'₁) ant-eq Π1'_subst_raw
        Π1'_subst = subst (Γ'₁ ,, [ B' ^ (r' ∘ t_l) ] ⊢_) succ-eq-raw Π1'_subst_step1
        -- Π1'_subst : Γ'₁ ,, [ B' ^ (r' ∘ t_l) ] ⊢ Δ'₁

        -- Height preservation chain
        h-Π1'-subst : height Π1'_subst ≡ height Π1'
        h-Π1'-subst = height-subst-Δ succ-eq-raw Π1'_subst_step1
                     ∙ height-subst-Γ ant-eq Π1'_subst_raw
                     ∙ h-Π1'-subst-raw

        -- δ preservation chain
        δ-Π1'-subst : δ Π1'_subst ≡ δ Π1'
        δ-Π1'-subst = subst-preserves-δ succ-eq-raw Π1'_subst_step1
                     ∙ subst-preserves-δ-ctx ant-eq Π1'_subst_raw
                     ∙ δ-Π1'-subst-raw

        -- Make well-formed for Mix
        Π1'_subst_mwf = makeWellFormed Π1'_subst
        wfp1'_subst = makeWellFormed-WellFormed Π1'_subst

        -- Height and δ of makeWellFormed version
        h-Π1'-subst-mwf : height Π1'_subst_mwf ≡ height Π1'
        h-Π1'-subst-mwf = height-makeWellFormed Π1'_subst ∙ h-Π1'-subst
        δ-Π1'-subst-mwf : δ Π1'_subst_mwf ≡ δ Π1'
        δ-Π1'-subst-mwf = δ-makeWellFormed Π1'_subst ∙ δ-Π1'-subst

        -- ================================================================
        -- CROSS-CUT 1: Mix Π1 with (♢⊢ ext ... Π1') on A — height decrease left
        -- ================================================================
        h-dec-1 = mixHeight-dec-l (⊢♢ Π1) Π1 (♢⊢ ext freshΓ' freshΔ' Π1') (height-subproof-1 Π1)
        acc1 = accR _ (inr (refl , h-dec-1))
        res1-pair = Mix {Γ = Γ_sub} {Δ = [ B ^ (r ∘ t_l) ] ,, Δ_sub} degEq Π1 (♢⊢ ext freshΓ' freshΔ' Π1') wfp wfp' acc1
        res1 = fst res1-pair
        d-res1 = snd res1-pair
        -- res1 : Γ_sub ,, ((Γ'₁ ,, [(♢ B')^r']) - A) ⊢ ([B^(r∘t_l)] ,, Δ_sub) - A ,, Δ'₁

        -- Simplify res1 antecedent: (Γ'₁ ,, [(♢ B')^r']) - A = Γ'₁-A
        ant-simp-1 : (Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s) ≡ Γ'₁-A
        ant-simp-1 = lemma-removeAll-cons-eq {A = A ^ s} {B = (♢ B') ^ r'} {Γ = Γ'₁} eq2

        -- Simplify res1 succedent: ([B^(r∘t_l)] ,, Δ_sub) - A = [B^(r∘t_l)] ,, Δ_sub-A
        succ-simp-1 : ([ B ^ (r ∘ t_l) ] ,, Δ_sub) - (A ^ s) ≡ [ B ^ (r ∘ t_l) ] ,, Δ_sub-A
        succ-simp-1 = removeAll-prepend-pf-neq (λ eq → B-neq-A (sym eq))

        res1-cast : Γ_sub ,, Γ'₁-A ⊢ ([ B ^ (r ∘ t_l) ] ,, Δ_sub-A) ,, Δ'₁
        res1-cast = subst2 (λ G D → Γ_sub ,, G ⊢ D ,, Δ'₁) ant-simp-1 succ-simp-1 res1

        -- ================================================================
        -- CROSS-CUT 2: Mix (⊢♢ Π1) with Π1'_subst_mwf on A — height decrease right
        -- ================================================================
        h-dec-2-raw : height Π1'_subst_mwf < height (♢⊢ ext freshΓ' freshΔ' Π1')
        h-dec-2-raw = subst (_< height (♢⊢ ext freshΓ' freshΔ' Π1')) (sym h-Π1'-subst-mwf) (height-subproof-1 Π1')
        h-dec-2 = mixHeight-dec-r (⊢♢ Π1) (♢⊢ ext freshΓ' freshΔ' Π1') Π1'_subst_mwf h-dec-2-raw
        acc2 = accR _ (inr (refl , h-dec-2))
        res2-pair = Mix {Γ' = Γ'₁ ,, [ B' ^ (r' ∘ t_l) ]} {Δ' = Δ'₁} degEq (⊢♢ Π1) Π1'_subst_mwf wfp wfp1'_subst acc2
        res2 = fst res2-pair
        d-res2 = snd res2-pair
        -- res2 : Γ_sub ,, ((Γ'₁ ,, [B'^(r'∘t_l)]) - A) ⊢ ([(♢ B)^r] ,, Δ_sub) - A ,, Δ'₁

        -- Simplify res2 succedent: ([(♢ B)^r] ,, Δ_sub) - A = Δ_sub-A
        succ-simp-2 : ([ (♢ B) ^ r ] ,, Δ_sub) - (A ^ s) ≡ Δ_sub-A
        succ-simp-2 = lemma-removeAll-head-eq {A = A ^ s} {B = (♢ B) ^ r} {Γ = Δ_sub} eq1
        res2-succ : Γ_sub ,, ((Γ'₁ ,, [ B' ^ (r' ∘ t_l) ]) - (A ^ s)) ⊢ Δ_sub-A ,, Δ'₁
        res2-succ = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ B' ^ (r' ∘ t_l) ]) - (A ^ s)) ⊢ D ,, Δ'₁) succ-simp-2 res2

        -- Simplify res2 antecedent: (Γ'₁ ,, [B'^(r'∘t_l)]) - A = Γ'₁-A ,, [B'^(r'∘t_l)]
        B'-neq-A : (B' ^ (r' ∘ t_l)) ≢ (A ^ s)
        B'-neq-A eq = subformula-neq-♢ {B = B'} {s = r' ∘ t_l} {t = s}
                      (subst (λ X → B' ^ (r' ∘ t_l) ≡ X ^ s) (cong PFormula.form eq2) eq)
        ant-simp-2 : (Γ'₁ ,, [ B' ^ (r' ∘ t_l) ]) - (A ^ s) ≡ Γ'₁-A ,, [ B' ^ (r' ∘ t_l) ]
        ant-simp-2 = removeAll-++-r-pf-neq (λ eq → B'-neq-A (sym eq))

        -- Cast B'^(r'∘t_l) to B^(r∘t_l)
        res2-ant-cast : Γ_sub ,, (Γ'₁-A ,, [ B ^ (r ∘ t_l) ]) ⊢ Δ_sub-A ,, Δ'₁
        res2-ant-cast = subst (λ pf → Γ_sub ,, (Γ'₁-A ,, [ pf ]) ⊢ Δ_sub-A ,, Δ'₁)
                              (sym Brt-eq-B'r't)
                              (subst (λ G → Γ_sub ,, G ⊢ Δ_sub-A ,, Δ'₁) ant-simp-2 res2-succ)

        -- Reassociate antecedent
        ant-assoc : Γ_sub ,, (Γ'₁-A ,, [ B ^ (r ∘ t_l) ]) ≡ (Γ_sub ,, Γ'₁-A) ,, [ B ^ (r ∘ t_l) ]
        ant-assoc = sym (++-assoc Γ_sub Γ'₁-A [ B ^ (r ∘ t_l) ])
        res2-cast : (Γ_sub ,, Γ'₁-A) ,, [ B ^ (r ∘ t_l) ] ⊢ Δ_sub-A ,, Δ'₁
        res2-cast = subst (_⊢ Δ_sub-A ,, Δ'₁) ant-assoc res2-ant-cast

        -- ================================================================
        -- FINAL MIX ON B^(r∘t_l): degree decrease
        -- res1-cast : Γ_sub ,, Γ'₁-A ⊢ [B^(r∘t_l)] ,, Δ_sub-A ,, Δ'₁
        -- res2-cast : (Γ_sub ,, Γ'₁-A) ,, [B^(r∘t_l)] ⊢ Δ_sub-A ,, Δ'₁
        -- ================================================================
        res1-wf = makeWellFormed res1-cast
        res2-wf = makeWellFormed res2-cast
        acc3 = accR (degree B , mixHeight res1-wf res2-wf) (inl degB-lt-n)
        mix3-pair = Mix {n = degree B} {A = B} {s = r ∘ t_l} refl
                       res1-wf res2-wf
                       (makeWellFormed-WellFormed res1-cast) (makeWellFormed-WellFormed res2-cast) acc3
        mix3 = fst mix3-pair
        d-mix3 = snd mix3-pair

        -- ================================================================
        -- STRUCTURAL CONTRACTION
        -- Goal ant: Γ_sub ,, Γ'₁-A
        -- Goal succ: Δ_sub-A ,, Δ'₁
        -- ================================================================
        sub-ant = subset-concat {G = Γ_sub ,, Γ'₁-A}
          (λ y yIn → yIn)
          (removeAll-append-singleton-⊆ (Γ_sub ,, Γ'₁-A) (B ^ (r ∘ t_l)))

        sub-succ = subset-concat {G = Δ_sub-A ,, Δ'₁}
          (removeAll-drop-singleton-r [] (Δ_sub-A ,, Δ'₁) (B ^ (r ∘ t_l)))
          (λ y yIn → yIn)

        p_struct = structural sub-ant sub-succ mix3

        -- TRANSPORT TO FULL GOAL TYPE
        p_ctx : GoalCtx ⊢ Δ_sub-A ,, Δ'₁
        p_ctx = subst (λ G → Γ_sub ,, G ⊢ Δ_sub-A ,, Δ'₁) (sym ant-simp-1) p_struct
        p' : GoalType
        p' = subst (GoalCtx ⊢_) (cong (_,, Δ'₁) (sym succ-simp-2)) p_ctx

        -- ================================================================
        -- DEGREE BOUND
        -- ================================================================
        -- res1 bound: δ res1-wf ≤ GoalBound (d-res1 ≤ GoalBound definitionally)
        δ-res1-cast-eq : δ res1-cast ≡ δ res1
        δ-res1-cast-eq = subst2-preserves-δ (Γ_sub ,,_) (_,, Δ'₁) ant-simp-1 succ-simp-1 res1
        δ-res1-wf-eq : δ res1-wf ≡ δ res1
        δ-res1-wf-eq = trans (δ-makeWellFormed res1-cast) δ-res1-cast-eq
        res1-bound : δ res1-wf ≤ GoalBound
        res1-bound = subst (_≤ GoalBound) (sym δ-res1-wf-eq) d-res1

        -- res2 bound: δ res2-wf ≤ GoalBound
        δ-res2-succ-eq : δ res2-succ ≡ δ res2
        δ-res2-succ-eq = subst-preserves-δ (cong (_,, Δ'₁) succ-simp-2) res2
        δ-res2-ant-eq : δ res2-ant-cast ≡ δ res2
        δ-res2-ant-eq = trans
          (subst-preserves-δ-ctx (cong (λ pf → Γ_sub ,, (Γ'₁-A ,, [ pf ])) (sym Brt-eq-B'r't))
            (subst (λ G → Γ_sub ,, G ⊢ Δ_sub-A ,, Δ'₁) ant-simp-2 res2-succ))
          (trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) ant-simp-2) res2-succ) δ-res2-succ-eq)
        δ-res2-cast-eq : δ res2-cast ≡ δ res2
        δ-res2-cast-eq = trans (subst-preserves-δ-ctx ant-assoc res2-ant-cast) δ-res2-ant-eq
        δ-res2-wf-eq : δ res2-wf ≡ δ res2
        δ-res2-wf-eq = trans (δ-makeWellFormed res2-cast) δ-res2-cast-eq
        res2-intermediate : max (δ (⊢♢ Π1)) (δ Π1'_subst_mwf) ≤ GoalBound
        res2-intermediate = max-least
          (left-≤-max {δ (⊢♢ Π1)} {δ (♢⊢ ext freshΓ' freshΔ' Π1')})
          (subst (_≤ GoalBound) (sym δ-Π1'-subst-mwf) (right-≤-max {δ (♢⊢ ext freshΓ' freshΔ' Π1')} {δ (⊢♢ Π1)}))
        res2-bound : δ res2-wf ≤ GoalBound
        res2-bound = subst (_≤ GoalBound) (sym δ-res2-wf-eq) (≤-trans d-res2 res2-intermediate)

        max-res-bound : max (δ res1-wf) (δ res2-wf) ≤ GoalBound
        max-res-bound = max-least res1-bound res2-bound
        mix3-bound : δ mix3 ≤ GoalBound
        mix3-bound = ≤-trans d-mix3 max-res-bound

        δ-p-struct : δ p_struct ≡ δ mix3
        δ-p-struct = structural-preserves-δ sub-ant sub-succ mix3
        δ-p-ctx : δ p_ctx ≡ δ p_struct
        δ-p-ctx = subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-simp-1)) p_struct
        δ-p' : δ p' ≡ δ p_ctx
        δ-p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-simp-2)) p_ctx
        d_final : δ p' ≤ GoalBound
        d_final = subst (_≤ GoalBound) (sym (δ-p' ∙ δ-p-ctx ∙ δ-p-struct)) mix3-bound
      in (p' , d_final)

-- =============================================================================
-- Catch-all: remaining non-principal cases
-- Left proof is right-intro, right proof is left-intro, non-matching pair
-- =============================================================================

-- Catch-all for left = ⊢¬

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (¬ B) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (B' ∧ C') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢¬ {.Γ_sub} {B} {t} {Δ_sub} Π_sub) Π'@(∧₁⊢ {Γ = Γ'₁} {A = B'} {s = r} {Δ = Δ'₁} {B = C'} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleNegAnd1 accRec (discretePFormula (A ^ s) ((¬ B) ^ t))
  where
    handleNegAnd1 : (∀ m' → m' <Lex (n , mixHeight (⊢¬ Π_sub) Π') → Acc _<Lex_ m')
                 → Dec ((A ^ s) ≡ ((¬ B) ^ t))
                 → Σ (Γ_sub ,, ((Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s)) ⊢ (([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
                     (λ p → δ p ≤ max (δ (⊢¬ Π_sub)) (δ (∧₁⊢ Π'_sub)))
    handleNegAnd1 accR (no neq) =
      let (p_no , d_no) = handleNegNoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (¬ B) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (¬ B) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢¬ Π_sub)) (δ (∧₁⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleNegAnd1 accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((B' ∧ C') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (¬ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec = mixHeight-dec-r (⊢¬ Π_sub) (∧₁⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢¬ Π_sub) Π'_sub wfp wfp'_s acc'
          Γ'₁-A = Γ'₁ - (A ^ s)
          GoalSucc = (([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
          sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          p_rule = ∧₁⊢ {Γ = Γ_sub ,, Γ'₁-A} {A = B'} {s = r} {Δ = GoalSucc} {B = C'} mix_r
          sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (B' ∧ C') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (B' ∧ C') ^ r ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((B' ∧ C') ^ r ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_rule
          ant-eq : (Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (B' ∧ C') ^ r ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (B' ∧ C') ^ r} {Γ = Γ'₁} neq_G
          p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
          d_final : δ p' ≤ max (δ (⊢¬ Π_sub)) (δ (∧₁⊢ Π'_sub))
          d_final = subst (_≤ max (δ (⊢¬ Π_sub)) (δ (∧₁⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (¬ B) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (C' ∧ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢¬ {.Γ_sub} {B} {t} {Δ_sub} Π_sub) Π'@(∧₂⊢ {Γ = Γ'₁} {B = B'} {s = r} {Δ = Δ'₁} {A = C'} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleNegAnd2 accRec (discretePFormula (A ^ s) ((¬ B) ^ t))
  where
    handleNegAnd2 : (∀ m' → m' <Lex (n , mixHeight (⊢¬ Π_sub) Π') → Acc _<Lex_ m')
                 → Dec ((A ^ s) ≡ ((¬ B) ^ t))
                 → Σ (Γ_sub ,, ((Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s)) ⊢ (([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
                     (λ p → δ p ≤ max (δ (⊢¬ Π_sub)) (δ (∧₂⊢ Π'_sub)))
    handleNegAnd2 accR (no neq) =
      let (p_no , d_no) = handleNegNoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (¬ B) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (¬ B) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢¬ Π_sub)) (δ (∧₂⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleNegAnd2 accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((C' ∧ B') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (¬ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec = mixHeight-dec-r (⊢¬ Π_sub) (∧₂⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢¬ Π_sub) Π'_sub wfp wfp'_s acc'
          Γ'₁-A = Γ'₁ - (A ^ s)
          GoalSucc = (([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
          sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          p_rule = ∧₂⊢ {Γ = Γ_sub ,, Γ'₁-A} {B = B'} {s = r} {Δ = GoalSucc} {A = C'} mix_r
          sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (C' ∧ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (C' ∧ B') ^ r ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((C' ∧ B') ^ r ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_rule
          ant-eq : (Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (C' ∧ B') ^ r ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (C' ∧ B') ^ r} {Γ = Γ'₁} neq_G
          p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
          d_final : δ p' ≤ max (δ (⊢¬ Π_sub)) (δ (∧₂⊢ Π'_sub))
          d_final = subst (_≤ max (δ (⊢¬ Π_sub)) (δ (∧₂⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (¬ B) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (□ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢¬ {.Γ_sub} {B} {t} {Δ_sub} Π_sub) Π'@(□⊢ {Γ = Γ'₁} {A = B'} {s = r} {t = δ'} {Δ = Δ'₁} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleNegBox accRec (discretePFormula (A ^ s) ((¬ B) ^ t))
  where
    handleNegBox : (∀ m' → m' <Lex (n , mixHeight (⊢¬ Π_sub) Π') → Acc _<Lex_ m')
                → Dec ((A ^ s) ≡ ((¬ B) ^ t))
                → Σ (Γ_sub ,, ((Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s)) ⊢ (([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
                    (λ p → δ p ≤ max (δ (⊢¬ Π_sub)) (δ (□⊢ Π'_sub)))
    handleNegBox accR (no neq) =
      let (p_no , d_no) = handleNegNoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (¬ B) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (¬ B) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢¬ Π_sub)) (δ (□⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleNegBox accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((□ B') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (¬ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec = mixHeight-dec-r (⊢¬ Π_sub) (□⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ (r ∘ δ') ]} {Δ' = Δ'₁} degEq (⊢¬ Π_sub) Π'_sub wfp wfp'_s acc'
          Γ'₁-A = Γ'₁ - (A ^ s)
          GoalSucc = (([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
          sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ (r ∘ δ') ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ (r ∘ δ') ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ (r ∘ δ') ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          p_rule = □⊢ {Γ_sub ,, Γ'₁-A} {B'} {r} {δ'} {GoalSucc} mix_r
          sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (□ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (□ B') ^ r ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((□ B') ^ r ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_rule
          ant-eq : (Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (□ B') ^ r ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (□ B') ^ r} {Γ = Γ'₁} neq_G
          p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
          d_final : δ p' ≤ max (δ (⊢¬ Π_sub)) (δ (□⊢ Π'_sub))
          d_final = subst (_≤ max (δ (⊢¬ Π_sub)) (δ (□⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (¬ B) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ r ])} {Δ' = .(Δ'₁ ,, Δ'₂)} {A = A} {s = s}
    degEq (⊢¬ {.Γ_sub} {B} {t} {Δ_sub} Π_sub) Π'@(∨⊢ {Γ₁ = Γ'₁} {A = B'} {s = r} {Δ₁ = Δ'₁} {Γ₂ = Γ'₂} {B = C'} {Δ₂ = Δ'₂} Π'1 Π'2) wfp wfp'@(wfp'1 , wfp'2) (acc accRec) =
    handleNegOr accRec (discretePFormula (A ^ s) ((¬ B) ^ t))
  where
    handleNegOr : (∀ m' → m' <Lex (n , mixHeight (⊢¬ Π_sub) Π') → Acc _<Lex_ m')
               → Dec ((A ^ s) ≡ ((¬ B) ^ t))
               → Σ (Γ_sub ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ r ]) - (A ^ s)) ⊢ (([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂))
                   (λ p → δ p ≤ max (δ (⊢¬ Π_sub)) (δ (∨⊢ Π'1 Π'2)))
    handleNegOr accR (no neq) =
      let (p_no , d_no) = handleNegNoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (¬ B) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (¬ B) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ r ]) - (A ^ s)) ⊢ D ,, (Δ'₁ ,, Δ'₂)) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢¬ Π_sub)) (δ (∨⊢ Π'1 Π'2))) (sym d_p') d_no
      in (p' , d_final)
    handleNegOr accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((B' ∨ C') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (¬ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec1 = mixHeight-dec-r (⊢¬ Π_sub) (∨⊢ Π'1 Π'2) Π'1 (height-subproof-2-l Π'1 Π'2)
          h-dec2 = mixHeight-dec-r (⊢¬ Π_sub) (∨⊢ Π'1 Π'2) Π'2 (height-subproof-2-r Π'1 Π'2)
          acc1 = accR _ (inr (refl , h-dec1))
          acc2 = accR _ (inr (refl , h-dec2))
          (mix1 , dmix1) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢¬ Π_sub) Π'1 wfp wfp'1 acc1
          (mix2 , dmix2) = Mix {Γ' = Γ'₂ ,, [ C' ^ r ]} {Δ' = Δ'₂} degEq (⊢¬ Π_sub) Π'2 wfp wfp'2 acc2
          Γ'₁-A = Γ'₁ - (A ^ s)
          Γ'₂-A = Γ'₂ - (A ^ s)
          Δ-rem = ([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s)
          -- Reorder mix1: extract [B'^r] from removeAll
          sub_left1 : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
          sub_left1 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
          mix1_r = structural sub_left1 subset-refl mix1
          -- Reorder mix2: extract [C'^r] from removeAll
          sub_left2 : (Γ_sub ,, ((Γ'₂ ,, [ C' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₂-A) ,, [ C' ^ r ])
          sub_left2 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₂ ∷ []) , (C' ^ r ∷ A ^ s ∷ [])) {refl}
          mix2_r = structural sub_left2 subset-refl mix2
          -- Apply ∨⊢
          p_rule = ∨⊢ {Γ₁ = Γ_sub ,, Γ'₁-A} {A = B'} {s = r} {Δ₁ = Δ-rem ,, Δ'₁} {Γ₂ = Γ_sub ,, Γ'₂-A} {B = C'} {Δ₂ = Δ-rem ,, Δ'₂} mix1_r mix2_r
          -- Reassociate
          eqAssocL : ((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A) ,, [ (B' ∨ C') ^ r ]) ≡ (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B' ∨ C') ^ r ])
          eqAssocL = sym (++-assoc (Γ_sub ,, Γ'₁-A) (Γ_sub ,, Γ'₂-A) [ (B' ∨ C') ^ r ])
          p_assoc = subst (λ G → G ⊢ (Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) eqAssocL p_rule
          -- Contract
          subLeft : (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B' ∨ C') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, (Γ'₂-A ,, [ (B' ∨ C') ^ r ])))
          subLeft = solve ((((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) ++ₑ elm 0)) (var 0 ++ₑ (var 1 ++ₑ (var 2 ++ₑ elm 0))) ((Γ_sub ∷ Γ'₁-A ∷ Γ'₂-A ∷ []) , ((B' ∨ C') ^ r ∷ [])) {refl}
          subRight : ((Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) ⊆ (Δ-rem ,, (Δ'₁ ,, Δ'₂))
          subRight = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Δ-rem ∷ Δ'₁ ∷ Δ'₂ ∷ []) , []) {refl}
          p_contracted = structural subLeft subRight p_assoc
          -- Transport antecedent
          eqGamma : (Γ'₁ ,, (Γ'₂ ,, [ (B' ∨ C') ^ r ])) - (A ^ s) ≡ Γ'₁-A ,, (Γ'₂-A ,, [ (B' ∨ C') ^ r ])
          eqGamma = trans (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ'₁ (Γ'₂ ,, [ (B' ∨ C') ^ r ]))
                          (cong (Γ'₁-A ,,_) (lemma-removeAll-cons-neq {A = A ^ s} {B = (B' ∨ C') ^ r} {Γ = Γ'₂} neq_G))
          p' = subst (λ G → Γ_sub ,, G ⊢ Δ-rem ,, (Δ'₁ ,, Δ'₂)) (sym eqGamma) p_contracted
          -- Degree
          cutBound = max (δ (⊢¬ Π_sub)) (δ (∨⊢ Π'1 Π'2))
          dΠ≤cb : δ (⊢¬ Π_sub) ≤ cutBound
          dΠ≤cb = left-≤-max {δ (⊢¬ Π_sub)} {δ (∨⊢ Π'1 Π'2)}
          dΠ'1≤cb : δ Π'1 ≤ cutBound
          dΠ'1≤cb = left-right-≤-max
          dΠ'2≤cb : δ Π'2 ≤ cutBound
          dΠ'2≤cb = right-right-≤-max
          dmix1' : δ mix1 ≤ cutBound
          dmix1' = ≤-trans dmix1 (max-least dΠ≤cb dΠ'1≤cb)
          dmix2' : δ mix2 ≤ cutBound
          dmix2' = ≤-trans dmix2 (max-least dΠ≤cb dΠ'2≤cb)
          d_mix1_r = structural-preserves-δ sub_left1 subset-refl mix1
          d_mix2_r = structural-preserves-δ sub_left2 subset-refl mix2
          dmix1r' = subst (_≤ cutBound) (sym d_mix1_r) dmix1'
          dmix2r' = subst (_≤ cutBound) (sym d_mix2_r) dmix2'
          dp_rule : δ p_rule ≤ cutBound
          dp_rule = max-least dmix1r' dmix2r'
          dp_assoc = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx eqAssocL p_rule)) dp_rule
          dp_contracted = subst (_≤ cutBound) (sym (structural-preserves-δ subLeft subRight p_assoc)) dp_assoc
          d_final : δ p' ≤ cutBound
          d_final = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym eqGamma)) p_contracted)) dp_contracted
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (¬ B) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])} {Δ' = .(Δ'₁ ,, Δ'₂)} {A = A} {s = s}
    degEq (⊢¬ {.Γ_sub} {B} {t} {Δ_sub} Π_sub) Π'@(⇒⊢ {Γ₁ = Γ'₁} {B = B'₂} {s = r} {Δ₁ = Δ'₁} {Γ₂ = Γ'₂} {A = B'₁} {Δ₂ = Δ'₂} Π'1 Π'2) wfp wfp'@(wfp'1 , wfp'2) (acc accRec) =
    handleNegImpl accRec (discretePFormula (A ^ s) ((¬ B) ^ t))
  where
    handleNegImpl : (∀ m' → m' <Lex (n , mixHeight (⊢¬ Π_sub) Π') → Acc _<Lex_ m')
                 → Dec ((A ^ s) ≡ ((¬ B) ^ t))
                 → Σ (Γ_sub ,, ((Γ'₁ ,, Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ]) - (A ^ s)) ⊢ (([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂))
                     (λ p → δ p ≤ max (δ (⊢¬ Π_sub)) (δ (⇒⊢ Π'1 Π'2)))
    handleNegImpl accR (no neq) =
      let (p_no , d_no) = handleNegNoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (¬ B) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (¬ B) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ]) - (A ^ s)) ⊢ D ,, (Δ'₁ ,, Δ'₂)) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢¬ Π_sub)) (δ (⇒⊢ Π'1 Π'2))) (sym d_p') d_no
      in (p' , d_final)
    handleNegImpl accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((B'₁ ⇒ B'₂) ^ r)
          neq_G = λ eq' → snotz (cong (λ { (¬ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec1 = mixHeight-dec-r (⊢¬ Π_sub) (⇒⊢ Π'1 Π'2) Π'1 (height-subproof-2-l Π'1 Π'2)
          h-dec2 = mixHeight-dec-r (⊢¬ Π_sub) (⇒⊢ Π'1 Π'2) Π'2 (height-subproof-2-r Π'1 Π'2)
          acc1 = accR _ (inr (refl , h-dec1))
          acc2 = accR _ (inr (refl , h-dec2))
          (mix1 , dmix1) = Mix {Γ' = Γ'₁ ,, [ B'₂ ^ r ]} {Δ' = Δ'₁} degEq (⊢¬ Π_sub) Π'1 wfp wfp'1 acc1
          (mix2 , dmix2) = Mix {Γ' = Γ'₂} {Δ' = [ B'₁ ^ r ] ,, Δ'₂} degEq (⊢¬ Π_sub) Π'2 wfp wfp'2 acc2
          Γ'₁-A = Γ'₁ - (A ^ s)
          Γ'₂-A = Γ'₂ - (A ^ s)
          Δ-rem = ([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s)
          -- Reorder mix1: extract [B'₂^r] to end
          sub_left1 : (Γ_sub ,, ((Γ'₁ ,, [ B'₂ ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B'₂ ^ r ])
          sub_left1 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B'₂ ^ r ∷ A ^ s ∷ [])) {refl}
          mix1_r = structural sub_left1 subset-refl mix1
          -- Reorder mix2: move [B'₁^r] to front of succedent
          sub_right2 : (Δ-rem ,, ([ B'₁ ^ r ] ,, Δ'₂)) ⊆ ([ B'₁ ^ r ] ,, (Δ-rem ,, Δ'₂))
          sub_right2 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ'₂ ∷ []) , (B'₁ ^ r ∷ [])) {refl}
          mix2_r = structural subset-refl sub_right2 mix2
          -- Apply ⇒⊢
          p_rule = ⇒⊢ {Γ₁ = Γ_sub ,, Γ'₁-A} {B = B'₂} {s = r} {Δ₁ = Δ-rem ,, Δ'₁} {Γ₂ = Γ_sub ,, Γ'₂-A} {A = B'₁} {Δ₂ = Δ-rem ,, Δ'₂} mix1_r mix2_r
          -- Reassociate
          eqAssocL : ((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A) ,, [ (B'₁ ⇒ B'₂) ^ r ]) ≡ (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B'₁ ⇒ B'₂) ^ r ])
          eqAssocL = sym (++-assoc (Γ_sub ,, Γ'₁-A) (Γ_sub ,, Γ'₂-A) [ (B'₁ ⇒ B'₂) ^ r ])
          p_assoc = subst (λ G → G ⊢ (Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) eqAssocL p_rule
          -- Contract
          subLeft : (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B'₁ ⇒ B'₂) ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, (Γ'₂-A ,, [ (B'₁ ⇒ B'₂) ^ r ])))
          subLeft = solve ((((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) ++ₑ elm 0)) (var 0 ++ₑ (var 1 ++ₑ (var 2 ++ₑ elm 0))) ((Γ_sub ∷ Γ'₁-A ∷ Γ'₂-A ∷ []) , ((B'₁ ⇒ B'₂) ^ r ∷ [])) {refl}
          subRight : ((Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) ⊆ (Δ-rem ,, (Δ'₁ ,, Δ'₂))
          subRight = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Δ-rem ∷ Δ'₁ ∷ Δ'₂ ∷ []) , []) {refl}
          p_contracted = structural subLeft subRight p_assoc
          -- Transport antecedent
          eqGamma : (Γ'₁ ,, (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])) - (A ^ s) ≡ Γ'₁-A ,, (Γ'₂-A ,, [ (B'₁ ⇒ B'₂) ^ r ])
          eqGamma = trans (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ'₁ (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ]))
                          (cong (Γ'₁-A ,,_) (lemma-removeAll-cons-neq {A = A ^ s} {B = (B'₁ ⇒ B'₂) ^ r} {Γ = Γ'₂} neq_G))
          p' = subst (λ G → Γ_sub ,, G ⊢ Δ-rem ,, (Δ'₁ ,, Δ'₂)) (sym eqGamma) p_contracted
          -- Degree
          cutBound = max (δ (⊢¬ Π_sub)) (δ (⇒⊢ Π'1 Π'2))
          dΠ≤cb : δ (⊢¬ Π_sub) ≤ cutBound
          dΠ≤cb = left-≤-max {δ (⊢¬ Π_sub)} {δ (⇒⊢ Π'1 Π'2)}
          dΠ'1≤cb : δ Π'1 ≤ cutBound
          dΠ'1≤cb = left-right-≤-max
          dΠ'2≤cb : δ Π'2 ≤ cutBound
          dΠ'2≤cb = right-right-≤-max
          dmix1' : δ mix1 ≤ cutBound
          dmix1' = ≤-trans dmix1 (max-least dΠ≤cb dΠ'1≤cb)
          dmix2' : δ mix2 ≤ cutBound
          dmix2' = ≤-trans dmix2 (max-least dΠ≤cb dΠ'2≤cb)
          d_mix1_r = structural-preserves-δ sub_left1 subset-refl mix1
          d_mix2_r = structural-preserves-δ subset-refl sub_right2 mix2
          dmix1r' = subst (_≤ cutBound) (sym d_mix1_r) dmix1'
          dmix2r' = subst (_≤ cutBound) (sym d_mix2_r) dmix2'
          dp_rule : δ p_rule ≤ cutBound
          dp_rule = max-least dmix1r' dmix2r'
          dp_assoc = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx eqAssocL p_rule)) dp_rule
          dp_contracted = subst (_≤ cutBound) (sym (structural-preserves-δ subLeft subRight p_assoc)) dp_assoc
          d_final : δ p' ≤ cutBound
          d_final = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym eqGamma)) p_contracted)) dp_contracted
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (¬ B) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (♢ B') ^ r' ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢¬ {.Γ_sub} {B} {t} {Δ_sub} Π_sub) Π'@(♢⊢ {x'} {r'} {Γ'₁} {Δ'₁} {B'} ext' freshΓ' freshΔ' Π'_sub) wfp wfp'@(wf' , wfp'_s) (acc accRec) =
    handleNegDia accRec (discretePFormula (A ^ s) ((¬ B) ^ t))
  where
    handleNegDia : (∀ m' → m' <Lex (n , mixHeight (⊢¬ Π_sub) Π') → Acc _<Lex_ m')
                → Dec ((A ^ s) ≡ ((¬ B) ^ t))
                → Σ (Γ_sub ,, ((Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s)) ⊢ (([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
                    (λ p → δ p ≤ max (δ (⊢¬ Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub)))
    handleNegDia accR (no neq) =
      let (p_no , d_no) = handleNegNoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (¬ B) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (¬ B) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢¬ Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleNegDia accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((♢ B') ^ r')
          neq_G = λ eq' → snotz (cong (λ { (¬ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          -- Abbreviations
          Γ'₁-A = Γ'₁ - (A ^ s)
          Δ-rem = ([ (¬ B) ^ t ] ,, Δ_sub) - (A ^ s)
          GoalSucc = Δ-rem ,, Δ'₁
          combined = (Γ_sub ,, Γ'₁-A) ,, GoalSucc
          -- Eigenposition renaming
          y : Token
          y = freshTokenForRename r' combined Π'_sub
          eigent : Position
          eigent = insertToken x' r'
          t'' : Position
          t'' = substPos x' (singleton-pos y) eigent
          extSTE : IsSingleTokenExt r' eigent x'
          extSTE = mkSingleTokenExt r' x' ext'
          y-fresh-combined : TokenFresh y combined
          y-fresh-combined = freshTokenForRename-fresh r' combined Π'_sub
          y-eigenpos : maxEigenposToken Π'_sub < y
          y-eigenpos = freshTokenForRename-eigenpos r' combined Π'_sub
          y∉r' : y ∉Pos r'
          y∉r' = freshTokenForRename-∉r r' combined Π'_sub
          rename-result = renameEigenpos-♢⊢-premise-gen {r = r'} {t = eigent} {x = x'} {Γ = Γ'₁} {Δ = Δ'₁} {A = B'} Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
          Π'_renamed : Γ'₁ ,, [ B' ^ t'' ] ⊢ Δ'₁
          Π'_renamed = fst rename-result
          ext'' : IsSingleTokenExt r' t'' y
          ext'' = snd rename-result
          δ-eq-renamed : δ Π'_renamed ≡ δ Π'_sub
          δ-eq-renamed = δ-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
          height-eq-renamed : height Π'_renamed ≡ height Π'_sub
          height-eq-renamed = height-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
          wfp'_renamed : WellFormedProof Π'_renamed
          wfp'_renamed = WellFormed-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r' wfp'_s
          -- Height decrease
          h-dec-raw = mixHeight-dec-r (⊢¬ Π_sub) (♢⊢ ext' freshΓ' freshΔ' Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          mixHeight-eq = cong (λ h → height (⊢¬ Π_sub) + h) height-eq-renamed
          h-dec = subst (_< mixHeight (⊢¬ Π_sub) (♢⊢ ext' freshΓ' freshΔ' Π'_sub)) (sym mixHeight-eq) h-dec-raw
          acc' = accR _ (inr (refl , h-dec))
          -- Mix
          (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ t'' ]} {Δ' = Δ'₁} degEq (⊢¬ Π_sub) Π'_renamed wfp wfp'_renamed acc'
          -- Reorder antecedent: extract [B'^t''] to end
          sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ t'' ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ t'' ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ t'' ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          -- Transport t'' to insertToken y r'
          t''-eq : t'' ≡ insertToken y r'
          t''-eq = substPos-insertToken-eq x' y r' ext'
          -- Freshness of y for separated contexts
          fresh-split = TokenFresh-split (Γ_sub ,, Γ'₁-A) GoalSucc y y-fresh-combined
          freshΓ_new : TokenFresh y (Γ_sub ,, Γ'₁-A)
          freshΓ_new = fst fresh-split
          freshΔ_new : TokenFresh y GoalSucc
          freshΔ_new = snd fresh-split
          mix_transported : (Γ_sub ,, Γ'₁-A) ,, [ B' ^ insertToken y r' ] ⊢ GoalSucc
          mix_transported = subst (λ (p : Position) → (Γ_sub ,, Γ'₁-A) ,, [ B' ^ p ] ⊢ GoalSucc) t''-eq mix_r
          -- Apply ♢⊢
          p_dia = ♢⊢ {y} {r'} {Γ_sub ,, Γ'₁-A} {GoalSucc} {B'} y∉r' freshΓ_new freshΔ_new mix_transported
          -- Reorder: (Γ_sub ,, Γ'₁-A) ,, [(♢ B')^r'] → Γ_sub ,, (Γ'₁-A ,, [(♢ B')^r'])
          sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (♢ B') ^ r' ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (♢ B') ^ r' ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((♢ B') ^ r' ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_dia
          -- Transport antecedent
          ant-eq : (Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s) ≡ Γ'₁-A ,, [ (♢ B') ^ r' ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (♢ B') ^ r'} {Γ = Γ'₁} neq_G
          p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          -- Degree
          bound-eq : max (δ (⊢¬ Π_sub)) (δ Π'_renamed) ≡ max (δ (⊢¬ Π_sub)) (δ Π'_sub)
          bound-eq = cong (λ d → max (δ (⊢¬ Π_sub)) d) δ-eq-renamed
          dmix' : δ mix ≤ max (δ (⊢¬ Π_sub)) (δ Π'_sub)
          dmix' = subst (δ mix ≤_) bound-eq dmix
          d_mix_r = structural-preserves-δ sub_left subset-refl mix
          d_mix_transported : δ mix_transported ≡ δ mix_r
          d_mix_transported = subst-preserves-δ-ctx (cong (λ (p : Position) → (Γ_sub ,, Γ'₁-A) ,, [ B' ^ p ]) t''-eq) mix_r
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_dia)
                 (trans d_mix_transported (d_mix_r)))
          d_final : δ p' ≤ max (δ (⊢¬ Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))
          d_final = subst (_≤ max (δ (⊢¬ Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))) (sym d_p') dmix'
      in (p' , d_final)

-- Catch-all for left = ⊢∨₁
Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B ∨ C) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (¬ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢∨₁ {.Γ_sub} {B} {t} {Δ_sub} {C} Π_sub) Π'@(¬⊢ {Γ'₁} {B'} {r} {Δ'₁} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleDisj1Neg accRec (discretePFormula (A ^ s) ((B ∨ C) ^ t))
  where
    handleDisj1Neg :
      (∀ m' → m' <Lex (n , mixHeight (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B ∨ C) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s)) ⊢ (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (¬⊢ Π'_sub)))
    handleDisj1Neg accR (no neq) =
      let (p_no , d_no) = handleDisj1NoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (B ∨ C) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (¬⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleDisj1Neg accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((¬ B') ^ r)
        neq_G = λ eq' → snotz (cong (λ { (_ ∨ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        h-dec = mixHeight-dec-r (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) (¬⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
        acc' = accR _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ'₁} {Δ' = [ B' ^ r ] ,, Δ'₁} degEq (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) Π'_sub wfp wfp'_s acc'
        Γ'₁-A = Γ'₁ - (A ^ s)
        Δ-rem = ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)
        GoalSucc = Δ-rem ,, Δ'₁
        sub_right1 : (Δ-rem ,, ([ B' ^ r ] ,, Δ'₁)) ⊆ ([ B' ^ r ] ,, (Δ-rem ,, Δ'₁))
        sub_right1 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ'₁ ∷ []) , (B' ^ r ∷ [])) {refl}
        mix_r = structural subset-refl sub_right1 mix
        p_rule = ¬⊢ {Γ_sub ,, Γ'₁-A} {B'} {r} {GoalSucc} mix_r
        sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (¬ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (¬ B') ^ r ]))
        sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((¬ B') ^ r ∷ [])) {refl}
        p_reorder = structural sub_left2 subset-refl p_rule
        ant-eq : (Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (¬ B') ^ r ]
        ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (¬ B') ^ r} {Γ = Γ'₁} neq_G
        p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
               (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ subset-refl sub_right1 mix))
        d_final : δ p' ≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (¬⊢ Π'_sub))
        d_final = subst (_≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (¬⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B ∨ C) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (B' ∧ C') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢∨₁ {.Γ_sub} {B} {t} {Δ_sub} {C} Π_sub) Π'@(∧₁⊢ {Γ = Γ'₁} {A = B'} {s = r} {Δ = Δ'₁} {B = C'} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleDisj1And1 accRec (discretePFormula (A ^ s) ((B ∨ C) ^ t))
  where
    handleDisj1And1 :
      (∀ m' → m' <Lex (n , mixHeight (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B ∨ C) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s)) ⊢ (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (∧₁⊢ Π'_sub)))
    handleDisj1And1 accR (no neq) =
      let (p_no , d_no) = handleDisj1NoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (B ∨ C) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (∧₁⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleDisj1And1 accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((B' ∧ C') ^ r)
        neq_G = λ eq' → snotz (cong (λ { (_ ∨ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        h-dec = mixHeight-dec-r (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) (∧₁⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
        acc' = accR _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) Π'_sub wfp wfp'_s acc'
        Γ'₁-A = Γ'₁ - (A ^ s)
        GoalSucc = (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
        sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
        sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
        mix_r = structural sub_left subset-refl mix
        p_rule = ∧₁⊢ {Γ = Γ_sub ,, Γ'₁-A} {A = B'} {s = r} {Δ = GoalSucc} {B = C'} mix_r
        sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (B' ∧ C') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (B' ∧ C') ^ r ]))
        sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((B' ∧ C') ^ r ∷ [])) {refl}
        p_reorder = structural sub_left2 subset-refl p_rule
        ant-eq : (Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (B' ∧ C') ^ r ]
        ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (B' ∧ C') ^ r} {Γ = Γ'₁} neq_G
        p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
               (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
        d_final : δ p' ≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (∧₁⊢ Π'_sub))
        d_final = subst (_≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (∧₁⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B ∨ C) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (C' ∧ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢∨₁ {.Γ_sub} {B} {t} {Δ_sub} {C} Π_sub) Π'@(∧₂⊢ {Γ = Γ'₁} {B = B'} {s = r} {Δ = Δ'₁} {A = C'} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleDisj1And2 accRec (discretePFormula (A ^ s) ((B ∨ C) ^ t))
  where
    handleDisj1And2 :
      (∀ m' → m' <Lex (n , mixHeight (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B ∨ C) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s)) ⊢ (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (∧₂⊢ Π'_sub)))
    handleDisj1And2 accR (no neq) =
      let (p_no , d_no) = handleDisj1NoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (B ∨ C) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (∧₂⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleDisj1And2 accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((C' ∧ B') ^ r)
        neq_G = λ eq' → snotz (cong (λ { (_ ∨ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        h-dec = mixHeight-dec-r (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) (∧₂⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
        acc' = accR _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) Π'_sub wfp wfp'_s acc'
        Γ'₁-A = Γ'₁ - (A ^ s)
        GoalSucc = (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
        sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
        sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
        mix_r = structural sub_left subset-refl mix
        p_rule = ∧₂⊢ {Γ = Γ_sub ,, Γ'₁-A} {B = B'} {s = r} {Δ = GoalSucc} {A = C'} mix_r
        sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (C' ∧ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (C' ∧ B') ^ r ]))
        sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((C' ∧ B') ^ r ∷ [])) {refl}
        p_reorder = structural sub_left2 subset-refl p_rule
        ant-eq : (Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (C' ∧ B') ^ r ]
        ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (C' ∧ B') ^ r} {Γ = Γ'₁} neq_G
        p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
               (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
        d_final : δ p' ≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (∧₂⊢ Π'_sub))
        d_final = subst (_≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (∧₂⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B ∨ C) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (□ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢∨₁ {.Γ_sub} {B} {t} {Δ_sub} {C} Π_sub) Π'@(□⊢ {Γ = Γ'₁} {A = B'} {s = r} {t = δ'} {Δ = Δ'₁} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleDisj1Box accRec (discretePFormula (A ^ s) ((B ∨ C) ^ t))
  where
    handleDisj1Box :
      (∀ m' → m' <Lex (n , mixHeight (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B ∨ C) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s)) ⊢ (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (□⊢ Π'_sub)))
    handleDisj1Box accR (no neq) =
      let (p_no , d_no) = handleDisj1NoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (B ∨ C) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (□⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleDisj1Box accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((□ B') ^ r)
        neq_G = λ eq' → snotz (cong (λ { (_ ∨ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        h-dec = mixHeight-dec-r (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) (□⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
        acc' = accR _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ (r ∘ δ') ]} {Δ' = Δ'₁} degEq (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) Π'_sub wfp wfp'_s acc'
        Γ'₁-A = Γ'₁ - (A ^ s)
        GoalSucc = (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
        sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ (r ∘ δ') ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ (r ∘ δ') ])
        sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ (r ∘ δ') ∷ A ^ s ∷ [])) {refl}
        mix_r = structural sub_left subset-refl mix
        p_rule = □⊢ {Γ_sub ,, Γ'₁-A} {B'} {r} {δ'} {GoalSucc} mix_r
        sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (□ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (□ B') ^ r ]))
        sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((□ B') ^ r ∷ [])) {refl}
        p_reorder = structural sub_left2 subset-refl p_rule
        ant-eq : (Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (□ B') ^ r ]
        ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (□ B') ^ r} {Γ = Γ'₁} neq_G
        p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
               (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
        d_final : δ p' ≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (□⊢ Π'_sub))
        d_final = subst (_≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (□⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B ∨ C) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])} {Δ' = .(Δ'₁ ,, Δ'₂)} {A = A} {s = s}
    degEq (⊢∨₁ {.Γ_sub} {B} {t} {Δ_sub} {C} Π_sub) Π'@(⇒⊢ {Γ₁ = Γ'₁} {B = B'₂} {s = r} {Δ₁ = Δ'₁} {Γ₂ = Γ'₂} {A = B'₁} {Δ₂ = Δ'₂} Π'1 Π'2) wfp wfp'@(wfp'1 , wfp'2) (acc accRec) =
    handleDisj1Impl accRec (discretePFormula (A ^ s) ((B ∨ C) ^ t))
  where
    handleDisj1Impl :
      (∀ m' → m' <Lex (n , mixHeight (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B ∨ C) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])) - (A ^ s)) ⊢ (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂))
          (λ p → δ p ≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (⇒⊢ Π'1 Π'2)))
    handleDisj1Impl accR (no neq) =
      let (p_no , d_no) = handleDisj1NoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (B ∨ C) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])) - (A ^ s)) ⊢ D ,, (Δ'₁ ,, Δ'₂)) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (⇒⊢ Π'1 Π'2))) (sym d_p') d_no
      in (p' , d_final)
    handleDisj1Impl accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((B'₁ ⇒ B'₂) ^ r)
        neq_G = λ eq' → snotz (cong (λ { (_ ∨ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        h-dec1 = mixHeight-dec-r (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) (⇒⊢ Π'1 Π'2) Π'1 (height-subproof-2-l Π'1 Π'2)
        h-dec2 = mixHeight-dec-r (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) (⇒⊢ Π'1 Π'2) Π'2 (height-subproof-2-r Π'1 Π'2)
        acc1 = accR _ (inr (refl , h-dec1))
        acc2 = accR _ (inr (refl , h-dec2))
        (mix1 , dmix1) = Mix {Γ' = Γ'₁ ,, [ B'₂ ^ r ]} {Δ' = Δ'₁} degEq (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) Π'1 wfp wfp'1 acc1
        (mix2 , dmix2) = Mix {Γ' = Γ'₂} {Δ' = [ B'₁ ^ r ] ,, Δ'₂} degEq (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) Π'2 wfp wfp'2 acc2
        Γ'₁-A = Γ'₁ - (A ^ s)
        Γ'₂-A = Γ'₂ - (A ^ s)
        Δ-rem = ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)
        sub_left1 : (Γ_sub ,, ((Γ'₁ ,, [ B'₂ ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B'₂ ^ r ])
        sub_left1 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B'₂ ^ r ∷ A ^ s ∷ [])) {refl}
        mix1_r = structural sub_left1 subset-refl mix1
        sub_right2 : (Δ-rem ,, ([ B'₁ ^ r ] ,, Δ'₂)) ⊆ ([ B'₁ ^ r ] ,, (Δ-rem ,, Δ'₂))
        sub_right2 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ'₂ ∷ []) , (B'₁ ^ r ∷ [])) {refl}
        mix2_r = structural subset-refl sub_right2 mix2
        p_rule = ⇒⊢ {Γ₁ = Γ_sub ,, Γ'₁-A} {B = B'₂} {s = r} {Δ₁ = Δ-rem ,, Δ'₁} {Γ₂ = Γ_sub ,, Γ'₂-A} {A = B'₁} {Δ₂ = Δ-rem ,, Δ'₂} mix1_r mix2_r
        eqAssocL : ((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A) ,, [ (B'₁ ⇒ B'₂) ^ r ]) ≡ (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B'₁ ⇒ B'₂) ^ r ])
        eqAssocL = sym (++-assoc (Γ_sub ,, Γ'₁-A) (Γ_sub ,, Γ'₂-A) [ (B'₁ ⇒ B'₂) ^ r ])
        p_assoc = subst (λ G → G ⊢ (Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) eqAssocL p_rule
        subLeft : (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B'₁ ⇒ B'₂) ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, (Γ'₂-A ,, [ (B'₁ ⇒ B'₂) ^ r ])))
        subLeft = solve ((((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) ++ₑ elm 0)) (var 0 ++ₑ (var 1 ++ₑ (var 2 ++ₑ elm 0))) ((Γ_sub ∷ Γ'₁-A ∷ Γ'₂-A ∷ []) , ((B'₁ ⇒ B'₂) ^ r ∷ [])) {refl}
        subRight : ((Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) ⊆ (Δ-rem ,, (Δ'₁ ,, Δ'₂))
        subRight = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Δ-rem ∷ Δ'₁ ∷ Δ'₂ ∷ []) , []) {refl}
        p_contracted = structural subLeft subRight p_assoc
        eqGamma : (Γ'₁ ,, (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])) - (A ^ s) ≡ Γ'₁-A ,, (Γ'₂-A ,, [ (B'₁ ⇒ B'₂) ^ r ])
        eqGamma = trans (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ'₁ (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ]))
                        (cong (Γ'₁-A ,,_) (lemma-removeAll-cons-neq {A = A ^ s} {B = (B'₁ ⇒ B'₂) ^ r} {Γ = Γ'₂} neq_G))
        p' = subst (λ G → Γ_sub ,, G ⊢ Δ-rem ,, (Δ'₁ ,, Δ'₂)) (sym eqGamma) p_contracted
        cutBound = max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (⇒⊢ Π'1 Π'2))
        dΠ≤cb : δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) ≤ cutBound
        dΠ≤cb = left-≤-max {δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)} {δ (⇒⊢ Π'1 Π'2)}
        dΠ'1≤cb : δ Π'1 ≤ cutBound
        dΠ'1≤cb = left-right-≤-max
        dΠ'2≤cb : δ Π'2 ≤ cutBound
        dΠ'2≤cb = right-right-≤-max
        dmix1' : δ mix1 ≤ cutBound
        dmix1' = ≤-trans dmix1 (max-least dΠ≤cb dΠ'1≤cb)
        dmix2' : δ mix2 ≤ cutBound
        dmix2' = ≤-trans dmix2 (max-least dΠ≤cb dΠ'2≤cb)
        d_mix1_r = structural-preserves-δ sub_left1 subset-refl mix1
        d_mix2_r = structural-preserves-δ subset-refl sub_right2 mix2
        dmix1r' = subst (_≤ cutBound) (sym d_mix1_r) dmix1'
        dmix2r' = subst (_≤ cutBound) (sym d_mix2_r) dmix2'
        dp_rule : δ p_rule ≤ cutBound
        dp_rule = max-least dmix1r' dmix2r'
        dp_assoc = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx eqAssocL p_rule)) dp_rule
        dp_contracted = subst (_≤ cutBound) (sym (structural-preserves-δ subLeft subRight p_assoc)) dp_assoc
        d_final : δ p' ≤ cutBound
        d_final = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym eqGamma)) p_contracted)) dp_contracted
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B ∨ C) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (♢ B') ^ r' ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢∨₁ {.Γ_sub} {B} {t} {Δ_sub} {C} Π_sub) Π'@(♢⊢ {x'} {r'} {Γ'₁} {Δ'₁} {B'} ext' freshΓ' freshΔ' Π'_sub) wfp wfp'@(wf' , wfp'_s) (acc accRec) =
    handleDisj1Dia accRec (discretePFormula (A ^ s) ((B ∨ C) ^ t))
  where
    handleDisj1Dia :
      (∀ m' → m' <Lex (n , mixHeight (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B ∨ C) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s)) ⊢ (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub)))
    handleDisj1Dia accR (no neq) =
      let (p_no , d_no) = handleDisj1NoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (B ∨ C) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleDisj1Dia accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((♢ B') ^ r')
        neq_G = λ eq' → snotz (cong (λ { (_ ∨ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        Γ'₁-A = Γ'₁ - (A ^ s)
        Δ-rem = ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)
        GoalSucc = Δ-rem ,, Δ'₁
        combined = (Γ_sub ,, Γ'₁-A) ,, GoalSucc
        y : Token
        y = freshTokenForRename r' combined Π'_sub
        eigent : Position
        eigent = insertToken x' r'
        t'' : Position
        t'' = substPos x' (singleton-pos y) eigent
        extSTE : IsSingleTokenExt r' eigent x'
        extSTE = mkSingleTokenExt r' x' ext'
        y-fresh-combined : TokenFresh y combined
        y-fresh-combined = freshTokenForRename-fresh r' combined Π'_sub
        y-eigenpos : maxEigenposToken Π'_sub < y
        y-eigenpos = freshTokenForRename-eigenpos r' combined Π'_sub
        y∉r' : y ∉Pos r'
        y∉r' = freshTokenForRename-∉r r' combined Π'_sub
        rename-result = renameEigenpos-♢⊢-premise-gen {r = r'} {t = eigent} {x = x'} {Γ = Γ'₁} {Δ = Δ'₁} {A = B'} Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
        Π'_renamed : Γ'₁ ,, [ B' ^ t'' ] ⊢ Δ'₁
        Π'_renamed = fst rename-result
        ext'' : IsSingleTokenExt r' t'' y
        ext'' = snd rename-result
        δ-eq-renamed : δ Π'_renamed ≡ δ Π'_sub
        δ-eq-renamed = δ-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
        height-eq-renamed : height Π'_renamed ≡ height Π'_sub
        height-eq-renamed = height-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
        wfp'_renamed : WellFormedProof Π'_renamed
        wfp'_renamed = WellFormed-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r' wfp'_s
        h-dec-raw = mixHeight-dec-r (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) (♢⊢ ext' freshΓ' freshΔ' Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
        mixHeight-eq = cong (λ h → height (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) + h) height-eq-renamed
        h-dec = subst (_< mixHeight (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) (♢⊢ ext' freshΓ' freshΔ' Π'_sub)) (sym mixHeight-eq) h-dec-raw
        acc' = accR _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ t'' ]} {Δ' = Δ'₁} degEq (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) Π'_renamed wfp wfp'_renamed acc'
        sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ t'' ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ t'' ])
        sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ t'' ∷ A ^ s ∷ [])) {refl}
        mix_r = structural sub_left subset-refl mix
        t''-eq : t'' ≡ insertToken y r'
        t''-eq = substPos-insertToken-eq x' y r' ext'
        fresh-split = TokenFresh-split (Γ_sub ,, Γ'₁-A) GoalSucc y y-fresh-combined
        freshΓ_new : TokenFresh y (Γ_sub ,, Γ'₁-A)
        freshΓ_new = fst fresh-split
        freshΔ_new : TokenFresh y GoalSucc
        freshΔ_new = snd fresh-split
        mix_transported : (Γ_sub ,, Γ'₁-A) ,, [ B' ^ insertToken y r' ] ⊢ GoalSucc
        mix_transported = subst (λ (p : Position) → (Γ_sub ,, Γ'₁-A) ,, [ B' ^ p ] ⊢ GoalSucc) t''-eq mix_r
        p_dia = ♢⊢ {y} {r'} {Γ_sub ,, Γ'₁-A} {GoalSucc} {B'} y∉r' freshΓ_new freshΔ_new mix_transported
        sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (♢ B') ^ r' ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (♢ B') ^ r' ]))
        sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((♢ B') ^ r' ∷ [])) {refl}
        p_reorder = structural sub_left2 subset-refl p_dia
        ant-eq : (Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s) ≡ Γ'₁-A ,, [ (♢ B') ^ r' ]
        ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (♢ B') ^ r'} {Γ = Γ'₁} neq_G
        p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
        bound-eq : max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ Π'_renamed) ≡ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ Π'_sub)
        bound-eq = cong (λ d → max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) d) δ-eq-renamed
        dmix' : δ mix ≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ Π'_sub)
        dmix' = subst (δ mix ≤_) bound-eq dmix
        d_mix_r = structural-preserves-δ sub_left subset-refl mix
        d_mix_transported : δ mix_transported ≡ δ mix_r
        d_mix_transported = subst-preserves-δ-ctx (cong (λ (p : Position) → (Γ_sub ,, Γ'₁-A) ,, [ B' ^ p ]) t''-eq) mix_r
        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
               (trans (structural-preserves-δ sub_left2 subset-refl p_dia)
               (trans d_mix_transported (d_mix_r)))
        d_final : δ p' ≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))
        d_final = subst (_≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))) (sym d_p') dmix'
      in (p' , d_final)

-- Catch-all for left = ⊢∨₂
Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B ∨ C) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (¬ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢∨₂ {.Γ_sub} {C} {t} {Δ_sub} {B} Π_sub) Π'@(¬⊢ {Γ'₁} {B'} {r} {Δ'₁} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleDisj2Neg accRec (discretePFormula (A ^ s) ((B ∨ C) ^ t))
  where
    handleDisj2Neg :
      (∀ m' → m' <Lex (n , mixHeight (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B ∨ C) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s)) ⊢ (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (¬⊢ Π'_sub)))
    handleDisj2Neg accR (no neq) =
      let (p_no , d_no) = handleDisj2NoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (B ∨ C) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (¬⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleDisj2Neg accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((¬ B') ^ r)
        neq_G = λ eq' → snotz (cong (λ { (_ ∨ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        h-dec = mixHeight-dec-r (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) (¬⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
        acc' = accR _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ'₁} {Δ' = [ B' ^ r ] ,, Δ'₁} degEq (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) Π'_sub wfp wfp'_s acc'
        Γ'₁-A = Γ'₁ - (A ^ s)
        Δ-rem = ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)
        GoalSucc = Δ-rem ,, Δ'₁
        sub_right1 : (Δ-rem ,, ([ B' ^ r ] ,, Δ'₁)) ⊆ ([ B' ^ r ] ,, (Δ-rem ,, Δ'₁))
        sub_right1 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ'₁ ∷ []) , (B' ^ r ∷ [])) {refl}
        mix_r = structural subset-refl sub_right1 mix
        p_rule = ¬⊢ {Γ_sub ,, Γ'₁-A} {B'} {r} {GoalSucc} mix_r
        sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (¬ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (¬ B') ^ r ]))
        sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((¬ B') ^ r ∷ [])) {refl}
        p_reorder = structural sub_left2 subset-refl p_rule
        ant-eq : (Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (¬ B') ^ r ]
        ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (¬ B') ^ r} {Γ = Γ'₁} neq_G
        p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
               (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ subset-refl sub_right1 mix))
        d_final : δ p' ≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (¬⊢ Π'_sub))
        d_final = subst (_≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (¬⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B ∨ C) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (B' ∧ C') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢∨₂ {.Γ_sub} {C} {t} {Δ_sub} {B} Π_sub) Π'@(∧₁⊢ {Γ = Γ'₁} {A = B'} {s = r} {Δ = Δ'₁} {B = C'} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleDisj2And1 accRec (discretePFormula (A ^ s) ((B ∨ C) ^ t))
  where
    handleDisj2And1 :
      (∀ m' → m' <Lex (n , mixHeight (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B ∨ C) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s)) ⊢ (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (∧₁⊢ Π'_sub)))
    handleDisj2And1 accR (no neq) =
      let (p_no , d_no) = handleDisj2NoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (B ∨ C) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (∧₁⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleDisj2And1 accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((B' ∧ C') ^ r)
        neq_G = λ eq' → snotz (cong (λ { (_ ∨ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        h-dec = mixHeight-dec-r (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) (∧₁⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
        acc' = accR _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) Π'_sub wfp wfp'_s acc'
        Γ'₁-A = Γ'₁ - (A ^ s)
        GoalSucc = (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
        sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
        sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
        mix_r = structural sub_left subset-refl mix
        p_rule = ∧₁⊢ {Γ = Γ_sub ,, Γ'₁-A} {A = B'} {s = r} {Δ = GoalSucc} {B = C'} mix_r
        sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (B' ∧ C') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (B' ∧ C') ^ r ]))
        sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((B' ∧ C') ^ r ∷ [])) {refl}
        p_reorder = structural sub_left2 subset-refl p_rule
        ant-eq : (Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (B' ∧ C') ^ r ]
        ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (B' ∧ C') ^ r} {Γ = Γ'₁} neq_G
        p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
               (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
        d_final : δ p' ≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (∧₁⊢ Π'_sub))
        d_final = subst (_≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (∧₁⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B ∨ C) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (C' ∧ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢∨₂ {.Γ_sub} {C} {t} {Δ_sub} {B} Π_sub) Π'@(∧₂⊢ {Γ = Γ'₁} {B = B'} {s = r} {Δ = Δ'₁} {A = C'} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleDisj2And2 accRec (discretePFormula (A ^ s) ((B ∨ C) ^ t))
  where
    handleDisj2And2 :
      (∀ m' → m' <Lex (n , mixHeight (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B ∨ C) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s)) ⊢ (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (∧₂⊢ Π'_sub)))
    handleDisj2And2 accR (no neq) =
      let (p_no , d_no) = handleDisj2NoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (B ∨ C) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (∧₂⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleDisj2And2 accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((C' ∧ B') ^ r)
        neq_G = λ eq' → snotz (cong (λ { (_ ∨ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        h-dec = mixHeight-dec-r (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) (∧₂⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
        acc' = accR _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) Π'_sub wfp wfp'_s acc'
        Γ'₁-A = Γ'₁ - (A ^ s)
        GoalSucc = (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
        sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
        sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
        mix_r = structural sub_left subset-refl mix
        p_rule = ∧₂⊢ {Γ = Γ_sub ,, Γ'₁-A} {B = B'} {s = r} {Δ = GoalSucc} {A = C'} mix_r
        sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (C' ∧ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (C' ∧ B') ^ r ]))
        sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((C' ∧ B') ^ r ∷ [])) {refl}
        p_reorder = structural sub_left2 subset-refl p_rule
        ant-eq : (Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (C' ∧ B') ^ r ]
        ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (C' ∧ B') ^ r} {Γ = Γ'₁} neq_G
        p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
               (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
        d_final : δ p' ≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (∧₂⊢ Π'_sub))
        d_final = subst (_≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (∧₂⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B ∨ C) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (□ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢∨₂ {.Γ_sub} {C} {t} {Δ_sub} {B} Π_sub) Π'@(□⊢ {Γ = Γ'₁} {A = B'} {s = r} {t = δ'} {Δ = Δ'₁} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleDisj2Box accRec (discretePFormula (A ^ s) ((B ∨ C) ^ t))
  where
    handleDisj2Box :
      (∀ m' → m' <Lex (n , mixHeight (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B ∨ C) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s)) ⊢ (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (□⊢ Π'_sub)))
    handleDisj2Box accR (no neq) =
      let (p_no , d_no) = handleDisj2NoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (B ∨ C) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (□⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleDisj2Box accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((□ B') ^ r)
        neq_G = λ eq' → snotz (cong (λ { (_ ∨ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        h-dec = mixHeight-dec-r (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) (□⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
        acc' = accR _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ (r ∘ δ') ]} {Δ' = Δ'₁} degEq (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) Π'_sub wfp wfp'_s acc'
        Γ'₁-A = Γ'₁ - (A ^ s)
        GoalSucc = (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
        sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ (r ∘ δ') ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ (r ∘ δ') ])
        sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ (r ∘ δ') ∷ A ^ s ∷ [])) {refl}
        mix_r = structural sub_left subset-refl mix
        p_rule = □⊢ {Γ_sub ,, Γ'₁-A} {B'} {r} {δ'} {GoalSucc} mix_r
        sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (□ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (□ B') ^ r ]))
        sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((□ B') ^ r ∷ [])) {refl}
        p_reorder = structural sub_left2 subset-refl p_rule
        ant-eq : (Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (□ B') ^ r ]
        ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (□ B') ^ r} {Γ = Γ'₁} neq_G
        p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
               (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
        d_final : δ p' ≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (□⊢ Π'_sub))
        d_final = subst (_≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (□⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B ∨ C) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])} {Δ' = .(Δ'₁ ,, Δ'₂)} {A = A} {s = s}
    degEq (⊢∨₂ {.Γ_sub} {C} {t} {Δ_sub} {B} Π_sub) Π'@(⇒⊢ {Γ₁ = Γ'₁} {B = B'₂} {s = r} {Δ₁ = Δ'₁} {Γ₂ = Γ'₂} {A = B'₁} {Δ₂ = Δ'₂} Π'1 Π'2) wfp wfp'@(wfp'1 , wfp'2) (acc accRec) =
    handleDisj2Impl accRec (discretePFormula (A ^ s) ((B ∨ C) ^ t))
  where
    handleDisj2Impl :
      (∀ m' → m' <Lex (n , mixHeight (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B ∨ C) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])) - (A ^ s)) ⊢ (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂))
          (λ p → δ p ≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (⇒⊢ Π'1 Π'2)))
    handleDisj2Impl accR (no neq) =
      let (p_no , d_no) = handleDisj2NoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (B ∨ C) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])) - (A ^ s)) ⊢ D ,, (Δ'₁ ,, Δ'₂)) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (⇒⊢ Π'1 Π'2))) (sym d_p') d_no
      in (p' , d_final)
    handleDisj2Impl accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((B'₁ ⇒ B'₂) ^ r)
        neq_G = λ eq' → snotz (cong (λ { (_ ∨ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        h-dec1 = mixHeight-dec-r (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) (⇒⊢ Π'1 Π'2) Π'1 (height-subproof-2-l Π'1 Π'2)
        h-dec2 = mixHeight-dec-r (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) (⇒⊢ Π'1 Π'2) Π'2 (height-subproof-2-r Π'1 Π'2)
        acc1 = accR _ (inr (refl , h-dec1))
        acc2 = accR _ (inr (refl , h-dec2))
        (mix1 , dmix1) = Mix {Γ' = Γ'₁ ,, [ B'₂ ^ r ]} {Δ' = Δ'₁} degEq (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) Π'1 wfp wfp'1 acc1
        (mix2 , dmix2) = Mix {Γ' = Γ'₂} {Δ' = [ B'₁ ^ r ] ,, Δ'₂} degEq (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) Π'2 wfp wfp'2 acc2
        Γ'₁-A = Γ'₁ - (A ^ s)
        Γ'₂-A = Γ'₂ - (A ^ s)
        Δ-rem = ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)
        sub_left1 : (Γ_sub ,, ((Γ'₁ ,, [ B'₂ ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B'₂ ^ r ])
        sub_left1 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B'₂ ^ r ∷ A ^ s ∷ [])) {refl}
        mix1_r = structural sub_left1 subset-refl mix1
        sub_right2 : (Δ-rem ,, ([ B'₁ ^ r ] ,, Δ'₂)) ⊆ ([ B'₁ ^ r ] ,, (Δ-rem ,, Δ'₂))
        sub_right2 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ'₂ ∷ []) , (B'₁ ^ r ∷ [])) {refl}
        mix2_r = structural subset-refl sub_right2 mix2
        p_rule = ⇒⊢ {Γ₁ = Γ_sub ,, Γ'₁-A} {B = B'₂} {s = r} {Δ₁ = Δ-rem ,, Δ'₁} {Γ₂ = Γ_sub ,, Γ'₂-A} {A = B'₁} {Δ₂ = Δ-rem ,, Δ'₂} mix1_r mix2_r
        eqAssocL : ((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A) ,, [ (B'₁ ⇒ B'₂) ^ r ]) ≡ (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B'₁ ⇒ B'₂) ^ r ])
        eqAssocL = sym (++-assoc (Γ_sub ,, Γ'₁-A) (Γ_sub ,, Γ'₂-A) [ (B'₁ ⇒ B'₂) ^ r ])
        p_assoc = subst (λ G → G ⊢ (Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) eqAssocL p_rule
        subLeft : (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B'₁ ⇒ B'₂) ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, (Γ'₂-A ,, [ (B'₁ ⇒ B'₂) ^ r ])))
        subLeft = solve ((((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) ++ₑ elm 0)) (var 0 ++ₑ (var 1 ++ₑ (var 2 ++ₑ elm 0))) ((Γ_sub ∷ Γ'₁-A ∷ Γ'₂-A ∷ []) , ((B'₁ ⇒ B'₂) ^ r ∷ [])) {refl}
        subRight : ((Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) ⊆ (Δ-rem ,, (Δ'₁ ,, Δ'₂))
        subRight = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Δ-rem ∷ Δ'₁ ∷ Δ'₂ ∷ []) , []) {refl}
        p_contracted = structural subLeft subRight p_assoc
        eqGamma : (Γ'₁ ,, (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])) - (A ^ s) ≡ Γ'₁-A ,, (Γ'₂-A ,, [ (B'₁ ⇒ B'₂) ^ r ])
        eqGamma = trans (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ'₁ (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ]))
                        (cong (Γ'₁-A ,,_) (lemma-removeAll-cons-neq {A = A ^ s} {B = (B'₁ ⇒ B'₂) ^ r} {Γ = Γ'₂} neq_G))
        p' = subst (λ G → Γ_sub ,, G ⊢ Δ-rem ,, (Δ'₁ ,, Δ'₂)) (sym eqGamma) p_contracted
        cutBound = max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (⇒⊢ Π'1 Π'2))
        dΠ≤cb : δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) ≤ cutBound
        dΠ≤cb = left-≤-max {δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)} {δ (⇒⊢ Π'1 Π'2)}
        dΠ'1≤cb : δ Π'1 ≤ cutBound
        dΠ'1≤cb = left-right-≤-max
        dΠ'2≤cb : δ Π'2 ≤ cutBound
        dΠ'2≤cb = right-right-≤-max
        dmix1' : δ mix1 ≤ cutBound
        dmix1' = ≤-trans dmix1 (max-least dΠ≤cb dΠ'1≤cb)
        dmix2' : δ mix2 ≤ cutBound
        dmix2' = ≤-trans dmix2 (max-least dΠ≤cb dΠ'2≤cb)
        d_mix1_r = structural-preserves-δ sub_left1 subset-refl mix1
        d_mix2_r = structural-preserves-δ subset-refl sub_right2 mix2
        dmix1r' = subst (_≤ cutBound) (sym d_mix1_r) dmix1'
        dmix2r' = subst (_≤ cutBound) (sym d_mix2_r) dmix2'
        dp_rule : δ p_rule ≤ cutBound
        dp_rule = max-least dmix1r' dmix2r'
        dp_assoc = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx eqAssocL p_rule)) dp_rule
        dp_contracted = subst (_≤ cutBound) (sym (structural-preserves-δ subLeft subRight p_assoc)) dp_assoc
        d_final : δ p' ≤ cutBound
        d_final = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym eqGamma)) p_contracted)) dp_contracted
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B ∨ C) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (♢ B') ^ r' ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢∨₂ {.Γ_sub} {C} {t} {Δ_sub} {B} Π_sub) Π'@(♢⊢ {x'} {r'} {Γ'₁} {Δ'₁} {B'} ext' freshΓ' freshΔ' Π'_sub) wfp wfp'@(wf' , wfp'_s) (acc accRec) =
    handleDisj2Dia accRec (discretePFormula (A ^ s) ((B ∨ C) ^ t))
  where
    handleDisj2Dia :
      (∀ m' → m' <Lex (n , mixHeight (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B ∨ C) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s)) ⊢ (([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub)))
    handleDisj2Dia accR (no neq) =
      let (p_no , d_no) = handleDisj2NoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (B ∨ C) ^ t ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B ∨ C) ^ t} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleDisj2Dia accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((♢ B') ^ r')
        neq_G = λ eq' → snotz (cong (λ { (_ ∨ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        Γ'₁-A = Γ'₁ - (A ^ s)
        Δ-rem = ([ (B ∨ C) ^ t ] ,, Δ_sub) - (A ^ s)
        GoalSucc = Δ-rem ,, Δ'₁
        combined = (Γ_sub ,, Γ'₁-A) ,, GoalSucc
        y : Token
        y = freshTokenForRename r' combined Π'_sub
        eigent : Position
        eigent = insertToken x' r'
        t'' : Position
        t'' = substPos x' (singleton-pos y) eigent
        extSTE : IsSingleTokenExt r' eigent x'
        extSTE = mkSingleTokenExt r' x' ext'
        y-fresh-combined : TokenFresh y combined
        y-fresh-combined = freshTokenForRename-fresh r' combined Π'_sub
        y-eigenpos : maxEigenposToken Π'_sub < y
        y-eigenpos = freshTokenForRename-eigenpos r' combined Π'_sub
        y∉r' : y ∉Pos r'
        y∉r' = freshTokenForRename-∉r r' combined Π'_sub
        rename-result = renameEigenpos-♢⊢-premise-gen {r = r'} {t = eigent} {x = x'} {Γ = Γ'₁} {Δ = Δ'₁} {A = B'} Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
        Π'_renamed : Γ'₁ ,, [ B' ^ t'' ] ⊢ Δ'₁
        Π'_renamed = fst rename-result
        ext'' : IsSingleTokenExt r' t'' y
        ext'' = snd rename-result
        δ-eq-renamed : δ Π'_renamed ≡ δ Π'_sub
        δ-eq-renamed = δ-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
        height-eq-renamed : height Π'_renamed ≡ height Π'_sub
        height-eq-renamed = height-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
        wfp'_renamed : WellFormedProof Π'_renamed
        wfp'_renamed = WellFormed-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r' wfp'_s
        h-dec-raw = mixHeight-dec-r (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) (♢⊢ ext' freshΓ' freshΔ' Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
        mixHeight-eq = cong (λ h → height (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) + h) height-eq-renamed
        h-dec = subst (_< mixHeight (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) (♢⊢ ext' freshΓ' freshΔ' Π'_sub)) (sym mixHeight-eq) h-dec-raw
        acc' = accR _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ t'' ]} {Δ' = Δ'₁} degEq (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) Π'_renamed wfp wfp'_renamed acc'
        sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ t'' ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ t'' ])
        sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ t'' ∷ A ^ s ∷ [])) {refl}
        mix_r = structural sub_left subset-refl mix
        t''-eq : t'' ≡ insertToken y r'
        t''-eq = substPos-insertToken-eq x' y r' ext'
        fresh-split = TokenFresh-split (Γ_sub ,, Γ'₁-A) GoalSucc y y-fresh-combined
        freshΓ_new : TokenFresh y (Γ_sub ,, Γ'₁-A)
        freshΓ_new = fst fresh-split
        freshΔ_new : TokenFresh y GoalSucc
        freshΔ_new = snd fresh-split
        mix_transported : (Γ_sub ,, Γ'₁-A) ,, [ B' ^ insertToken y r' ] ⊢ GoalSucc
        mix_transported = subst (λ (p : Position) → (Γ_sub ,, Γ'₁-A) ,, [ B' ^ p ] ⊢ GoalSucc) t''-eq mix_r
        p_dia = ♢⊢ {y} {r'} {Γ_sub ,, Γ'₁-A} {GoalSucc} {B'} y∉r' freshΓ_new freshΔ_new mix_transported
        sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (♢ B') ^ r' ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (♢ B') ^ r' ]))
        sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((♢ B') ^ r' ∷ [])) {refl}
        p_reorder = structural sub_left2 subset-refl p_dia
        ant-eq : (Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s) ≡ Γ'₁-A ,, [ (♢ B') ^ r' ]
        ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (♢ B') ^ r'} {Γ = Γ'₁} neq_G
        p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
        bound-eq : max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ Π'_renamed) ≡ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ Π'_sub)
        bound-eq = cong (λ d → max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) d) δ-eq-renamed
        dmix' : δ mix ≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ Π'_sub)
        dmix' = subst (δ mix ≤_) bound-eq dmix
        d_mix_r = structural-preserves-δ sub_left subset-refl mix
        d_mix_transported : δ mix_transported ≡ δ mix_r
        d_mix_transported = subst-preserves-δ-ctx (cong (λ (p : Position) → (Γ_sub ,, Γ'₁-A) ,, [ B' ^ p ]) t''-eq) mix_r
        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
               (trans (structural-preserves-δ sub_left2 subset-refl p_dia)
               (trans d_mix_transported (d_mix_r)))
        d_final : δ p' ≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))
        d_final = subst (_≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))) (sym d_p') dmix'
      in (p' , d_final)

-- Catch-all for left = ⊢♢
Mix {n = n} {Γ = Γ_sub} {Δ = .([ (♢ B_l) ^ r_l ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (¬ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢♢ {.Γ_sub} {B_l} {r_l} {t_l} {Δ_sub} Π_sub) Π'@(¬⊢ {Γ'₁} {B'} {r} {Δ'₁} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleDiaNeg accRec (discretePFormula (A ^ s) ((♢ B_l) ^ r_l))
  where
    handleDiaNeg :
      (∀ m' → m' <Lex (n , mixHeight (⊢♢ Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((♢ B_l) ^ r_l))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s)) ⊢ (([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢♢ Π_sub)) (δ (¬⊢ Π'_sub)))
    handleDiaNeg accR (no neq) =
      let (p_no , d_no) = handleDiaNoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s) ≡ [ (♢ B_l) ^ r_l ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (♢ B_l) ^ r_l} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢♢ Π_sub)) (δ (¬⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleDiaNeg accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((¬ B') ^ r)
        neq_G = λ eq' → snotz (cong (λ { (♢ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        h-dec = mixHeight-dec-r (⊢♢ Π_sub) (¬⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
        acc' = accR _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ'₁} {Δ' = [ B' ^ r ] ,, Δ'₁} degEq (⊢♢ Π_sub) Π'_sub wfp wfp'_s acc'
        Γ'₁-A = Γ'₁ - (A ^ s)
        Δ-rem = ([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)
        GoalSucc = Δ-rem ,, Δ'₁
        sub_right1 : (Δ-rem ,, ([ B' ^ r ] ,, Δ'₁)) ⊆ ([ B' ^ r ] ,, (Δ-rem ,, Δ'₁))
        sub_right1 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ'₁ ∷ []) , (B' ^ r ∷ [])) {refl}
        mix_r = structural subset-refl sub_right1 mix
        p_rule = ¬⊢ {Γ_sub ,, Γ'₁-A} {B'} {r} {GoalSucc} mix_r
        sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (¬ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (¬ B') ^ r ]))
        sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((¬ B') ^ r ∷ [])) {refl}
        p_reorder = structural sub_left2 subset-refl p_rule
        ant-eq : (Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (¬ B') ^ r ]
        ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (¬ B') ^ r} {Γ = Γ'₁} neq_G
        p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
               (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ subset-refl sub_right1 mix))
        d_final : δ p' ≤ max (δ (⊢♢ Π_sub)) (δ (¬⊢ Π'_sub))
        d_final = subst (_≤ max (δ (⊢♢ Π_sub)) (δ (¬⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (♢ B_l) ^ r_l ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (B' ∧ C') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢♢ {.Γ_sub} {B_l} {r_l} {t_l} {Δ_sub} Π_sub) Π'@(∧₁⊢ {Γ = Γ'₁} {A = B'} {s = r} {Δ = Δ'₁} {B = C'} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleDiaAnd1 accRec (discretePFormula (A ^ s) ((♢ B_l) ^ r_l))
  where
    handleDiaAnd1 :
      (∀ m' → m' <Lex (n , mixHeight (⊢♢ Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((♢ B_l) ^ r_l))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s)) ⊢ (([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢♢ Π_sub)) (δ (∧₁⊢ Π'_sub)))
    handleDiaAnd1 accR (no neq) =
      let (p_no , d_no) = handleDiaNoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s) ≡ [ (♢ B_l) ^ r_l ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (♢ B_l) ^ r_l} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢♢ Π_sub)) (δ (∧₁⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleDiaAnd1 accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((B' ∧ C') ^ r)
        neq_G = λ eq' → snotz (cong (λ { (♢ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        h-dec = mixHeight-dec-r (⊢♢ Π_sub) (∧₁⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
        acc' = accR _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢♢ Π_sub) Π'_sub wfp wfp'_s acc'
        Γ'₁-A = Γ'₁ - (A ^ s)
        GoalSucc = (([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
        sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
        sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
        mix_r = structural sub_left subset-refl mix
        p_rule = ∧₁⊢ {Γ = Γ_sub ,, Γ'₁-A} {A = B'} {s = r} {Δ = GoalSucc} {B = C'} mix_r
        sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (B' ∧ C') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (B' ∧ C') ^ r ]))
        sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((B' ∧ C') ^ r ∷ [])) {refl}
        p_reorder = structural sub_left2 subset-refl p_rule
        ant-eq : (Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (B' ∧ C') ^ r ]
        ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (B' ∧ C') ^ r} {Γ = Γ'₁} neq_G
        p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
               (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
        d_final : δ p' ≤ max (δ (⊢♢ Π_sub)) (δ (∧₁⊢ Π'_sub))
        d_final = subst (_≤ max (δ (⊢♢ Π_sub)) (δ (∧₁⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (♢ B_l) ^ r_l ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (C' ∧ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢♢ {.Γ_sub} {B_l} {r_l} {t_l} {Δ_sub} Π_sub) Π'@(∧₂⊢ {Γ = Γ'₁} {B = B'} {s = r} {Δ = Δ'₁} {A = C'} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleDiaAnd2 accRec (discretePFormula (A ^ s) ((♢ B_l) ^ r_l))
  where
    handleDiaAnd2 :
      (∀ m' → m' <Lex (n , mixHeight (⊢♢ Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((♢ B_l) ^ r_l))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s)) ⊢ (([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢♢ Π_sub)) (δ (∧₂⊢ Π'_sub)))
    handleDiaAnd2 accR (no neq) =
      let (p_no , d_no) = handleDiaNoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s) ≡ [ (♢ B_l) ^ r_l ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (♢ B_l) ^ r_l} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢♢ Π_sub)) (δ (∧₂⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleDiaAnd2 accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((C' ∧ B') ^ r)
        neq_G = λ eq' → snotz (cong (λ { (♢ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        h-dec = mixHeight-dec-r (⊢♢ Π_sub) (∧₂⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
        acc' = accR _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢♢ Π_sub) Π'_sub wfp wfp'_s acc'
        Γ'₁-A = Γ'₁ - (A ^ s)
        GoalSucc = (([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
        sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
        sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
        mix_r = structural sub_left subset-refl mix
        p_rule = ∧₂⊢ {Γ = Γ_sub ,, Γ'₁-A} {B = B'} {s = r} {Δ = GoalSucc} {A = C'} mix_r
        sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (C' ∧ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (C' ∧ B') ^ r ]))
        sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((C' ∧ B') ^ r ∷ [])) {refl}
        p_reorder = structural sub_left2 subset-refl p_rule
        ant-eq : (Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (C' ∧ B') ^ r ]
        ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (C' ∧ B') ^ r} {Γ = Γ'₁} neq_G
        p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
               (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
        d_final : δ p' ≤ max (δ (⊢♢ Π_sub)) (δ (∧₂⊢ Π'_sub))
        d_final = subst (_≤ max (δ (⊢♢ Π_sub)) (δ (∧₂⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (♢ B_l) ^ r_l ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (□ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢♢ {.Γ_sub} {B_l} {r_l} {t_l} {Δ_sub} Π_sub) Π'@(□⊢ {Γ = Γ'₁} {A = B'} {s = r} {t = δ'} {Δ = Δ'₁} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleDiaBox accRec (discretePFormula (A ^ s) ((♢ B_l) ^ r_l))
  where
    handleDiaBox :
      (∀ m' → m' <Lex (n , mixHeight (⊢♢ Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((♢ B_l) ^ r_l))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s)) ⊢ (([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢♢ Π_sub)) (δ (□⊢ Π'_sub)))
    handleDiaBox accR (no neq) =
      let (p_no , d_no) = handleDiaNoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s) ≡ [ (♢ B_l) ^ r_l ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (♢ B_l) ^ r_l} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢♢ Π_sub)) (δ (□⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleDiaBox accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((□ B') ^ r)
        neq_G = λ eq' → snotz (cong (λ { (♢ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        h-dec = mixHeight-dec-r (⊢♢ Π_sub) (□⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
        acc' = accR _ (inr (refl , h-dec))
        (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ (r ∘ δ') ]} {Δ' = Δ'₁} degEq (⊢♢ Π_sub) Π'_sub wfp wfp'_s acc'
        Γ'₁-A = Γ'₁ - (A ^ s)
        GoalSucc = (([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
        sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ (r ∘ δ') ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ (r ∘ δ') ])
        sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ (r ∘ δ') ∷ A ^ s ∷ [])) {refl}
        mix_r = structural sub_left subset-refl mix
        p_rule = □⊢ {Γ_sub ,, Γ'₁-A} {B'} {r} {δ'} {GoalSucc} mix_r
        sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (□ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (□ B') ^ r ]))
        sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((□ B') ^ r ∷ [])) {refl}
        p_reorder = structural sub_left2 subset-refl p_rule
        ant-eq : (Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (□ B') ^ r ]
        ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (□ B') ^ r} {Γ = Γ'₁} neq_G
        p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
        d_p' : δ p' ≡ δ mix
        d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
               (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
        d_final : δ p' ≤ max (δ (⊢♢ Π_sub)) (δ (□⊢ Π'_sub))
        d_final = subst (_≤ max (δ (⊢♢ Π_sub)) (δ (□⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (♢ B_l) ^ r_l ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ r ])} {Δ' = .(Δ'₁ ,, Δ'₂)} {A = A} {s = s}
    degEq (⊢♢ {.Γ_sub} {B_l} {r_l} {t_l} {Δ_sub} Π_sub)
          Π'@(∨⊢ {Γ₁ = Γ'₁} {A = B'} {s = r} {Δ₁ = Δ'₁} {Γ₂ = Γ'₂} {B = C'} {Δ₂ = Δ'₂} Π'1 Π'2) wfp wfp'@(wfp'1 , wfp'2) (acc accRec) =
    handleDiaOr accRec (discretePFormula (A ^ s) ((♢ B_l) ^ r_l))
  where
    handleDiaOr :
      (∀ m' → m' <Lex (n , mixHeight (⊢♢ Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((♢ B_l) ^ r_l))
      → Σ (Γ_sub ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ r ]) - (A ^ s)) ⊢ (([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂))
          (λ p → δ p ≤ max (δ (⊢♢ Π_sub)) (δ (∨⊢ Π'1 Π'2)))
    handleDiaOr accR (no neq) =
      let (p_no , d_no) = handleDiaNoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s) ≡ [ (♢ B_l) ^ r_l ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (♢ B_l) ^ r_l} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ r ]) - (A ^ s)) ⊢ D ,, (Δ'₁ ,, Δ'₂)) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢♢ Π_sub)) (δ (∨⊢ Π'1 Π'2))) (sym d_p') d_no
      in (p' , d_final)
    handleDiaOr accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((B' ∨ C') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (♢ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec1 = mixHeight-dec-r (⊢♢ Π_sub) (∨⊢ Π'1 Π'2) Π'1 (height-subproof-2-l Π'1 Π'2)
          h-dec2 = mixHeight-dec-r (⊢♢ Π_sub) (∨⊢ Π'1 Π'2) Π'2 (height-subproof-2-r Π'1 Π'2)
          acc1 = accR _ (inr (refl , h-dec1))
          acc2 = accR _ (inr (refl , h-dec2))
          (mix1 , dmix1) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢♢ Π_sub) Π'1 wfp wfp'1 acc1
          (mix2 , dmix2) = Mix {Γ' = Γ'₂ ,, [ C' ^ r ]} {Δ' = Δ'₂} degEq (⊢♢ Π_sub) Π'2 wfp wfp'2 acc2
          Γ'₁-A = Γ'₁ - (A ^ s)
          Γ'₂-A = Γ'₂ - (A ^ s)
          Δ-rem = ([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)
          sub_left1 : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
          sub_left1 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
          mix1_r = structural sub_left1 subset-refl mix1
          sub_left2 : (Γ_sub ,, ((Γ'₂ ,, [ C' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₂-A) ,, [ C' ^ r ])
          sub_left2 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₂ ∷ []) , (C' ^ r ∷ A ^ s ∷ [])) {refl}
          mix2_r = structural sub_left2 subset-refl mix2
          p_rule = ∨⊢ {Γ₁ = Γ_sub ,, Γ'₁-A} {A = B'} {s = r} {Δ₁ = Δ-rem ,, Δ'₁} {Γ₂ = Γ_sub ,, Γ'₂-A} {B = C'} {Δ₂ = Δ-rem ,, Δ'₂} mix1_r mix2_r
          eqAssocL : ((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A) ,, [ (B' ∨ C') ^ r ]) ≡ (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B' ∨ C') ^ r ])
          eqAssocL = sym (++-assoc (Γ_sub ,, Γ'₁-A) (Γ_sub ,, Γ'₂-A) [ (B' ∨ C') ^ r ])
          p_assoc = subst (λ G → G ⊢ (Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) eqAssocL p_rule
          subLeft : (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B' ∨ C') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, (Γ'₂-A ,, [ (B' ∨ C') ^ r ])))
          subLeft = solve ((((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) ++ₑ elm 0)) (var 0 ++ₑ (var 1 ++ₑ (var 2 ++ₑ elm 0))) ((Γ_sub ∷ Γ'₁-A ∷ Γ'₂-A ∷ []) , ((B' ∨ C') ^ r ∷ [])) {refl}
          subRight : ((Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) ⊆ (Δ-rem ,, (Δ'₁ ,, Δ'₂))
          subRight = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Δ-rem ∷ Δ'₁ ∷ Δ'₂ ∷ []) , []) {refl}
          p_contracted = structural subLeft subRight p_assoc
          eqGamma : (Γ'₁ ,, (Γ'₂ ,, [ (B' ∨ C') ^ r ])) - (A ^ s) ≡ Γ'₁-A ,, (Γ'₂-A ,, [ (B' ∨ C') ^ r ])
          eqGamma = trans (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ'₁ (Γ'₂ ,, [ (B' ∨ C') ^ r ]))
                          (cong (Γ'₁-A ,,_) (lemma-removeAll-cons-neq {A = A ^ s} {B = (B' ∨ C') ^ r} {Γ = Γ'₂} neq_G))
          p' = subst (λ G → Γ_sub ,, G ⊢ Δ-rem ,, (Δ'₁ ,, Δ'₂)) (sym eqGamma) p_contracted
          cutBound = max (δ (⊢♢ Π_sub)) (δ (∨⊢ Π'1 Π'2))
          dΠ≤cb : δ (⊢♢ Π_sub) ≤ cutBound
          dΠ≤cb = left-≤-max {δ (⊢♢ Π_sub)} {δ (∨⊢ Π'1 Π'2)}
          dΠ'1≤cb : δ Π'1 ≤ cutBound
          dΠ'1≤cb = left-right-≤-max
          dΠ'2≤cb : δ Π'2 ≤ cutBound
          dΠ'2≤cb = right-right-≤-max
          dmix1' : δ mix1 ≤ cutBound
          dmix1' = ≤-trans dmix1 (max-least dΠ≤cb dΠ'1≤cb)
          dmix2' : δ mix2 ≤ cutBound
          dmix2' = ≤-trans dmix2 (max-least dΠ≤cb dΠ'2≤cb)
          d_mix1_r = structural-preserves-δ sub_left1 subset-refl mix1
          d_mix2_r = structural-preserves-δ sub_left2 subset-refl mix2
          dmix1r' = subst (_≤ cutBound) (sym d_mix1_r) dmix1'
          dmix2r' = subst (_≤ cutBound) (sym d_mix2_r) dmix2'
          dp_rule : δ p_rule ≤ cutBound
          dp_rule = max-least dmix1r' dmix2r'
          dp_assoc = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx eqAssocL p_rule)) dp_rule
          dp_contracted = subst (_≤ cutBound) (sym (structural-preserves-δ subLeft subRight p_assoc)) dp_assoc
          d_final : δ p' ≤ cutBound
          d_final = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym eqGamma)) p_contracted)) dp_contracted
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (♢ B_l) ^ r_l ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])} {Δ' = .(Δ'₁ ,, Δ'₂)} {A = A} {s = s}
    degEq (⊢♢ {.Γ_sub} {B_l} {r_l} {t_l} {Δ_sub} Π_sub) Π'@(⇒⊢ {Γ₁ = Γ'₁} {B = B'₂} {s = r} {Δ₁ = Δ'₁} {Γ₂ = Γ'₂} {A = B'₁} {Δ₂ = Δ'₂} Π'1 Π'2) wfp wfp'@(wfp'1 , wfp'2) (acc accRec) =
    handleDiaImpl accRec (discretePFormula (A ^ s) ((♢ B_l) ^ r_l))
  where
    handleDiaImpl :
      (∀ m' → m' <Lex (n , mixHeight (⊢♢ Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((♢ B_l) ^ r_l))
      → Σ (Γ_sub ,, ((Γ'₁ ,, (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])) - (A ^ s)) ⊢ (([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂))
          (λ p → δ p ≤ max (δ (⊢♢ Π_sub)) (δ (⇒⊢ Π'1 Π'2)))
    handleDiaImpl accR (no neq) =
      let (p_no , d_no) = handleDiaNoEq degEq Π_sub Π' wfp wfp' accR neq
          succ-eq : ([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s) ≡ [ (♢ B_l) ^ r_l ] ,, (Δ_sub - (A ^ s))
          succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (♢ B_l) ^ r_l} {Γ = Δ_sub} neq
          p' = subst (λ D → Γ_sub ,, ((Γ'₁ ,, (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])) - (A ^ s)) ⊢ D ,, (Δ'₁ ,, Δ'₂)) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢♢ Π_sub)) (δ (⇒⊢ Π'1 Π'2))) (sym d_p') d_no
      in (p' , d_final)
    handleDiaImpl accR (yes eq) =
      let
        neq_G : (A ^ s) ≢ ((B'₁ ⇒ B'₂) ^ r)
        neq_G = λ eq' → snotz (cong (λ { (♢ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
        h-dec1 = mixHeight-dec-r (⊢♢ Π_sub) (⇒⊢ Π'1 Π'2) Π'1 (height-subproof-2-l Π'1 Π'2)
        h-dec2 = mixHeight-dec-r (⊢♢ Π_sub) (⇒⊢ Π'1 Π'2) Π'2 (height-subproof-2-r Π'1 Π'2)
        acc1 = accR _ (inr (refl , h-dec1))
        acc2 = accR _ (inr (refl , h-dec2))
        (mix1 , dmix1) = Mix {Γ' = Γ'₁ ,, [ B'₂ ^ r ]} {Δ' = Δ'₁} degEq (⊢♢ Π_sub) Π'1 wfp wfp'1 acc1
        (mix2 , dmix2) = Mix {Γ' = Γ'₂} {Δ' = [ B'₁ ^ r ] ,, Δ'₂} degEq (⊢♢ Π_sub) Π'2 wfp wfp'2 acc2
        Γ'₁-A = Γ'₁ - (A ^ s)
        Γ'₂-A = Γ'₂ - (A ^ s)
        Δ-rem = ([ (♢ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)
        sub_left1 : (Γ_sub ,, ((Γ'₁ ,, [ B'₂ ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B'₂ ^ r ])
        sub_left1 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B'₂ ^ r ∷ A ^ s ∷ [])) {refl}
        mix1_r = structural sub_left1 subset-refl mix1
        sub_right2 : (Δ-rem ,, ([ B'₁ ^ r ] ,, Δ'₂)) ⊆ ([ B'₁ ^ r ] ,, (Δ-rem ,, Δ'₂))
        sub_right2 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ'₂ ∷ []) , (B'₁ ^ r ∷ [])) {refl}
        mix2_r = structural subset-refl sub_right2 mix2
        p_rule = ⇒⊢ {Γ₁ = Γ_sub ,, Γ'₁-A} {B = B'₂} {s = r} {Δ₁ = Δ-rem ,, Δ'₁} {Γ₂ = Γ_sub ,, Γ'₂-A} {A = B'₁} {Δ₂ = Δ-rem ,, Δ'₂} mix1_r mix2_r
        eqAssocL : ((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A) ,, [ (B'₁ ⇒ B'₂) ^ r ]) ≡ (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B'₁ ⇒ B'₂) ^ r ])
        eqAssocL = sym (++-assoc (Γ_sub ,, Γ'₁-A) (Γ_sub ,, Γ'₂-A) [ (B'₁ ⇒ B'₂) ^ r ])
        p_assoc = subst (λ G → G ⊢ (Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) eqAssocL p_rule
        subLeft : (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B'₁ ⇒ B'₂) ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, (Γ'₂-A ,, [ (B'₁ ⇒ B'₂) ^ r ])))
        subLeft = solve ((((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) ++ₑ elm 0)) (var 0 ++ₑ (var 1 ++ₑ (var 2 ++ₑ elm 0))) ((Γ_sub ∷ Γ'₁-A ∷ Γ'₂-A ∷ []) , ((B'₁ ⇒ B'₂) ^ r ∷ [])) {refl}
        subRight : ((Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) ⊆ (Δ-rem ,, (Δ'₁ ,, Δ'₂))
        subRight = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Δ-rem ∷ Δ'₁ ∷ Δ'₂ ∷ []) , []) {refl}
        p_contracted = structural subLeft subRight p_assoc
        eqGamma : (Γ'₁ ,, (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])) - (A ^ s) ≡ Γ'₁-A ,, (Γ'₂-A ,, [ (B'₁ ⇒ B'₂) ^ r ])
        eqGamma = trans (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ'₁ (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ]))
                        (cong (Γ'₁-A ,,_) (lemma-removeAll-cons-neq {A = A ^ s} {B = (B'₁ ⇒ B'₂) ^ r} {Γ = Γ'₂} neq_G))
        p' = subst (λ G → Γ_sub ,, G ⊢ Δ-rem ,, (Δ'₁ ,, Δ'₂)) (sym eqGamma) p_contracted
        cutBound = max (δ (⊢♢ Π_sub)) (δ (⇒⊢ Π'1 Π'2))
        dΠ≤cb : δ (⊢♢ Π_sub) ≤ cutBound
        dΠ≤cb = left-≤-max {δ (⊢♢ Π_sub)} {δ (⇒⊢ Π'1 Π'2)}
        dΠ'1≤cb : δ Π'1 ≤ cutBound
        dΠ'1≤cb = left-right-≤-max
        dΠ'2≤cb : δ Π'2 ≤ cutBound
        dΠ'2≤cb = right-right-≤-max
        dmix1' : δ mix1 ≤ cutBound
        dmix1' = ≤-trans dmix1 (max-least dΠ≤cb dΠ'1≤cb)
        dmix2' : δ mix2 ≤ cutBound
        dmix2' = ≤-trans dmix2 (max-least dΠ≤cb dΠ'2≤cb)
        d_mix1_r = structural-preserves-δ sub_left1 subset-refl mix1
        d_mix2_r = structural-preserves-δ subset-refl sub_right2 mix2
        dmix1r' = subst (_≤ cutBound) (sym d_mix1_r) dmix1'
        dmix2r' = subst (_≤ cutBound) (sym d_mix2_r) dmix2'
        dp_rule : δ p_rule ≤ cutBound
        dp_rule = max-least dmix1r' dmix2r'
        dp_assoc = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx eqAssocL p_rule)) dp_rule
        dp_contracted = subst (_≤ cutBound) (sym (structural-preserves-δ subLeft subRight p_assoc)) dp_assoc
        d_final : δ p' ≤ cutBound
        d_final = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym eqGamma)) p_contracted)) dp_contracted
      in (p' , d_final)

-- Catch-all for left = ⊢∧ (two-premise)
Mix {n = n} {Γ = .(Γ_sub₁ ,, Γ_sub₂)} {Δ = .([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂)} {Γ' = .(Γ'₁ ,, [ (¬ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢∧ {Γ₁ = Γ_sub₁} {A = B_l} {s = t} {Δ₁ = Δ_sub₁} {Γ₂ = Γ_sub₂} {B = C_l} {Δ₂ = Δ_sub₂} Π₁ Π₂)
          Π'@(¬⊢ {Γ'₁} {B'} {r} {Δ'₁} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleConjNeg accRec (discretePFormula (A ^ s) ((B_l ∧ C_l) ^ t))
  where
    handleConjNeg :
      (∀ m' → m' <Lex (n , mixHeight (⊢∧ Π₁ Π₂) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B_l ∧ C_l) ^ t))
      → Σ ((Γ_sub₁ ,, Γ_sub₂) ,, ((Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s)) ⊢ (([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢∧ Π₁ Π₂)) (δ (¬⊢ Π'_sub)))
    handleConjNeg accR (no neq) =
      let (p_no , d_no) = handleConjNoEq degEq Π₁ Π₂ Π' wfp wfp' accR neq
          succ-eq : ([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s) ≡ [ (B_l ∧ C_l) ^ t ] ,, ((Δ_sub₁ - (A ^ s)) ,, (Δ_sub₂ - (A ^ s)))
          succ-eq = trans (lemma-removeAll-head-neq {A = A ^ s} {B = (B_l ∧ C_l) ^ t} {Γ = Δ_sub₁ ,, Δ_sub₂} neq)
                          (cong ([ (B_l ∧ C_l) ^ t ] ,,_) (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Δ_sub₁ Δ_sub₂))
          p' = subst (λ D → (Γ_sub₁ ,, Γ_sub₂) ,, ((Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∧ Π₁ Π₂)) (δ (¬⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleConjNeg accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((¬ B') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (_ ∧ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec = mixHeight-dec-r (⊢∧ Π₁ Π₂) (¬⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁} {Δ' = [ B' ^ r ] ,, Δ'₁} degEq (⊢∧ Π₁ Π₂) Π'_sub wfp wfp'_s acc'
          Γ'₁-A = Γ'₁ - (A ^ s)
          Δ-rem = ([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s)
          GoalSucc = Δ-rem ,, Δ'₁
          sub_right1 : (Δ-rem ,, ([ B' ^ r ] ,, Δ'₁)) ⊆ ([ B' ^ r ] ,, (Δ-rem ,, Δ'₁))
          sub_right1 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ'₁ ∷ []) , (B' ^ r ∷ [])) {refl}
          mix_r = structural subset-refl sub_right1 mix
          p_rule = ¬⊢ {(Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A} {B'} {r} {GoalSucc} mix_r
          sub_left2 : (((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, [ (¬ B') ^ r ]) ⊆ ((Γ_sub₁ ,, Γ_sub₂) ,, (Γ'₁-A ,, [ (¬ B') ^ r ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) (((Γ_sub₁ ,, Γ_sub₂) ∷ Γ'₁-A ∷ []) , ((¬ B') ^ r ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_rule
          ant-eq : (Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (¬ B') ^ r ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (¬ B') ^ r} {Γ = Γ'₁} neq_G
          p' = subst (λ G → (Γ_sub₁ ,, Γ_sub₂) ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong ((Γ_sub₁ ,, Γ_sub₂) ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ subset-refl sub_right1 mix))
          d_final : δ p' ≤ max (δ (⊢∧ Π₁ Π₂)) (δ (¬⊢ Π'_sub))
          d_final = subst (_≤ max (δ (⊢∧ Π₁ Π₂)) (δ (¬⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = .(Γ_sub₁ ,, Γ_sub₂)} {Δ = .([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂)} {Γ' = .(Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ r ])} {Δ' = .(Δ'₁ ,, Δ'₂)} {A = A} {s = s}
    degEq (⊢∧ {Γ₁ = Γ_sub₁} {A = B_l} {s = t} {Δ₁ = Δ_sub₁} {Γ₂ = Γ_sub₂} {B = C_l} {Δ₂ = Δ_sub₂} Π₁ Π₂)
          Π'@(∨⊢ {Γ₁ = Γ'₁} {A = B'} {s = r} {Δ₁ = Δ'₁} {Γ₂ = Γ'₂} {B = C'} {Δ₂ = Δ'₂} Π'1 Π'2) wfp wfp'@(wfp'1 , wfp'2) (acc accRec) =
    handleConjOr accRec (discretePFormula (A ^ s) ((B_l ∧ C_l) ^ t))
  where
    handleConjOr :
      (∀ m' → m' <Lex (n , mixHeight (⊢∧ Π₁ Π₂) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B_l ∧ C_l) ^ t))
      → Σ ((Γ_sub₁ ,, Γ_sub₂) ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ r ]) - (A ^ s)) ⊢ (([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂))
          (λ p → δ p ≤ max (δ (⊢∧ Π₁ Π₂)) (δ (∨⊢ Π'1 Π'2)))
    handleConjOr accR (no neq) =
      let (p_no , d_no) = handleConjNoEq degEq Π₁ Π₂ Π' wfp wfp' accR neq
          succ-eq : ([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s) ≡ [ (B_l ∧ C_l) ^ t ] ,, ((Δ_sub₁ - (A ^ s)) ,, (Δ_sub₂ - (A ^ s)))
          succ-eq = trans (lemma-removeAll-head-neq {A = A ^ s} {B = (B_l ∧ C_l) ^ t} {Γ = Δ_sub₁ ,, Δ_sub₂} neq)
                          (cong ([ (B_l ∧ C_l) ^ t ] ,,_) (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Δ_sub₁ Δ_sub₂))
          p' = subst (λ D → (Γ_sub₁ ,, Γ_sub₂) ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ r ]) - (A ^ s)) ⊢ D ,, (Δ'₁ ,, Δ'₂)) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∧ Π₁ Π₂)) (δ (∨⊢ Π'1 Π'2))) (sym d_p') d_no
      in (p' , d_final)
    handleConjOr accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((B' ∨ C') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (_ ∧ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec1 = mixHeight-dec-r (⊢∧ Π₁ Π₂) (∨⊢ Π'1 Π'2) Π'1 (height-subproof-2-l Π'1 Π'2)
          h-dec2 = mixHeight-dec-r (⊢∧ Π₁ Π₂) (∨⊢ Π'1 Π'2) Π'2 (height-subproof-2-r Π'1 Π'2)
          acc1 = accR _ (inr (refl , h-dec1))
          acc2 = accR _ (inr (refl , h-dec2))
          (mix1 , dmix1) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢∧ Π₁ Π₂) Π'1 wfp wfp'1 acc1
          (mix2 , dmix2) = Mix {Γ' = Γ'₂ ,, [ C' ^ r ]} {Δ' = Δ'₂} degEq (⊢∧ Π₁ Π₂) Π'2 wfp wfp'2 acc2
          Γ'₁-A = Γ'₁ - (A ^ s)
          Γ'₂-A = Γ'₂ - (A ^ s)
          Δ-rem = ([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s)
          sub_left1 : ((Γ_sub₁ ,, Γ_sub₂) ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ (((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, [ B' ^ r ])
          sub_left1 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) (((Γ_sub₁ ,, Γ_sub₂) ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
          mix1_r = structural sub_left1 subset-refl mix1
          sub_left2 : ((Γ_sub₁ ,, Γ_sub₂) ,, ((Γ'₂ ,, [ C' ^ r ]) - (A ^ s))) ⊆ (((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₂-A) ,, [ C' ^ r ])
          sub_left2 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) (((Γ_sub₁ ,, Γ_sub₂) ∷ Γ'₂ ∷ []) , (C' ^ r ∷ A ^ s ∷ [])) {refl}
          mix2_r = structural sub_left2 subset-refl mix2
          p_rule = ∨⊢ {Γ₁ = (Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A} {A = B'} {s = r} {Δ₁ = Δ-rem ,, Δ'₁} {Γ₂ = (Γ_sub₁ ,, Γ_sub₂) ,, Γ'₂-A} {B = C'} {Δ₂ = Δ-rem ,, Δ'₂} mix1_r mix2_r
          eqAssocL : (((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₂-A) ,, [ (B' ∨ C') ^ r ]) ≡ ((((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₂-A)) ,, [ (B' ∨ C') ^ r ])
          eqAssocL = sym (++-assoc ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₂-A) [ (B' ∨ C') ^ r ])
          p_assoc = subst (λ G → G ⊢ (Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) eqAssocL p_rule
          subLeft : ((((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₂-A)) ,, [ (B' ∨ C') ^ r ]) ⊆ ((Γ_sub₁ ,, Γ_sub₂) ,, (Γ'₁-A ,, (Γ'₂-A ,, [ (B' ∨ C') ^ r ])))
          subLeft = solve ((((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) ++ₑ elm 0)) (var 0 ++ₑ (var 1 ++ₑ (var 2 ++ₑ elm 0))) (((Γ_sub₁ ,, Γ_sub₂) ∷ Γ'₁-A ∷ Γ'₂-A ∷ []) , ((B' ∨ C') ^ r ∷ [])) {refl}
          subRight : ((Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) ⊆ (Δ-rem ,, (Δ'₁ ,, Δ'₂))
          subRight = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Δ-rem ∷ Δ'₁ ∷ Δ'₂ ∷ []) , []) {refl}
          p_contracted = structural subLeft subRight p_assoc
          eqGamma : (Γ'₁ ,, (Γ'₂ ,, [ (B' ∨ C') ^ r ])) - (A ^ s) ≡ Γ'₁-A ,, (Γ'₂-A ,, [ (B' ∨ C') ^ r ])
          eqGamma = trans (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ'₁ (Γ'₂ ,, [ (B' ∨ C') ^ r ]))
                          (cong (Γ'₁-A ,,_) (lemma-removeAll-cons-neq {A = A ^ s} {B = (B' ∨ C') ^ r} {Γ = Γ'₂} neq_G))
          p' = subst (λ G → (Γ_sub₁ ,, Γ_sub₂) ,, G ⊢ Δ-rem ,, (Δ'₁ ,, Δ'₂)) (sym eqGamma) p_contracted
          cutBound = max (δ (⊢∧ Π₁ Π₂)) (δ (∨⊢ Π'1 Π'2))
          dΠ≤cb : δ (⊢∧ Π₁ Π₂) ≤ cutBound
          dΠ≤cb = left-≤-max {δ (⊢∧ Π₁ Π₂)} {δ (∨⊢ Π'1 Π'2)}
          dΠ'1≤cb : δ Π'1 ≤ cutBound
          dΠ'1≤cb = left-right-≤-max
          dΠ'2≤cb : δ Π'2 ≤ cutBound
          dΠ'2≤cb = right-right-≤-max
          dmix1' : δ mix1 ≤ cutBound
          dmix1' = ≤-trans dmix1 (max-least dΠ≤cb dΠ'1≤cb)
          dmix2' : δ mix2 ≤ cutBound
          dmix2' = ≤-trans dmix2 (max-least dΠ≤cb dΠ'2≤cb)
          d_mix1_r = structural-preserves-δ sub_left1 subset-refl mix1
          d_mix2_r = structural-preserves-δ sub_left2 subset-refl mix2
          dmix1r' = subst (_≤ cutBound) (sym d_mix1_r) dmix1'
          dmix2r' = subst (_≤ cutBound) (sym d_mix2_r) dmix2'
          dp_rule : δ p_rule ≤ cutBound
          dp_rule = max-least dmix1r' dmix2r'
          dp_assoc = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx eqAssocL p_rule)) dp_rule
          dp_contracted = subst (_≤ cutBound) (sym (structural-preserves-δ subLeft subRight p_assoc)) dp_assoc
          d_final : δ p' ≤ cutBound
          d_final = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx (cong ((Γ_sub₁ ,, Γ_sub₂) ,,_) (sym eqGamma)) p_contracted)) dp_contracted
      in (p' , d_final)

Mix {n = n} {Γ = .(Γ_sub₁ ,, Γ_sub₂)} {Δ = .([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂)} {Γ' = .(Γ'₁ ,, Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])} {Δ' = .(Δ'₁ ,, Δ'₂)} {A = A} {s = s}
    degEq (⊢∧ {Γ₁ = Γ_sub₁} {A = B_l} {s = t} {Δ₁ = Δ_sub₁} {Γ₂ = Γ_sub₂} {B = C_l} {Δ₂ = Δ_sub₂} Π₁ Π₂)
          Π'@(⇒⊢ {Γ₁ = Γ'₁} {B = B'₂} {s = r} {Δ₁ = Δ'₁} {Γ₂ = Γ'₂} {A = B'₁} {Δ₂ = Δ'₂} Π'1 Π'2) wfp wfp'@(wfp'1 , wfp'2) (acc accRec) =
    handleConjImpl accRec (discretePFormula (A ^ s) ((B_l ∧ C_l) ^ t))
  where
    handleConjImpl :
      (∀ m' → m' <Lex (n , mixHeight (⊢∧ Π₁ Π₂) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B_l ∧ C_l) ^ t))
      → Σ ((Γ_sub₁ ,, Γ_sub₂) ,, ((Γ'₁ ,, Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ]) - (A ^ s)) ⊢ (([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂))
          (λ p → δ p ≤ max (δ (⊢∧ Π₁ Π₂)) (δ (⇒⊢ Π'1 Π'2)))
    handleConjImpl accR (no neq) =
      let (p_no , d_no) = handleConjNoEq degEq Π₁ Π₂ Π' wfp wfp' accR neq
          succ-eq : ([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s) ≡ [ (B_l ∧ C_l) ^ t ] ,, ((Δ_sub₁ - (A ^ s)) ,, (Δ_sub₂ - (A ^ s)))
          succ-eq = trans (lemma-removeAll-head-neq {A = A ^ s} {B = (B_l ∧ C_l) ^ t} {Γ = Δ_sub₁ ,, Δ_sub₂} neq)
                          (cong ([ (B_l ∧ C_l) ^ t ] ,,_) (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Δ_sub₁ Δ_sub₂))
          p' = subst (λ D → (Γ_sub₁ ,, Γ_sub₂) ,, ((Γ'₁ ,, Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ]) - (A ^ s)) ⊢ D ,, (Δ'₁ ,, Δ'₂)) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, (Δ'₁ ,, Δ'₂)) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∧ Π₁ Π₂)) (δ (⇒⊢ Π'1 Π'2))) (sym d_p') d_no
      in (p' , d_final)
    handleConjImpl accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((B'₁ ⇒ B'₂) ^ r)
          neq_G = λ eq' → snotz (cong (λ { (_ ∧ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec1 = mixHeight-dec-r (⊢∧ Π₁ Π₂) (⇒⊢ Π'1 Π'2) Π'1 (height-subproof-2-l Π'1 Π'2)
          h-dec2 = mixHeight-dec-r (⊢∧ Π₁ Π₂) (⇒⊢ Π'1 Π'2) Π'2 (height-subproof-2-r Π'1 Π'2)
          acc1 = accR _ (inr (refl , h-dec1))
          acc2 = accR _ (inr (refl , h-dec2))
          (mix1 , dmix1) = Mix {Γ' = Γ'₁ ,, [ B'₂ ^ r ]} {Δ' = Δ'₁} degEq (⊢∧ Π₁ Π₂) Π'1 wfp wfp'1 acc1
          (mix2 , dmix2) = Mix {Γ' = Γ'₂} {Δ' = [ B'₁ ^ r ] ,, Δ'₂} degEq (⊢∧ Π₁ Π₂) Π'2 wfp wfp'2 acc2
          Γ'₁-A = Γ'₁ - (A ^ s)
          Γ'₂-A = Γ'₂ - (A ^ s)
          Δ-rem = ([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s)
          sub_left1 : ((Γ_sub₁ ,, Γ_sub₂) ,, ((Γ'₁ ,, [ B'₂ ^ r ]) - (A ^ s))) ⊆ (((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, [ B'₂ ^ r ])
          sub_left1 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) (((Γ_sub₁ ,, Γ_sub₂) ∷ Γ'₁ ∷ []) , (B'₂ ^ r ∷ A ^ s ∷ [])) {refl}
          mix1_r = structural sub_left1 subset-refl mix1
          sub_right2 : (Δ-rem ,, ([ B'₁ ^ r ] ,, Δ'₂)) ⊆ ([ B'₁ ^ r ] ,, (Δ-rem ,, Δ'₂))
          sub_right2 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ'₂ ∷ []) , (B'₁ ^ r ∷ [])) {refl}
          mix2_r = structural subset-refl sub_right2 mix2
          p_rule = ⇒⊢ {Γ₁ = (Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A} {B = B'₂} {s = r} {Δ₁ = Δ-rem ,, Δ'₁} {Γ₂ = (Γ_sub₁ ,, Γ_sub₂) ,, Γ'₂-A} {A = B'₁} {Δ₂ = Δ-rem ,, Δ'₂} mix1_r mix2_r
          eqAssocL : (((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₂-A) ,, [ (B'₁ ⇒ B'₂) ^ r ]) ≡ ((((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₂-A)) ,, [ (B'₁ ⇒ B'₂) ^ r ])
          eqAssocL = sym (++-assoc ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₂-A) [ (B'₁ ⇒ B'₂) ^ r ])
          p_assoc = subst (λ G → G ⊢ (Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) eqAssocL p_rule
          subLeft : ((((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₂-A)) ,, [ (B'₁ ⇒ B'₂) ^ r ]) ⊆ ((Γ_sub₁ ,, Γ_sub₂) ,, (Γ'₁-A ,, (Γ'₂-A ,, [ (B'₁ ⇒ B'₂) ^ r ])))
          subLeft = solve ((((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) ++ₑ elm 0)) (var 0 ++ₑ (var 1 ++ₑ (var 2 ++ₑ elm 0))) (((Γ_sub₁ ,, Γ_sub₂) ∷ Γ'₁-A ∷ Γ'₂-A ∷ []) , ((B'₁ ⇒ B'₂) ^ r ∷ [])) {refl}
          subRight : ((Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) ⊆ (Δ-rem ,, (Δ'₁ ,, Δ'₂))
          subRight = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Δ-rem ∷ Δ'₁ ∷ Δ'₂ ∷ []) , []) {refl}
          p_contracted = structural subLeft subRight p_assoc
          eqGamma : (Γ'₁ ,, (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])) - (A ^ s) ≡ Γ'₁-A ,, (Γ'₂-A ,, [ (B'₁ ⇒ B'₂) ^ r ])
          eqGamma = trans (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ'₁ (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ]))
                          (cong (Γ'₁-A ,,_) (lemma-removeAll-cons-neq {A = A ^ s} {B = (B'₁ ⇒ B'₂) ^ r} {Γ = Γ'₂} neq_G))
          p' = subst (λ G → (Γ_sub₁ ,, Γ_sub₂) ,, G ⊢ Δ-rem ,, (Δ'₁ ,, Δ'₂)) (sym eqGamma) p_contracted
          cutBound = max (δ (⊢∧ Π₁ Π₂)) (δ (⇒⊢ Π'1 Π'2))
          dΠ≤cb : δ (⊢∧ Π₁ Π₂) ≤ cutBound
          dΠ≤cb = left-≤-max {δ (⊢∧ Π₁ Π₂)} {δ (⇒⊢ Π'1 Π'2)}
          dΠ'1≤cb : δ Π'1 ≤ cutBound
          dΠ'1≤cb = left-right-≤-max
          dΠ'2≤cb : δ Π'2 ≤ cutBound
          dΠ'2≤cb = right-right-≤-max
          dmix1' : δ mix1 ≤ cutBound
          dmix1' = ≤-trans dmix1 (max-least dΠ≤cb dΠ'1≤cb)
          dmix2' : δ mix2 ≤ cutBound
          dmix2' = ≤-trans dmix2 (max-least dΠ≤cb dΠ'2≤cb)
          d_mix1_r = structural-preserves-δ sub_left1 subset-refl mix1
          d_mix2_r = structural-preserves-δ subset-refl sub_right2 mix2
          dmix1r' = subst (_≤ cutBound) (sym d_mix1_r) dmix1'
          dmix2r' = subst (_≤ cutBound) (sym d_mix2_r) dmix2'
          dp_rule : δ p_rule ≤ cutBound
          dp_rule = max-least dmix1r' dmix2r'
          dp_assoc = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx eqAssocL p_rule)) dp_rule
          dp_contracted = subst (_≤ cutBound) (sym (structural-preserves-δ subLeft subRight p_assoc)) dp_assoc
          d_final : δ p' ≤ cutBound
          d_final = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx (cong ((Γ_sub₁ ,, Γ_sub₂) ,,_) (sym eqGamma)) p_contracted)) dp_contracted
      in (p' , d_final)

Mix {n = n} {Γ = .(Γ_sub₁ ,, Γ_sub₂)} {Δ = .([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂)} {Γ' = .(Γ'₁ ,, [ (□ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢∧ {Γ₁ = Γ_sub₁} {A = B_l} {s = t} {Δ₁ = Δ_sub₁} {Γ₂ = Γ_sub₂} {B = C_l} {Δ₂ = Δ_sub₂} Π₁ Π₂)
          Π'@(□⊢ {Γ = Γ'₁} {A = B'} {s = r} {t = δ'} {Δ = Δ'₁} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleConjBox accRec (discretePFormula (A ^ s) ((B_l ∧ C_l) ^ t))
  where
    handleConjBox :
      (∀ m' → m' <Lex (n , mixHeight (⊢∧ Π₁ Π₂) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B_l ∧ C_l) ^ t))
      → Σ ((Γ_sub₁ ,, Γ_sub₂) ,, ((Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s)) ⊢ (([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢∧ Π₁ Π₂)) (δ (□⊢ Π'_sub)))
    handleConjBox accR (no neq) =
      let (p_no , d_no) = handleConjNoEq degEq Π₁ Π₂ Π' wfp wfp' accR neq
          succ-eq : ([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s) ≡ [ (B_l ∧ C_l) ^ t ] ,, ((Δ_sub₁ - (A ^ s)) ,, (Δ_sub₂ - (A ^ s)))
          succ-eq = trans (lemma-removeAll-head-neq {A = A ^ s} {B = (B_l ∧ C_l) ^ t} {Γ = Δ_sub₁ ,, Δ_sub₂} neq)
                          (cong ([ (B_l ∧ C_l) ^ t ] ,,_) (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Δ_sub₁ Δ_sub₂))
          p' = subst (λ D → (Γ_sub₁ ,, Γ_sub₂) ,, ((Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∧ Π₁ Π₂)) (δ (□⊢ Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleConjBox accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((□ B') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (_ ∧ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec = mixHeight-dec-r (⊢∧ Π₁ Π₂) (□⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ (r ∘ δ') ]} {Δ' = Δ'₁} degEq (⊢∧ Π₁ Π₂) Π'_sub wfp wfp'_s acc'
          Γ'₁-A = Γ'₁ - (A ^ s)
          GoalSucc = (([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s)) ,, Δ'₁
          sub_left : ((Γ_sub₁ ,, Γ_sub₂) ,, ((Γ'₁ ,, [ B' ^ (r ∘ δ') ]) - (A ^ s))) ⊆ (((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, [ B' ^ (r ∘ δ') ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) (((Γ_sub₁ ,, Γ_sub₂) ∷ Γ'₁ ∷ []) , (B' ^ (r ∘ δ') ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          p_rule = □⊢ {(Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A} {B'} {r} {δ'} {GoalSucc} mix_r
          sub_left2 : (((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, [ (□ B') ^ r ]) ⊆ ((Γ_sub₁ ,, Γ_sub₂) ,, (Γ'₁-A ,, [ (□ B') ^ r ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) (((Γ_sub₁ ,, Γ_sub₂) ∷ Γ'₁-A ∷ []) , ((□ B') ^ r ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_rule
          ant-eq : (Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (□ B') ^ r ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (□ B') ^ r} {Γ = Γ'₁} neq_G
          p' = subst (λ G → (Γ_sub₁ ,, Γ_sub₂) ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong ((Γ_sub₁ ,, Γ_sub₂) ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
          d_final : δ p' ≤ max (δ (⊢∧ Π₁ Π₂)) (δ (□⊢ Π'_sub))
          d_final = subst (_≤ max (δ (⊢∧ Π₁ Π₂)) (δ (□⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = .(Γ_sub₁ ,, Γ_sub₂)} {Δ = .([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂)} {Γ' = .(Γ'₁ ,, [ (♢ B') ^ r' ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢∧ {Γ₁ = Γ_sub₁} {A = B_l} {s = t} {Δ₁ = Δ_sub₁} {Γ₂ = Γ_sub₂} {B = C_l} {Δ₂ = Δ_sub₂} Π₁ Π₂)
          Π'@(♢⊢ {x'} {r'} {Γ'₁} {Δ'₁} {B'} ext' freshΓ' freshΔ' Π'_sub) wfp wfp'@(wf' , wfp'_s) (acc accRec) =
    handleConjDia accRec (discretePFormula (A ^ s) ((B_l ∧ C_l) ^ t))
  where
    handleConjDia :
      (∀ m' → m' <Lex (n , mixHeight (⊢∧ Π₁ Π₂) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B_l ∧ C_l) ^ t))
      → Σ ((Γ_sub₁ ,, Γ_sub₂) ,, ((Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s)) ⊢ (([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢∧ Π₁ Π₂)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub)))
    handleConjDia accR (no neq) =
      let (p_no , d_no) = handleConjNoEq degEq Π₁ Π₂ Π' wfp wfp' accR neq
          succ-eq : ([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s) ≡ [ (B_l ∧ C_l) ^ t ] ,, ((Δ_sub₁ - (A ^ s)) ,, (Δ_sub₂ - (A ^ s)))
          succ-eq = trans (lemma-removeAll-head-neq {A = A ^ s} {B = (B_l ∧ C_l) ^ t} {Γ = Δ_sub₁ ,, Δ_sub₂} neq)
                          (cong ([ (B_l ∧ C_l) ^ t ] ,,_) (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Δ_sub₁ Δ_sub₂))
          p' = subst (λ D → (Γ_sub₁ ,, Γ_sub₂) ,, ((Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s)) ⊢ D ,, Δ'₁) (sym succ-eq) p_no
          d_p' = subst-preserves-δ (cong (_,, Δ'₁) (sym succ-eq)) p_no
          d_final = subst (_≤ max (δ (⊢∧ Π₁ Π₂)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))) (sym d_p') d_no
      in (p' , d_final)
    handleConjDia accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((♢ B') ^ r')
          neq_G = λ eq' → snotz (cong (λ { (_ ∧ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          Γ'₁-A = Γ'₁ - (A ^ s)
          Δ-rem = ([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s)
          GoalSucc = Δ-rem ,, Δ'₁
          combined = ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, GoalSucc
          y : Token
          y = freshTokenForRename r' combined Π'_sub
          eigent : Position
          eigent = insertToken x' r'
          t'' : Position
          t'' = substPos x' (singleton-pos y) eigent
          extSTE : IsSingleTokenExt r' eigent x'
          extSTE = mkSingleTokenExt r' x' ext'
          y-fresh-combined : TokenFresh y combined
          y-fresh-combined = freshTokenForRename-fresh r' combined Π'_sub
          y-eigenpos : maxEigenposToken Π'_sub < y
          y-eigenpos = freshTokenForRename-eigenpos r' combined Π'_sub
          y∉r' : y ∉Pos r'
          y∉r' = freshTokenForRename-∉r r' combined Π'_sub
          rename-result = renameEigenpos-♢⊢-premise-gen {r = r'} {t = eigent} {x = x'} {Γ = Γ'₁} {Δ = Δ'₁} {A = B'} Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
          Π'_renamed : Γ'₁ ,, [ B' ^ t'' ] ⊢ Δ'₁
          Π'_renamed = fst rename-result
          ext'' : IsSingleTokenExt r' t'' y
          ext'' = snd rename-result
          δ-eq-renamed : δ Π'_renamed ≡ δ Π'_sub
          δ-eq-renamed = δ-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
          height-eq-renamed : height Π'_renamed ≡ height Π'_sub
          height-eq-renamed = height-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
          wfp'_renamed : WellFormedProof Π'_renamed
          wfp'_renamed = WellFormed-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r' wfp'_s
          h-dec-raw = mixHeight-dec-r (⊢∧ Π₁ Π₂) (♢⊢ ext' freshΓ' freshΔ' Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          mixHeight-eq = cong (λ h → height (⊢∧ Π₁ Π₂) + h) height-eq-renamed
          h-dec = subst (_< mixHeight (⊢∧ Π₁ Π₂) (♢⊢ ext' freshΓ' freshΔ' Π'_sub)) (sym mixHeight-eq) h-dec-raw
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ t'' ]} {Δ' = Δ'₁} degEq (⊢∧ Π₁ Π₂) Π'_renamed wfp wfp'_renamed acc'
          sub_left : ((Γ_sub₁ ,, Γ_sub₂) ,, ((Γ'₁ ,, [ B' ^ t'' ]) - (A ^ s))) ⊆ (((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, [ B' ^ t'' ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) (((Γ_sub₁ ,, Γ_sub₂) ∷ Γ'₁ ∷ []) , (B' ^ t'' ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          t''-eq : t'' ≡ insertToken y r'
          t''-eq = substPos-insertToken-eq x' y r' ext'
          fresh-split = TokenFresh-split ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) GoalSucc y y-fresh-combined
          freshΓ_new : TokenFresh y ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A)
          freshΓ_new = fst fresh-split
          freshΔ_new : TokenFresh y GoalSucc
          freshΔ_new = snd fresh-split
          mix_transported : ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, [ B' ^ insertToken y r' ] ⊢ GoalSucc
          mix_transported = subst (λ (p : Position) → ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, [ B' ^ p ] ⊢ GoalSucc) t''-eq mix_r
          p_dia = ♢⊢ {y} {r'} {(Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A} {GoalSucc} {B'} y∉r' freshΓ_new freshΔ_new mix_transported
          sub_left2 : (((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, [ (♢ B') ^ r' ]) ⊆ ((Γ_sub₁ ,, Γ_sub₂) ,, (Γ'₁-A ,, [ (♢ B') ^ r' ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) (((Γ_sub₁ ,, Γ_sub₂) ∷ Γ'₁-A ∷ []) , ((♢ B') ^ r' ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_dia
          ant-eq : (Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s) ≡ Γ'₁-A ,, [ (♢ B') ^ r' ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (♢ B') ^ r'} {Γ = Γ'₁} neq_G
          p' = subst (λ G → (Γ_sub₁ ,, Γ_sub₂) ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          bound-eq : max (δ (⊢∧ Π₁ Π₂)) (δ Π'_renamed) ≡ max (δ (⊢∧ Π₁ Π₂)) (δ Π'_sub)
          bound-eq = cong (λ d → max (δ (⊢∧ Π₁ Π₂)) d) δ-eq-renamed
          dmix' : δ mix ≤ max (δ (⊢∧ Π₁ Π₂)) (δ Π'_sub)
          dmix' = subst (δ mix ≤_) bound-eq dmix
          d_mix_r = structural-preserves-δ sub_left subset-refl mix
          d_mix_transported : δ mix_transported ≡ δ mix_r
          d_mix_transported = subst-preserves-δ-ctx (cong (λ (p : Position) → ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'₁-A) ,, [ B' ^ p ]) t''-eq) mix_r
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong ((Γ_sub₁ ,, Γ_sub₂) ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_dia)
                 (trans d_mix_transported (d_mix_r)))
          d_final : δ p' ≤ max (δ (⊢∧ Π₁ Π₂)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))
          d_final = subst (_≤ max (δ (⊢∧ Π₁ Π₂)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))) (sym d_p') dmix'
      in (p' , d_final)
-- Catch-all for left = ⊢⇒
Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (¬ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢⇒ {.Γ_sub} {B_l} {t} {C_l} {Δ_sub} Π_sub)
          Π'@(¬⊢ {Γ'₁} {B'} {r} {Δ'₁} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleImplNeg accRec (discretePFormula (A ^ s) ((B_l ⇒ C_l) ^ t))
  where
    handleImplNeg :
      (∀ m' → m' <Lex (n , mixHeight (⊢⇒ Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B_l ⇒ C_l) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s)) ⊢ (([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢⇒ Π_sub)) (δ (¬⊢ Π'_sub)))
    handleImplNeg accR (no neq) = handleImplNoEq degEq Π_sub Π' wfp wfp' accR neq
    handleImplNeg accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((¬ B') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (_ ⇒ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec = mixHeight-dec-r (⊢⇒ Π_sub) (¬⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁} {Δ' = [ B' ^ r ] ,, Δ'₁} degEq (⊢⇒ Π_sub) Π'_sub wfp wfp'_s acc'
          Γ'₁-A = Γ'₁ - (A ^ s)
          Δ-rem = ([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub) - (A ^ s)
          GoalSucc = Δ-rem ,, Δ'₁
          sub_right1 : (Δ-rem ,, ([ B' ^ r ] ,, Δ'₁)) ⊆ ([ B' ^ r ] ,, (Δ-rem ,, Δ'₁))
          sub_right1 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ'₁ ∷ []) , (B' ^ r ∷ [])) {refl}
          mix_r = structural subset-refl sub_right1 mix
          p_rule = ¬⊢ {Γ_sub ,, Γ'₁-A} {B'} {r} {GoalSucc} mix_r
          sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (¬ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (¬ B') ^ r ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((¬ B') ^ r ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_rule
          ant-eq : (Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (¬ B') ^ r ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (¬ B') ^ r} {Γ = Γ'₁} neq_G
          p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ subset-refl sub_right1 mix))
          d_final : δ p' ≤ max (δ (⊢⇒ Π_sub)) (δ (¬⊢ Π'_sub))
          d_final = subst (_≤ max (δ (⊢⇒ Π_sub)) (δ (¬⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (B' ∧ C') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢⇒ {.Γ_sub} {B_l} {t} {C_l} {Δ_sub} Π_sub)
          Π'@(∧₁⊢ {Γ = Γ'₁} {A = B'} {s = r} {Δ = Δ'₁} {B = C'} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleImplAnd1 accRec (discretePFormula (A ^ s) ((B_l ⇒ C_l) ^ t))
  where
    handleImplAnd1 :
      (∀ m' → m' <Lex (n , mixHeight (⊢⇒ Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B_l ⇒ C_l) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s)) ⊢ (([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢⇒ Π_sub)) (δ (∧₁⊢ Π'_sub)))
    handleImplAnd1 accR (no neq) = handleImplNoEq degEq Π_sub Π' wfp wfp' accR neq
    handleImplAnd1 accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((B' ∧ C') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (_ ⇒ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec = mixHeight-dec-r (⊢⇒ Π_sub) (∧₁⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢⇒ Π_sub) Π'_sub wfp wfp'_s acc'
          Γ'₁-A = Γ'₁ - (A ^ s)
          GoalSucc = (([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
          sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          p_rule = ∧₁⊢ {Γ = Γ_sub ,, Γ'₁-A} {A = B'} {s = r} {Δ = GoalSucc} {B = C'} mix_r
          sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (B' ∧ C') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (B' ∧ C') ^ r ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((B' ∧ C') ^ r ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_rule
          ant-eq : (Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (B' ∧ C') ^ r ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (B' ∧ C') ^ r} {Γ = Γ'₁} neq_G
          p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
          d_final : δ p' ≤ max (δ (⊢⇒ Π_sub)) (δ (∧₁⊢ Π'_sub))
          d_final = subst (_≤ max (δ (⊢⇒ Π_sub)) (δ (∧₁⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (C' ∧ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢⇒ {.Γ_sub} {B_l} {t} {C_l} {Δ_sub} Π_sub)
          Π'@(∧₂⊢ {Γ = Γ'₁} {B = B'} {s = r} {Δ = Δ'₁} {A = C'} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleImplAnd2 accRec (discretePFormula (A ^ s) ((B_l ⇒ C_l) ^ t))
  where
    handleImplAnd2 :
      (∀ m' → m' <Lex (n , mixHeight (⊢⇒ Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B_l ⇒ C_l) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s)) ⊢ (([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢⇒ Π_sub)) (δ (∧₂⊢ Π'_sub)))
    handleImplAnd2 accR (no neq) = handleImplNoEq degEq Π_sub Π' wfp wfp' accR neq
    handleImplAnd2 accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((C' ∧ B') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (_ ⇒ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec = mixHeight-dec-r (⊢⇒ Π_sub) (∧₂⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢⇒ Π_sub) Π'_sub wfp wfp'_s acc'
          Γ'₁-A = Γ'₁ - (A ^ s)
          GoalSucc = (([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
          sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          p_rule = ∧₂⊢ {Γ = Γ_sub ,, Γ'₁-A} {B = B'} {s = r} {Δ = GoalSucc} {A = C'} mix_r
          sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (C' ∧ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (C' ∧ B') ^ r ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((C' ∧ B') ^ r ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_rule
          ant-eq : (Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (C' ∧ B') ^ r ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (C' ∧ B') ^ r} {Γ = Γ'₁} neq_G
          p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
          d_final : δ p' ≤ max (δ (⊢⇒ Π_sub)) (δ (∧₂⊢ Π'_sub))
          d_final = subst (_≤ max (δ (⊢⇒ Π_sub)) (δ (∧₂⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ r ])} {Δ' = .(Δ'₁ ,, Δ'₂)} {A = A} {s = s}
    degEq (⊢⇒ {.Γ_sub} {B_l} {t} {C_l} {Δ_sub} Π_sub)
          Π'@(∨⊢ {Γ₁ = Γ'₁} {A = B'} {s = r} {Δ₁ = Δ'₁} {Γ₂ = Γ'₂} {B = C'} {Δ₂ = Δ'₂} Π'1 Π'2) wfp wfp'@(wfp'1 , wfp'2) (acc accRec) =
    handleImplOr accRec (discretePFormula (A ^ s) ((B_l ⇒ C_l) ^ t))
  where
    handleImplOr :
      (∀ m' → m' <Lex (n , mixHeight (⊢⇒ Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B_l ⇒ C_l) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ r ]) - (A ^ s)) ⊢ (([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂))
          (λ p → δ p ≤ max (δ (⊢⇒ Π_sub)) (δ (∨⊢ Π'1 Π'2)))
    handleImplOr accR (no neq) = handleImplNoEq degEq Π_sub Π' wfp wfp' accR neq
    handleImplOr accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((B' ∨ C') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (_ ⇒ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec1 = mixHeight-dec-r (⊢⇒ Π_sub) (∨⊢ Π'1 Π'2) Π'1 (height-subproof-2-l Π'1 Π'2)
          h-dec2 = mixHeight-dec-r (⊢⇒ Π_sub) (∨⊢ Π'1 Π'2) Π'2 (height-subproof-2-r Π'1 Π'2)
          acc1 = accR _ (inr (refl , h-dec1))
          acc2 = accR _ (inr (refl , h-dec2))
          (mix1 , dmix1) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢⇒ Π_sub) Π'1 wfp wfp'1 acc1
          (mix2 , dmix2) = Mix {Γ' = Γ'₂ ,, [ C' ^ r ]} {Δ' = Δ'₂} degEq (⊢⇒ Π_sub) Π'2 wfp wfp'2 acc2
          Γ'₁-A = Γ'₁ - (A ^ s)
          Γ'₂-A = Γ'₂ - (A ^ s)
          Δ-rem = ([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub) - (A ^ s)
          sub_left1 : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
          sub_left1 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
          mix1_r = structural sub_left1 subset-refl mix1
          sub_left2 : (Γ_sub ,, ((Γ'₂ ,, [ C' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₂-A) ,, [ C' ^ r ])
          sub_left2 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₂ ∷ []) , (C' ^ r ∷ A ^ s ∷ [])) {refl}
          mix2_r = structural sub_left2 subset-refl mix2
          p_rule = ∨⊢ {Γ₁ = Γ_sub ,, Γ'₁-A} {A = B'} {s = r} {Δ₁ = Δ-rem ,, Δ'₁} {Γ₂ = Γ_sub ,, Γ'₂-A} {B = C'} {Δ₂ = Δ-rem ,, Δ'₂} mix1_r mix2_r
          eqAssocL : ((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A) ,, [ (B' ∨ C') ^ r ]) ≡ (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B' ∨ C') ^ r ])
          eqAssocL = sym (++-assoc (Γ_sub ,, Γ'₁-A) (Γ_sub ,, Γ'₂-A) [ (B' ∨ C') ^ r ])
          p_assoc = subst (λ G → G ⊢ (Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) eqAssocL p_rule
          subLeft : (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B' ∨ C') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, (Γ'₂-A ,, [ (B' ∨ C') ^ r ])))
          subLeft = solve ((((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) ++ₑ elm 0)) (var 0 ++ₑ (var 1 ++ₑ (var 2 ++ₑ elm 0))) ((Γ_sub ∷ Γ'₁-A ∷ Γ'₂-A ∷ []) , ((B' ∨ C') ^ r ∷ [])) {refl}
          subRight : ((Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) ⊆ (Δ-rem ,, (Δ'₁ ,, Δ'₂))
          subRight = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Δ-rem ∷ Δ'₁ ∷ Δ'₂ ∷ []) , []) {refl}
          p_contracted = structural subLeft subRight p_assoc
          eqGamma : (Γ'₁ ,, (Γ'₂ ,, [ (B' ∨ C') ^ r ])) - (A ^ s) ≡ Γ'₁-A ,, (Γ'₂-A ,, [ (B' ∨ C') ^ r ])
          eqGamma = trans (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ'₁ (Γ'₂ ,, [ (B' ∨ C') ^ r ]))
                          (cong (Γ'₁-A ,,_) (lemma-removeAll-cons-neq {A = A ^ s} {B = (B' ∨ C') ^ r} {Γ = Γ'₂} neq_G))
          p' = subst (λ G → Γ_sub ,, G ⊢ Δ-rem ,, (Δ'₁ ,, Δ'₂)) (sym eqGamma) p_contracted
          cutBound = max (δ (⊢⇒ Π_sub)) (δ (∨⊢ Π'1 Π'2))
          dΠ≤cb : δ (⊢⇒ Π_sub) ≤ cutBound
          dΠ≤cb = left-≤-max {δ (⊢⇒ Π_sub)} {δ (∨⊢ Π'1 Π'2)}
          dΠ'1≤cb : δ Π'1 ≤ cutBound
          dΠ'1≤cb = left-right-≤-max
          dΠ'2≤cb : δ Π'2 ≤ cutBound
          dΠ'2≤cb = right-right-≤-max
          dmix1' : δ mix1 ≤ cutBound
          dmix1' = ≤-trans dmix1 (max-least dΠ≤cb dΠ'1≤cb)
          dmix2' : δ mix2 ≤ cutBound
          dmix2' = ≤-trans dmix2 (max-least dΠ≤cb dΠ'2≤cb)
          d_mix1_r = structural-preserves-δ sub_left1 subset-refl mix1
          d_mix2_r = structural-preserves-δ sub_left2 subset-refl mix2
          dmix1r' = subst (_≤ cutBound) (sym d_mix1_r) dmix1'
          dmix2r' = subst (_≤ cutBound) (sym d_mix2_r) dmix2'
          dp_rule : δ p_rule ≤ cutBound
          dp_rule = max-least dmix1r' dmix2r'
          dp_assoc = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx eqAssocL p_rule)) dp_rule
          dp_contracted = subst (_≤ cutBound) (sym (structural-preserves-δ subLeft subRight p_assoc)) dp_assoc
          d_final : δ p' ≤ cutBound
          d_final = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym eqGamma)) p_contracted)) dp_contracted
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (□ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢⇒ {.Γ_sub} {B_l} {t} {C_l} {Δ_sub} Π_sub)
          Π'@(□⊢ {Γ = Γ'₁} {A = B'} {s = r} {t = δ'} {Δ = Δ'₁} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleImplBox accRec (discretePFormula (A ^ s) ((B_l ⇒ C_l) ^ t))
  where
    handleImplBox :
      (∀ m' → m' <Lex (n , mixHeight (⊢⇒ Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B_l ⇒ C_l) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s)) ⊢ (([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢⇒ Π_sub)) (δ (□⊢ Π'_sub)))
    handleImplBox accR (no neq) = handleImplNoEq degEq Π_sub Π' wfp wfp' accR neq
    handleImplBox accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((□ B') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (_ ⇒ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec = mixHeight-dec-r (⊢⇒ Π_sub) (□⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ (r ∘ δ') ]} {Δ' = Δ'₁} degEq (⊢⇒ Π_sub) Π'_sub wfp wfp'_s acc'
          Γ'₁-A = Γ'₁ - (A ^ s)
          GoalSucc = (([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
          sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ (r ∘ δ') ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ (r ∘ δ') ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ (r ∘ δ') ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          p_rule = □⊢ {Γ_sub ,, Γ'₁-A} {B'} {r} {δ'} {GoalSucc} mix_r
          sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (□ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (□ B') ^ r ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((□ B') ^ r ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_rule
          ant-eq : (Γ'₁ ,, [ (□ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (□ B') ^ r ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (□ B') ^ r} {Γ = Γ'₁} neq_G
          p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
          d_final : δ p' ≤ max (δ (⊢⇒ Π_sub)) (δ (□⊢ Π'_sub))
          d_final = subst (_≤ max (δ (⊢⇒ Π_sub)) (δ (□⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (♢ B') ^ r' ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢⇒ {.Γ_sub} {B_l} {t} {C_l} {Δ_sub} Π_sub)
          Π'@(♢⊢ {x'} {r'} {Γ'₁} {Δ'₁} {B'} ext' freshΓ' freshΔ' Π'_sub) wfp wfp'@(wf' , wfp'_s) (acc accRec) =
    handleImplDia accRec (discretePFormula (A ^ s) ((B_l ⇒ C_l) ^ t))
  where
    handleImplDia :
      (∀ m' → m' <Lex (n , mixHeight (⊢⇒ Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((B_l ⇒ C_l) ^ t))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s)) ⊢ (([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢⇒ Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub)))
    handleImplDia accR (no neq) = handleImplNoEq degEq Π_sub Π' wfp wfp' accR neq
    handleImplDia accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((♢ B') ^ r')
          neq_G = λ eq' → snotz (cong (λ { (_ ⇒ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          Γ'₁-A = Γ'₁ - (A ^ s)
          Δ-rem = ([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub) - (A ^ s)
          GoalSucc = Δ-rem ,, Δ'₁
          combined = (Γ_sub ,, Γ'₁-A) ,, GoalSucc
          y : Token
          y = freshTokenForRename r' combined Π'_sub
          eigent : Position
          eigent = insertToken x' r'
          t'' : Position
          t'' = substPos x' (singleton-pos y) eigent
          extSTE : IsSingleTokenExt r' eigent x'
          extSTE = mkSingleTokenExt r' x' ext'
          y-fresh-combined : TokenFresh y combined
          y-fresh-combined = freshTokenForRename-fresh r' combined Π'_sub
          y-eigenpos : maxEigenposToken Π'_sub < y
          y-eigenpos = freshTokenForRename-eigenpos r' combined Π'_sub
          y∉r' : y ∉Pos r'
          y∉r' = freshTokenForRename-∉r r' combined Π'_sub
          rename-result = renameEigenpos-♢⊢-premise-gen {r = r'} {t = eigent} {x = x'} {Γ = Γ'₁} {Δ = Δ'₁} {A = B'} Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
          Π'_renamed : Γ'₁ ,, [ B' ^ t'' ] ⊢ Δ'₁
          Π'_renamed = fst rename-result
          ext'' : IsSingleTokenExt r' t'' y
          ext'' = snd rename-result
          δ-eq-renamed : δ Π'_renamed ≡ δ Π'_sub
          δ-eq-renamed = δ-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
          height-eq-renamed : height Π'_renamed ≡ height Π'_sub
          height-eq-renamed = height-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
          wfp'_renamed : WellFormedProof Π'_renamed
          wfp'_renamed = WellFormed-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r' wfp'_s
          h-dec-raw = mixHeight-dec-r (⊢⇒ Π_sub) (♢⊢ ext' freshΓ' freshΔ' Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          mixHeight-eq = cong (λ h → height (⊢⇒ Π_sub) + h) height-eq-renamed
          h-dec = subst (_< mixHeight (⊢⇒ Π_sub) (♢⊢ ext' freshΓ' freshΔ' Π'_sub)) (sym mixHeight-eq) h-dec-raw
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ t'' ]} {Δ' = Δ'₁} degEq (⊢⇒ Π_sub) Π'_renamed wfp wfp'_renamed acc'
          sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ t'' ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ t'' ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ t'' ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          t''-eq : t'' ≡ insertToken y r'
          t''-eq = substPos-insertToken-eq x' y r' ext'
          fresh-split = TokenFresh-split (Γ_sub ,, Γ'₁-A) GoalSucc y y-fresh-combined
          freshΓ_new : TokenFresh y (Γ_sub ,, Γ'₁-A)
          freshΓ_new = fst fresh-split
          freshΔ_new : TokenFresh y GoalSucc
          freshΔ_new = snd fresh-split
          mix_transported : (Γ_sub ,, Γ'₁-A) ,, [ B' ^ insertToken y r' ] ⊢ GoalSucc
          mix_transported = subst (λ (p : Position) → (Γ_sub ,, Γ'₁-A) ,, [ B' ^ p ] ⊢ GoalSucc) t''-eq mix_r
          p_dia = ♢⊢ {y} {r'} {Γ_sub ,, Γ'₁-A} {GoalSucc} {B'} y∉r' freshΓ_new freshΔ_new mix_transported
          sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (♢ B') ^ r' ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (♢ B') ^ r' ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((♢ B') ^ r' ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_dia
          ant-eq : (Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s) ≡ Γ'₁-A ,, [ (♢ B') ^ r' ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (♢ B') ^ r'} {Γ = Γ'₁} neq_G
          p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          bound-eq : max (δ (⊢⇒ Π_sub)) (δ Π'_renamed) ≡ max (δ (⊢⇒ Π_sub)) (δ Π'_sub)
          bound-eq = cong (λ d → max (δ (⊢⇒ Π_sub)) d) δ-eq-renamed
          dmix' : δ mix ≤ max (δ (⊢⇒ Π_sub)) (δ Π'_sub)
          dmix' = subst (δ mix ≤_) bound-eq dmix
          d_mix_r = structural-preserves-δ sub_left subset-refl mix
          d_mix_transported : δ mix_transported ≡ δ mix_r
          d_mix_transported = subst-preserves-δ-ctx (cong (λ (p : Position) → (Γ_sub ,, Γ'₁-A) ,, [ B' ^ p ]) t''-eq) mix_r
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_dia)
                 (trans d_mix_transported (d_mix_r)))
          d_final : δ p' ≤ max (δ (⊢⇒ Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))
          d_final = subst (_≤ max (δ (⊢⇒ Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))) (sym d_p') dmix'
      in (p' , d_final)
-- Catch-all for left = ⊢□ (eigenposition renaming in no-neq branch)
Mix {n = n} {Γ = Γ_sub} {Δ = .([ (□ B_l) ^ r_l ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (¬ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢□ {x_l} {r_l} {.Γ_sub} {Δ_sub} {B_l} ext_l freshΓ_l freshΔ_l Π_sub)
          Π'@(¬⊢ {Γ'₁} {B'} {r} {Δ'₁} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleBoxNeg accRec (discretePFormula (A ^ s) ((□ B_l) ^ r_l))
  where
    handleBoxNeg :
      (∀ m' → m' <Lex (n , mixHeight (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((□ B_l) ^ r_l))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s)) ⊢ (([ (□ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (¬⊢ Π'_sub)))
    handleBoxNeg accR (no neq) = handleBoxNoEq degEq ext_l freshΓ_l freshΔ_l Π_sub Π' wfp wfp' accR neq
    handleBoxNeg accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((¬ B') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (□ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec = mixHeight-dec-r (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) (¬⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁} {Δ' = [ B' ^ r ] ,, Δ'₁} degEq (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π'_sub wfp wfp'_s acc'
          Γ'₁-A = Γ'₁ - (A ^ s)
          Δ-rem = ([ (□ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)
          GoalSucc = Δ-rem ,, Δ'₁
          sub_right1 : (Δ-rem ,, ([ B' ^ r ] ,, Δ'₁)) ⊆ ([ B' ^ r ] ,, (Δ-rem ,, Δ'₁))
          sub_right1 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ'₁ ∷ []) , (B' ^ r ∷ [])) {refl}
          mix_r = structural subset-refl sub_right1 mix
          p_rule = ¬⊢ {Γ_sub ,, Γ'₁-A} {B'} {r} {GoalSucc} mix_r
          sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (¬ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (¬ B') ^ r ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((¬ B') ^ r ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_rule
          ant-eq : (Γ'₁ ,, [ (¬ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (¬ B') ^ r ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (¬ B') ^ r} {Γ = Γ'₁} neq_G
          p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ subset-refl sub_right1 mix))
          d_final : δ p' ≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (¬⊢ Π'_sub))
          d_final = subst (_≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (¬⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (□ B_l) ^ r_l ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (B' ∧ C') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢□ {x_l} {r_l} {.Γ_sub} {Δ_sub} {B_l} ext_l freshΓ_l freshΔ_l Π_sub)
          Π'@(∧₁⊢ {Γ = Γ'₁} {A = B'} {s = r} {Δ = Δ'₁} {B = C'} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleBoxAnd1 accRec (discretePFormula (A ^ s) ((□ B_l) ^ r_l))
  where
    handleBoxAnd1 :
      (∀ m' → m' <Lex (n , mixHeight (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((□ B_l) ^ r_l))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s)) ⊢ (([ (□ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (∧₁⊢ Π'_sub)))
    handleBoxAnd1 accR (no neq) = handleBoxNoEq degEq ext_l freshΓ_l freshΔ_l Π_sub Π' wfp wfp' accR neq
    handleBoxAnd1 accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((B' ∧ C') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (□ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec = mixHeight-dec-r (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) (∧₁⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π'_sub wfp wfp'_s acc'
          Γ'₁-A = Γ'₁ - (A ^ s)
          GoalSucc = (([ (□ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
          sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          p_rule = ∧₁⊢ {Γ = Γ_sub ,, Γ'₁-A} {A = B'} {s = r} {Δ = GoalSucc} {B = C'} mix_r
          sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (B' ∧ C') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (B' ∧ C') ^ r ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((B' ∧ C') ^ r ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_rule
          ant-eq : (Γ'₁ ,, [ (B' ∧ C') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (B' ∧ C') ^ r ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (B' ∧ C') ^ r} {Γ = Γ'₁} neq_G
          p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
          d_final : δ p' ≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (∧₁⊢ Π'_sub))
          d_final = subst (_≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (∧₁⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (□ B_l) ^ r_l ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (C' ∧ B') ^ r ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢□ {x_l} {r_l} {.Γ_sub} {Δ_sub} {B_l} ext_l freshΓ_l freshΔ_l Π_sub)
          Π'@(∧₂⊢ {Γ = Γ'₁} {B = B'} {s = r} {Δ = Δ'₁} {A = C'} Π'_sub) wfp wfp'@wfp'_s (acc accRec) =
    handleBoxAnd2 accRec (discretePFormula (A ^ s) ((□ B_l) ^ r_l))
  where
    handleBoxAnd2 :
      (∀ m' → m' <Lex (n , mixHeight (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((□ B_l) ^ r_l))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s)) ⊢ (([ (□ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (∧₂⊢ Π'_sub)))
    handleBoxAnd2 accR (no neq) = handleBoxNoEq degEq ext_l freshΓ_l freshΔ_l Π_sub Π' wfp wfp' accR neq
    handleBoxAnd2 accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((C' ∧ B') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (□ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec = mixHeight-dec-r (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) (∧₂⊢ Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π'_sub wfp wfp'_s acc'
          Γ'₁-A = Γ'₁ - (A ^ s)
          GoalSucc = (([ (□ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁
          sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          p_rule = ∧₂⊢ {Γ = Γ_sub ,, Γ'₁-A} {B = B'} {s = r} {Δ = GoalSucc} {A = C'} mix_r
          sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (C' ∧ B') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (C' ∧ B') ^ r ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((C' ∧ B') ^ r ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_rule
          ant-eq : (Γ'₁ ,, [ (C' ∧ B') ^ r ]) - (A ^ s) ≡ Γ'₁-A ,, [ (C' ∧ B') ^ r ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (C' ∧ B') ^ r} {Γ = Γ'₁} neq_G
          p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_rule) (structural-preserves-δ sub_left subset-refl mix))
          d_final : δ p' ≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (∧₂⊢ Π'_sub))
          d_final = subst (_≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (∧₂⊢ Π'_sub))) (sym d_p') dmix
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (□ B_l) ^ r_l ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ r ])} {Δ' = .(Δ'₁ ,, Δ'₂)} {A = A} {s = s}
    degEq (⊢□ {x_l} {r_l} {.Γ_sub} {Δ_sub} {B_l} ext_l freshΓ_l freshΔ_l Π_sub)
          Π'@(∨⊢ {Γ₁ = Γ'₁} {A = B'} {s = r} {Δ₁ = Δ'₁} {Γ₂ = Γ'₂} {B = C'} {Δ₂ = Δ'₂} Π'1 Π'2) wfp wfp'@(wfp'1 , wfp'2) (acc accRec) =
    handleBoxOr accRec (discretePFormula (A ^ s) ((□ B_l) ^ r_l))
  where
    handleBoxOr :
      (∀ m' → m' <Lex (n , mixHeight (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((□ B_l) ^ r_l))
      → Σ (Γ_sub ,, ((Γ'₁ ,, Γ'₂ ,, [ (B' ∨ C') ^ r ]) - (A ^ s)) ⊢ (([ (□ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂))
          (λ p → δ p ≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (∨⊢ Π'1 Π'2)))
    handleBoxOr accR (no neq) = handleBoxNoEq degEq ext_l freshΓ_l freshΔ_l Π_sub Π' wfp wfp' accR neq
    handleBoxOr accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((B' ∨ C') ^ r)
          neq_G = λ eq' → snotz (cong (λ { (□ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec1 = mixHeight-dec-r (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) (∨⊢ Π'1 Π'2) Π'1 (height-subproof-2-l Π'1 Π'2)
          h-dec2 = mixHeight-dec-r (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) (∨⊢ Π'1 Π'2) Π'2 (height-subproof-2-r Π'1 Π'2)
          acc1 = accR _ (inr (refl , h-dec1))
          acc2 = accR _ (inr (refl , h-dec2))
          (mix1 , dmix1) = Mix {Γ' = Γ'₁ ,, [ B' ^ r ]} {Δ' = Δ'₁} degEq (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π'1 wfp wfp'1 acc1
          (mix2 , dmix2) = Mix {Γ' = Γ'₂ ,, [ C' ^ r ]} {Δ' = Δ'₂} degEq (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π'2 wfp wfp'2 acc2
          Γ'₁-A = Γ'₁ - (A ^ s)
          Γ'₂-A = Γ'₂ - (A ^ s)
          Δ-rem = ([ (□ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)
          sub_left1 : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ r ])
          sub_left1 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ r ∷ A ^ s ∷ [])) {refl}
          mix1_r = structural sub_left1 subset-refl mix1
          sub_left2 : (Γ_sub ,, ((Γ'₂ ,, [ C' ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₂-A) ,, [ C' ^ r ])
          sub_left2 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₂ ∷ []) , (C' ^ r ∷ A ^ s ∷ [])) {refl}
          mix2_r = structural sub_left2 subset-refl mix2
          p_rule = ∨⊢ {Γ₁ = Γ_sub ,, Γ'₁-A} {A = B'} {s = r} {Δ₁ = Δ-rem ,, Δ'₁} {Γ₂ = Γ_sub ,, Γ'₂-A} {B = C'} {Δ₂ = Δ-rem ,, Δ'₂} mix1_r mix2_r
          eqAssocL : ((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A) ,, [ (B' ∨ C') ^ r ]) ≡ (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B' ∨ C') ^ r ])
          eqAssocL = sym (++-assoc (Γ_sub ,, Γ'₁-A) (Γ_sub ,, Γ'₂-A) [ (B' ∨ C') ^ r ])
          p_assoc = subst (λ G → G ⊢ (Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) eqAssocL p_rule
          subLeft : (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B' ∨ C') ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, (Γ'₂-A ,, [ (B' ∨ C') ^ r ])))
          subLeft = solve ((((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) ++ₑ elm 0)) (var 0 ++ₑ (var 1 ++ₑ (var 2 ++ₑ elm 0))) ((Γ_sub ∷ Γ'₁-A ∷ Γ'₂-A ∷ []) , ((B' ∨ C') ^ r ∷ [])) {refl}
          subRight : ((Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) ⊆ (Δ-rem ,, (Δ'₁ ,, Δ'₂))
          subRight = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Δ-rem ∷ Δ'₁ ∷ Δ'₂ ∷ []) , []) {refl}
          p_contracted = structural subLeft subRight p_assoc
          eqGamma : (Γ'₁ ,, (Γ'₂ ,, [ (B' ∨ C') ^ r ])) - (A ^ s) ≡ Γ'₁-A ,, (Γ'₂-A ,, [ (B' ∨ C') ^ r ])
          eqGamma = trans (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ'₁ (Γ'₂ ,, [ (B' ∨ C') ^ r ]))
                          (cong (Γ'₁-A ,,_) (lemma-removeAll-cons-neq {A = A ^ s} {B = (B' ∨ C') ^ r} {Γ = Γ'₂} neq_G))
          p' = subst (λ G → Γ_sub ,, G ⊢ Δ-rem ,, (Δ'₁ ,, Δ'₂)) (sym eqGamma) p_contracted
          cutBound = max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (∨⊢ Π'1 Π'2))
          dΠ≤cb : δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) ≤ cutBound
          dΠ≤cb = left-≤-max {δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)} {δ (∨⊢ Π'1 Π'2)}
          dΠ'1≤cb : δ Π'1 ≤ cutBound
          dΠ'1≤cb = left-right-≤-max
          dΠ'2≤cb : δ Π'2 ≤ cutBound
          dΠ'2≤cb = right-right-≤-max
          dmix1' : δ mix1 ≤ cutBound
          dmix1' = ≤-trans dmix1 (max-least dΠ≤cb dΠ'1≤cb)
          dmix2' : δ mix2 ≤ cutBound
          dmix2' = ≤-trans dmix2 (max-least dΠ≤cb dΠ'2≤cb)
          d_mix1_r = structural-preserves-δ sub_left1 subset-refl mix1
          d_mix2_r = structural-preserves-δ sub_left2 subset-refl mix2
          dmix1r' = subst (_≤ cutBound) (sym d_mix1_r) dmix1'
          dmix2r' = subst (_≤ cutBound) (sym d_mix2_r) dmix2'
          dp_rule : δ p_rule ≤ cutBound
          dp_rule = max-least dmix1r' dmix2r'
          dp_assoc = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx eqAssocL p_rule)) dp_rule
          dp_contracted = subst (_≤ cutBound) (sym (structural-preserves-δ subLeft subRight p_assoc)) dp_assoc
          d_final : δ p' ≤ cutBound
          d_final = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym eqGamma)) p_contracted)) dp_contracted
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (□ B_l) ^ r_l ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])} {Δ' = .(Δ'₁ ,, Δ'₂)} {A = A} {s = s}
    degEq (⊢□ {x_l} {r_l} {.Γ_sub} {Δ_sub} {B_l} ext_l freshΓ_l freshΔ_l Π_sub)
          Π'@(⇒⊢ {Γ₁ = Γ'₁} {B = B'₂} {s = r} {Δ₁ = Δ'₁} {Γ₂ = Γ'₂} {A = B'₁} {Δ₂ = Δ'₂} Π'1 Π'2) wfp wfp'@(wfp'1 , wfp'2) (acc accRec) =
    handleBoxImpl accRec (discretePFormula (A ^ s) ((□ B_l) ^ r_l))
  where
    handleBoxImpl :
      (∀ m' → m' <Lex (n , mixHeight (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((□ B_l) ^ r_l))
      → Σ (Γ_sub ,, ((Γ'₁ ,, Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ]) - (A ^ s)) ⊢ (([ (□ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, (Δ'₁ ,, Δ'₂))
          (λ p → δ p ≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (⇒⊢ Π'1 Π'2)))
    handleBoxImpl accR (no neq) = handleBoxNoEq degEq ext_l freshΓ_l freshΔ_l Π_sub Π' wfp wfp' accR neq
    handleBoxImpl accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((B'₁ ⇒ B'₂) ^ r)
          neq_G = λ eq' → snotz (cong (λ { (□ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          h-dec1 = mixHeight-dec-r (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) (⇒⊢ Π'1 Π'2) Π'1 (height-subproof-2-l Π'1 Π'2)
          h-dec2 = mixHeight-dec-r (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) (⇒⊢ Π'1 Π'2) Π'2 (height-subproof-2-r Π'1 Π'2)
          acc1 = accR _ (inr (refl , h-dec1))
          acc2 = accR _ (inr (refl , h-dec2))
          (mix1 , dmix1) = Mix {Γ' = Γ'₁ ,, [ B'₂ ^ r ]} {Δ' = Δ'₁} degEq (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π'1 wfp wfp'1 acc1
          (mix2 , dmix2) = Mix {Γ' = Γ'₂} {Δ' = [ B'₁ ^ r ] ,, Δ'₂} degEq (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π'2 wfp wfp'2 acc2
          Γ'₁-A = Γ'₁ - (A ^ s)
          Γ'₂-A = Γ'₂ - (A ^ s)
          Δ-rem = ([ (□ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)
          sub_left1 : (Γ_sub ,, ((Γ'₁ ,, [ B'₂ ^ r ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B'₂ ^ r ])
          sub_left1 = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B'₂ ^ r ∷ A ^ s ∷ [])) {refl}
          mix1_r = structural sub_left1 subset-refl mix1
          sub_right2 : (Δ-rem ,, ([ B'₁ ^ r ] ,, Δ'₂)) ⊆ ([ B'₁ ^ r ] ,, (Δ-rem ,, Δ'₂))
          sub_right2 = solve (var 0 ++ₑ (elm 0 ++ₑ var 1)) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ-rem ∷ Δ'₂ ∷ []) , (B'₁ ^ r ∷ [])) {refl}
          mix2_r = structural subset-refl sub_right2 mix2
          p_rule = ⇒⊢ {Γ₁ = Γ_sub ,, Γ'₁-A} {B = B'₂} {s = r} {Δ₁ = Δ-rem ,, Δ'₁} {Γ₂ = Γ_sub ,, Γ'₂-A} {A = B'₁} {Δ₂ = Δ-rem ,, Δ'₂} mix1_r mix2_r
          eqAssocL : ((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A) ,, [ (B'₁ ⇒ B'₂) ^ r ]) ≡ (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B'₁ ⇒ B'₂) ^ r ])
          eqAssocL = sym (++-assoc (Γ_sub ,, Γ'₁-A) (Γ_sub ,, Γ'₂-A) [ (B'₁ ⇒ B'₂) ^ r ])
          p_assoc = subst (λ G → G ⊢ (Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) eqAssocL p_rule
          subLeft : (((Γ_sub ,, Γ'₁-A) ,, (Γ_sub ,, Γ'₂-A)) ,, [ (B'₁ ⇒ B'₂) ^ r ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, (Γ'₂-A ,, [ (B'₁ ⇒ B'₂) ^ r ])))
          subLeft = solve ((((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) ++ₑ elm 0)) (var 0 ++ₑ (var 1 ++ₑ (var 2 ++ₑ elm 0))) ((Γ_sub ∷ Γ'₁-A ∷ Γ'₂-A ∷ []) , ((B'₁ ⇒ B'₂) ^ r ∷ [])) {refl}
          subRight : ((Δ-rem ,, Δ'₁) ,, (Δ-rem ,, Δ'₂)) ⊆ (Δ-rem ,, (Δ'₁ ,, Δ'₂))
          subRight = solve ((var 0 ++ₑ var 1) ++ₑ (var 0 ++ₑ var 2)) (var 0 ++ₑ (var 1 ++ₑ var 2)) ((Δ-rem ∷ Δ'₁ ∷ Δ'₂ ∷ []) , []) {refl}
          p_contracted = structural subLeft subRight p_assoc
          eqGamma : (Γ'₁ ,, (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ])) - (A ^ s) ≡ Γ'₁-A ,, (Γ'₂-A ,, [ (B'₁ ⇒ B'₂) ^ r ])
          eqGamma = trans (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Γ'₁ (Γ'₂ ,, [ (B'₁ ⇒ B'₂) ^ r ]))
                          (cong (Γ'₁-A ,,_) (lemma-removeAll-cons-neq {A = A ^ s} {B = (B'₁ ⇒ B'₂) ^ r} {Γ = Γ'₂} neq_G))
          p' = subst (λ G → Γ_sub ,, G ⊢ Δ-rem ,, (Δ'₁ ,, Δ'₂)) (sym eqGamma) p_contracted
          cutBound = max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (⇒⊢ Π'1 Π'2))
          dΠ≤cb : δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) ≤ cutBound
          dΠ≤cb = left-≤-max {δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)} {δ (⇒⊢ Π'1 Π'2)}
          dΠ'1≤cb : δ Π'1 ≤ cutBound
          dΠ'1≤cb = left-right-≤-max
          dΠ'2≤cb : δ Π'2 ≤ cutBound
          dΠ'2≤cb = right-right-≤-max
          dmix1' : δ mix1 ≤ cutBound
          dmix1' = ≤-trans dmix1 (max-least dΠ≤cb dΠ'1≤cb)
          dmix2' : δ mix2 ≤ cutBound
          dmix2' = ≤-trans dmix2 (max-least dΠ≤cb dΠ'2≤cb)
          d_mix1_r = structural-preserves-δ sub_left1 subset-refl mix1
          d_mix2_r = structural-preserves-δ subset-refl sub_right2 mix2
          dmix1r' = subst (_≤ cutBound) (sym d_mix1_r) dmix1'
          dmix2r' = subst (_≤ cutBound) (sym d_mix2_r) dmix2'
          dp_rule : δ p_rule ≤ cutBound
          dp_rule = max-least dmix1r' dmix2r'
          dp_assoc = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx eqAssocL p_rule)) dp_rule
          dp_contracted = subst (_≤ cutBound) (sym (structural-preserves-δ subLeft subRight p_assoc)) dp_assoc
          d_final : δ p' ≤ cutBound
          d_final = subst (_≤ cutBound) (sym (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym eqGamma)) p_contracted)) dp_contracted
      in (p' , d_final)

Mix {n = n} {Γ = Γ_sub} {Δ = .([ (□ B_l) ^ r_l ] ,, Δ_sub)} {Γ' = .(Γ'₁ ,, [ (♢ B') ^ r' ])} {Δ' = Δ'₁} {A = A} {s = s}
    degEq (⊢□ {x_l} {r_l} {.Γ_sub} {Δ_sub} {B_l} ext_l freshΓ_l freshΔ_l Π_sub)
          Π'@(♢⊢ {x'_r} {r'} {Γ'₁} {Δ'₁} {B'} ext' freshΓ' freshΔ' Π'_sub) wfp wfp'@(wf' , wfp'_s) (acc accRec) =
    handleBoxDia accRec (discretePFormula (A ^ s) ((□ B_l) ^ r_l))
  where
    handleBoxDia :
      (∀ m' → m' <Lex (n , mixHeight (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π') → Acc _<Lex_ m')
      → Dec ((A ^ s) ≡ ((□ B_l) ^ r_l))
      → Σ (Γ_sub ,, ((Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s)) ⊢ (([ (□ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)) ,, Δ'₁)
          (λ p → δ p ≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub)))
    handleBoxDia accR (no neq) = handleBoxNoEq degEq ext_l freshΓ_l freshΔ_l Π_sub Π' wfp wfp' accR neq
    handleBoxDia accR (yes eq) =
      let neq_G : (A ^ s) ≢ ((♢ B') ^ r')
          neq_G = λ eq' → snotz (cong (λ { (□ _) → 1 ; _ → 0 }) (cong PFormula.form (sym eq ∙ eq')))
          Γ'₁-A = Γ'₁ - (A ^ s)
          Δ-rem = ([ (□ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s)
          GoalSucc = Δ-rem ,, Δ'₁
          combined = (Γ_sub ,, Γ'₁-A) ,, GoalSucc
          y : Token
          y = freshTokenForRename r' combined Π'_sub
          eigent : Position
          eigent = insertToken x'_r r'
          t'' : Position
          t'' = substPos x'_r (singleton-pos y) eigent
          extSTE : IsSingleTokenExt r' eigent x'_r
          extSTE = mkSingleTokenExt r' x'_r ext'
          y-fresh-combined : TokenFresh y combined
          y-fresh-combined = freshTokenForRename-fresh r' combined Π'_sub
          y-eigenpos : maxEigenposToken Π'_sub < y
          y-eigenpos = freshTokenForRename-eigenpos r' combined Π'_sub
          y∉r' : y ∉Pos r'
          y∉r' = freshTokenForRename-∉r r' combined Π'_sub
          rename-result = renameEigenpos-♢⊢-premise-gen {r = r'} {t = eigent} {x = x'_r} {Γ = Γ'₁} {Δ = Δ'₁} {A = B'} Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
          Π'_renamed : Γ'₁ ,, [ B' ^ t'' ] ⊢ Δ'₁
          Π'_renamed = fst rename-result
          ext'' : IsSingleTokenExt r' t'' y
          ext'' = snd rename-result
          δ-eq-renamed : δ Π'_renamed ≡ δ Π'_sub
          δ-eq-renamed = δ-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
          height-eq-renamed : height Π'_renamed ≡ height Π'_sub
          height-eq-renamed = height-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r'
          wfp'_renamed : WellFormedProof Π'_renamed
          wfp'_renamed = WellFormed-renameEigenpos-♢⊢-premise-gen Π'_sub extSTE freshΓ' freshΔ' wf' y y-eigenpos y∉r' wfp'_s
          h-dec-raw = mixHeight-dec-r (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) (♢⊢ ext' freshΓ' freshΔ' Π'_sub) Π'_sub (height-subproof-1 Π'_sub)
          mixHeight-eq = cong (λ h → height (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) + h) height-eq-renamed
          h-dec = subst (_< mixHeight (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) (♢⊢ ext' freshΓ' freshΔ' Π'_sub)) (sym mixHeight-eq) h-dec-raw
          acc' = accR _ (inr (refl , h-dec))
          (mix , dmix) = Mix {Γ' = Γ'₁ ,, [ B' ^ t'' ]} {Δ' = Δ'₁} degEq (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π'_renamed wfp wfp'_renamed acc'
          sub_left : (Γ_sub ,, ((Γ'₁ ,, [ B' ^ t'' ]) - (A ^ s))) ⊆ ((Γ_sub ,, Γ'₁-A) ,, [ B' ^ t'' ])
          sub_left = solve (var 0 ++ₑ rem (var 1 ++ₑ elm 0) 1) ((var 0 ++ₑ rem (var 1) 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'₁ ∷ []) , (B' ^ t'' ∷ A ^ s ∷ [])) {refl}
          mix_r = structural sub_left subset-refl mix
          t''-eq : t'' ≡ insertToken y r'
          t''-eq = substPos-insertToken-eq x'_r y r' ext'
          fresh-split = TokenFresh-split (Γ_sub ,, Γ'₁-A) GoalSucc y y-fresh-combined
          freshΓ_new : TokenFresh y (Γ_sub ,, Γ'₁-A)
          freshΓ_new = fst fresh-split
          freshΔ_new : TokenFresh y GoalSucc
          freshΔ_new = snd fresh-split
          mix_transported : (Γ_sub ,, Γ'₁-A) ,, [ B' ^ insertToken y r' ] ⊢ GoalSucc
          mix_transported = subst (λ (p : Position) → (Γ_sub ,, Γ'₁-A) ,, [ B' ^ p ] ⊢ GoalSucc) t''-eq mix_r
          p_dia = ♢⊢ {y} {r'} {Γ_sub ,, Γ'₁-A} {GoalSucc} {B'} y∉r' freshΓ_new freshΔ_new mix_transported
          sub_left2 : ((Γ_sub ,, Γ'₁-A) ,, [ (♢ B') ^ r' ]) ⊆ (Γ_sub ,, (Γ'₁-A ,, [ (♢ B') ^ r' ]))
          sub_left2 = solve ((var 0 ++ₑ var 1) ++ₑ elm 0) (var 0 ++ₑ (var 1 ++ₑ elm 0)) ((Γ_sub ∷ Γ'₁-A ∷ []) , ((♢ B') ^ r' ∷ [])) {refl}
          p_reorder = structural sub_left2 subset-refl p_dia
          ant-eq : (Γ'₁ ,, [ (♢ B') ^ r' ]) - (A ^ s) ≡ Γ'₁-A ,, [ (♢ B') ^ r' ]
          ant-eq = lemma-removeAll-cons-neq {A = A ^ s} {B = (♢ B') ^ r'} {Γ = Γ'₁} neq_G
          p' = subst (λ G → Γ_sub ,, G ⊢ GoalSucc) (sym ant-eq) p_reorder
          bound-eq : max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ Π'_renamed) ≡ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ Π'_sub)
          bound-eq = cong (λ d → max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) d) δ-eq-renamed
          dmix' : δ mix ≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ Π'_sub)
          dmix' = subst (δ mix ≤_) bound-eq dmix
          d_mix_r = structural-preserves-δ sub_left subset-refl mix
          d_mix_transported : δ mix_transported ≡ δ mix_r
          d_mix_transported = subst-preserves-δ-ctx (cong (λ (p : Position) → (Γ_sub ,, Γ'₁-A) ,, [ B' ^ p ]) t''-eq) mix_r
          d_p' : δ p' ≡ δ mix
          d_p' = trans (subst-preserves-δ-ctx (cong (Γ_sub ,,_) (sym ant-eq)) p_reorder)
                 (trans (structural-preserves-δ sub_left2 subset-refl p_dia)
                 (trans d_mix_transported (d_mix_r)))
          d_final : δ p' ≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))
          d_final = subst (_≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ (♢⊢ ext' freshΓ' freshΔ' Π'_sub))) (sym d_p') dmix'
      in (p' , d_final)
handleNegNoEq {Γ_sub = Γ_sub} {B = B} {t = t} {Δ_sub = Δ_sub}
              {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
              degEq Π_sub Π' wfp wfp' accRec neq =
  let h-dec = mixHeight-dec-l (⊢¬ Π_sub) Π_sub Π' (height-subproof-1 Π_sub)
      acc' = accRec _ (inr (refl , h-dec))
      (mix , dmix) = Mix {Γ = Γ_sub ,, [ B ^ t ]} {Δ = Δ_sub} degEq Π_sub Π' wfp wfp' acc'
      Γ'-rem = Γ' - (A ^ s)
      Δ_sub-rem = Δ_sub - (A ^ s)
      sub_left : ((Γ_sub ,, [ B ^ t ]) ,, Γ'-rem) ⊆ ((Γ_sub ,, Γ'-rem) ,, [ B ^ t ])
      sub_left = solve ((var 0 ++ₑ elm 0) ++ₑ var 1) ((var 0 ++ₑ var 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'-rem ∷ []) , (B ^ t ∷ [])) {refl}
      mix_r = structural sub_left subset-refl mix
      p_neg = ⊢¬ {Γ = Γ_sub ,, Γ'-rem} {A = B} {s = t} {Δ = Δ_sub-rem ,, Δ'} mix_r
      sub_right : ([ (¬ B) ^ t ] ,, (Δ_sub-rem ,, Δ')) ⊆ (([ (¬ B) ^ t ] ,, Δ_sub-rem) ,, Δ')
      sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((elm 0 ++ₑ var 0) ++ₑ var 1) ((Δ_sub-rem ∷ Δ' ∷ []) , ((¬ B) ^ t ∷ [])) {refl}
      p' = structural subset-refl sub_right p_neg
      d_p' : δ p' ≡ δ mix
      d_p' = trans (structural-preserves-δ subset-refl sub_right p_neg)
             (structural-preserves-δ sub_left subset-refl mix)
      d_final : δ p' ≤ max (δ (⊢¬ Π_sub)) (δ Π')
      d_final = subst (_≤ max (δ (⊢¬ Π_sub)) (δ Π')) (sym d_p') dmix
  in (p' , d_final)

-- =============================================================================
-- Public wrapper used by CutElimination.agda
-- =============================================================================

mix : ∀ {n} {Γ Δ Γ' Δ' : Ctx} {A : Formula} {s : Position}
    → degree A ≡ n
    → (Π : Γ ⊢ Δ)
    → (Π' : Γ' ⊢ Δ')
    → δ Π ≤ n
    → δ Π' ≤ n
    → Σ (Γ ,, Γ' - (A ^ s) ⊢ Δ - (A ^ s) ,, Δ') (λ p → δ p ≤ n)
mix {n} degEq Π Π' dΠ≤n dΠ'≤n =
  let
    Π-wf = makeWellFormed Π
    Π'-wf = makeWellFormed Π'
    wfp = makeWellFormed-WellFormed Π
    wfp' = makeWellFormed-WellFormed Π'
    result = Mix degEq Π-wf Π'-wf wfp wfp' (<Lex-wf (n , mixHeight Π-wf Π'-wf))
    p = fst result
    dp = snd result
    dp' : δ p ≤ max (δ Π) (δ Π')
    dp' = subst (λ x → δ p ≤ max x (δ Π'))
            (δ-makeWellFormed Π)
            (subst (λ x → δ p ≤ max (δ Π-wf) x) (δ-makeWellFormed Π') dp)
    dp≤n : δ p ≤ n
    dp≤n = ≤-trans dp' (max-least dΠ≤n dΠ'≤n)
  in
  p , dp≤n

handleDisj1NoEq {Γ_sub = Γ_sub} {B = B} {t = t} {Δ_sub = Δ_sub} {C = C}
                {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
                degEq Π_sub Π' wfp wfp' accRec neq =
  let h-dec = mixHeight-dec-l (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub) Π_sub Π' (height-subproof-1 Π_sub)
      acc' = accRec _ (inr (refl , h-dec))
      (mix , dmix) = Mix {Γ = Γ_sub} {Δ = [ B ^ t ] ,, Δ_sub} degEq Π_sub Π' wfp wfp' acc'
      Γ'-rem = Γ' - (A ^ s)
      Δ_sub-rem = Δ_sub - (A ^ s)
      succ-split : ([ B ^ t ] ,, Δ_sub) - (A ^ s) ≡ ([ B ^ t ] - (A ^ s)) ,, Δ_sub-rem
      succ-split = S4dot2.CutElimination.Base.removeAll-++ (A ^ s) [ B ^ t ] Δ_sub
      mix_split = subst (λ D → Γ_sub ,, Γ'-rem ⊢ D ,, Δ') succ-split mix
      sub_succ : ((([ B ^ t ] - (A ^ s)) ,, Δ_sub-rem) ,, Δ') ⊆ ([ B ^ t ] ,, (Δ_sub-rem ,, Δ'))
      sub_succ = solve ((rem (elm 0) 1 ++ₑ var 0) ++ₑ var 1) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ_sub-rem ∷ Δ' ∷ []) , (B ^ t ∷ A ^ s ∷ [])) {refl}
      mix_w = structural subset-refl sub_succ mix_split
      p_disj = ⊢∨₁ {Γ_sub ,, Γ'-rem} {B} {t} {Δ_sub-rem ,, Δ'} {C} mix_w
      sub_right : ([ (B ∨ C) ^ t ] ,, (Δ_sub-rem ,, Δ')) ⊆ (([ (B ∨ C) ^ t ] ,, Δ_sub-rem) ,, Δ')
      sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((elm 0 ++ₑ var 0) ++ₑ var 1) ((Δ_sub-rem ∷ Δ' ∷ []) , ((B ∨ C) ^ t ∷ [])) {refl}
      p' = structural subset-refl sub_right p_disj
      d_p' : δ p' ≡ δ mix
      d_p' = trans (structural-preserves-δ subset-refl sub_right p_disj)
             (trans (structural-preserves-δ subset-refl sub_succ mix_split)
             (subst-preserves-δ (cong (_,, Δ') succ-split) mix))
      d_final : δ p' ≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ Π')
      d_final = subst (_≤ max (δ (⊢∨₁ {Γ = Γ_sub} {A = B} {s = t} {Δ = Δ_sub} {B = C} Π_sub)) (δ Π')) (sym d_p') dmix
  in (p' , d_final)

handleDisj2NoEq {Γ_sub = Γ_sub} {C = C} {t = t} {Δ_sub = Δ_sub} {B = B}
                {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
                degEq Π_sub Π' wfp wfp' accRec neq =
  let h-dec = mixHeight-dec-l (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub) Π_sub Π' (height-subproof-1 Π_sub)
      acc' = accRec _ (inr (refl , h-dec))
      (mix , dmix) = Mix {Γ = Γ_sub} {Δ = [ C ^ t ] ,, Δ_sub} degEq Π_sub Π' wfp wfp' acc'
      Γ'-rem = Γ' - (A ^ s)
      Δ_sub-rem = Δ_sub - (A ^ s)
      succ-split : ([ C ^ t ] ,, Δ_sub) - (A ^ s) ≡ ([ C ^ t ] - (A ^ s)) ,, Δ_sub-rem
      succ-split = S4dot2.CutElimination.Base.removeAll-++ (A ^ s) [ C ^ t ] Δ_sub
      mix_split = subst (λ D → Γ_sub ,, Γ'-rem ⊢ D ,, Δ') succ-split mix
      sub_succ : ((([ C ^ t ] - (A ^ s)) ,, Δ_sub-rem) ,, Δ') ⊆ ([ C ^ t ] ,, (Δ_sub-rem ,, Δ'))
      sub_succ = solve ((rem (elm 0) 1 ++ₑ var 0) ++ₑ var 1) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ_sub-rem ∷ Δ' ∷ []) , (C ^ t ∷ A ^ s ∷ [])) {refl}
      mix_w = structural subset-refl sub_succ mix_split
      p_disj = ⊢∨₂ {Γ_sub ,, Γ'-rem} {C} {t} {Δ_sub-rem ,, Δ'} {B} mix_w
      sub_right : ([ (B ∨ C) ^ t ] ,, (Δ_sub-rem ,, Δ')) ⊆ (([ (B ∨ C) ^ t ] ,, Δ_sub-rem) ,, Δ')
      sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((elm 0 ++ₑ var 0) ++ₑ var 1) ((Δ_sub-rem ∷ Δ' ∷ []) , ((B ∨ C) ^ t ∷ [])) {refl}
      p' = structural subset-refl sub_right p_disj
      d_p' : δ p' ≡ δ mix
      d_p' = trans (structural-preserves-δ subset-refl sub_right p_disj)
             (trans (structural-preserves-δ subset-refl sub_succ mix_split)
             (subst-preserves-δ (cong (_,, Δ') succ-split) mix))
      d_final : δ p' ≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ Π')
      d_final = subst (_≤ max (δ (⊢∨₂ {Γ = Γ_sub} {B = C} {s = t} {Δ = Δ_sub} {A = B} Π_sub)) (δ Π')) (sym d_p') dmix
  in (p' , d_final)

handleDiaNoEq {Γ_sub = Γ_sub} {B_l = B_l} {r_l = r_l} {t_l = t_l} {Δ_sub = Δ_sub}
              {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
              degEq Π_sub Π' wfp wfp' accRec neq =
  let fullPos = r_l ∘ t_l
      h-dec = mixHeight-dec-l (⊢♢ Π_sub) Π_sub Π' (height-subproof-1 Π_sub)
      acc' = accRec _ (inr (refl , h-dec))
      (mix , dmix) = Mix {Γ = Γ_sub} {Δ = [ B_l ^ fullPos ] ,, Δ_sub} degEq Π_sub Π' wfp wfp' acc'
      Γ'-rem = Γ' - (A ^ s)
      Δ_sub-rem = Δ_sub - (A ^ s)
      succ-split : ([ B_l ^ fullPos ] ,, Δ_sub) - (A ^ s) ≡ ([ B_l ^ fullPos ] - (A ^ s)) ,, Δ_sub-rem
      succ-split = S4dot2.CutElimination.Base.removeAll-++ (A ^ s) [ B_l ^ fullPos ] Δ_sub
      mix_split = subst (λ D → Γ_sub ,, Γ'-rem ⊢ D ,, Δ') succ-split mix
      sub_succ : ((([ B_l ^ fullPos ] - (A ^ s)) ,, Δ_sub-rem) ,, Δ') ⊆ ([ B_l ^ fullPos ] ,, (Δ_sub-rem ,, Δ'))
      sub_succ = solve ((rem (elm 0) 1 ++ₑ var 0) ++ₑ var 1) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ_sub-rem ∷ Δ' ∷ []) , (B_l ^ fullPos ∷ A ^ s ∷ [])) {refl}
      mix_w = structural subset-refl sub_succ mix_split
      p_dia = ⊢♢ {Γ_sub ,, Γ'-rem} {B_l} {r_l} {t_l} {Δ_sub-rem ,, Δ'} mix_w
      sub_right : ([ (♢ B_l) ^ r_l ] ,, (Δ_sub-rem ,, Δ')) ⊆ (([ (♢ B_l) ^ r_l ] ,, Δ_sub-rem) ,, Δ')
      sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((elm 0 ++ₑ var 0) ++ₑ var 1) ((Δ_sub-rem ∷ Δ' ∷ []) , ((♢ B_l) ^ r_l ∷ [])) {refl}
      p' = structural subset-refl sub_right p_dia
      d_p' : δ p' ≡ δ mix
      d_p' = trans (structural-preserves-δ subset-refl sub_right p_dia)
             (trans (structural-preserves-δ subset-refl sub_succ mix_split)
             (subst-preserves-δ (cong (_,, Δ') succ-split) mix))
      d_final : δ p' ≤ max (δ (⊢♢ Π_sub)) (δ Π')
      d_final = subst (_≤ max (δ (⊢♢ Π_sub)) (δ Π')) (sym d_p') dmix
  in (p' , d_final)

handleConjNoEq {Γ_sub₁ = Γ_sub₁} {Γ_sub₂ = Γ_sub₂} {B_l = B_l} {C_l = C_l} {t = t}
               {Δ_sub₁ = Δ_sub₁} {Δ_sub₂ = Δ_sub₂}
               {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
               degEq Π₁ Π₂ Π' wfp wfp' accRec neq =
  let wfp₁ = fst wfp
      wfp₂ = snd wfp
      h-dec1 = mixHeight-dec-l (⊢∧ Π₁ Π₂) Π₁ Π' (height-subproof-2-l Π₁ Π₂)
      h-dec2 = mixHeight-dec-l (⊢∧ Π₁ Π₂) Π₂ Π' (height-subproof-2-r Π₁ Π₂)
      acc1 = accRec _ (inr (refl , h-dec1))
      acc2 = accRec _ (inr (refl , h-dec2))
      (mix1 , dmix1) = Mix {Γ = Γ_sub₁} {Δ = [ B_l ^ t ] ,, Δ_sub₁} degEq Π₁ Π' wfp₁ wfp' acc1
      (mix2 , dmix2) = Mix {Γ = Γ_sub₂} {Δ = [ C_l ^ t ] ,, Δ_sub₂} degEq Π₂ Π' wfp₂ wfp' acc2
      Γ'-rem = Γ' - (A ^ s)
      Δ_sub₁-rem = Δ_sub₁ - (A ^ s)
      Δ_sub₂-rem = Δ_sub₂ - (A ^ s)
      succ-split1 : ([ B_l ^ t ] ,, Δ_sub₁) - (A ^ s) ≡ ([ B_l ^ t ] - (A ^ s)) ,, Δ_sub₁-rem
      succ-split1 = S4dot2.CutElimination.Base.removeAll-++ (A ^ s) [ B_l ^ t ] Δ_sub₁
      mix1_split = subst (λ D → Γ_sub₁ ,, Γ'-rem ⊢ D ,, Δ') succ-split1 mix1
      sub_succ1 : ((([ B_l ^ t ] - (A ^ s)) ,, Δ_sub₁-rem) ,, Δ') ⊆ ([ B_l ^ t ] ,, (Δ_sub₁-rem ,, Δ'))
      sub_succ1 = solve ((rem (elm 0) 1 ++ₑ var 0) ++ₑ var 1) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ_sub₁-rem ∷ Δ' ∷ []) , (B_l ^ t ∷ A ^ s ∷ [])) {refl}
      mix1_w = structural subset-refl sub_succ1 mix1_split
      succ-split2 : ([ C_l ^ t ] ,, Δ_sub₂) - (A ^ s) ≡ ([ C_l ^ t ] - (A ^ s)) ,, Δ_sub₂-rem
      succ-split2 = S4dot2.CutElimination.Base.removeAll-++ (A ^ s) [ C_l ^ t ] Δ_sub₂
      mix2_split = subst (λ D → Γ_sub₂ ,, Γ'-rem ⊢ D ,, Δ') succ-split2 mix2
      sub_succ2 : ((([ C_l ^ t ] - (A ^ s)) ,, Δ_sub₂-rem) ,, Δ') ⊆ ([ C_l ^ t ] ,, (Δ_sub₂-rem ,, Δ'))
      sub_succ2 = solve ((rem (elm 0) 1 ++ₑ var 0) ++ₑ var 1) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ_sub₂-rem ∷ Δ' ∷ []) , (C_l ^ t ∷ A ^ s ∷ [])) {refl}
      mix2_w = structural subset-refl sub_succ2 mix2_split
      p_conj = ⊢∧ {Γ₁ = Γ_sub₁ ,, Γ'-rem} {A = B_l} {s = t} {Δ₁ = Δ_sub₁-rem ,, Δ'} {Γ₂ = Γ_sub₂ ,, Γ'-rem} {B = C_l} {Δ₂ = Δ_sub₂-rem ,, Δ'} mix1_w mix2_w
      subLeft : ((Γ_sub₁ ,, Γ'-rem) ,, (Γ_sub₂ ,, Γ'-rem)) ⊆ ((Γ_sub₁ ,, Γ_sub₂) ,, Γ'-rem)
      subLeft = solve ((var 0 ++ₑ var 2) ++ₑ (var 1 ++ₑ var 2)) ((var 0 ++ₑ var 1) ++ₑ var 2) ((Γ_sub₁ ∷ Γ_sub₂ ∷ Γ'-rem ∷ []) , []) {refl}
      subRight : ([ (B_l ∧ C_l) ^ t ] ,, (Δ_sub₁-rem ,, Δ') ,, (Δ_sub₂-rem ,, Δ')) ⊆ (([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁-rem ,, Δ_sub₂-rem) ,, Δ')
      subRight = solve (elm 0 ++ₑ (var 0 ++ₑ var 2) ++ₑ (var 1 ++ₑ var 2)) ((elm 0 ++ₑ var 0 ++ₑ var 1) ++ₑ var 2) ((Δ_sub₁-rem ∷ Δ_sub₂-rem ∷ Δ' ∷ []) , ((B_l ∧ C_l) ^ t ∷ [])) {refl}
      p_contracted = structural subLeft subRight p_conj
      succ-eq : ([ (B_l ∧ C_l) ^ t ] ,, Δ_sub₁ ,, Δ_sub₂) - (A ^ s) ≡ [ (B_l ∧ C_l) ^ t ] ,, (Δ_sub₁-rem ,, Δ_sub₂-rem)
      succ-eq = trans (lemma-removeAll-head-neq {A = A ^ s} {B = (B_l ∧ C_l) ^ t} {Γ = Δ_sub₁ ,, Δ_sub₂} neq)
                      (cong ([ (B_l ∧ C_l) ^ t ] ,,_) (S4dot2.CutElimination.Base.removeAll-++ (A ^ s) Δ_sub₁ Δ_sub₂))
      p' = subst (λ D → (Γ_sub₁ ,, Γ_sub₂) ,, Γ'-rem ⊢ D ,, Δ') (sym succ-eq) p_contracted
      cutBound = max (δ (⊢∧ Π₁ Π₂)) (δ Π')
      dΠ₁≤cb : δ Π₁ ≤ cutBound
      dΠ₁≤cb = left-left-≤-max
      dΠ₂≤cb : δ Π₂ ≤ cutBound
      dΠ₂≤cb = right-left-≤-max
      dΠ'≤cb : δ Π' ≤ cutBound
      dΠ'≤cb = right-≤-max {δ Π'} {δ (⊢∧ Π₁ Π₂)}
      dmix1' : δ mix1 ≤ cutBound
      dmix1' = ≤-trans dmix1 (max-least dΠ₁≤cb dΠ'≤cb)
      dmix2' : δ mix2 ≤ cutBound
      dmix2' = ≤-trans dmix2 (max-least dΠ₂≤cb dΠ'≤cb)
      d_mix1_split = subst-preserves-δ (cong (_,, Δ') succ-split1) mix1
      d_mix1_w = structural-preserves-δ subset-refl sub_succ1 mix1_split
      d_mix1_w_eq : δ mix1_w ≡ δ mix1
      d_mix1_w_eq = trans d_mix1_w d_mix1_split
      dmix1w' = subst (_≤ cutBound) (sym d_mix1_w_eq) dmix1'
      d_mix2_split = subst-preserves-δ (cong (_,, Δ') succ-split2) mix2
      d_mix2_w = structural-preserves-δ subset-refl sub_succ2 mix2_split
      d_mix2_w_eq : δ mix2_w ≡ δ mix2
      d_mix2_w_eq = trans d_mix2_w d_mix2_split
      dmix2w' = subst (_≤ cutBound) (sym d_mix2_w_eq) dmix2'
      dp_conj : δ p_conj ≤ cutBound
      dp_conj = max-least dmix1w' dmix2w'
      dp_contracted = subst (_≤ cutBound) (sym (structural-preserves-δ subLeft subRight p_conj)) dp_conj
      d_final : δ p_contracted ≤ cutBound
      d_final = dp_contracted
  in (p_contracted , d_final)

handleImplNoEq {Γ_sub = Γ_sub} {B_l = B_l} {t = t} {C_l = C_l} {Δ_sub = Δ_sub}
               {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
               degEq Π_sub Π' wfp wfp' accRec neq =
  let h-dec = mixHeight-dec-l (⊢⇒ Π_sub) Π_sub Π' (height-subproof-1 Π_sub)
      acc' = accRec _ (inr (refl , h-dec))
      (mix , dmix) = Mix {Γ = Γ_sub ,, [ B_l ^ t ]} {Δ = [ C_l ^ t ] ,, Δ_sub} degEq Π_sub Π' wfp wfp' acc'
      Γ'-rem = Γ' - (A ^ s)
      Δ_sub-rem = Δ_sub - (A ^ s)
      succ-split : ([ C_l ^ t ] ,, Δ_sub) - (A ^ s) ≡ ([ C_l ^ t ] - (A ^ s)) ,, Δ_sub-rem
      succ-split = S4dot2.CutElimination.Base.removeAll-++ (A ^ s) [ C_l ^ t ] Δ_sub
      mix_split = subst (λ D → (Γ_sub ,, [ B_l ^ t ]) ,, Γ'-rem ⊢ D ,, Δ') succ-split mix
      sub_left : ((Γ_sub ,, [ B_l ^ t ]) ,, Γ'-rem) ⊆ ((Γ_sub ,, Γ'-rem) ,, [ B_l ^ t ])
      sub_left = solve ((var 0 ++ₑ elm 0) ++ₑ var 1) ((var 0 ++ₑ var 1) ++ₑ elm 0) ((Γ_sub ∷ Γ'-rem ∷ []) , (B_l ^ t ∷ [])) {refl}
      sub_succ : ((([ C_l ^ t ] - (A ^ s)) ,, Δ_sub-rem) ,, Δ') ⊆ ([ C_l ^ t ] ,, (Δ_sub-rem ,, Δ'))
      sub_succ = solve ((rem (elm 0) 1 ++ₑ var 0) ++ₑ var 1) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ_sub-rem ∷ Δ' ∷ []) , (C_l ^ t ∷ A ^ s ∷ [])) {refl}
      mix_rw = structural sub_left sub_succ mix_split
      p_impl = ⊢⇒ {Γ_sub ,, Γ'-rem} {B_l} {t} {C_l} {Δ_sub-rem ,, Δ'} mix_rw
      sub_right : ([ (B_l ⇒ C_l) ^ t ] ,, (Δ_sub-rem ,, Δ')) ⊆ (([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub-rem) ,, Δ')
      sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((elm 0 ++ₑ var 0) ++ₑ var 1) ((Δ_sub-rem ∷ Δ' ∷ []) , ((B_l ⇒ C_l) ^ t ∷ [])) {refl}
      p_reorder = structural subset-refl sub_right p_impl
      succ-eq : ([ (B_l ⇒ C_l) ^ t ] ,, Δ_sub) - (A ^ s) ≡ [ (B_l ⇒ C_l) ^ t ] ,, Δ_sub-rem
      succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (B_l ⇒ C_l) ^ t} {Γ = Δ_sub} neq
      p' = subst (λ D → Γ_sub ,, Γ'-rem ⊢ D ,, Δ') (sym succ-eq) p_reorder
      d_reorder : δ p_reorder ≡ δ mix
      d_reorder = trans (structural-preserves-δ subset-refl sub_right p_impl)
                  (trans (structural-preserves-δ sub_left sub_succ mix_split)
                  (subst-preserves-δ (cong (_,, Δ') succ-split) mix))
      d_p' : δ p' ≡ δ p_reorder
      d_p' = subst-preserves-δ (cong (_,, Δ') (sym succ-eq)) p_reorder
      dmix' : δ p_reorder ≤ max (δ (⊢⇒ Π_sub)) (δ Π')
      dmix' = subst (_≤ max (δ (⊢⇒ Π_sub)) (δ Π')) (sym d_reorder) dmix
      d_final : δ p' ≤ max (δ (⊢⇒ Π_sub)) (δ Π')
      d_final = subst (_≤ max (δ (⊢⇒ Π_sub)) (δ Π')) (sym d_p') dmix'
  in (p' , d_final)

handleBoxNoEq {x_l = x_l} {r_l = r_l} {Γ_sub = Γ_sub} {Δ_sub = Δ_sub} {B_l = B_l}
              {Γ' = Γ'} {Δ' = Δ'} {A = A} {s = s}
              degEq ext_l freshΓ_l freshΔ_l Π_sub Π' wfp wfp' accRec neq =
  let Γ'-rem = Γ' - (A ^ s)
      Δ_sub-rem = Δ_sub - (A ^ s)
      combined = (Γ_sub ,, Γ'-rem) ,, (Δ_sub-rem ,, Δ')
      wf_l : maxEigenposToken Π_sub < x_l
      wf_l = fst wfp
      wfp_sub : WellFormedProof Π_sub
      wfp_sub = snd wfp
      eigent_l : Position
      eigent_l = insertToken x_l r_l
      x' : Token
      x' = freshTokenForRename r_l combined Π_sub
      x'-fresh-combined : TokenFresh x' combined
      x'-fresh-combined = freshTokenForRename-fresh r_l combined Π_sub
      x'-eigenpos : maxEigenposToken Π_sub < x'
      x'-eigenpos = freshTokenForRename-eigenpos r_l combined Π_sub
      x'∉r_l : x' ∉Pos r_l
      x'∉r_l = freshTokenForRename-∉r r_l combined Π_sub
      t' : Position
      t' = substPos x_l (singleton-pos x') eigent_l
      extSTE_l : IsSingleTokenExt r_l eigent_l x_l
      extSTE_l = mkSingleTokenExt r_l x_l ext_l
      rename-result = renameEigenpos-⊢□-premise-gen {r = r_l} {t = eigent_l} {x = x_l} {Γ = Γ_sub} {Δ = Δ_sub} {A = B_l} Π_sub extSTE_l freshΓ_l freshΔ_l wf_l x' x'-eigenpos x'∉r_l
      Π_sub_renamed : Γ_sub ⊢ ([ B_l ^ t' ] ,, Δ_sub)
      Π_sub_renamed = fst rename-result
      δ-eq-renamed : δ Π_sub_renamed ≡ δ Π_sub
      δ-eq-renamed = δ-renameEigenpos-⊢□-premise-gen Π_sub extSTE_l freshΓ_l freshΔ_l wf_l x' x'-eigenpos x'∉r_l
      height-eq-renamed : height Π_sub_renamed ≡ height Π_sub
      height-eq-renamed = height-renameEigenpos-⊢□-premise-gen Π_sub extSTE_l freshΓ_l freshΔ_l wf_l x' x'-eigenpos x'∉r_l
      wfp_renamed : WellFormedProof Π_sub_renamed
      wfp_renamed = WellFormed-renameEigenpos-⊢□-premise-gen Π_sub extSTE_l freshΓ_l freshΔ_l wf_l x' x'-eigenpos x'∉r_l wfp_sub
      h-dec-raw = mixHeight-dec-l (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π_sub Π' (height-subproof-1 Π_sub)
      mixHeight-eq = cong (λ h → h + height Π') height-eq-renamed
      h-dec = subst (_< mixHeight (⊢□ ext_l freshΓ_l freshΔ_l Π_sub) Π') (sym mixHeight-eq) h-dec-raw
      (mix , dmix) = Mix {Γ = Γ_sub} {Δ = [ B_l ^ t' ] ,, Δ_sub} degEq Π_sub_renamed Π' wfp_renamed wfp' (accRec _ (inr (refl , h-dec)))
      succ-split : ([ B_l ^ t' ] ,, Δ_sub) - (A ^ s) ≡ ([ B_l ^ t' ] - (A ^ s)) ,, Δ_sub-rem
      succ-split = S4dot2.CutElimination.Base.removeAll-++ (A ^ s) [ B_l ^ t' ] Δ_sub
      mix_split = subst (λ D → Γ_sub ,, Γ'-rem ⊢ D ,, Δ') succ-split mix
      sub_succ : ((([ B_l ^ t' ] - (A ^ s)) ,, Δ_sub-rem) ,, Δ') ⊆ ([ B_l ^ t' ] ,, (Δ_sub-rem ,, Δ'))
      sub_succ = solve ((rem (elm 0) 1 ++ₑ var 0) ++ₑ var 1) (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((Δ_sub-rem ∷ Δ' ∷ []) , (B_l ^ t' ∷ A ^ s ∷ [])) {refl}
      mix_w = structural subset-refl sub_succ mix_split
      t'-eq : t' ≡ insertToken x' r_l
      t'-eq = substPos-insertToken-eq x_l x' r_l ext_l
      mix_transported : Γ_sub ,, Γ'-rem ⊢ [ B_l ^ insertToken x' r_l ] ,, (Δ_sub-rem ,, Δ')
      mix_transported = subst (λ (p : Position) → Γ_sub ,, Γ'-rem ⊢ [ B_l ^ p ] ,, (Δ_sub-rem ,, Δ')) t'-eq mix_w
      fresh-split = TokenFresh-split (Γ_sub ,, Γ'-rem) (Δ_sub-rem ,, Δ') x' x'-fresh-combined
      freshΓ_new : TokenFresh x' (Γ_sub ,, Γ'-rem)
      freshΓ_new = fst fresh-split
      freshΔ_new : TokenFresh x' (Δ_sub-rem ,, Δ')
      freshΔ_new = snd fresh-split
      p_boxed = ⊢□ {x'} {r_l} {Γ_sub ,, Γ'-rem} {Δ_sub-rem ,, Δ'} {B_l} x'∉r_l freshΓ_new freshΔ_new mix_transported
      sub_right : ([ (□ B_l) ^ r_l ] ,, (Δ_sub-rem ,, Δ')) ⊆ (([ (□ B_l) ^ r_l ] ,, Δ_sub-rem) ,, Δ')
      sub_right = solve (elm 0 ++ₑ (var 0 ++ₑ var 1)) ((elm 0 ++ₑ var 0) ++ₑ var 1) ((Δ_sub-rem ∷ Δ' ∷ []) , ((□ B_l) ^ r_l ∷ [])) {refl}
      p_reordered = structural subset-refl sub_right p_boxed
      succ-eq : ([ (□ B_l) ^ r_l ] ,, Δ_sub) - (A ^ s) ≡ [ (□ B_l) ^ r_l ] ,, Δ_sub-rem
      succ-eq = lemma-removeAll-head-neq {A = A ^ s} {B = (□ B_l) ^ r_l} {Γ = Δ_sub} neq
      p' = subst (λ D → Γ_sub ,, Γ'-rem ⊢ D ,, Δ') (sym succ-eq) p_reordered
      d_mix_split : δ mix_split ≡ δ mix
      d_mix_split = subst-preserves-δ (cong (_,, Δ') succ-split) mix
      d_mix_w : δ mix_w ≡ δ mix
      d_mix_w = trans (structural-preserves-δ subset-refl sub_succ mix_split) d_mix_split
      d_mix_transported : δ mix_transported ≡ δ mix_w
      d_mix_transported = subst-preserves-δ (cong (λ (p : Position) → [ B_l ^ p ] ,, (Δ_sub-rem ,, Δ')) t'-eq) mix_w
      d_reordered : δ p_reordered ≡ δ mix
      d_reordered = trans (structural-preserves-δ subset-refl sub_right p_boxed)
                    (trans d_mix_transported d_mix_w)
      d_p' : δ p' ≡ δ p_reordered
      d_p' = subst-preserves-δ (cong (_,, Δ') (sym succ-eq)) p_reordered
      bound-eq : max (δ Π_sub_renamed) (δ Π') ≡ max (δ Π_sub) (δ Π')
      bound-eq = cong (λ d → max d (δ Π')) δ-eq-renamed
      dmix' : δ mix ≤ max (δ Π_sub) (δ Π')
      dmix' = subst (δ mix ≤_) bound-eq dmix
      dmix'' : δ p_reordered ≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ Π')
      dmix'' = subst (_≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ Π')) (sym d_reordered) dmix'
      d_final : δ p' ≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ Π')
      d_final = subst (_≤ max (δ (⊢□ ext_l freshΓ_l freshΔ_l Π_sub)) (δ Π')) (sym d_p') dmix''
  in (p' , d_final)
