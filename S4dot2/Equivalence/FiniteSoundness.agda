{-# OPTIONS --cubical --safe #-}

-- Constructive Soundness for S4.2 using Finite Models
-- Key insight: decidable satisfaction enables constructive proofs
-- without classical postulates (for propositional rules)

module S4dot2.Equivalence.FiniteSoundness where

open import Cubical.Foundations.Prelude hiding (_∧_; _∨_)
open import Cubical.Data.List hiding ([_])
open import Cubical.Data.List.Properties using (++-assoc)
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Bool using (Bool; true; false; _and_; _or_; not; false≢true)
open import Cubical.Relation.Nullary hiding (¬_)

open import S4dot2.Syntax hiding (_⊢_) renaming (_∧_ to _and'_; _∨_ to _or'_)
open import S4dot2.System hiding (Ctx)
open import S4dot2.System using (Ctx; _,,_)
open import S4dot2.Equivalence.FiniteModel
open import S4dot2.BoolReflect

not-false-eq : ∀ {a} → a ≡ false → not a ≡ true
not-false-eq {false} _ = refl
not-false-eq {true} p = ⊥-rec (false≢true (sym p))

not-true-is-false : ∀ {a} → not a ≡ true → a ≡ false
not-true-is-false {false} _ = refl
not-true-is-false {true} p = ⊥-rec (false≢true p)

or-right-true : ∀ {a b} → a or b ≡ true → a ≡ false → b ≡ true
or-right-true {false} {b} p _ = p
or-right-true {true} {b} p eq = ⊥-rec (false≢true (sym eq))

impl-true : ∀ {a b} → not a or b ≡ true → a ≡ true → b ≡ true
impl-true {true} {b} p _ = p
impl-true {false} {b} p eq = ⊥-rec (false≢true eq)

-- =============================================================================
-- Context and Succedent Lemmas
-- =============================================================================

⊩Ctx-here : ∀ {M ρ pf Γ} → M , ρ ⊩ᶠ pf → M , ρ ⊩Ctxᶠ Γ → M , ρ ⊩Ctxᶠ (pf ∷ Γ)
⊩Ctx-here sat satΓ pf' here = sat
⊩Ctx-here sat satΓ pf' (there mem) = satΓ pf' mem

⊩Ctx-tail : ∀ {M ρ pf Γ} → M , ρ ⊩Ctxᶠ (pf ∷ Γ) → M , ρ ⊩Ctxᶠ Γ
⊩Ctx-tail satCtx pf' mem = satCtx pf' (there mem)

⊩Ctx-head : ∀ {M ρ pf Γ} → M , ρ ⊩Ctxᶠ (pf ∷ Γ) → M , ρ ⊩ᶠ pf
⊩Ctx-head satCtx = satCtx _ here

-- Remove last element from context (for W⊢ which adds at end)
⊩Ctx-init : ∀ {M ρ pf} (Γ : Ctx) → M , ρ ⊩Ctxᶠ (Γ ,, [ pf ]) → M , ρ ⊩Ctxᶠ Γ
⊩Ctx-init Γ sat pf' mem = sat pf' (mem-++-l mem)

-- Get last element of context
⊩Ctx-last : ∀ {M ρ pf} (Γ : Ctx) → M , ρ ⊩Ctxᶠ (Γ ,, [ pf ]) → M , ρ ⊩ᶠ pf
⊩Ctx-last Γ sat = sat _ (mem-++-r Γ here)

-- Membership at last position
∈-last : ∀ {ℓ} {A : Type ℓ} {x : A} (xs : List A) → x ∈ (xs ,, [ x ])
∈-last xs = mem-++-r xs here

⊩Ctx-split-l : ∀ {M ρ} (Γ₁ Γ₂ : Ctx) → M , ρ ⊩Ctxᶠ (Γ₁ ,, Γ₂) → M , ρ ⊩Ctxᶠ Γ₁
⊩Ctx-split-l Γ₁ Γ₂ sat pf mem = sat pf (mem-++-l mem)

⊩Ctx-split-r : ∀ {M ρ} (Γ₁ Γ₂ : Ctx) → M , ρ ⊩Ctxᶠ (Γ₁ ,, Γ₂) → M , ρ ⊩Ctxᶠ Γ₂
⊩Ctx-split-r Γ₁ Γ₂ sat pf mem = sat pf (mem-++-r Γ₁ mem)

-- Helper: split membership in concatenated lists
mem-split : ∀ {ℓ} {A : Type ℓ} (xs : List A) {ys : List A} {x : A}
          → x ∈ xs ++ ys → (x ∈ xs) ⊎ (x ∈ ys)
mem-split [] mem = inr mem
mem-split (y ∷ xs) here = inl here
mem-split (y ∷ xs) (there mem) with mem-split xs mem
... | inl inXs = inl (there inXs)
... | inr inYs = inr inYs

⊩Ctx-snoc : ∀ {M ρ pf} (Γ : Ctx) → M , ρ ⊩Ctxᶠ Γ → M , ρ ⊩ᶠ pf → M , ρ ⊩Ctxᶠ (Γ ,, [ pf ])
⊩Ctx-snoc Γ satΓ satPf pf' mem with mem-split Γ mem
... | inl inΓ = satΓ pf' inΓ
... | inr here = satPf
... | inr (there ())

-- Duplicate last element (for C⊢ which contracts last two identical elements)
-- ,, is left-associative: Γ ,, [ pf ] ,, [ pf ] = (Γ ++ [ pf ]) ++ [ pf ]
⊩Ctx-dup-last : ∀ {M ρ pf} (Γ : Ctx) → M , ρ ⊩Ctxᶠ (Γ ++ [ pf ]) → M , ρ ⊩Ctxᶠ ((Γ ++ [ pf ]) ++ [ pf ])
⊩Ctx-dup-last {M} {ρ} {pf} Γ sat pf' mem =
  helper (mem-split (Γ ++ [ pf ]) {ys = [ pf ]} mem)
  where
    helper : (pf' ∈ (Γ ++ [ pf ])) ⊎ (pf' ∈ [ pf ]) → M , ρ ⊩ᶠ pf'
    helper (inl inΓpf) = sat pf' inΓpf
    helper (inr here) = sat pf' (mem-++-r Γ here)
    helper (inr (there ()))

⊩Succ-here : ∀ {M ρ pf Δ} → M , ρ ⊩ᶠ pf → M , ρ ⊩Succᶠ (pf ∷ Δ)
⊩Succ-here sat = (_ , here , sat)

⊩Succ-there : ∀ {M ρ pf Δ} → M , ρ ⊩Succᶠ Δ → M , ρ ⊩Succᶠ (pf ∷ Δ)
⊩Succ-there (pf' , mem , sat) = (pf' , there mem , sat)

⊩Succ-,,-l : ∀ {M ρ} (Δ₁ Δ₂ : Ctx) → M , ρ ⊩Succᶠ Δ₁ → M , ρ ⊩Succᶠ (Δ₁ ,, Δ₂)
⊩Succ-,,-l (x ∷ Δ₁) Δ₂ (pf , here , sat) = (pf , here , sat)
⊩Succ-,,-l (x ∷ Δ₁) Δ₂ (pf , there mem , sat) =
  ⊩Succ-there (⊩Succ-,,-l Δ₁ Δ₂ (pf , mem , sat))

⊩Succ-,,-r : ∀ {M ρ} (Δ₁ Δ₂ : Ctx) → M , ρ ⊩Succᶠ Δ₂ → M , ρ ⊩Succᶠ (Δ₁ ,, Δ₂)
⊩Succ-,,-r [] Δ₂ sat = sat
⊩Succ-,,-r (x ∷ Δ₁) Δ₂ sat = ⊩Succ-there (⊩Succ-,,-r Δ₁ Δ₂ sat)

-- Helper: split membership in concatenated lists
mem-∈-++⁻ : ∀ {ℓ} {A : Type ℓ} (xs : List A) {ys : List A} {x : A} 
          → x ∈ xs ++ ys → (x ∈ xs) ⊎ (x ∈ ys)
mem-∈-++⁻ [] mem = inr mem
mem-∈-++⁻ (y ∷ xs) here = inl here
mem-∈-++⁻ (y ∷ xs) (there mem) with mem-∈-++⁻ xs mem
... | inl inXs = inl (there inXs)
... | inr inYs = inr inYs

-- =============================================================================
-- Exchange Helpers - Context and Succedent exchange
-- =============================================================================

-- Helper for Exc⊢: exchange two adjacent elements in context
-- Swaps [B^t] and [A^s] in ((Γ₁ ++ [B^t]) ++ [A^s]) ++ Γ₂ to get ((Γ₁ ++ [A^s]) ++ [B^t]) ++ Γ₂
⊩Ctx-exchange : ∀ {M ρ} (Γ₁ : Ctx) (A : Formula) (s : Position) (B : Formula) (t : Position) (Γ₂ : Ctx)
              → M , ρ ⊩Ctxᶠ (((Γ₁ ++ [ B ^ t ]) ++ [ A ^ s ]) ++ Γ₂)
              → M , ρ ⊩Ctxᶠ (((Γ₁ ++ [ A ^ s ]) ++ [ B ^ t ]) ++ Γ₂)
⊩Ctx-exchange {M} {ρ} Γ₁ A s B t Γ₂ sat pf mem
  with mem-split ((Γ₁ ++ [ A ^ s ]) ++ [ B ^ t ]) {Γ₂} {pf} mem
... | inr inΓ₂ = sat pf (mem-++-r ((Γ₁ ++ [ B ^ t ]) ++ [ A ^ s ]) inΓ₂)
... | inl inPrefix with mem-split (Γ₁ ++ [ A ^ s ]) {[ B ^ t ]} {pf} inPrefix
... | inr here = sat pf (mem-++-l (mem-++-l (mem-++-r Γ₁ here)))  -- B^t in input is at position after Γ₁
... | inl inΓ₁A with mem-split Γ₁ {[ A ^ s ]} {pf} inΓ₁A
... | inl inΓ₁ = sat pf (mem-++-l (mem-++-l (mem-++-l inΓ₁)))    -- pf in Γ₁
... | inr here = sat pf (mem-++-l (mem-++-r (Γ₁ ++ [ B ^ t ]) here))  -- A^s in input goes to after Γ₁++[B^t]
... | inr (there ())

-- Helper for ⊢Exc: exchange two adjacent elements in succedent
-- Swaps [A^s] and [B^t] in ((Δ₁ ++ [A^s]) ++ [B^t]) ++ Δ₂ to get ((Δ₁ ++ [B^t]) ++ [A^s]) ++ Δ₂
⊩Succ-exchange : ∀ {M ρ} (Δ₁ : Ctx) (A : Formula) (s : Position) (B : Formula) (t : Position) (Δ₂ : Ctx)
               → M , ρ ⊩Succᶠ (((Δ₁ ++ [ A ^ s ]) ++ [ B ^ t ]) ++ Δ₂)
               → M , ρ ⊩Succᶠ (((Δ₁ ++ [ B ^ t ]) ++ [ A ^ s ]) ++ Δ₂)
⊩Succ-exchange {M} {ρ} Δ₁ A s B t Δ₂ (pf , mem , sat)
  with mem-split ((Δ₁ ++ [ A ^ s ]) ++ [ B ^ t ]) {Δ₂} {pf} mem
... | inr inΔ₂ = (pf , mem-++-r ((Δ₁ ++ [ B ^ t ]) ++ [ A ^ s ]) inΔ₂ , sat)
... | inl inPrefix with mem-split (Δ₁ ++ [ A ^ s ]) {[ B ^ t ]} {pf} inPrefix
... | inr here = (pf , mem-++-l (mem-++-l (mem-++-r Δ₁ here)) , sat)  -- B^t in input goes to after Δ₁
... | inl inΔ₁A with mem-split Δ₁ {[ A ^ s ]} {pf} inΔ₁A
... | inl inΔ₁ = (pf , mem-++-l (mem-++-l (mem-++-l inΔ₁)) , sat)    -- pf in Δ₁
... | inr here = (pf , mem-++-l (mem-++-r (Δ₁ ++ [ B ^ t ]) here) , sat)  -- A^s in input goes to after Δ₁++[B^t]
... | inr (there ())

-- =============================================================================
-- Soundness Helpers - Dispatch on Succedent Membership
-- =============================================================================

-- Helper for ⊢C: contract the succedent result
contract-succ : ∀ {M ρ A s Δ} 
              → M , ρ ⊩Succᶠ ([ A ^ s ] ++ [ A ^ s ] ++ Δ)
              → M , ρ ⊩Succᶠ ([ A ^ s ] ++ Δ)
contract-succ (pf , here , sat) = (pf , here , sat)
contract-succ (pf , there here , sat) = (pf , here , sat)
contract-succ (pf , there (there mem) , sat) = (pf , there mem , sat)

-- Helper for ⊢¬: when A is satisfied, IH gives us something from Δ
-- We just need to shift it past the ¬A position
shift-past-neg : ∀ {M ρ A s Δ}
               → M , ρ ⊩Succᶠ Δ
               → M , ρ ⊩Succᶠ ([ (¬ A) ^ s ] ++ Δ)
shift-past-neg (pf , mem , sat) = (pf , there mem , sat)

-- Helper for ⊢⇒: dispatch on whether B is in first position
dispatch-impl : ∀ {M ρ A B s Δ}
              → M , ρ ⊩Succᶠ ([ B ^ s ] ++ Δ)
              → M , ρ ⊩Succᶠ ([ (A ⇒ B) ^ s ] ++ Δ)
dispatch-impl (pf , here , satB) = ⊩Succ-here (or-true-intro-r satB)
dispatch-impl (pf , there mem , sat) = ⊩Succ-there (pf , mem , sat)

-- Helper for ⊢∨₁
dispatch-or1 : ∀ {M ρ A B s Δ}
             → M , ρ ⊩Succᶠ ([ A ^ s ] ++ Δ)
             → M , ρ ⊩Succᶠ ([ (A or' B) ^ s ] ++ Δ)
dispatch-or1 (pf , here , satA) = ⊩Succ-here (or-true-intro-l satA)
dispatch-or1 (pf , there mem , sat) = ⊩Succ-there (pf , mem , sat)

-- Helper for ⊢∨₂
dispatch-or2 : ∀ {M ρ A B s Δ}
             → M , ρ ⊩Succᶠ ([ B ^ s ] ++ Δ)
             → M , ρ ⊩Succᶠ ([ (A or' B) ^ s ] ++ Δ)
dispatch-or2 (pf , here , satB) = ⊩Succ-here (or-true-intro-r satB)
dispatch-or2 (pf , there mem , sat) = ⊩Succ-there (pf , mem , sat)

-- =============================================================================
-- Constructive Soundness Theorem
-- =============================================================================

-- The soundness theorem requires a ModalSemantics proof for the model
-- This ensures the model has proper Kripke semantics for modal operators
finiteSoundness : ∀ {Γ Δ} → Γ ⊢ Δ 
                → (M : FiniteModel) → (ms : ModalSemantics M) → (ρ : FiniteInterpretation M)
                → M , ρ ⊩Ctxᶠ Γ → M , ρ ⊩Succᶠ Δ

-- =============================================================================
-- Eigenposition Lemmas for Finite Models
-- =============================================================================
-- These lemmas capture the semantic content of the eigenposition condition.
-- The eigenposition condition IsEigenposition s t Γ Δ states that (s ++ [t])
-- is not an initial segment of any position in Γ ++ Δ. This is used to ensure
-- that the token t can be "instantiated" to any accessible world without
-- affecting the satisfaction of formulas in the context.

-- Helper: extract freshness for a specific formula from TokenFresh
TokenFresh-lookup : ∀ {x : Token} {Γ : List PFormula} → TokenFresh x Γ
                  → (pf : PFormula) → pf ∈ Γ → x ∉Pos (PFormula.pos pf)
TokenFresh-lookup (x∉pf , _) pf here = x∉pf
TokenFresh-lookup (_ , fresh-rest) pf (there mem) = TokenFresh-lookup fresh-rest pf mem

-- Eigenposition update: ρ[t/v](s ∘ [t]) = ρ(s) ⊔ v when t ∉Pos s
eigenpos-pos-update : ∀ (M : FiniteModel) (ρ : FiniteInterpretation M) (t : Token) (v : World M) (s : Position)
                    → t ∉Pos s
                    → ρ-pos-fin M (_[_/_]ᶠ {M} ρ t v) (s ∘ singleton-pos t) ≡ _⊔_ M (ρ-pos-fin M ρ s) v
eigenpos-pos-update M ρ t v s t∉s =
  cong (ρ-pos-fin M (_[_/_]ᶠ {M} ρ t v)) (merge-singleton s t)
  ∙ ρ-pos-fin-insertToken M (_[_/_]ᶠ {M} ρ t v) t s (λ mem → t∉s mem)
  ∙ cong₂ (_⊔_ M) (update-same M ρ t v) (ρ-pos-update-not-in M ρ t v s t∉s)
  ∙ ⊔-comm M v (ρ-pos-fin M ρ s)

lub-eq-when-leq : ∀ (M : FiniteModel) (ws v : World M) → _≤?_ M ws v ≡ true → _⊔_ M ws v ≡ v
lub-eq-when-leq M ws v leq = ≤?-⊔ M ws v leq

-- Eigenpos-preserve-ctx: updating at a fresh token preserves context satisfaction
eigenpos-preserve-ctx : ∀ (M : FiniteModel) (ρ : FiniteInterpretation M) (v : World M)
                          (t : Token) (Γ : List PFormula)
                        → TokenFresh t Γ
                        → M , ρ ⊩Ctxᶠ Γ → M , (_[_/_]ᶠ {M} ρ t v) ⊩Ctxᶠ Γ
eigenpos-preserve-ctx M ρ v t Γ freshΓ satΓ pf mem =
  ⊩ᶠ-update-not-in-rev M ρ t v pf (TokenFresh-lookup freshΓ pf mem) (satΓ pf mem)

-- Eigenpos-succ-back: succedent satisfaction transfers back when token is fresh
eigenpos-succ-back : ∀ (M : FiniteModel) (ρ : FiniteInterpretation M) (v : World M)
                       (t : Token) (Δ : List PFormula)
                     → TokenFresh t Δ
                     → M , (_[_/_]ᶠ {M} ρ t v) ⊩Succᶠ Δ → M , ρ ⊩Succᶠ Δ
eigenpos-succ-back M ρ v t Δ freshΔ (pf , mem , sat) =
  (pf , mem , ⊩ᶠ-update-not-in M ρ t v pf (TokenFresh-lookup freshΔ pf mem) sat)

-- =============================================================================
-- Soundness Clauses
-- =============================================================================

-- Axiom
finiteSoundness Ax M ms ρ satΓ = ⊩Succ-here (⊩Ctx-head satΓ)

-- Cut - use findSatisfied for decidable dispatch
finiteSoundness (Cut {Γ₁} {A} {s} {Δ₁} {Γ₂} {Δ₂} d₁ d₂) M ms ρ satΓ = 
  let satΓ₁ = ⊩Ctx-split-l Γ₁ Γ₂ satΓ
      satΓ₂ = ⊩Ctx-split-r Γ₁ Γ₂ satΓ
      ih₁ = finiteSoundness d₁ M ms ρ satΓ₁
  in cut-dispatch ih₁
  where
    cut-dispatch : M , ρ ⊩Succᶠ ([ A ^ s ] ++ Δ₁) → M , ρ ⊩Succᶠ (Δ₁ ++ Δ₂)
    cut-dispatch (pf , here , satA) =
      let satΓ₂A = ⊩Ctx-snoc Γ₂ (⊩Ctx-split-r Γ₁ Γ₂ satΓ) satA
      in ⊩Succ-,,-r Δ₁ Δ₂ (finiteSoundness d₂ M ms ρ satΓ₂A)
    cut-dispatch (pf , there mem , sat) = ⊩Succ-,,-l Δ₁ Δ₂ (pf , mem , sat)

-- Weakening (W⊢ adds to end of context, so use ⊩Ctx-init)
finiteSoundness (W⊢ {Γ} d) M ms ρ satΓ = finiteSoundness d M ms ρ (⊩Ctx-init Γ satΓ)
finiteSoundness (⊢W d) M ms ρ satΓ = ⊩Succ-there (finiteSoundness d M ms ρ satΓ)

-- Contraction (C⊢ contracts last two identical elements into one)
-- Note: ,, is left-associative but ++ is right-associative, need to be careful
finiteSoundness (C⊢ {Γ = Γ₀} {A} {s} d) M ms ρ satΓ =
  finiteSoundness d M ms ρ (⊩Ctx-dup-last Γ₀ satΓ)

finiteSoundness (⊢C d) M ms ρ satΓ = contract-succ (finiteSoundness d M ms ρ satΓ)

-- Exchange left
-- Conclusion context: Γ₁ ,, [ B ^ t ] ,, [ A ^ s ] ,, Γ₂
-- Premise context: Γ₁ ,, [ A ^ s ] ,, [ B ^ t ] ,, Γ₂
finiteSoundness (Exc⊢ {Γ₁} {A} {s} {B} {t} {Γ₂} d) M ms ρ satΓ =
  finiteSoundness d M ms ρ (⊩Ctx-exchange Γ₁ A s B t Γ₂ satΓ)

-- Exchange right
-- Premise succedent: Δ₁ ,, [ A ^ s ] ,, [ B ^ t ] ,, Δ₂
-- Conclusion succedent: Δ₁ ,, [ B ^ t ] ,, [ A ^ s ] ,, Δ₂
finiteSoundness (⊢Exc {Γ} {Δ₁} {A} {s} {B} {t} {Δ₂} d) M ms ρ satΓ =
  ⊩Succ-exchange Δ₁ A s B t Δ₂ (finiteSoundness d M ms ρ satΓ)

-- Negation left
-- ¬⊢ : (Γ ⊢ [ A ^ s ] ,, Δ) → (Γ ,, [ (¬ A) ^ s ] ⊢ Δ)
-- Conclusion context is Γ ++ [ (¬ A) ^ s ], so (¬ A) is at the END
finiteSoundness (¬⊢ {Γ} {A} {s} {Δ} d) M ms ρ satΓ =
  neg-left-dispatch (finiteSoundness d M ms ρ (⊩Ctx-init Γ satΓ))
  where
    neg-left-dispatch : M , ρ ⊩Succᶠ ([ A ^ s ] ,, Δ) → M , ρ ⊩Succᶠ Δ
    neg-left-dispatch (pf , here , satA) =
      -- satA : eval M w A ≡ true
      -- sat¬A : not (eval M w A) ≡ true, so eval M w A ≡ false
      let sat¬A = ⊩Ctx-last Γ satΓ
          A-false : eval M (ρ-pos-fin M ρ s) A ≡ false
          A-false = not-true-is-false sat¬A
      in ⊥-rec (false≢true (sym A-false ∙ satA))
    neg-left-dispatch (pf , there mem , sat) = (pf , mem , sat)

-- Negation right - KEY CONSTRUCTIVE CASE
-- ⊢¬ : (Γ ,, [ A ^ s ] ⊢ Δ) → (Γ ⊢ [ (¬ A) ^ s ] ,, Δ)
-- Premise adds A ^ s at the END of context
finiteSoundness (⊢¬ {Γ} {A} {s} {Δ} d) M ms ρ satΓ
  with decide-⊨ᶠ M (ρ-pos-fin M ρ s) A
... | yes satA = shift-past-neg (finiteSoundness d M ms ρ (⊩Ctx-snoc Γ satΓ satA))
... | no ¬satA = ⊩Succ-here (not-false-eq (decide-no-means-false ¬satA))

-- Conjunction left
-- ∧₁⊢ : (Γ ,, [ A ^ s ] ⊢ Δ) → (Γ ,, [ (A ∧ B) ^ s ] ⊢ Δ)
-- ∧₂⊢ : (Γ ,, [ B ^ s ] ⊢ Δ) → (Γ ,, [ (A ∧ B) ^ s ] ⊢ Δ)
-- Conclusion has (A ∧ B) at END, premise has A or B at END
finiteSoundness (∧₁⊢ {Γ} d) M ms ρ satΓ =
  let satA∧B = ⊩Ctx-last Γ satΓ
      satA = and-true-l satA∧B
  in finiteSoundness d M ms ρ (⊩Ctx-snoc Γ (⊩Ctx-init Γ satΓ) satA)

finiteSoundness (∧₂⊢ {Γ} d) M ms ρ satΓ =
  let satA∧B = ⊩Ctx-last Γ satΓ
      satB = and-true-r satA∧B
  in finiteSoundness d M ms ρ (⊩Ctx-snoc Γ (⊩Ctx-init Γ satΓ) satB)

-- Conjunction right
finiteSoundness (⊢∧ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} d₁ d₂) M ms ρ satΓ = 
  let satΓ₁ = ⊩Ctx-split-l Γ₁ Γ₂ satΓ
      satΓ₂ = ⊩Ctx-split-r Γ₁ Γ₂ satΓ
      ih₁ = finiteSoundness d₁ M ms ρ satΓ₁
      ih₂ = finiteSoundness d₂ M ms ρ satΓ₂
  in and-dispatch ih₁ ih₂
  where
    and-dispatch : M , ρ ⊩Succᶠ ([ A ^ s ] ++ Δ₁)
                 → M , ρ ⊩Succᶠ ([ B ^ s ] ++ Δ₂)
                 → M , ρ ⊩Succᶠ ([ (A and' B) ^ s ] ++ Δ₁ ++ Δ₂)
    and-dispatch (pf₁ , here , satA) (pf₂ , here , satB) = 
      ⊩Succ-here (and-intro satA satB)
    and-dispatch (pf₁ , here , satA) (pf₂ , there mem₂ , sat₂) = 
      ⊩Succ-,,-r ([ (A and' B) ^ s ] ++ Δ₁) Δ₂ (pf₂ , mem₂ , sat₂)
    and-dispatch (pf₁ , there mem₁ , sat₁) _ = 
      ⊩Succ-there (⊩Succ-,,-l Δ₁ Δ₂ (pf₁ , mem₁ , sat₁))

-- Disjunction left - KEY CONSTRUCTIVE CASE
-- ∨⊢ : (Γ₁ ,, [ A ^ s ] ⊢ Δ₁) → (Γ₂ ,, [ B ^ s ] ⊢ Δ₂) → (Γ₁ ,, Γ₂ ,, [ (A ∨ B) ^ s ] ⊢ Δ₁ ,, Δ₂)
-- Note: ,, is right-associative, so Γ₁ ,, Γ₂ ,, [ pf ] = Γ₁ ++ (Γ₂ ++ [ pf ])
-- Need to use ++-assoc to get (Γ₁ ++ Γ₂) ++ [ pf ]
finiteSoundness (∨⊢ {Γ₁} {A} {s} {Δ₁} {Γ₂} {B} {Δ₂} d₁ d₂) M ms ρ satΓ =
  or-dispatch (decide-⊨ᶠ M (ρ-pos-fin M ρ s) A)
  where
    -- Convert satΓ using associativity: Γ₁ ++ (Γ₂ ++ [pf]) → (Γ₁ ++ Γ₂) ++ [pf]
    -- ++-assoc gives (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs), so we need sym
    satΓ' : M , ρ ⊩Ctxᶠ ((Γ₁ ++ Γ₂) ++ [ (A or' B) ^ s ])
    satΓ' = subst (λ ctx → M , ρ ⊩Ctxᶠ ctx) (sym (++-assoc Γ₁ Γ₂ [ (A or' B) ^ s ])) satΓ

    or-dispatch : Dec (eval M (ρ-pos-fin M ρ s) A ≡ true) → M , ρ ⊩Succᶠ (Δ₁ ++ Δ₂)
    or-dispatch (yes satA) =
      let satΓ₁₂ = ⊩Ctx-init (Γ₁ ++ Γ₂) satΓ'
          satΓ₁ = ⊩Ctx-split-l Γ₁ Γ₂ satΓ₁₂
          satΓ₁A = ⊩Ctx-snoc Γ₁ satΓ₁ satA
      in ⊩Succ-,,-l Δ₁ Δ₂ (finiteSoundness d₁ M ms ρ satΓ₁A)
    or-dispatch (no ¬satA) =
      let sat∨ = ⊩Ctx-last (Γ₁ ++ Γ₂) satΓ'
          satB = or-right-true sat∨ (decide-no-means-false ¬satA)
          satΓ₁₂ = ⊩Ctx-init (Γ₁ ++ Γ₂) satΓ'
          satΓ₂ = ⊩Ctx-split-r Γ₁ Γ₂ satΓ₁₂
          satΓ₂B = ⊩Ctx-snoc Γ₂ satΓ₂ satB
      in ⊩Succ-,,-r Δ₁ Δ₂ (finiteSoundness d₂ M ms ρ satΓ₂B)

-- Disjunction right
finiteSoundness (⊢∨₁ d) M ms ρ satΓ = dispatch-or1 (finiteSoundness d M ms ρ satΓ)
finiteSoundness (⊢∨₂ d) M ms ρ satΓ = dispatch-or2 (finiteSoundness d M ms ρ satΓ)

-- Implication left - KEY CONSTRUCTIVE CASE
-- ⇒⊢ : (Γ₁ ,, [ B ^ s ] ⊢ Δ₁) → (Γ₂ ⊢ [ A ^ s ] ,, Δ₂) → (Γ₁ ,, Γ₂ ,, [ (A ⇒ B) ^ s ] ⊢ Δ₁ ,, Δ₂)
-- Note: ,, is right-associative, so need associativity conversion
finiteSoundness (⇒⊢ {Γ₁} {B} {s} {Δ₁} {Γ₂} {A} {Δ₂} d₁ d₂) M ms ρ satΓ =
  impl-dispatch (decide-⊨ᶠ M (ρ-pos-fin M ρ s) A)
  where
    -- Convert satΓ using associativity
    satΓ' : M , ρ ⊩Ctxᶠ ((Γ₁ ++ Γ₂) ++ [ (A ⇒ B) ^ s ])
    satΓ' = subst (λ ctx → M , ρ ⊩Ctxᶠ ctx) (sym (++-assoc Γ₁ Γ₂ [ (A ⇒ B) ^ s ])) satΓ

    impl-dispatch : Dec (eval M (ρ-pos-fin M ρ s) A ≡ true) → M , ρ ⊩Succᶠ (Δ₁ ++ Δ₂)
    impl-dispatch (no ¬satA) =
      let satΓ₁₂ = ⊩Ctx-init (Γ₁ ++ Γ₂) satΓ'
          satΓ₂ = ⊩Ctx-split-r Γ₁ Γ₂ satΓ₁₂
      in impl-left-no-A ¬satA (finiteSoundness d₂ M ms ρ satΓ₂)
      where
        impl-left-no-A : (eval M (ρ-pos-fin M ρ s) A ≡ true → ⊥)
                       → M , ρ ⊩Succᶠ ([ A ^ s ] ,, Δ₂) → M , ρ ⊩Succᶠ (Δ₁ ,, Δ₂)
        impl-left-no-A ¬satA (pf , here , satA) = ⊥-rec (¬satA satA)
        impl-left-no-A ¬satA (pf , there mem , sat) = ⊩Succ-,,-r Δ₁ Δ₂ (pf , mem , sat)
    impl-dispatch (yes satA) =
      let sat⇒ = ⊩Ctx-last (Γ₁ ++ Γ₂) satΓ'
          satB = impl-true sat⇒ satA
          satΓ₁₂ = ⊩Ctx-init (Γ₁ ++ Γ₂) satΓ'
          satΓ₁ = ⊩Ctx-split-l Γ₁ Γ₂ satΓ₁₂
          satΓ₁B = ⊩Ctx-snoc Γ₁ satΓ₁ satB
      in ⊩Succ-,,-l Δ₁ Δ₂ (finiteSoundness d₁ M ms ρ satΓ₁B)

-- Implication right - KEY CONSTRUCTIVE CASE
-- ⊢⇒ : (Γ ,, [ A ^ s ] ⊢ [ B ^ s ] ,, Δ) → (Γ ⊢ [ (A ⇒ B) ^ s ] ,, Δ)
-- Premise adds A at END
finiteSoundness (⊢⇒ {Γ} {A} {s} {B} {Δ} d) M ms ρ satΓ
  with decide-⊨ᶠ M (ρ-pos-fin M ρ s) A
... | yes satA = dispatch-impl (finiteSoundness d M ms ρ (⊩Ctx-snoc Γ satΓ satA))
... | no ¬satA = ⊩Succ-here (or-true-intro-l (not-false-eq (decide-no-means-false ¬satA)))

-- =============================================================================
-- Modal Rules - Soundness
-- =============================================================================

-- □⊢ : (Γ ,, [ A ^ (s ∘ t) ] ⊢ Δ) → (Γ ,, [ (□ A) ^ s ] ⊢ Δ)
-- Implicit order: Γ, A, s, t, Δ
finiteSoundness (□⊢ {Γ} {A} {s} {t} {Δ} d) M ms ρ satΓ =
  -- If □A holds at ρ(s), then A holds at ρ(s ∘ t) since s ⊑ (s ∘ t)
  let sat□As : M , ρ ⊩ᶠ ((□ A) ^ s)
      sat□As = satΓ ((□ A) ^ s) (∈-last Γ)
      -- ρ(s) ≤ ρ(s ∘ t) since s ⊑ (s ∘ t)
      ws = ρ-pos-fin M ρ s
      wst = ρ-pos-fin M ρ (s ∘ t)
      accessible : _≤?_ M ws wst ≡ true
      accessible = subset-to-≤ M ρ s (s ∘ t) (⊑-merge-l s t)
      satAst : M , ρ ⊩ᶠ (A ^ (s ∘ t))
      satAst = box-accessible M ms {A} {ws} {wst} sat□As accessible
      satΓ' = ⊩Ctx-init Γ satΓ
  in finiteSoundness d M ms ρ (⊩Ctx-snoc Γ satΓ' satAst)

-- ⊢□ : x ∉Pos s → TokenFresh x Γ → TokenFresh x Δ → (Γ ⊢ [ A ^ insertToken x s ] ,, Δ) → (Γ ⊢ [ (□ A) ^ s ] ,, Δ)
-- The eigentoken t is fresh, so A holds at all extensions of s
-- Implicit order: x, s, Γ, Δ, A
finiteSoundness (⊢□ {t} {s} {Γ} {Δ} {A} t∉s freshΓ freshΔ d) M ms ρ satΓ =
  -- First check if Δ is already satisfied - if so, we're done
  box-case (findSatisfied M ρ Δ)
  where
    ws = ρ-pos-fin M ρ s
    -- exts is insertToken t s (the extended position)
    exts = insertToken t s

    box-case : Dec (M , ρ ⊩Succᶠ Δ) → M , ρ ⊩Succᶠ ([ (□ A) ^ s ] ,, Δ)
    -- Case: Δ is satisfied at ρ, just return that
    box-case (yes satΔ) = ⊩Succ-there satΔ
    -- Case: Δ is not satisfied, so we prove □A
    box-case (no ¬satΔ) = ⊩Succ-here box-proof
      where
        -- For any v accessible from ws, A holds at v
        all-accessible-hold : (v : World M) → _≤?_ M ws v ≡ true → eval M v A ≡ true
        all-accessible-hold v acc =
          let -- Update interpretation: ρ' = ρ[t/v]
              ρ' = _[_/_]ᶠ {M} ρ t v
              -- Context Γ is still satisfied by ρ' (t is fresh in Γ)
              satΓ' : M , ρ' ⊩Ctxᶠ Γ
              satΓ' = eigenpos-preserve-ctx M ρ v t Γ freshΓ satΓ
              -- Apply IH: get satisfaction of [A^exts] ++ Δ
              ih = finiteSoundness d M ms ρ' satΓ'
          in case-analysis ih
          where
            case-analysis : M , (_[_/_]ᶠ {M} ρ t v) ⊩Succᶠ ([ A ^ exts ] ,, Δ) → eval M v A ≡ true
            -- Case: A^exts is satisfied
            case-analysis (pf , here , satA) =
              -- satA : eval M (ρ-pos-fin M (ρ[t/v]) exts) A ≡ true
              -- exts = insertToken t s = s ∘ [t]
              -- (ρ[t/v])(exts) = (ρ[t/v])(s ∘ [t]) = ρ(s) ⊔ v = v (since ws ≤ v)
              let pos-eq : ρ-pos-fin M (_[_/_]ᶠ {M} ρ t v) exts ≡ v
                  pos-eq = cong (ρ-pos-fin M (_[_/_]ᶠ {M} ρ t v)) (sym (merge-singleton s t))
                         ∙ eigenpos-pos-update M ρ t v s t∉s
                         ∙ lub-eq-when-leq M ws v acc
              in subst (λ w → eval M w A ≡ true) pos-eq satA
            -- Case: Something in Δ is satisfied under ρ[t/v]
            case-analysis (pf , there mem , sat) =
              -- Transfer back to ρ: since t is fresh in Δ, M, ρ ⊩Succᶠ Δ
              -- But we assumed ¬satΔ, contradiction!
              let satΔ = eigenpos-succ-back M ρ v t Δ freshΔ (pf , mem , sat)
              in ⊥-rec (¬satΔ satΔ)

        box-proof : eval M ws (□ A) ≡ true
        box-proof = box-eigen-sem ms A ws all-accessible-hold

-- ♢⊢ : x ∉Pos s → TokenFresh x Γ → TokenFresh x Δ → (Γ ,, [ A ^ insertToken x s ] ⊢ Δ) → (Γ ,, [ (♢ A) ^ s ] ⊢ Δ)
-- The eigentoken t witnesses the ♢A decomposition
-- Implicit order: x, s, Γ, Δ, A
finiteSoundness (♢⊢ {t} {s} {Γ} {Δ} {A} t∉s freshΓ freshΔ d) M ms ρ satΓ =
  -- Get ♢A at ρ(s) from the context
  let sat♢A : M , ρ ⊩ᶠ ((♢ A) ^ s)
      sat♢A = ⊩Ctx-last Γ satΓ
      -- Use diamond-eigen-sem to get a witness world v where A holds
      ws = ρ-pos-fin M ρ s
      (v , acc , satAv) = diamond-eigen-sem ms A ws sat♢A
      -- Update interpretation: ρ' = ρ[t/v]
      ρ' = _[_/_]ᶠ {M} ρ t v
      -- exts is insertToken t s
      exts = insertToken t s
      -- Context Γ (without ♢A) is still satisfied by ρ' (t is fresh in Γ)
      satΓ-init : M , ρ ⊩Ctxᶠ Γ
      satΓ-init = ⊩Ctx-init Γ satΓ
      satΓ' : M , ρ' ⊩Ctxᶠ Γ
      satΓ' = eigenpos-preserve-ctx M ρ v t Γ freshΓ satΓ-init
      -- A^exts is satisfied under ρ' since ρ'(exts) = ρ'(s++[t]) = ws ⊔ v = v
      pos-eq : ρ-pos-fin M ρ' exts ≡ v
      pos-eq = cong (ρ-pos-fin M ρ') (sym (merge-singleton s t))
             ∙ eigenpos-pos-update M ρ t v s t∉s
             ∙ lub-eq-when-leq M ws v acc
      satA' : M , ρ' ⊩ᶠ (A ^ exts)
      satA' = subst (λ w → eval M w A ≡ true) (sym pos-eq) satAv
      -- Build full context satisfaction: Γ ++ [A^exts]
      satΓA' : M , ρ' ⊩Ctxᶠ (Γ ,, [ A ^ exts ])
      satΓA' = ⊩Ctx-snoc Γ satΓ' satA'
      -- Apply IH: get satisfaction of Δ under ρ'
      ih : M , ρ' ⊩Succᶠ Δ
      ih = finiteSoundness d M ms ρ' satΓA'
  -- Transfer back to ρ: since t is fresh in Δ
  in eigenpos-succ-back M ρ v t Δ freshΔ ih

-- ⊢♢ : (Γ ⊢ [ A ^ (s ∘ t) ] ,, Δ) → (Γ ⊢ [ (♢ A) ^ s ] ,, Δ)
-- Implicit order: Γ, A, s, t, Δ
finiteSoundness (⊢♢ {Γ} {A} {s} {t} {Δ} d) M ms ρ satΓ =
  diamond-dispatch (finiteSoundness d M ms ρ satΓ)
  where
    -- s ⊑ (s ∘ t), so ρ(s) ≤ ρ(s ∘ t)
    diamond-dispatch : M , ρ ⊩Succᶠ ([ A ^ (s ∘ t) ] ,, Δ) → M , ρ ⊩Succᶠ ([ (♢ A) ^ s ] ,, Δ)
    diamond-dispatch (pf , here , satAst) =
      -- If A holds at ρ(s ∘ t) and s ⊑ (s ∘ t), then ♢A holds at ρ(s)
      let ws = ρ-pos-fin M ρ s
          wst = ρ-pos-fin M ρ (s ∘ t)
          accessible : _≤?_ M ws wst ≡ true
          accessible = subset-to-≤ M ρ s (s ∘ t) (⊑-merge-l s t)
          sat♢ : M , ρ ⊩ᶠ ((♢ A) ^ s)
          sat♢ = diamond-accessible M ms {A} {ws} {wst} satAst accessible
      in ⊩Succ-here sat♢
    diamond-dispatch (pf , there mem , sat) = ⊩Succ-there (pf , mem , sat)