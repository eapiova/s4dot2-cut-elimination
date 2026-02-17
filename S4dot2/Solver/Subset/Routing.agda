{-# OPTIONS --safe #-}

module S4dot2.Solver.Subset.Routing where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Data.Bool using (Bool; true; false; not; _and_; if_then_else_)
open import Cubical.Data.Empty as Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Relation.Nullary using (Discrete; yes; no; Dec)
open import Cubical.Data.Maybe using (Maybe; just; nothing)
open import Cubical.Data.Unit using (Unit*; tt*)
open import Cubical.Data.Sigma using (Σ; _,_; _×_; fst; snd)

open import S4dot2.BoolReflect using (and-true-l; and-true-r)

-- Inspect pattern for with-abstraction (private to avoid namespace conflicts)
private
  data Singleton {a} {A : Set a} (x : A) : Set a where
    _with≡_ : (y : A) → x ≡ y → Singleton x

  inspect : ∀ {a} {A : Set a} (x : A) → Singleton x
  inspect x = x with≡ refl

open import S4dot2.ListExt using (_∈_; here; there; _⊆_; mem-++-l; mem-++-r)
open import S4dot2.Solver.Subset.Core
open import S4dot2.Solver.Subset.Normal

private
  variable
    ℓ : Level

-- Routing module, parameterized by element type
module Routing {A : Type ℓ} (_≟_ : Discrete A) where

  open NormalForm _≟_ public

  -- Helper for impossible cases in Bool proofs
  false≢true : false ≡ true → ⊥
  false≢true p = subst (λ b → if b then ⊥ else Unit*) p tt*

  -- Helper for impossible cases in Maybe proofs
  nothing≢just : ∀ {X : Type ℓ} {x : X} → nothing ≡ just x → ⊥
  nothing≢just {X = X} p = subst (λ { nothing → Unit* ; (just _) → ⊥ }) p tt*

  -- Check if two naturals are equal
  _≟ℕ_ : ℕ → ℕ → Bool
  zero ≟ℕ zero = true
  zero ≟ℕ suc _ = false
  suc _ ≟ℕ zero = false
  suc m ≟ℕ suc n = m ≟ℕ n

  -- Check if element (index) is in removal list (of indices)
  elemInList : ℕ → List ℕ → Bool
  elemInList x [] = false
  elemInList x (y ∷ ys) with x ≟ℕ y
  ... | true = true
  ... | false = elemInList x ys

  -- Check if all elements in first list are in second list
  allIn : List ℕ → List ℕ → Bool
  allIn [] _ = true
  allIn (x ∷ xs) ys = elemInList x ys and allIn xs ys

  -- Check if an LHS atom can route to an RHS atom
  atomCanRouteTo : Atom → Atom → Bool
  atomCanRouteTo (list-atom i rs1) (list-atom j rs2) = (i ≟ℕ j) and allIn rs2 rs1
  atomCanRouteTo (elem-atom i rs1) (elem-atom j rs2) = (i ≟ℕ j) and allIn rs2 rs1
  atomCanRouteTo _ _ = false

  -- Find which RHS atom an LHS atom can route to
  findRoute : Atom → NormalForm → Maybe Atom
  findRoute a [] = nothing
  findRoute a (b ∷ bs) = if atomCanRouteTo a b then just b else findRoute a bs

  -- Check if all LHS atoms can route to some RHS atom
  canSolve : NormalForm → NormalForm → Bool
  canSolve [] _ = true
  canSolve (a ∷ as) rhs with findRoute a rhs
  ... | nothing = false
  ... | just _ = canSolve as rhs

  -- Soundness of ≟ℕ
  ≟ℕ-sound : ∀ m n → m ≟ℕ n ≡ true → m ≡ n
  ≟ℕ-sound zero zero _ = refl
  ≟ℕ-sound zero (suc n) p = ⊥-rec (false≢true p)
  ≟ℕ-sound (suc m) zero p = ⊥-rec (false≢true p)
  ≟ℕ-sound (suc m) (suc n) p = cong suc (≟ℕ-sound m n p)

  -- elemInList correctness
  elemInList-sound : ∀ (x : ℕ) (ys : List ℕ) → elemInList x ys ≡ true → x ∈ ys
  elemInList-sound x [] p = ⊥-rec (false≢true p)
  elemInList-sound x (y ∷ ys) p = helper (x ≟ℕ y) refl p
    where
      helper : (b : Bool) → x ≟ℕ y ≡ b → elemInList x (y ∷ ys) ≡ true → x ∈ (y ∷ ys)
      helper true eq _ = subst (_∈ (y ∷ ys)) (sym (≟ℕ-sound x y eq)) here
      helper false eq p' = there (elemInList-sound x ys (lemma eq p'))
        where
          -- elemInList x (y ∷ ys) when (x ≟ℕ y) = false reduces to elemInList x ys
          lemma : x ≟ℕ y ≡ false → elemInList x (y ∷ ys) ≡ true → elemInList x ys ≡ true
          lemma eq2 p2 with x ≟ℕ y
          ... | true = ⊥-rec (false≢true (sym eq2))
          ... | false = p2

  -- allIn correctness
  allIn-sound : ∀ (rs2 rs1 : List ℕ) → allIn rs2 rs1 ≡ true → rs2 ⊆ rs1
  allIn-sound [] rs1 p x ()
  allIn-sound (r ∷ rs2) rs1 p x here = elemInList-sound r rs1 (and-true-l p)
  allIn-sound (r ∷ rs2) rs1 p x (there xIn) = allIn-sound rs2 rs1 (and-true-r p) x xIn

  -- removeIndices monotonicity: if rs2 ⊆ rs1, then removeIndices rs1 xs ⊆ removeIndices rs2 xs
  -- Note: removeIndices rs2 xs means "remove elements indexed by rs2".
  -- If rs2 ⊆ rs1, then rs1 removes MORE (or same) than rs2.
  -- So removeIndices rs1 xs ⊆ removeIndices rs2 xs.
  
  -- We need to prove this.
  -- removeIndices is defined by recursion on list of indices.
  -- Proving monotonicity for arbitrary subsets is hard definitionally.
  -- But we can prove for single removal: removeIndices (k::rs) xs subseteq removeIndices rs xs.
  -- removeIndices (k::rs) xs = removeIndices rs (evalRem k xs) ...
  -- This approach is hard.
  
  -- Better: Prove `y ∈ removeIndices rs xs ρe → y ∈ xs × (∀ k. k ∈ rs → val(k) != y)`?
  -- If we can characterize membership in `removeIndices` like `mem-removeMany-intro`.
  
  -- Lemma: y ∈ evalRem k xs ρe -> y ∈ xs
  mem-evalRem-subset : ∀ (k : ℕ) (xs : List A) (ρe : List A) (y : A)
                     → y ∈ evalRem k xs ρe → y ∈ xs
  mem-evalRem-subset k xs ρe y yIn with lookupElem ρe k
  ... | nothing = yIn
  ... | just v = mem-removeAll-subset yIn

  -- Lemma: y ∈ removeIndices rs xs ρe -> y ∈ xs
  mem-removeIndices-subset : ∀ (rs : List ℕ) (xs : List A) (ρe : List A) (y : A)
                           → y ∈ removeIndices rs xs ρe → y ∈ xs
  mem-removeIndices-subset [] xs ρe y yIn = yIn
  mem-removeIndices-subset (r ∷ rs) xs ρe y yIn =
    let yInEval = mem-removeIndices-subset rs (evalRem r xs ρe) ρe y yIn
    in mem-evalRem-subset r xs ρe y yInEval

  -- Main characteristic lemma: if y in xs and for all k in rs, val(k) != y, then y in removeIndices rs xs
  -- We need the converse too?
  -- We need `removeIndices-mono`.
  
  -- Let's define `removeIndices-mono` directly if possible or via membership.
  -- `mem-removeIndices : y ∈ removeIndices rs xs ρe <-> y ∈ xs AND (∀ k ∈ rs, lookup k != just y)`
  
  mem-removeIndices-intro : ∀ (rs : List ℕ) (xs : List A) (ρe : List A) (y : A)
                          → y ∈ xs
                          → (∀ k → k ∈ rs → ∀ v → lookupElem ρe k ≡ just v → y ≢ v)
                          → y ∈ removeIndices rs xs ρe
  mem-removeIndices-intro [] xs ρe y yIn _ = yIn
  mem-removeIndices-intro (r ∷ rs) xs ρe y yIn notIn =
       mem-removeIndices-intro rs (evalRem r xs ρe) ρe y yInEval notInRs
    where
       -- y is not removed by r
       yNotInR : ∀ v → lookupElem ρe r ≡ just v → y ≢ v
       yNotInR v eq = notIn r here v eq

       helper : (m : Maybe A) → lookupElem ρe r ≡ m → y ∈ xs → (∀ v → m ≡ just v → y ≢ v) → y ∈ evalRem r xs ρe
       helper nothing eq yIn' _ = subst (y ∈_) (sym (evalRem-nothing r xs ρe eq)) yIn'
       helper (just v) eq yIn' neq = subst (y ∈_) (sym (evalRem-just r xs ρe v eq)) (mem-removeAll-neq yIn' (λ y≡v → neq v refl (sym y≡v)))

       yInEval : y ∈ evalRem r xs ρe
       yInEval = helper (lookupElem ρe r) refl yIn yNotInR

       notInRs : ∀ k → k ∈ rs → ∀ v → lookupElem ρe k ≡ just v → y ≢ v
       notInRs k kIn v eq = notIn k (there kIn) v eq

  not-eq-from-removeIndices : ∀ (rs : List ℕ) (xs : List A) (ρe : List A) (y : A)
                            → y ∈ removeIndices rs xs ρe
                            → ∀ k → k ∈ rs → ∀ v → lookupElem ρe k ≡ just v → y ≢ v
  not-eq-from-removeIndices (r ∷ rs) xs ρe y yIn k here v eq =
     -- k = r. y ∈ removeIndices rs (evalRem r xs)
     -- y ∈ evalRem r ... -> y != val(r)
     let yInEval = mem-removeIndices-subset rs (evalRem r xs ρe) ρe y yIn
     in helper (lookupElem ρe r) refl yInEval v eq
     where
       just-inj' : ∀ {X : Type ℓ} {x y : X} → _≡_ {A = Maybe X} (just x) (just y) → x ≡ y
       just-inj' {X = X} {x = x} p = subst (λ m → x ≡ fromJust' m x) p refl
         where
           fromJust' : Maybe X → X → X
           fromJust' (just a) _ = a
           fromJust' nothing def = def

       helper : (m : Maybe A) → lookupElem ρe r ≡ m → y ∈ evalRem r xs ρe → (v : A) → m ≡ just v → y ≢ v
       helper nothing meq _ v meq2 _ = ⊥-rec (nothing≢just meq2)
       helper (just v') meq yIn' v eq y≡v =
         -- yIn' : y ∈ evalRem r xs ρe
         -- eq : just v' ≡ just v, extract v' ≡ v
         let v'≡v = just-inj' eq
             -- With meq : lookupElem ρe r ≡ just v', we know evalRem r xs ρe = removeAll v' xs
             yIn'' = subst (y ∈_) (evalRem-just r xs ρe v' meq) yIn'
             -- yIn'' : y ∈ removeAll v' xs
             -- Given y ≡ v and v' ≡ v, we get y ≡ v', so y ∈ removeAll v' xs → v' ∈ removeAll v' xs
             v'In' = subst (_∈ removeAll v' xs) (y≡v ∙ sym v'≡v) yIn''
         in not-in-removeAll v' xs v'In'
  not-eq-from-removeIndices (r ∷ rs) xs ρe y yIn k (there kIn) v eq =
     not-eq-from-removeIndices rs (evalRem r xs ρe) ρe y yIn k kIn v eq

  removeIndices-mono : ∀ (rs1 rs2 : List ℕ) (xs : List A) (ρe : List A)
                     → rs2 ⊆ rs1 -- rs2 restricts less? No. rs2 ⊆ rs1 means rs2 is SUBSET of removals.
                     -- Wait, if rs2 has FEWER removals, result is LARGER.
                     -- We want: LHS ⊆ RHS.
                     -- routing: atomCanRouteTo LHS RHS.
                     -- `allIn rs2 rs1`. Means `rs2 ⊆ rs1`.
                     -- LHS has removals `rs1`. RHS has removals `rs2`.
                     -- `rs2` is subset of `rs1`.
                     -- So LHS has MORE removals.
                     -- So LHS is smaller.
                     -- So LHS ⊆ RHS. Correct.
                     → removeIndices rs1 xs ρe ⊆ removeIndices rs2 xs ρe
  removeIndices-mono rs1 rs2 xs ρe sub y yIn =
    let yInXs = mem-removeIndices-subset rs1 xs ρe y yIn
        notInRs1 = not-eq-from-removeIndices rs1 xs ρe y yIn
        
        notInRs2 : ∀ k → k ∈ rs2 → ∀ v → lookupElem ρe k ≡ just v → y ≢ v
        notInRs2 k kIn v eq = notInRs1 k (sub k kIn) v eq
    in mem-removeIndices-intro rs2 xs ρe y yInXs notInRs2

  -- Soundness of atomCanRouteTo for list atoms
  atomRoute-list-sound : ∀ (i j : ℕ) (rs1 rs2 : List ℕ) (ρ : Env)
                       → (i ≟ℕ j) and allIn rs2 rs1 ≡ true
                       → ⟦ list-atom i rs1 ⟧atom ρ ⊆ ⟦ list-atom j rs2 ⟧atom ρ
  atomRoute-list-sound i j rs1 rs2 (ρl , ρe) p =
    let i≡j : i ≡ j
        i≡j = ≟ℕ-sound i j (and-true-l p)
        rs2⊆rs1 : rs2 ⊆ rs1
        rs2⊆rs1 = allIn-sound rs2 rs1 (and-true-r p)
    in subst (λ k → removeIndices rs1 (lookupList ρl k) ρe ⊆ removeIndices rs2 (lookupList ρl j) ρe) (sym i≡j)
             (removeIndices-mono rs1 rs2 (lookupList ρl j) ρe rs2⊆rs1)

  -- Soundness of atomCanRouteTo for elem atoms
  atomRoute-elem-sound : ∀ (i j : ℕ) (rs1 rs2 : List ℕ) (ρ : Env)
                       → atomCanRouteTo (elem-atom i rs1) (elem-atom j rs2) ≡ true
                       → ⟦ elem-atom i rs1 ⟧atom ρ ⊆ ⟦ elem-atom j rs2 ⟧atom ρ
  atomRoute-elem-sound i j rs1 rs2 (ρl , ρe) p =
    let i≡j : i ≡ j
        i≡j = ≟ℕ-sound i j (and-true-l p)
        rs2⊆rs1 : rs2 ⊆ rs1
        rs2⊆rs1 = allIn-sound rs2 rs1 (and-true-r p)
    in subst (λ k → ⟦ elem-atom k rs1 ⟧atom (ρl , ρe) ⊆ ⟦ elem-atom j rs2 ⟧atom (ρl , ρe)) (sym i≡j)
             (helper rs1 rs2 j ρe rs2⊆rs1)
    where
      helper : ∀ (rs1 rs2 : List ℕ) (j : ℕ) (ρe : List A)
             → rs2 ⊆ rs1
             → ⟦ elem-atom j rs1 ⟧atom (ρl , ρe) ⊆ ⟦ elem-atom j rs2 ⟧atom (ρl , ρe)
      helper rs1 rs2 j ρe sub y yIn with lookupElem ρe j
      ... | nothing = yIn -- [] ⊆ []
      ... | just v = removeIndices-mono rs1 rs2 (v ∷ []) ρe sub y yIn

  -- Combined soundness of atomCanRouteTo
  atomCanRouteTo-sound : ∀ (a b : Atom) (ρ : Env)
                       → atomCanRouteTo a b ≡ true
                       → ⟦ a ⟧atom ρ ⊆ ⟦ b ⟧atom ρ
  atomCanRouteTo-sound (list-atom i rs1) (list-atom j rs2) ρ p =
    atomRoute-list-sound i j rs1 rs2 ρ p
  atomCanRouteTo-sound (list-atom _ _) (elem-atom _ _) _ p = ⊥-rec (false≢true p)
  atomCanRouteTo-sound (elem-atom _ _) (list-atom _ _) _ p = ⊥-rec (false≢true p)
  atomCanRouteTo-sound (elem-atom i rs1) (elem-atom j rs2) ρ p =
    atomRoute-elem-sound i j rs1 rs2 ρ p

  -- Helper: if atom is in nf, its semantics is a subset of nf semantics
  atom-in-nf-⊆ : ∀ (b : Atom) (rhs : NormalForm) (ρ : Env)
               → b ∈ rhs
               → ⟦ b ⟧atom ρ ⊆ ⟦ rhs ⟧nf ρ
  atom-in-nf-⊆ b (b' ∷ bs) ρ here y yIn = mem-++-l yIn
  atom-in-nf-⊆ b (b' ∷ bs) ρ (there bIn) y yIn =
    mem-++-r (⟦ b' ⟧atom ρ) (atom-in-nf-⊆ b bs ρ bIn y yIn)

  -- Helper for Maybe injectivity
  just-injective : ∀ {X : Type ℓ} {x y : X} → _≡_ {A = Maybe X} (just x) (just y) → x ≡ y
  just-injective {x = x} p = subst (λ m → x ≡ fromJust m x) p refl
    where
      fromJust : ∀ {X : Type ℓ} → Maybe X → X → X
      fromJust (just a) _ = a
      fromJust nothing def = def

  -- Helper for findRoute proofs: handles both membership and routing proof in one pass
  findRoute-aux : ∀ (a : Atom) (rhs : NormalForm) (b : Atom)
                → findRoute a rhs ≡ just b
                → (b ∈ rhs) × (atomCanRouteTo a b ≡ true)
  findRoute-aux a [] b p = ⊥-rec (nothing≢just p)
  findRoute-aux a (b' ∷ bs) b p = helper (atomCanRouteTo a b') refl
    where
      helper : (v : Bool) → atomCanRouteTo a b' ≡ v
             → (b ∈ (b' ∷ bs)) × (atomCanRouteTo a b ≡ true)
      helper true eq =
        let p' : just b' ≡ just b
            p' = subst (λ v → (if v then just b' else findRoute a bs) ≡ just b) eq p
            b'≡b : b' ≡ b
            b'≡b = just-injective p'
        in (subst (_∈ (b' ∷ bs)) b'≡b here) , subst (λ x → atomCanRouteTo a x ≡ true) b'≡b eq
      helper false eq =
        let p' : findRoute a bs ≡ just b
            p' = subst (λ v → (if v then just b' else findRoute a bs) ≡ just b) eq p
            rec = findRoute-aux a bs b p'
        in (there (fst rec)) , (snd rec)

  -- Helper: findRoute returns an atom that's in the RHS
  findRoute-∈ : ∀ (a : Atom) (rhs : NormalForm) (b : Atom)
              → findRoute a rhs ≡ just b
              → b ∈ rhs
  findRoute-∈ a rhs b p = fst (findRoute-aux a rhs b p)

  -- Helper: findRoute returns an atom that routes from a
  findRoute-routes : ∀ (a : Atom) (rhs : NormalForm) (b : Atom)
                   → findRoute a rhs ≡ just b
                   → atomCanRouteTo a b ≡ true
  findRoute-routes a rhs b p = snd (findRoute-aux a rhs b p)

  -- Soundness of findRoute: if findRoute succeeds, membership transfers
  findRoute-sound : ∀ (a : Atom) (rhs : NormalForm) (b : Atom) (ρ : Env)
                  → findRoute a rhs ≡ just b
                  → ⟦ a ⟧atom ρ ⊆ ⟦ rhs ⟧nf ρ
  findRoute-sound a rhs b ρ p y yIn =
    let routes : atomCanRouteTo a b ≡ true
        routes = findRoute-routes a rhs b p
        yInB : y ∈ ⟦ b ⟧atom ρ
        yInB = atomCanRouteTo-sound a b ρ routes y yIn
        bInRhs : b ∈ rhs
        bInRhs = findRoute-∈ a rhs b p
    in atom-in-nf-⊆ b rhs ρ bInRhs y yInB

  -- Helper for canSolve: extract findRoute result when canSolve succeeds
  canSolve-findRoute : ∀ (a : Atom) (as : NormalForm) (rhs : NormalForm)
                     → canSolve (a ∷ as) rhs ≡ true
                     → Σ Atom (λ b → findRoute a rhs ≡ just b)
  canSolve-findRoute a as rhs p = helper (findRoute a rhs) refl p
    where
      helper : (fr : Maybe Atom) → findRoute a rhs ≡ fr
             → canSolve (a ∷ as) rhs ≡ true
             → Σ Atom (λ b → findRoute a rhs ≡ just b)
      helper (just b) eq _ = b , eq
      helper nothing eq p with findRoute a rhs
      helper nothing eq p | just _  = ⊥-rec (nothing≢just (sym eq))
      helper nothing eq p | nothing = ⊥-rec (false≢true p)

  -- Helper for canSolve: the tail also satisfies canSolve
  canSolve-tail : ∀ (a : Atom) (as : NormalForm) (rhs : NormalForm)
                → canSolve (a ∷ as) rhs ≡ true
                → canSolve as rhs ≡ true
  canSolve-tail a as rhs p with findRoute a rhs
  ... | just _  = p
  ... | nothing = ⊥-rec (false≢true p)

  -- Private helper: membership in concatenation splits (avoid namespace conflict)
  private
    mem-++-split' : ∀ {xs ys : List A} {y : A} → y ∈ xs ++ ys → (y ∈ xs) ⊎ (y ∈ ys)
    mem-++-split' {[]} yIn = inr yIn
    mem-++-split' {x ∷ xs} here = inl here
    mem-++-split' {x ∷ xs} (there yIn) with mem-++-split' {xs} yIn
    ... | inl yInXs = inl (there yInXs)
    ... | inr yInYs = inr yInYs

  -- Main solver for normal forms
  solveNF : ∀ (lhs rhs : NormalForm) (ρ : Env)
          → canSolve lhs rhs ≡ true
          → ⟦ lhs ⟧nf ρ ⊆ ⟦ rhs ⟧nf ρ
  solveNF [] rhs ρ _ y ()
  solveNF (a ∷ as) rhs ρ p y yIn with mem-++-split' {⟦ a ⟧atom ρ} yIn
  ... | inl yInA =
    let (b , route) = canSolve-findRoute a as rhs p
    in findRoute-sound a rhs b ρ route y yInA
  ... | inr yInAs =
    let tailOk = canSolve-tail a as rhs p
    in solveNF as rhs ρ tailOk y yInAs
