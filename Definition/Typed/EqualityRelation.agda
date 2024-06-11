------------------------------------------------------------------------
-- An abstract set of equality relations over which the logical relation
-- is parameterized.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.Typed.EqualityRelation
  {ℓ} {M : Set ℓ}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  where

open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R hiding (_,_)
open import Definition.Typed.Weakening R using (_∷_⊇_)

import Graded.Derived.Erased.Untyped 𝕄 as Erased

open import Tools.Fin
open import Tools.Function
open import Tools.Level hiding (_⊔_)
open import Tools.Nat
open import Tools.Relation

private
  variable
    p q q′ r : M
    n n′ l₁ l₂ : Nat
    Γ : Con Term n
    Δ : Con Term n′
    ρ : Wk n′ n
    A A₁ A₂ A′ B B₁ B₂ B′ C : Term n
    a a′ b b′ e e′ : Term n
    k l m t t₁ t₂ u u₁ u₂ v v₁ v₂ w₁ w₂ : Term n
    s : Strength
    bm : BinderMode

-- Generic equality relation used with the logical relation

record EqRelSet : Set (lsuc ℓ) where
  constructor eqRel
  field
    ---------------
    -- Relations --
    ---------------

    -- Equality of types
    _⊢_≅_   : Con Term n → (A B : Term n)   → Set ℓ

    -- Equality of terms
    _⊢_≅_∷_ : Con Term n → (t u A : Term n) → Set ℓ

    -- Equality of neutral terms
    _⊢_~_∷_ : Con Term n → (t u A : Term n) → Set ℓ

    ----------------
    -- Properties --
    ----------------

    -- Generic equality compatibility
    ~-to-≅ₜ : Γ ⊢ k ~ l ∷ A
            → Γ ⊢ k ≅ l ∷ A

    -- Judgmental conversion compatibility
    ≅-eq  : Γ ⊢ A ≅ B
          → Γ ⊢ A ≡ B
    ≅ₜ-eq : Γ ⊢ t ≅ u ∷ A
          → Γ ⊢ t ≡ u ∷ A

    -- Universe
    ≅-univ : Γ ⊢ A ≅ B ∷ U l₁
           → Γ ⊢ A ≅ B

    -- Symmetry
    ≅-sym  : Γ ⊢ A ≅ B     → Γ ⊢ B ≅ A
    ≅ₜ-sym : Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ t ∷ A
    ~-sym  : Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ k ∷ A

    -- Transitivity
    ≅-trans  : Γ ⊢ A ≅ B     → Γ ⊢ B ≅ C     → Γ ⊢ A ≅ C
    ≅ₜ-trans : Γ ⊢ t ≅ u ∷ A → Γ ⊢ u ≅ v ∷ A → Γ ⊢ t ≅ v ∷ A
    ~-trans  : Γ ⊢ k ~ l ∷ A → Γ ⊢ l ~ m ∷ A → Γ ⊢ k ~ m ∷ A

    -- Conversion
    ≅-conv : Γ ⊢ t ≅ u ∷ A → Γ ⊢ A ≡ B → Γ ⊢ t ≅ u ∷ B
    ~-conv : Γ ⊢ k ~ l ∷ A → Γ ⊢ A ≡ B → Γ ⊢ k ~ l ∷ B

    -- Weakening
    ≅-wk  : ρ ∷ Δ ⊇ Γ
          → ⊢ Δ
          → Γ ⊢ A ≅ B
          → Δ ⊢ wk ρ A ≅ wk ρ B
    ≅ₜ-wk : ρ ∷ Δ ⊇ Γ
          → ⊢ Δ
          → Γ ⊢ t ≅ u ∷ A
          → Δ ⊢ wk ρ t ≅ wk ρ u ∷ wk ρ A
    ~-wk  : ρ ∷ Δ ⊇ Γ
          → ⊢ Δ
          → Γ ⊢ k ~ l ∷ A
          → Δ ⊢ wk ρ k ~ wk ρ l ∷ wk ρ A

    -- Weak head expansion
    ≅-red : Γ ⊢ A ⇒* A′
          → Γ ⊢ B ⇒* B′
          → Whnf A′
          → Whnf B′
          → Γ ⊢ A′ ≅ B′
          → Γ ⊢ A  ≅ B

    ≅ₜ-red : Γ ⊢ A ⇒* B
           → Γ ⊢ a ⇒* a′ ∷ B
           → Γ ⊢ b ⇒* b′ ∷ B
           → Whnf B
           → Whnf a′
           → Whnf b′
           → Γ ⊢ a′ ≅ b′ ∷ B
           → Γ ⊢ a  ≅ b  ∷ A

    -- Universe type reflexivity
    ≅-Urefl   : ⊢ Γ → Γ ⊢ U l₁ ≅ U l₁ ∷ U (1+ l₁)

    -- Natural number type reflexivity
    ≅ₜ-ℕrefl : ⊢ Γ → Γ ⊢ ℕ ≅ ℕ ∷ U 0

    -- Empty type reflexivity
    ≅ₜ-Emptyrefl : ⊢ Γ → Γ ⊢ Empty ≅ Empty ∷ U 0

    -- Unit type reflexivity
    ≅ₜ-Unitrefl : ⊢ Γ → Unit-allowed s → Γ ⊢ Unit s ≅ Unit s ∷ U 0

    -- Unit η-equality
    ≅ₜ-η-unit : Γ ⊢ e ∷ Unit s
              → Γ ⊢ e′ ∷ Unit s
              → Unit-with-η s
              → Γ ⊢ e ≅ e′ ∷ Unit s

    -- Π- and Σ-congruence

    ≅-ΠΣ-cong : ∀ {F G H E}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H
              → Γ ∙ F ⊢ G ≅ E
              → ΠΣ-allowed bm p q
              → Γ ⊢ ΠΣ⟨ bm ⟩ p , q ▷ F ▹ G ≅ ΠΣ⟨ bm ⟩ p , q ▷ H ▹ E

    ≅ₜ-ΠΣ-cong
              : ∀ {F G H E}
              → Γ ⊢ F
              → Γ ⊢ F ≅ H ∷ U l₁
              → Γ ∙ F ⊢ G ≅ E ∷ U l₂
              → ΠΣ-allowed bm p q
              → Γ ⊢ ΠΣ⟨ bm ⟩ p , q ▷ F ▹ G ≅ ΠΣ⟨ bm ⟩ p , q ▷ H ▹ E ∷ U (l₁ ⊔ l₂)

    -- Zero reflexivity
    ≅ₜ-zerorefl : ⊢ Γ → Γ ⊢ zero ≅ zero ∷ ℕ

    -- Successor congruence
    ≅-suc-cong : ∀ {m n} → Γ ⊢ m ≅ n ∷ ℕ → Γ ⊢ suc m ≅ suc n ∷ ℕ

    -- Product congruence
    ≅-prod-cong : ∀ {F G t t′ u u′}
                → Γ ⊢ F
                → Γ ∙ F ⊢ G
                → Γ ⊢ t ≅ t′ ∷ F
                → Γ ⊢ u ≅ u′ ∷ G [ t ]₀
                → Σʷ-allowed p q
                → Γ ⊢ prodʷ p t u ≅ prodʷ p t′ u′ ∷ Σʷ p , q ▷ F ▹ G

    -- η-equality
    ≅-η-eq : ∀ {f g F G}
           → Γ ⊢ F
           → Γ ⊢ f ∷ Π p , q ▷ F ▹ G
           → Γ ⊢ g ∷ Π p , q ▷ F ▹ G
           → Function f
           → Function g
           → Γ ∙ F ⊢ wk1 f ∘⟨ p ⟩ var x0 ≅ wk1 g ∘⟨ p ⟩ var x0 ∷ G
           → Γ ⊢ f ≅ g ∷ Π p , q ▷ F ▹ G

    -- η for product types
    ≅-Σ-η : ∀ {r s F G}
          → Γ ⊢ F
          → Γ ∙ F ⊢ G
          → Γ ⊢ r ∷ Σˢ p , q ▷ F ▹ G
          → Γ ⊢ s ∷ Σˢ p , q ▷ F ▹ G
          → Product r
          → Product s
          → Γ ⊢ fst p r ≅ fst p s ∷ F
          → Γ ⊢ snd p r ≅ snd p s ∷ G [ fst p r ]₀
          → Γ ⊢ r ≅ s ∷ Σˢ p , q ▷ F ▹ G

    -- Variable reflexivity
    ~-var : ∀ {x A} → Γ ⊢ var x ∷ A → Γ ⊢ var x ~ var x ∷ A

    -- Application congruence
    ~-app : ∀ {a b f g F G}
          → Γ ⊢ f ~ g ∷ Π p , q ▷ F ▹ G
          → Γ ⊢ a ≅ b ∷ F
          → Γ ⊢ f ∘⟨ p ⟩ a ~ g ∘⟨ p ⟩ b ∷ G [ a ]₀

    -- Product projections congruence
    ~-fst : ∀ {r s F G}
          → Γ ⊢ F
          → Γ ∙ F ⊢ G
          → Γ ⊢ r ~ s ∷ Σˢ p , q ▷ F ▹ G
          → Γ ⊢ fst p r ~ fst p s ∷ F

    ~-snd : ∀ {r s F G}
          → Γ ⊢ F
          → Γ ∙ F ⊢ G
          → Γ ⊢ r ~ s ∷ Σˢ p , q ▷ F ▹ G
          → Γ ⊢ snd p r ~ snd p s ∷ G [ fst p r ]₀

    -- Natural recursion congruence
    ~-natrec : ∀ {z z′ s s′ n n′ F F′}
             → Γ ∙ ℕ     ⊢ F
             → Γ ∙ ℕ     ⊢ F ≅ F′
             → Γ         ⊢ z ≅ z′ ∷ F [ zero ]₀
             → Γ ∙ ℕ ∙ F ⊢ s ≅ s′ ∷ F [ suc (var x1) ]↑²
             → Γ         ⊢ n ~ n′ ∷ ℕ
             → Γ         ⊢ natrec p q r F z s n ~ natrec p q r F′ z′ s′ n′ ∷ F [ n ]₀

    -- Product recursion congruence
    ~-prodrec : ∀ {F G A A′ t t′ u u′}
             → Γ                      ⊢ F
             → Γ ∙ F                  ⊢ G
             → Γ ∙ (Σʷ p , q ▷ F ▹ G) ⊢ A ≅ A′
             → Γ                      ⊢ t ~ t′ ∷ Σʷ p , q ▷ F ▹ G
             → Γ ∙ F ∙ G              ⊢ u ≅ u′ ∷ A [ prodʷ p (var x1) (var x0) ]↑²
             → Σʷ-allowed p q
             → Γ                      ⊢ prodrec r p q′ A t u ~ prodrec r p q′ A′ t′ u′ ∷ A [ t ]₀

    -- Empty recursion congruence
    ~-emptyrec : ∀ {n n′ F F′}
               → Γ ⊢ F ≅ F′
               → Γ ⊢ n ~ n′ ∷ Empty
               → Γ ⊢ emptyrec p F n ~ emptyrec p F′ n′ ∷ F

    -- Weak unit type recursion congruence
    ~-unitrec : ∀ {A A′ t t′ u u′}
              → Γ ∙ Unitʷ ⊢ A ≅ A′
              → Γ ⊢ t ~ t′ ∷ Unitʷ
              → Γ ⊢ u ≅ u′ ∷ A [ starʷ ]₀
              → Unitʷ-allowed
              → ¬ Unitʷ-η
              → Γ ⊢ unitrec p q A t u ~ unitrec p q A′ t′ u′ ∷ A [ t ]₀

    -- Star reflexivity
    ≅ₜ-starrefl : ⊢ Γ → Unit-allowed s → Γ ⊢ star s ≅ star s ∷ Unit s

    -- Id preserves "equality".
    ≅-Id-cong
      : Γ ⊢ A₁ ≅ A₂
      → Γ ⊢ t₁ ≅ t₂ ∷ A₁
      → Γ ⊢ u₁ ≅ u₂ ∷ A₁
      → Γ ⊢ Id A₁ t₁ u₁ ≅ Id A₂ t₂ u₂
    ≅ₜ-Id-cong
      : Γ ⊢ A₁ ≅ A₂ ∷ U l₁
      → Γ ⊢ t₁ ≅ t₂ ∷ A₁
      → Γ ⊢ u₁ ≅ u₂ ∷ A₁
      → Γ ⊢ Id A₁ t₁ u₁ ≅ Id A₂ t₂ u₂ ∷ U l₁

    -- Reflexivity for rfl.
    ≅ₜ-rflrefl : Γ ⊢ t ∷ A → Γ ⊢ rfl ≅ rfl ∷ Id A t t

    -- J preserves the _⊢_~_ relation (in a certain way).
    ~-J
      : Γ ⊢ A₁
      → Γ ⊢ A₁ ≅ A₂
      → Γ ⊢ t₁ ∷ A₁
      → Γ ⊢ t₁ ≅ t₂ ∷ A₁
      → Γ ∙ A₁ ∙ Id (wk1 A₁) (wk1 t₁) (var x0) ⊢ B₁ ≅ B₂
      → Γ ⊢ u₁ ≅ u₂ ∷ B₁ [ t₁ , rfl ]₁₀
      → Γ ⊢ v₁ ≅ v₂ ∷ A₁
      → Γ ⊢ w₁ ~ w₂ ∷ Id A₁ t₁ v₁
      → Γ ⊢ J p q A₁ t₁ B₁ u₁ v₁ w₁ ~ J p q A₂ t₂ B₂ u₂ v₂ w₂ ∷
          B₁ [ v₁ , w₁ ]₁₀

    -- K preserves the _⊢_~_ relation (in a certain way).
    ~-K
      : Γ ⊢ A₁ ≅ A₂
      → Γ ⊢ t₁ ∷ A₁
      → Γ ⊢ t₁ ≅ t₂ ∷ A₁
      → Γ ∙ Id A₁ t₁ t₁ ⊢ B₁ ≅ B₂
      → Γ ⊢ u₁ ≅ u₂ ∷ B₁ [ rfl ]₀
      → Γ ⊢ v₁ ~ v₂ ∷ Id A₁ t₁ t₁
      → K-allowed
      → Γ ⊢ K p A₁ t₁ B₁ u₁ v₁ ~ K p A₂ t₂ B₂ u₂ v₂ ∷ B₁ [ v₁ ]₀

    -- If []-cong is allowed, then []-cong preserves the _⊢_~_
    -- relation (in a certain way).
    ~-[]-cong
      : Γ ⊢ A₁ ≅ A₂
      → Γ ⊢ t₁ ≅ t₂ ∷ A₁
      → Γ ⊢ u₁ ≅ u₂ ∷ A₁
      → Γ ⊢ v₁ ~ v₂ ∷ Id A₁ t₁ u₁
      → []-cong-allowed s
      → let open Erased s in
        Γ ⊢ []-cong s A₁ t₁ u₁ v₁ ~ []-cong s A₂ t₂ u₂ v₂ ∷
          Id (Erased A₁) ([ t₁ ]) ([ u₁ ])


  -- Composition of universe and generic equality compatibility
  ~-to-≅ : ∀ {k l l′} → Γ ⊢ k ~ l ∷ U l′ → Γ ⊢ k ≅ l
  ~-to-≅ k~l = ≅-univ (~-to-≅ₜ k~l)

  opaque

    -- A variant of ≅ₜ-ℕrefl.

    ≅-ℕrefl : ⊢ Γ → Γ ⊢ ℕ ≅ ℕ
    ≅-ℕrefl = ≅-univ ∘→ ≅ₜ-ℕrefl

  opaque

    -- A variant of ≅ₜ-Emptyrefl.

    ≅-Emptyrefl : ⊢ Γ → Γ ⊢ Empty ≅ Empty
    ≅-Emptyrefl = ≅-univ ∘→ ≅ₜ-Emptyrefl

  opaque

    -- A variant of ≅ₜ-Unitrefl.

    ≅-Unitrefl : ⊢ Γ → Unit-allowed s → Γ ⊢ Unit s ≅ Unit s
    ≅-Unitrefl ⊢Γ ok = ≅-univ (≅ₜ-Unitrefl ⊢Γ ok)

  ≅-W-cong : ∀ {F G H E} W
          → Γ ⊢ F
          → Γ ⊢ F ≅ H
          → Γ ∙ F ⊢ G ≅ E
          → BindingType-allowed W
          → Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ H ▹ E
  ≅-W-cong BΠ! = ≅-ΠΣ-cong
  ≅-W-cong BΣ! = ≅-ΠΣ-cong

  ≅ₜ-W-cong : ∀ {F G H E} W
            → Γ ⊢ F
            → Γ ⊢ F ≅ H ∷ U l₁
            → Γ ∙ F ⊢ G ≅ E ∷ U l₂
            → BindingType-allowed W
            → Γ ⊢ ⟦ W ⟧ F ▹ G ≅ ⟦ W ⟧ H ▹ E ∷ U (l₁ ⊔ l₂)
  ≅ₜ-W-cong BΠ! = ≅ₜ-ΠΣ-cong
  ≅ₜ-W-cong BΣ! = ≅ₜ-ΠΣ-cong
