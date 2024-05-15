------------------------------------------------------------------------
-- Embedding of the logical relation into higher type levels
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.MaybeEmb
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M hiding (_∷_)
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Universe R

open import Tools.Nat using (Nat)

private
  variable
    n             : Nat
    Γ             : Con Term n
    A B t u       : Term n
    l l₁ l₂ l₃ l′ : TypeLevel

------------------------------------------------------------------------
-- Some lemmas related to _<_ and _≤_

opaque

  -- The relation _<_ is transitive.

  <-trans : l₁ < l₂ → l₂ < l₃ → l₁ < l₃
  <-trans 0<1 ()

opaque

  -- The relation _≤_ is transitive.

  ≤-trans : l₁ ≤ l₂ → l₂ ≤ l₃ → l₁ ≤ l₃
  ≤-trans refl    q       = q
  ≤-trans p       refl    = p
  ≤-trans (emb p) (emb q) = emb (<-trans p q)

opaque

  -- The level ⁰ is the lowest level.

  ⁰≤ : ⁰ ≤ l
  ⁰≤ {l = ⁰} = refl
  ⁰≤ {l = ¹} = emb 0<1

opaque

  -- The level ¹ is the highest level.

  ≤¹ : l ≤ ¹
  ≤¹ {l = ⁰} = emb 0<1
  ≤¹ {l = ¹} = refl

------------------------------------------------------------------------
-- Embedding lemmas

-- The lowest level can be embedded in any level.
maybeEmb′ : ∀ {l A}
          → Γ ⊩⟨ 0 ⟩ A
          → Γ ⊩⟨ l ⟩ A
maybeEmb′ {l = ⁰} [A] = [A]
maybeEmb′ {l = ¹} [A] = emb 0<1 [A]

opaque

  -- A variant of emb.

  emb-≤-⊩ : l ≤ l′ → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l′ ⟩ A
  emb-≤-⊩ refl      ⊩A = ⊩A
  emb-≤-⊩ (emb 0<1) ⊩A = emb 0<1 ⊩A

opaque
  unfolding emb-≤-⊩

  -- A cast lemma related to emb-≤-⊩.

  emb-≤-≡ :
    {l≤l′ : l ≤ l′} {⊩A : Γ ⊩⟨ l ⟩ A} →
    Γ ⊩⟨ l ⟩ A ≡ B / ⊩A →
    Γ ⊩⟨ l′ ⟩ A ≡ B / emb-≤-⊩ l≤l′ ⊩A
  emb-≤-≡ {l≤l′ = refl}    A≡B = A≡B
  emb-≤-≡ {l≤l′ = emb 0<1} A≡B = A≡B

opaque
  unfolding emb-≤-⊩

  -- A cast lemma related to emb-≤-⊩.

  emb-≤-∷ :
    {l≤l′ : l ≤ l′} {⊩A : Γ ⊩⟨ l ⟩ A} →
    Γ ⊩⟨ l ⟩ t ∷ A / ⊩A →
    Γ ⊩⟨ l′ ⟩ t ∷ A / emb-≤-⊩ l≤l′ ⊩A
  emb-≤-∷ {l≤l′ = refl}    ⊩t = ⊩t
  emb-≤-∷ {l≤l′ = emb 0<1} ⊩t = ⊩t

opaque
  unfolding emb-≤-⊩

  -- A cast lemma related to emb-≤-⊩.

  emb-≤-≡∷ :
    {l≤l′ : l ≤ l′} {⊩A : Γ ⊩⟨ l ⟩ A} →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A / emb-≤-⊩ l≤l′ ⊩A
  emb-≤-≡∷ {l≤l′ = refl}    t≡u = t≡u
  emb-≤-≡∷ {l≤l′ = emb 0<1} t≡u = t≡u
