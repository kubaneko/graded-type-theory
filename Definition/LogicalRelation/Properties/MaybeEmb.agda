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

open import Definition.Untyped M
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Universe R
open import Definition.LogicalRelation.Irrelevance R

open import Tools.Nat using (Nat; 1+; ≤′-step; ≤′-refl; <⇒<′; <′⇒<;  ≤⇒≤′; ≤′⇒≤; s≤s)

private
  variable
    n ℓ            : Nat
    Γ             : Con Term n
    A B t u       : Term n
    l l₁ l₂ l₃ l′ : TypeLevel

------------------------------------------------------------------------
-- Some lemmas related to _<_ and _≤_

opaque

  -- The relation _<_ is transitive.

  <-trans : l₁ < l₂ → l₂ < l₃ → l₁ < l₃
  <-trans a ≤′-refl = ≤′-step a
  <-trans a (≤′-step b) = ≤′-step (<-trans a b)

opaque

  -- The relation _≤_ is transitive.

  ≤-trans : l₁ ≤ l₂ → l₂ ≤ l₃ → l₁ ≤ l₃
  ≤-trans p ≤′-refl     = p
  ≤-trans p (≤′-step q) = ≤′-step (≤-trans p q)

opaque

  -- The level ⁰ is the lowest level.

  ⁰≤ : 0 ≤ l
  ⁰≤ {l = 0} = ≤′-refl
  ⁰≤ {l = 1+ l} =
    let k = ⁰≤ {l} in s k
    where
    s : 0 ≤ l → 0 ≤ 1+ l
    s ≤′-refl = ≤′-step ≤′-refl
    s (≤′-step x) = ≤′-step (≤′-step x)


------------------------------------------------------------------------
-- Embedding lemmas

-- The lowest level can be embedded in any level.
maybeEmb′ : ∀ {l A}
          → Γ ⊩⟨ 0 ⟩ A
          → Γ ⊩⟨ l ⟩ A
maybeEmb′ {l = 0} [A] = [A]
maybeEmb′ {l = 1+ l} [A] = emb {l′ = 0} (₀< {l}) (lemma (₀< {l}) [A])
  where
  lemma : {l′ l : TypeLevel} {Γ : Con Term ℓ} {A : Term ℓ} → (p : l′ < l) → Γ ⊩⟨ l′ ⟩ A → LogRelKit._⊩_ (kit′ p) Γ A
  lemma ≤′-refl A = A
  lemma (≤′-step p) A = lemma p A
  ₀< : ∀{l} → 0 < 1+ l
  ₀< {0} = ≤′-refl
  ₀< {1+ l} = ≤′-step (₀< {l})

opaque

  -- A variant of emb.

  emb-≤-⊩ : l ≤ l′ → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l′ ⟩ A
  emb-≤-⊩ ≤′-refl      ⊩A = ⊩A
  emb-≤-⊩ (≤′-step p) ⊩A  =
    let a = ≤′⇒≤ p
    in emb-⊩ (<⇒<′ (s≤s a)) ⊩A

opaque
  unfolding emb-≤-⊩

  -- A cast lemma related to emb-≤-⊩.

  emb-≤-≡ :
    {l≤l′ : l ≤ l′} {⊩A : Γ ⊩⟨ l ⟩ A} →
    Γ ⊩⟨ l ⟩ A ≡ B / ⊩A →
    Γ ⊩⟨ l′ ⟩ A ≡ B / emb-≤-⊩ l≤l′ ⊩A
  emb-≤-≡ {l≤l′ = ≤′-refl}  A≡B = A≡B
  emb-≤-≡ {l≤l′ = ≤′-step l<} {⊩A = ⊩A} A≡B =
    irrelevanceEq ⊩A (emb-≤-⊩ (≤′-step l<) ⊩A) A≡B

opaque
  unfolding emb-≤-⊩

  -- A cast lemma related to emb-≤-⊩.

  emb-≤-∷ :
    {l≤l′ : l ≤ l′} {⊩A : Γ ⊩⟨ l ⟩ A} →
    Γ ⊩⟨ l ⟩ t ∷ A / ⊩A →
    Γ ⊩⟨ l′ ⟩ t ∷ A / emb-≤-⊩ l≤l′ ⊩A
  emb-≤-∷ {l≤l′ = ≤′-refl}    ⊩t = ⊩t
  emb-≤-∷ {l≤l′ = ≤′-step l<} {⊩A = ⊩A} ⊩t =
    irrelevanceTerm ⊩A (emb-≤-⊩ (≤′-step l<) ⊩A) ⊩t

opaque
  unfolding emb-≤-⊩

  -- A cast lemma related to emb-≤-⊩.

  emb-≤-≡∷ :
    {l≤l′ : l ≤ l′} {⊩A : Γ ⊩⟨ l ⟩ A} →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A / emb-≤-⊩ l≤l′ ⊩A
  emb-≤-≡∷ {l≤l′ = ≤′-refl}    t≡u = t≡u
  emb-≤-≡∷ {l≤l′ = ≤′-step l<} {⊩A = ⊩A} t≡u =
    irrelevanceEqTerm ⊩A (emb-≤-⊩ (≤′-step l<) ⊩A) t≡u
