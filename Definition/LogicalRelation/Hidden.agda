------------------------------------------------------------------------
-- A variant of the logical relation with hidden reducibility
-- arguments, along with variants of some other relations
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Hidden
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Conversion R
open import Definition.LogicalRelation.Substitution.Escape R
open import
  Definition.LogicalRelation.Substitution.Introductions.DoubleSubst R
open import
  Definition.LogicalRelation.Substitution.Introductions.SingleSubst R
import Definition.LogicalRelation.Substitution.Irrelevance R as Irr
open import Definition.LogicalRelation.Substitution.MaybeEmbed R
open import Definition.LogicalRelation.Substitution.Cumulativity R as C
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Reducibility R
open import Definition.LogicalRelation.Substitution.Reduction R
open import Definition.LogicalRelation.Substitution.Reflexivity R
open import Definition.LogicalRelation.Substitution.Weakening R
import Definition.LogicalRelation.Weakening R as W

open import Definition.Typed R
open import Definition.Typed.Weakening R as TW using (_∷_⊇_)

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+; ≤′-refl; ≤′-step)
open import Tools.Product as Σ
import Tools.PropositionalEquality as PE
open import Tools.Reasoning.PropositionalEquality

private variable
  m n                                                   : Nat
  x                                                     : Fin _
  Γ Δ Η                                                 : Con Term _
  A A₁ A₂ B B₁ B₂ C C₁ C₂ D E t t₁ t₂ u u₁ u₂ v v₁ v₂ w : Term _
  σ σ₁ σ₂ σ₃                                            : Subst _ _
  ρ                                                     : Wk _ _
  l l′ l″ l‴                                            : TypeLevel
  k                                                     : LogRelKit
  ⊢Δ                                                    : ⊢ _
  ⊩Γ                                                    : ⊩ᵛ _

------------------------------------------------------------------------
-- The type formers

opaque

  -- Reducible terms.

  infix 4 _⊩⟨_⟩_∷_

  _⊩⟨_⟩_∷_ : Con Term n → TypeLevel → Term n → Term n → Set a
  Γ ⊩⟨ l ⟩ t ∷ A =
    ∃ λ (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ t ∷ A / ⊩A

opaque

  -- Reducible type equality.

  infix 4 _⊩⟨_⟩_≡_

  _⊩⟨_⟩_≡_ : Con Term n → TypeLevel → Term n → Term n → Set a
  Γ ⊩⟨ l ⟩ A ≡ B =
    ∃ λ (⊩A : Γ ⊩⟨ l ⟩ A) → (Γ ⊩⟨ l ⟩ B) × Γ ⊩⟨ l ⟩ A ≡ B / ⊩A

opaque

  -- Reducible term equality.

  infix 4 _⊩⟨_⟩_≡_∷_

  _⊩⟨_⟩_≡_∷_ : Con Term n → TypeLevel → Term n → Term n → Term n → Set a
  Γ ⊩⟨ l ⟩ t ≡ u ∷ A =
    ∃ λ (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ t ∷ A / ⊩A ×
    Γ ⊩⟨ l ⟩ u ∷ A / ⊩A ×
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A

opaque

  infix 4 _⊩ᵛ⟨_⟩_

  -- Valid types.

  _⊩ᵛ⟨_⟩_ : Con Term n → TypeLevel → Term n → Set a
  Γ ⊩ᵛ⟨ l ⟩ A =
    ∃ λ (⊩Γ : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ

opaque

  infix 4 _⊩ᵛ⟨_⟩_∷_

  -- Valid terms.

  _⊩ᵛ⟨_⟩_∷_ : Con Term n → TypeLevel → Term n → Term n → Set a
  Γ ⊩ᵛ⟨ l ⟩ t ∷ A =
    ∃ λ (⊩Γ : ⊩ᵛ Γ) →
    ∃ λ (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A

opaque

  infix 4 _⊩ˢ_∷_

  -- Valid substitutions.

  _⊩ˢ_∷_ : Con Term m → Subst m n → Con Term n → Set a
  Δ ⊩ˢ σ ∷ Γ =
    ∃ λ (⊩Γ : ⊩ᵛ Γ) →
    ∃ λ (⊢Δ : ⊢ Δ) →
    Δ ⊩ˢ σ ∷ Γ / ⊩Γ / ⊢Δ

opaque

  infix 4 _⊩ᵛ⟨_⟩_≡_

  -- Valid type equality.

  _⊩ᵛ⟨_⟩_≡_ : Con Term n → TypeLevel → Term n → Term n → Set a
  Γ ⊩ᵛ⟨ l ⟩ A ≡ B =
    ∃ λ (⊩Γ : ⊩ᵛ Γ) →
    ∃ λ (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ) →
    Γ ⊩ᵛ⟨ l ⟩ B / ⊩Γ ×
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B / ⊩Γ / ⊩A

opaque

  infix 4 _⊩ᵛ⟨_⟩_≡_∷_

  -- Valid term equality.

  _⊩ᵛ⟨_⟩_≡_∷_ :
    Con Term n → TypeLevel → Term n → Term n → Term n → Set a
  Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A =
    ∃ λ (⊩Γ : ⊩ᵛ Γ) →
    [ Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / ⊩Γ ]

opaque

  infix 4 _⊩ˢ_≡_∷_

  -- Valid substitution equality.

  _⊩ˢ_≡_∷_ : Con Term m → Subst m n → Subst m n → Con Term n → Set a
  Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ =
    ∃ λ (⊩Γ : ⊩ᵛ Γ) →
    ∃ λ (⊢Δ : ⊢ Δ) →
    ∃ λ (⊩σ₁ : Δ ⊩ˢ σ₁ ∷ Γ / ⊩Γ / ⊢Δ) →
    Δ ⊩ˢ σ₂ ∷ Γ / ⊩Γ / ⊢Δ ×
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ / ⊩Γ / ⊢Δ / ⊩σ₁

------------------------------------------------------------------------
-- Conversions to the underlying type formers

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A conversion to _⊩⟨_⟩_∷_/_.

  ⊩∷→⊩∷/ : (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l′ ⟩ t ∷ A → Γ ⊩⟨ l ⟩ t ∷ A / ⊩A
  ⊩∷→⊩∷/ ⊩A (⊩A′ , ⊩t) = irrelevanceTerm ⊩A′ ⊩A ⊩t

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A conversion to _⊩⟨_⟩_≡_/_.

  ⊩≡→⊩≡/ : (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l′ ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ B / ⊩A
  ⊩≡→⊩≡/ ⊩A (⊩A′ , _ , A≡B) = irrelevanceEq ⊩A′ ⊩A A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- A conversion to _⊩⟨_⟩_≡_∷_/_.

  ⊩≡∷→⊩≡∷/ :
    (⊩A : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A
  ⊩≡∷→⊩≡∷/ ⊩A (⊩A′ , _ , _ , t≡u) = irrelevanceEqTerm ⊩A′ ⊩A t≡u

opaque
  unfolding _⊩ᵛ⟨_⟩_

  -- A conversion to _⊩ᵛ⟨_⟩_/_.

  ⊩ᵛ→⊩ᵛ/ : Γ ⊩ᵛ⟨ l ⟩ A → Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ
  ⊩ᵛ→⊩ᵛ/ {⊩Γ} (⊩Γ′ , ⊩A) = Irr.irrelevance ⊩Γ′ ⊩Γ ⊩A

opaque
  unfolding _⊩ᵛ⟨_⟩_∷_

  -- A conversion to _⊩ᵛ⟨_⟩_∷_/_/_.

  ⊩ᵛ∷→⊩ᵛ∷// :
    (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ) → Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A / ⊩Γ / ⊩A
  ⊩ᵛ∷→⊩ᵛ∷// {t} ⊩A (_ , ⊩A′ , ⊩t) =
    Irr.irrelevanceTerm {t = t} _ _ ⊩A′ ⊩A ⊩t

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_

  -- A conversion to _⊩ᵛ⟨_⟩_≡_/_/_.

  ⊩ᵛ≡→⊩ᵛ≡// :
    (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ) → Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B / ⊩Γ / ⊩A
  ⊩ᵛ≡→⊩ᵛ≡// {B} ⊩A (_ , ⊩A′ , _ , A≡B) =
    Irr.irrelevanceEq {B = B} _ _ ⊩A′ ⊩A A≡B

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_∷_

  -- A conversion to _⊩ᵛ⟨_⟩_≡_∷_/_/_.

  ⊩ᵛ≡∷→⊩ᵛ≡∷// :
    (⊩A : Γ ⊩ᵛ⟨ l ⟩ A / ⊩Γ) → Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A / ⊩Γ / ⊩A
  ⊩ᵛ≡∷→⊩ᵛ≡∷// {t} {u} ⊩A (_ , modelsTermEq ⊩A′ _ _ t≡u) =
    Irr.irrelevanceEqTerm {t = t} {u = u} _ _ ⊩A′ ⊩A t≡u

opaque
  unfolding _⊩ˢ_∷_

  -- A conversion to _⊩ˢ⟨_⟩_∷_/_/_.

  ⊩ˢ∷→⊩ˢ∷// : Δ ⊩ˢ σ ∷ Γ → Δ ⊩ˢ σ ∷ Γ / ⊩Γ / ⊢Δ
  ⊩ˢ∷→⊩ˢ∷// (_ , _ , ⊩σ) =
    Irr.irrelevanceSubst _ _ _ _ ⊩σ

opaque
  unfolding _⊩ˢ_≡_∷_

  -- A conversion to _⊩ˢ⟨_⟩_≡_∷_/_/_/_.

  ⊩ˢ≡∷→⊩ˢ≡∷/// :
    {⊩σ₁ : Δ ⊩ˢ σ₁ ∷ Γ / ⊩Γ / ⊢Δ} →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ / ⊩Γ / ⊢Δ / ⊩σ₁
  ⊩ˢ≡∷→⊩ˢ≡∷/// (_ , _ , _ , _ , σ₁≡σ₂) =
    Irr.irrelevanceSubstEq _ _ _ _ _ _ σ₁≡σ₂

------------------------------------------------------------------------
-- Reflexivity

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Reflexivity for _⊩⟨_⟩_≡_.

  refl-⊩≡ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l ⟩ A ≡ A
  refl-⊩≡ ⊩A =
    ⊩A , ⊩A , reflEq ⊩A

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- Reflexivity for _⊩⟨_⟩_≡_∷_.

  refl-⊩≡∷ :
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ t ∷ A
  refl-⊩≡∷ (⊩A , ⊩t) =
    ⊩A , ⊩t , ⊩t , reflEqTerm ⊩A ⊩t

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_

  -- Reflexivity for _⊩ᵛ⟨_⟩_≡_.

  refl-⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l ⟩ A ≡ A
  refl-⊩ᵛ≡ (_ , ⊩A) =
    _ , ⊩A , ⊩A , reflᵛ _ ⊩A

opaque
  unfolding _⊩ᵛ⟨_⟩_∷_ _⊩ᵛ⟨_⟩_≡_∷_

  -- Reflexivity for _⊩ᵛ⟨_⟩_≡_∷_.

  refl-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ t ∷ A
  refl-⊩ᵛ≡∷ {t} (_ , ⊩A , ⊩t) =
    _ , modelsTermEq ⊩A ⊩t ⊩t (reflᵗᵛ {t = t} _ ⊩A ⊩t)

opaque
  unfolding _⊩ˢ_∷_ _⊩ˢ_≡_∷_

  -- Reflexivity for _⊩ˢ_≡_∷_.

  refl-⊩ˢ≡∷ :
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩ˢ σ ≡ σ ∷ Γ
  refl-⊩ˢ≡∷ (_ , _ , ⊩σ) =
    _ , _ , ⊩σ , ⊩σ , reflSubst _ _ ⊩σ

------------------------------------------------------------------------
-- Symmetry

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Symmetry for _⊩⟨_⟩_≡_.

  sym-⊩≡ :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l ⟩ B ≡ A
  sym-⊩≡ (⊩A , ⊩B , A≡B) =
    ⊩B , ⊩A , symEq ⊩A ⊩B A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Symmetry for _⊩⟨_⟩_≡_∷_.

  sym-⊩≡∷ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ u ≡ t ∷ A
  sym-⊩≡∷ (⊩A , ⊩t , ⊩u , t≡u) =
    ⊩A , ⊩u , ⊩t , symEqTerm ⊩A t≡u

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_

  -- Symmetry for _⊩ᵛ⟨_⟩_≡_.

  sym-⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l ⟩ B ≡ A
  sym-⊩ᵛ≡ (_ , ⊩A , ⊩B , A≡B) =
    _ , ⊩B , ⊩A , sym-⊩ᵛ≡// ⊩A ⊩B A≡B

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_∷_

  -- Symmetry for _⊩ᵛ⟨_⟩_≡_∷_.

  sym-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ u ≡ t ∷ A
  sym-⊩ᵛ≡∷ {t} {u} (_ , modelsTermEq ⊩A ⊩t ⊩u t≡u) =
    _ , modelsTermEq ⊩A ⊩u ⊩t (sym-⊩ᵛ≡∷// t u ⊩A t≡u)

opaque
  unfolding _⊩ˢ_≡_∷_

  -- Symmetry for _⊩ˢ_≡_∷_.

  sym-⊩ˢ≡∷ :
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩ˢ σ₂ ≡ σ₁ ∷ Γ
  sym-⊩ˢ≡∷ (_ , _ , ⊩σ₁ , ⊩σ₂ , σ₁≡σ₂) =
    _ , _ , ⊩σ₂ , ⊩σ₁ , symS _ _ _ _ σ₁≡σ₂

------------------------------------------------------------------------
-- Transitivity

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Transitivity for _⊩⟨_⟩_≡_.

  trans-⊩≡ :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l ⟩ B ≡ C →
    Γ ⊩⟨ l ⟩ A ≡ C
  trans-⊩≡ (⊩A , _ , A≡B) (⊩B , ⊩C , B≡C) =
    ⊩A , ⊩C , transEq ⊩A ⊩B ⊩C A≡B B≡C

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Transitivity for _⊩⟨_⟩_≡_∷_.

  trans-⊩≡∷ :
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ u ≡ v ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  trans-⊩≡∷ (⊩A′ , ⊩t , _ , t≡u) (⊩A , _ , ⊩v , u≡v) =
      ⊩A , irrelevanceTerm ⊩A′ ⊩A ⊩t , ⊩v
    , transEqTerm ⊩A (irrelevanceEqTerm ⊩A′ ⊩A t≡u) u≡v

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_

  -- Transitivity for _⊩ᵛ⟨_⟩_≡_.

  trans-⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l ⟩ B ≡ C →
    Γ ⊩ᵛ⟨ l ⟩ A ≡ C
  trans-⊩ᵛ≡ {C} (_ , ⊩A , ⊩B , A≡B) (_ , ⊩B′ , ⊩C , B≡C) =
    case Irr.irrelevance _ _ ⊩C of λ
      ⊩C′ →
      _ , ⊩A , ⊩C′
    , trans-⊩ᵛ≡// ⊩A ⊩B ⊩C′ A≡B
        (Irr.irrelevanceEq {B = C} _ _ ⊩B′ ⊩B B≡C)

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_∷_

  -- Transitivity for _⊩ᵛ⟨_⟩_≡_∷_.

  trans-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ u ≡ v ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ v ∷ A
  trans-⊩ᵛ≡∷
    {t} {u} {v}
    (_ , modelsTermEq ⊩A′ ⊩t _ t≡u) (_ , modelsTermEq ⊩A _ ⊩v u≡v) =
      _
    , modelsTermEq ⊩A (Irr.irrelevanceTerm {t = t} _ _ ⊩A′ ⊩A ⊩t) ⊩v
        (trans-⊩ᵛ≡∷// t u v ⊩A
           (Irr.irrelevanceEqTerm {t = t} {u = u} _ _ ⊩A′ ⊩A t≡u)
           u≡v)

opaque
  unfolding _⊩ˢ_≡_∷_

  -- Transitivity for _⊩ˢ_≡_∷_.

  trans-⊩ˢ≡ :
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩ˢ σ₂ ≡ σ₃ ∷ Γ →
    Δ ⊩ˢ σ₁ ≡ σ₃ ∷ Γ
  trans-⊩ˢ≡ (_ , _ , _ , ⊩σ₂ , σ₁≡σ₂) (_ , _ , _ , ⊩σ₃ , σ₂≡σ₃) =
    case Irr.irrelevanceSubst _ _ _ _ ⊩σ₃ of λ
      ⊩σ₃ →
      _ , _ , _ , ⊩σ₃
    , transS _ _ _ _ ⊩σ₃ σ₁≡σ₂
        (Irr.irrelevanceSubstEq _ _ _ _ _ ⊩σ₂ σ₂≡σ₃)

------------------------------------------------------------------------
-- Well-formedness lemmas

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A well-formedness lemma for _⊩⟨_⟩_∷_.

  wf-⊩∷ : Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊩⟨ l ⟩ A
  wf-⊩∷ (⊩A , _) = ⊩A

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A well-formedness lemma for _⊩⟨_⟩_≡_.

  wf-⊩≡ : Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A × Γ ⊩⟨ l ⟩ B
  wf-⊩≡ (⊩A , ⊩B , _) = ⊩A , ⊩B

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A well-formedness lemma for _⊩⟨_⟩_≡_∷_.

  wf-⊩≡∷ :
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A × Γ ⊩⟨ l ⟩ u ∷ A
  wf-⊩≡∷ (⊩A , ⊩t , ⊩u , _) = (⊩A , ⊩t) , (⊩A , ⊩u)

opaque
  unfolding _⊩ᵛ⟨_⟩_

  -- A well-formedness lemma for ⊩ᵛ_.

  wf-⊩ᵛ-∙ : ⊩ᵛ Γ ∙ A → ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A
  wf-⊩ᵛ-∙ (_ ∙ ⊩A) = _ , _ , ⊩A

opaque
  unfolding _⊩ᵛ⟨_⟩_

  -- A well-formedness lemma for _⊩ᵛ⟨_⟩_.

  wf-⊩ᵛ : Γ ⊩ᵛ⟨ l ⟩ A → ⊩ᵛ Γ
  wf-⊩ᵛ (⊩Γ , _) = ⊩Γ

opaque
  unfolding _⊩ᵛ⟨_⟩_

  -- Another well-formedness lemma for _⊩ᵛ⟨_⟩_.

  wf-∙-⊩ᵛ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    ∃ λ l′ → Γ ⊩ᵛ⟨ l′ ⟩ A
  wf-∙-⊩ᵛ ⊩B =
    case wf-⊩ᵛ ⊩B of λ {
      (_ ∙ ⊩A) →
    _ , _ , ⊩A }

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_∷_

  -- A well-formedness lemma for _⊩ᵛ⟨_⟩_∷_.

  wf-⊩ᵛ∷ : Γ ⊩ᵛ⟨ l ⟩ t ∷ A → Γ ⊩ᵛ⟨ l ⟩ A
  wf-⊩ᵛ∷ (_ , ⊩A , _) = _ , ⊩A

opaque
  unfolding _⊩ˢ_∷_

  -- A well-formedness lemma for _⊩ˢ_∷_.

  wf-⊩ˢ∷ : Δ ⊩ˢ σ ∷ Γ → ⊩ᵛ Γ
  wf-⊩ˢ∷ (⊩Γ , _) = ⊩Γ

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_

  -- A well-formedness lemma for _⊩ᵛ⟨_⟩_≡_.

  wf-⊩ᵛ≡ : Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Γ ⊩ᵛ⟨ l ⟩ A × Γ ⊩ᵛ⟨ l ⟩ B
  wf-⊩ᵛ≡ (_ , ⊩A , ⊩B , _) = (_ , ⊩A) , (_ , ⊩B)

opaque
  unfolding _⊩ᵛ⟨_⟩_∷_ _⊩ᵛ⟨_⟩_≡_∷_

  -- A well-formedness lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  wf-⊩ᵛ≡∷ : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A → Γ ⊩ᵛ⟨ l ⟩ t ∷ A × Γ ⊩ᵛ⟨ l ⟩ u ∷ A
  wf-⊩ᵛ≡∷ (_ , modelsTermEq ⊩A ⊩t ⊩u _) =
    (_ , ⊩A , ⊩t) , (_ , ⊩A , ⊩u)

opaque
  unfolding _⊩ˢ_∷_ _⊩ˢ_≡_∷_

  -- A well-formedness lemma for _⊩ˢ_≡_∷_.

  wf-⊩ˢ≡∷ : Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩ˢ σ₁ ∷ Γ × Δ ⊩ˢ σ₂ ∷ Γ
  wf-⊩ˢ≡∷ (_ , _ , ⊩σ₁ , ⊩σ₂ , _) = (_ , _ , ⊩σ₁) , (_ , _ , ⊩σ₂)

------------------------------------------------------------------------
-- Changing type levels

opaque
  unfolding _⊩⟨_⟩_∷_

  -- Changing type levels for _⊩⟨_⟩_∷_.

  level-⊩∷ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l′ ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A
  level-⊩∷ ⊩A ⊩t =
    ⊩A , ⊩∷→⊩∷/ ⊩A ⊩t

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Changing type levels for _⊩⟨_⟩_≡_.

  level-⊩≡ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l ⟩ B →
    Γ ⊩⟨ l′ ⟩ A ≡ B →
    Γ ⊩⟨ l ⟩ A ≡ B
  level-⊩≡ ⊩A ⊩B A≡B =
    ⊩A , ⊩B , ⊩≡→⊩≡/ ⊩A A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Changing type levels for _⊩⟨_⟩_≡_∷_.

  level-⊩≡∷ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  level-⊩≡∷ ⊩A t≡u =
    case wf-⊩≡∷ t≡u of λ
      (⊩t , ⊩u) →
    ⊩A , ⊩∷→⊩∷/ ⊩A ⊩t , ⊩∷→⊩∷/ ⊩A ⊩u , ⊩≡∷→⊩≡∷/ ⊩A t≡u

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_∷_

  -- Changing type levels for _⊩ᵛ⟨_⟩_∷_.

  level-⊩ᵛ∷ :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A
  level-⊩ᵛ∷ {t} (_ , ⊩A) ⊩t =
    _ , ⊩A , ⊩ᵛ∷→⊩ᵛ∷// {t = t} ⊩A ⊩t

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_

  -- Changing type levels for _⊩ᵛ⟨_⟩_≡_.

  level-⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B
  level-⊩ᵛ≡ (_ , ⊩A) ⊩B A≡B =
    _ , ⊩A , ⊩ᵛ→⊩ᵛ/ ⊩B , ⊩ᵛ≡→⊩ᵛ≡// ⊩A A≡B

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_∷_

  -- Changing type levels for _⊩ᵛ⟨_⟩_≡_∷_.

  level-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A
  level-⊩ᵛ≡∷ {t} {u} (_ , ⊩A) t≡u =
    case wf-⊩ᵛ≡∷ t≡u of λ
      (⊩t , ⊩u) →
      _
    , modelsTermEq ⊩A (⊩ᵛ∷→⊩ᵛ∷// ⊩A ⊩t) (⊩ᵛ∷→⊩ᵛ∷// ⊩A ⊩u)
        (⊩ᵛ≡∷→⊩ᵛ≡∷// ⊩A t≡u)

------------------------------------------------------------------------
-- Conversion

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_∷_

  -- Conversion for _⊩⟨_⟩_∷_.

  conv-⊩∷ :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l′ ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ B
  conv-⊩∷ (⊩A , ⊩B , A≡B) (⊩A′ , ⊩t) =
    ⊩B , convTerm₁ ⊩A′ ⊩B (irrelevanceEq ⊩A ⊩A′ A≡B) ⊩t

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_

  -- Conversion for _⊩⟨_⟩_≡_∷_.

  conv-⊩≡∷ :
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ B
  conv-⊩≡∷ (⊩A , ⊩B , A≡B) (⊩A′ , ⊩t , ⊩u , t≡u) =
    case irrelevanceEq ⊩A ⊩A′ A≡B of λ
      A≡B →
      ⊩B , convTerm₁ ⊩A′ ⊩B A≡B ⊩t , convTerm₁ ⊩A′ ⊩B A≡B ⊩u
    , convEqTerm₁ ⊩A′ ⊩B A≡B t≡u

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_

  -- Conversion for the context for _⊩ᵛ⟨_⟩_.

  conv-∙-⊩ᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ C →
    Γ ∙ B ⊩ᵛ⟨ l ⟩ C
  conv-∙-⊩ᵛ (_ , ⊩A , ⊩B , A≡B) (_ , ⊩C) =
    _ , Irr.irrelevanceLift _ ⊩A ⊩B A≡B (Irr.irrelevance _ _ ⊩C)

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_

  -- Another kind of conversion for the context for _⊩ᵛ⟨_⟩_.

  conv-∙∙-⊩ᵛ :
    Γ ⊩ᵛ⟨ l′ ⟩ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊩ᵛ⟨ l″ ⟩ B₁ ≡ B₂ →
    Γ ∙ A₁ ∙ B₁ ⊩ᵛ⟨ l ⟩ C →
    Γ ∙ A₂ ∙ B₂ ⊩ᵛ⟨ l ⟩ C
  conv-∙∙-⊩ᵛ
    {B₂} (_ , ⊩A₁ , ⊩A₂ , A₁≡A₂) (_ , ⊩B₁ , ⊩B₂ , B₁≡B₂) (_ , ⊩C) =
    case Irr.irrelevance _ _ ⊩B₁ of λ
      ⊩B₁′ →
      _
    , Irr.irrelevanceLift₂
        {⊩A₁ = ⊩A₁}
        {⊩B₁ = ⊩B₁′}
        {⊩B₂ = Irr.irrelevanceLift _ ⊩A₁ ⊩A₂ A₁≡A₂
                 (Irr.irrelevance _ _ ⊩B₂)}
        A₁≡A₂
        (Irr.irrelevanceEq {B = B₂} _ _ ⊩B₁ ⊩B₁′ B₁≡B₂)
        (Irr.irrelevance _ _ ⊩C)

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_ _⊩ᵛ⟨_⟩_∷_

  -- Conversion for _⊩ᵛ⟨_⟩_∷_.

  conv-⊩ᵛ∷ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ B
  conv-⊩ᵛ∷ {B} {t} (_ , ⊩A , ⊩B , A≡B) ⊩t =
    case level-⊩ᵛ∷ {t = t} (_ , ⊩A) ⊩t of λ
      (_ , ⊩A′ , ⊩t) →
    case Irr.irrelevance _ _ ⊩A′ of λ
      ⊩A″ →
      _ , ⊩B
    , convᵛ {t = t} _ ⊩A″ ⊩B (Irr.irrelevanceEq {B = B} _ _ ⊩A ⊩A″ A≡B)
        (Irr.irrelevanceTerm {t = t} _ _ ⊩A′ ⊩A″ ⊩t)

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_ _⊩ᵛ⟨_⟩_∷_

  -- Conversion for the context for _⊩ᵛ⟨_⟩_∷_.

  conv-∙-⊩ᵛ∷ :
    Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ C →
    Γ ∙ B ⊩ᵛ⟨ l ⟩ t ∷ C
  conv-∙-⊩ᵛ∷ {t} (_ , ⊩A , ⊩B , A≡B) (_ , ⊩C , ⊩t) =
    case Irr.irrelevance _ _ ⊩C of λ
      ⊩C′ →
      _ , Irr.irrelevanceLift _ ⊩A ⊩B A≡B ⊩C′
    , Irr.irrelevanceTermLift {t = t} _ ⊩A ⊩B A≡B ⊩C′
        (Irr.irrelevanceTerm {t = t} _ _ ⊩C ⊩C′ ⊩t)

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_ _⊩ᵛ⟨_⟩_≡_∷_

  -- Conversion for _⊩ᵛ⟨_⟩_≡_∷_.

  conv-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ B
  conv-⊩ᵛ≡∷ {B} {t} {u} (_ , ⊩A , ⊩B , A≡B) t≡u =
    case level-⊩ᵛ≡∷ (_ , ⊩A) t≡u of λ
      (_ , modelsTermEq ⊩A′ ⊩t ⊩u t≡u) →
    case Irr.irrelevance _ _ ⊩A′ of λ
      ⊩A″ →
    case (λ {k Δ σ} →
            Irr.irrelevanceEq {B = B} _ _ ⊩A ⊩A″ A≡B
              {k = k} {Δ = Δ} {σ = σ}) of λ
      A≡B →
      _
    , modelsTermEq ⊩B
        (convᵛ {t = t} _ ⊩A″ ⊩B A≡B
           (Irr.irrelevanceTerm {t = t} _ _ ⊩A′ ⊩A″ ⊩t))
        (convᵛ {t = u} _ ⊩A″ ⊩B A≡B
           (Irr.irrelevanceTerm {t = u} _ _ ⊩A′ ⊩A″ ⊩u))
        (convEqᵛ {t = t} {u = u} _ ⊩A″ ⊩B A≡B
           (Irr.irrelevanceEqTerm {t = t} {u = u} _ _ ⊩A′ ⊩A″ t≡u))

------------------------------------------------------------------------
-- Weakening

opaque

  -- Weakening for _⊩⟨_⟩_.

  wk-⊩ : ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊩⟨ l ⟩ A → Δ ⊩⟨ l ⟩ wk ρ A
  wk-⊩ = W.wk

opaque
  unfolding _⊩⟨_⟩_∷_

  -- Weakening for _⊩⟨_⟩_∷_.

  wk-⊩∷ : ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊩⟨ l ⟩ t ∷ A → Δ ⊩⟨ l ⟩ wk ρ t ∷ wk ρ A
  wk-⊩∷ Δ⊇Γ ⊢Δ (⊩A , ⊩t) =
    W.wk Δ⊇Γ ⊢Δ ⊩A , W.wkTerm Δ⊇Γ ⊢Δ ⊩A ⊩t

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Weakening for _⊩⟨_⟩_≡_.

  wk-⊩≡ : ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊩⟨ l ⟩ A ≡ B → Δ ⊩⟨ l ⟩ wk ρ A ≡ wk ρ B
  wk-⊩≡ Δ⊇Γ ⊢Δ (⊩A , ⊩B , A≡B) =
    W.wk Δ⊇Γ ⊢Δ ⊩A , W.wk Δ⊇Γ ⊢Δ ⊩B , W.wkEq Δ⊇Γ ⊢Δ ⊩A A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Weakening for _⊩⟨_⟩_≡_∷_.

  wk-⊩≡∷ :
    ρ ∷ Δ ⊇ Γ → ⊢ Δ → Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Δ ⊩⟨ l ⟩ wk ρ t ≡ wk ρ u ∷ wk ρ A
  wk-⊩≡∷ Δ⊇Γ ⊢Δ (⊩A , ⊩t , ⊩u , t≡u) =
      W.wk Δ⊇Γ ⊢Δ ⊩A , W.wkTerm Δ⊇Γ ⊢Δ ⊩A ⊩t , W.wkTerm Δ⊇Γ ⊢Δ ⊩A ⊩u
    , W.wkEqTerm Δ⊇Γ ⊢Δ ⊩A t≡u

opaque
  unfolding _⊩ᵛ⟨_⟩_

  -- Single-step weakening for _⊩ᵛ⟨_⟩_.
  --
  -- See also wk-⊩ᵛ below.

  wk1-⊩ᵛ : Γ ⊩ᵛ⟨ l′ ⟩ B → Γ ⊩ᵛ⟨ l ⟩ A → Γ ∙ B ⊩ᵛ⟨ l ⟩ wk1 A
  wk1-⊩ᵛ ⊩B (_ , ⊩A) =
    _ , wk1ᵛ _ (⊩ᵛ→⊩ᵛ/ ⊩B) ⊩A

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_∷_

  -- Single-step weakening for _⊩ᵛ⟨_⟩_∷_.
  --
  -- See also wk-⊩ᵛ∷ below.

  wk1-⊩ᵛ∷ : Γ ⊩ᵛ⟨ l′ ⟩ B → Γ ⊩ᵛ⟨ l ⟩ t ∷ A → Γ ∙ B ⊩ᵛ⟨ l ⟩ wk1 t ∷ wk1 A
  wk1-⊩ᵛ∷ {t} (_ , ⊩B) (_ , ⊩A , ⊩t) =
    case Irr.irrelevance _ _ ⊩B of λ
      ⊩B →
    _ , wk1ᵛ _ ⊩B ⊩A , wk1Termᵛ t ⊩A ⊩B ⊩t

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_

  -- Single-step weakening for _⊩ᵛ⟨_⟩_≡_.
  --
  -- See also wk-⊩ᵛ≡ below.

  wk1-⊩ᵛ≡ : Γ ⊩ᵛ⟨ l′ ⟩ C → Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Γ ∙ C ⊩ᵛ⟨ l ⟩ wk1 A ≡ wk1 B
  wk1-⊩ᵛ≡ {B} (_ , ⊩C) (_ , ⊩A , ⊩B , A≡B) =
    case Irr.irrelevance _ _ ⊩C of λ
      ⊩C →
    _ , wk1ᵛ _ ⊩C ⊩A , wk1ᵛ _ ⊩C ⊩B , wk1Eqᵛ {B = B} _ ⊩C ⊩A A≡B

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_∷_

  -- Single-step weakening for _⊩ᵛ⟨_⟩_≡_∷_.
  --
  -- See also wk-⊩ᵛ≡∷ below.

  wk1-⊩ᵛ≡∷ :
    Γ ⊩ᵛ⟨ l′ ⟩ B → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A →
    Γ ∙ B ⊩ᵛ⟨ l ⟩ wk1 t ≡ wk1 u ∷ wk1 A
  wk1-⊩ᵛ≡∷ {t} {u} (_ , ⊩B) (_ , modelsTermEq ⊩A ⊩t ⊩u t≡u) =
    case Irr.irrelevance _ _ ⊩B of λ
      ⊩B →
      _
    , modelsTermEq (wk1ᵛ _ ⊩B ⊩A) (wk1Termᵛ t ⊩A ⊩B ⊩t)
        (wk1Termᵛ u ⊩A ⊩B ⊩u) (wk1EqTermᵛ t u t≡u)

------------------------------------------------------------------------
-- Reduction

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Closure under reduction for _⊩⟨_⟩_.

  ⊩-⇒* :
    Γ ⊢ A :⇒*: B →
    Γ ⊩⟨ l ⟩ A →
    (Γ ⊩⟨ l ⟩ B) × Γ ⊩⟨ l ⟩ A ≡ B
  ⊩-⇒* A⇒*B ⊩A =
    case redSubst*′ A⇒*B ⊩A of λ
      (⊩B , A≡B) →
    ⊩B , (⊩A , ⊩B , A≡B)

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- Closure under reduction for _⊩⟨_⟩_∷_.

  ⊩∷-⇒* :
    Γ ⊢ t :⇒*: u ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ u ∷ A × Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩∷-⇒* t⇒*u (⊩A , ⊩t) =
    case redSubst*Term′ t⇒*u ⊩A ⊩t of λ
      (⊩u , t≡u) →
    (⊩A , ⊩u) , (⊩A , ⊩t , ⊩u , t≡u)

------------------------------------------------------------------------
-- Expansion

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Closure under expansion for _⊩⟨_⟩_.

  ⊩-⇐* :
    Γ ⊢ A ⇒* B →
    Γ ⊩⟨ l ⟩ B →
    (Γ ⊩⟨ l ⟩ A) × Γ ⊩⟨ l ⟩ A ≡ B
  ⊩-⇐* A⇒*B ⊩B =
    case redSubst* A⇒*B ⊩B of λ
      (⊩A , A≡B) →
    ⊩A , (⊩A , ⊩B , A≡B)

opaque
  unfolding _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- Closure under expansion for _⊩⟨_⟩_∷_.

  ⊩∷-⇐* :
    Γ ⊢ t ⇒* u ∷ A →
    Γ ⊩⟨ l ⟩ u ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A × Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩∷-⇐* t⇒*u (⊩A , ⊩u) =
    case redSubst*Term t⇒*u ⊩A ⊩u of λ
      (⊩t , t≡u) →
    (⊩A , ⊩t) , (⊩A , ⊩t , ⊩u , t≡u)

opaque
  unfolding _⊩ᵛ⟨_⟩_∷_ _⊩ᵛ⟨_⟩_≡_∷_ _⊩ˢ_∷_

  -- Closure under expansion for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷-⇐ :
    (∀ {m Δ} {σ : Subst m n} →
     Δ ⊩ˢ σ ∷ Γ →
     Δ ⊢ t [ σ ] ⇒ u [ σ ] ∷ A [ σ ]) →
    Γ ⊩ᵛ⟨ l ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A × Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A
  ⊩ᵛ∷-⇐ {t} {u} t⇒u (_ , ⊩A , ⊩u) =
    case redSubstTermᵛ {t = t} {u = u} _
           (λ _ ⊩σ → t⇒u (_ , _ , ⊩σ))
           ⊩A ⊩u of λ
      (⊩t , t≡u) →
    (_ , ⊩A , ⊩t) , (_ , modelsTermEq ⊩A ⊩t ⊩u t≡u)

------------------------------------------------------------------------
-- Escape lemmas

opaque

  -- An escape lemma for _⊩⟨_⟩_.

  escape-⊩ : Γ ⊩⟨ l ⟩ A → Γ ⊢ A
  escape-⊩ = escape

opaque
  unfolding _⊩⟨_⟩_∷_

  -- An escape lemma for _⊩⟨_⟩_∷_.

  escape-⊩∷ : Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊢ t ∷ A
  escape-⊩∷ (⊩A , ⊩t) = escapeTerm ⊩A ⊩t

opaque
  unfolding _⊩⟨_⟩_≡_

  -- An escape lemma for _⊩⟨_⟩_≡_.

  escape-⊩≡ : Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊢ A ≅ B
  escape-⊩≡ (⊩A , _ , A≡B) = escapeEq ⊩A A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- An escape lemma for _⊩⟨_⟩_≡_∷_.

  escape-⊩≡∷ : Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊢ t ≅ u ∷ A
  escape-⊩≡∷ (⊩A , _ , _ , t≡u) = escapeTermEq ⊩A t≡u

opaque
  unfolding _⊩ᵛ⟨_⟩_

  -- An escape lemma for _⊩ᵛ⟨_⟩_.

  escape-⊩ᵛ : Γ ⊩ᵛ⟨ l ⟩ A → Γ ⊢ A
  escape-⊩ᵛ (_ , ⊩A) = escapeᵛ _ ⊩A

opaque
  unfolding _⊩ᵛ⟨_⟩_∷_

  -- An escape lemma for _⊩ᵛ⟨_⟩_∷_.

  escape-⊩ᵛ∷ : Γ ⊩ᵛ⟨ l ⟩ t ∷ A → Γ ⊢ t ∷ A
  escape-⊩ᵛ∷ (_ , ⊩A , ⊩t) = escapeTermᵛ _ ⊩A ⊩t

opaque
  unfolding _⊩ˢ_∷_

  -- An escape lemma for _⊩ˢ_∷_.

  escape-⊩ˢ∷ :
    Δ ⊩ˢ σ ∷ Γ →
    ⊢ Δ × Δ ⊢ˢ σ ∷ Γ
  escape-⊩ˢ∷ (_ , ⊢Δ , ⊩σ) =
    ⊢Δ , wellformedSubst _ _ ⊩σ

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_

  -- An escape lemma for _⊩ᵛ⟨_⟩_≡_.

  escape-⊩ᵛ≡ : Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Γ ⊢ A ≅ B
  escape-⊩ᵛ≡ (_ , ⊩A , _ , A≡B) = escapeEqᵛ _ ⊩A A≡B

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_∷_

  -- An escape lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  escape-⊩ᵛ≡∷ : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A → Γ ⊢ t ≅ u ∷ A
  escape-⊩ᵛ≡∷ (_ , modelsTermEq ⊩A _ _ t≡u) = escapeEqTermᵛ _ ⊩A t≡u

opaque
  unfolding _⊩ˢ_≡_∷_

  -- An escape lemma for _⊩ˢ_≡_∷_.

  escape-⊩ˢ≡∷ : Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → ⊢ Δ × Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ
  escape-⊩ˢ≡∷ (_ , ⊢Δ , _ , _ , σ₁≡σ₂) =
    ⊢Δ , wellformedSubstEq _ _ _ σ₁≡σ₂

------------------------------------------------------------------------
-- Reducibility from validity

opaque
  unfolding _⊩ᵛ⟨_⟩_

  -- If A is valid, then A is reducible.

  ⊩ᵛ→⊩ : Γ ⊩ᵛ⟨ l ⟩ A → Γ ⊩⟨ l ⟩ A
  ⊩ᵛ→⊩ (_ , ⊩A) = reducibleᵛ _ ⊩A

opaque
  unfolding _⊩ᵛ⟨_⟩_∷_ _⊩⟨_⟩_∷_

  -- If t is valid, then t is reducible.

  ⊩ᵛ∷→⊩∷ : Γ ⊩ᵛ⟨ l ⟩ t ∷ A → Γ ⊩⟨ l ⟩ t ∷ A
  ⊩ᵛ∷→⊩∷ (_ , ⊩A , ⊩t) =
    reducibleᵛ _ ⊩A , reducibleTermᵛ _ ⊩A ⊩t

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_ _⊩⟨_⟩_≡_

  -- If there is a valid equality between A and B, then there is a
  -- reducible equality between A and B.

  ⊩ᵛ≡→⊩≡ : Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ B
  ⊩ᵛ≡→⊩≡ (_ , ⊩A , ⊩B , A≡B) =
    reducibleᵛ _ ⊩A , reducibleᵛ _ ⊩B , reducibleEqᵛ _ ⊩A A≡B

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_∷_ _⊩⟨_⟩_≡_∷_

  -- If there is a valid equality between t and u, then there is a
  -- reducible equality between t and u.

  ⊩ᵛ≡∷→⊩≡∷ : Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩ᵛ≡∷→⊩≡∷ (_ , modelsTermEq ⊩A ⊩t ⊩u t≡u) =
      reducibleᵛ _ ⊩A , reducibleTermᵛ _ ⊩A ⊩t , reducibleTermᵛ _ ⊩A ⊩u
    , reducibleEqTermᵛ _ ⊩A t≡u

------------------------------------------------------------------------
-- Equational reasoning combinators

-- For more explanations of the combinators, see
-- Definition.Typed.Reasoning.Reduction.Primitive.

opaque

  -- Equational reasoning combinators for _⊩⟨_⟩_≡_.

  infix -1
    _∎⟨_⟩⊩ finally-⊩≡ finally-⊩≡˘
  infixr -2
    step-⊩≡ step-⊩≡˘ step-⊩≡≡ step-⊩≡≡˘ step-⊩≡⇒* step-⊩≡⇒ step-⊩≡⇐*
    step-⊩≡⇐ _≡⟨⟩⊩_ finally-⊩≡≡ finally-⊩≡≡˘ finally-⊩≡⇐* finally-⊩≡:⇒*:

  step-⊩≡ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡ _ = flip trans-⊩≡

  syntax step-⊩≡ A B≡C A≡B = A ≡⟨ A≡B ⟩⊩ B≡C

  step-⊩≡˘ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊩⟨ l ⟩ B ≡ A → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡˘ _ B≡C B≡A = trans-⊩≡ (sym-⊩≡ B≡A) B≡C

  syntax step-⊩≡˘ A B≡C B≡A = A ≡˘⟨ B≡A ⟩⊩ B≡C

  step-⊩≡≡ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → A PE.≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡≡ _ B≡C PE.refl = B≡C

  syntax step-⊩≡≡ A B≡C A≡B = A ≡⟨ A≡B ⟩⊩≡ B≡C

  step-⊩≡≡˘ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → B PE.≡ A → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡≡˘ _ B≡C PE.refl = B≡C

  syntax step-⊩≡≡˘ A B≡C B≡A = A ≡˘⟨ B≡A ⟩⊩≡ B≡C

  step-⊩≡⇒* : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊢ A ⇒* B → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡⇒* _ B≡C A⇒*B =
    trans-⊩≡ (⊩-⇐* A⇒*B (wf-⊩≡ B≡C .proj₁) .proj₂) B≡C

  syntax step-⊩≡⇒* A B≡C A⇒*B = A ⇒*⟨ A⇒*B ⟩⊩ B≡C

  step-⊩≡⇒ : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊢ A ⇒ B → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡⇒ _ B≡C A⇒B =
    step-⊩≡⇒* _ B≡C (A⇒B ⇨ id (escape (wf-⊩≡ B≡C .proj₁)))

  syntax step-⊩≡⇒ A B≡C A⇒B = A ⇒⟨ A⇒B ⟩⊩ B≡C

  step-⊩≡⇐* : ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊢ B :⇒*: A → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡⇐* _ B≡C B⇒*A =
    trans-⊩≡ (sym-⊩≡ (⊩-⇒* B⇒*A (wf-⊩≡ B≡C .proj₁) .proj₂)) B≡C

  syntax step-⊩≡⇐* A B≡C B⇒*A = A ⇐*⟨ B⇒*A ⟩⊩ B≡C

  step-⊩≡⇐ :
    ∀ A → Γ ⊩⟨ l ⟩ B ≡ C → Γ ⊢ B ⇒ A → Γ ⊢ A → Γ ⊩⟨ l ⟩ A ≡ C
  step-⊩≡⇐ _ B≡C B⇒A ⊢A =
    step-⊩≡⇐* _ B≡C
      ([_,_,_] (escape (wf-⊩≡ B≡C .proj₁)) ⊢A (B⇒A ⇨ id ⊢A))

  syntax step-⊩≡⇐ A B≡C B⇒A ⊢A = A ⇐⟨ B⇒A , ⊢A ⟩⊩ B≡C

  _≡⟨⟩⊩_ : ∀ A → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ B
  _ ≡⟨⟩⊩ A≡B = A≡B

  _∎⟨_⟩⊩ : ∀ A → Γ ⊩⟨ l ⟩ A → Γ ⊩⟨ l ⟩ A ≡ A
  _ ∎⟨ ⊩A ⟩⊩ = refl-⊩≡ ⊩A

  finally-⊩≡ : ∀ A B → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ B
  finally-⊩≡ _ _ A≡B = A≡B

  syntax finally-⊩≡ A B A≡B = A ≡⟨ A≡B ⟩⊩∎ B ∎

  finally-⊩≡˘ : ∀ A B → Γ ⊩⟨ l ⟩ B ≡ A → Γ ⊩⟨ l ⟩ A ≡ B
  finally-⊩≡˘ _ _ A≡B = sym-⊩≡ A≡B

  syntax finally-⊩≡˘ A B B≡A = A ≡˘⟨ B≡A ⟩⊩∎ B ∎

  finally-⊩≡≡ : ∀ A → B PE.≡ C → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  finally-⊩≡≡ _ PE.refl A≡B = A≡B

  syntax finally-⊩≡≡ A B≡C A≡B = A ≡⟨ A≡B ⟩⊩∎≡ B≡C

  finally-⊩≡≡˘ : ∀ A → B PE.≡ C → Γ ⊩⟨ l ⟩ B ≡ A → Γ ⊩⟨ l ⟩ A ≡ C
  finally-⊩≡≡˘ _ PE.refl B≡A = sym-⊩≡ B≡A

  syntax finally-⊩≡≡˘ A B≡C B≡A = A ≡˘⟨ B≡A ⟩⊩∎≡ B≡C

  finally-⊩≡⇐* :
    ∀ A → Γ ⊢ C ⇒* B → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  finally-⊩≡⇐* _ C⇒*B A≡B =
    trans-⊩≡ A≡B (sym-⊩≡ (⊩-⇐* C⇒*B (wf-⊩≡ A≡B .proj₂) .proj₂))

  syntax finally-⊩≡⇐* A C⇒*B A≡B = A ≡⟨ A≡B ⟩⊩⇐* C⇒*B

  finally-⊩≡:⇒*: :
    ∀ A → Γ ⊢ B :⇒*: C → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ A ≡ C
  finally-⊩≡:⇒*: _ B⇒*C A≡B =
    case wf-⊩≡ A≡B of λ
      (_ , ⊩B) →
    trans-⊩≡ A≡B (⊩-⇒* B⇒*C ⊩B .proj₂)

  syntax finally-⊩≡:⇒*: A B⇒*C A≡B = A ≡⟨ A≡B ⟩⊩:⇒*: B⇒*C

opaque

  -- Equational reasoning combinators for _⊩⟨_⟩_≡_∷_.

  infix -1
    _∎⟨_⟩⊩∷ finally-⊩≡∷ finally-⊩≡∷˘
  infix -2
    step-⊩≡∷-conv step-⊩≡∷-conv˘ step-⊩≡∷-conv-≡ step-⊩≡∷-conv-≡˘
  infixr -2
    step-⊩≡∷ step-⊩≡∷˘ step-⊩≡∷≡ step-⊩≡∷≡˘ step-⊩≡∷⇒* step-⊩≡∷⇒
    step-⊩≡∷⇐* step-⊩≡∷⇐ _≡⟨⟩⊩∷_ finally-⊩≡∷≡ finally-⊩≡∷≡˘
    finally-⊩≡∷⇐* finally-⊩≡∷:⇒*:

  step-⊩≡∷ :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷ _ = flip trans-⊩≡∷

  syntax step-⊩≡∷ t u≡v t≡u = t ≡⟨ t≡u ⟩⊩∷ u≡v

  step-⊩≡∷˘ :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊩⟨ l′ ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷˘ _ u≡v u≡t = trans-⊩≡∷ (sym-⊩≡∷ u≡t) u≡v

  syntax step-⊩≡∷˘ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊩∷ u≡v

  step-⊩≡∷≡ : ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → t PE.≡ u → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷≡ _ u≡v PE.refl = u≡v

  syntax step-⊩≡∷≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊩∷≡ u≡v

  step-⊩≡∷≡˘ : ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → u PE.≡ t → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷≡˘ _ u≡v PE.refl = u≡v

  syntax step-⊩≡∷≡˘ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊩∷≡ u≡v

  step-⊩≡∷⇒* :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ t ⇒* u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷⇒* _ u≡v t⇒*u =
    trans-⊩≡∷ (⊩∷-⇐* t⇒*u (wf-⊩≡∷ u≡v .proj₁) .proj₂) u≡v

  syntax step-⊩≡∷⇒* t u≡v t⇒*u = t ⇒*⟨ t⇒*u ⟩⊩∷ u≡v

  step-⊩≡∷⇒ :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ t ⇒ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷⇒ _ u≡v t⇒u =
    step-⊩≡∷⇒* _ u≡v (t⇒u ⇨ id (escape-⊩∷ (wf-⊩≡∷ u≡v .proj₁)))

  syntax step-⊩≡∷⇒ t u≡v t⇒u = t ⇒⟨ t⇒u ⟩⊩∷ u≡v

  step-⊩≡∷⇐* :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u :⇒*: t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷⇐* _ u≡v u⇒*t =
    trans-⊩≡∷ (sym-⊩≡∷ (⊩∷-⇒* u⇒*t (wf-⊩≡∷ u≡v .proj₁) .proj₂)) u≡v

  syntax step-⊩≡∷⇐* t u≡v u⇒*t = t ⇐*⟨ u⇒*t ⟩⊩∷ u≡v

  step-⊩≡∷⇐ :
    ∀ t → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u ⇒ t ∷ A → Γ ⊢ t ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷⇐ _ u≡v u⇒t ⊢t =
    step-⊩≡∷⇐* _ u≡v
      ([_,_,_] (escape-⊩∷ (wf-⊩≡∷ u≡v .proj₁)) ⊢t (u⇒t ⇨ id ⊢t))

  syntax step-⊩≡∷⇐ t u≡v u⇒t ⊢t = t ⇐⟨ u⇒t , ⊢t ⟩⊩∷ u≡v

  _≡⟨⟩⊩∷_ : ∀ t → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  _ ≡⟨⟩⊩∷ t≡u = t≡u

  step-⊩≡∷-conv :
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷-conv t≡u A≡B = conv-⊩≡∷ (sym-⊩≡ A≡B) t≡u

  syntax step-⊩≡∷-conv t≡u A≡B = ⟨ A≡B ⟩⊩∷ t≡u

  step-⊩≡∷-conv˘ :
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B → Γ ⊩⟨ l ⟩ B ≡ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷-conv˘ t≡u B≡A = conv-⊩≡∷ B≡A t≡u

  syntax step-⊩≡∷-conv˘ t≡u B≡A = ˘⟨ B≡A ⟩⊩∷ t≡u

  step-⊩≡∷-conv-≡ : Γ ⊩⟨ l ⟩ t ≡ u ∷ B → A PE.≡ B → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷-conv-≡ t≡u PE.refl = t≡u

  syntax step-⊩≡∷-conv-≡ t≡u A≡B = ⟨ A≡B ⟩⊩∷≡ t≡u

  step-⊩≡∷-conv-≡˘ : Γ ⊩⟨ l ⟩ t ≡ u ∷ B → B PE.≡ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷-conv-≡˘ t≡u PE.refl = t≡u

  syntax step-⊩≡∷-conv-≡˘ t≡u B≡A = ˘⟨ B≡A ⟩⊩∷≡ t≡u

  _∎⟨_⟩⊩∷ : ∀ t → Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ t ∷ A
  _ ∎⟨ ⊩t ⟩⊩∷ = refl-⊩≡∷ ⊩t

  finally-⊩≡∷ : ∀ t u → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  finally-⊩≡∷ _ _ t≡u = t≡u

  syntax finally-⊩≡∷ t u t≡u = t ≡⟨ t≡u ⟩⊩∷∎ u ∎

  finally-⊩≡∷˘ : ∀ t u → Γ ⊩⟨ l ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  finally-⊩≡∷˘ _ _ t≡u = sym-⊩≡∷ t≡u

  syntax finally-⊩≡∷˘ t u u≡t = t ≡˘⟨ u≡t ⟩⊩∷∎ u ∎

  finally-⊩≡∷≡ :
    ∀ t → u PE.≡ v → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷≡ _ PE.refl t≡u = t≡u

  syntax finally-⊩≡∷≡ t u≡v t≡u = t ≡⟨ t≡u ⟩⊩∷∎≡ u≡v

  finally-⊩≡∷≡˘ :
    ∀ t → u PE.≡ v → Γ ⊩⟨ l ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷≡˘ _ PE.refl u≡t = sym-⊩≡∷ u≡t

  syntax finally-⊩≡∷≡˘ t u≡v u≡t = t ≡˘⟨ u≡t ⟩⊩∷∎≡ u≡v

  finally-⊩≡∷⇐* :
    ∀ t → Γ ⊢ v ⇒* u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷⇐* _ v⇒*u t≡u =
    trans-⊩≡∷ t≡u (sym-⊩≡∷ (⊩∷-⇐* v⇒*u (wf-⊩≡∷ t≡u .proj₂) .proj₂))

  syntax finally-⊩≡∷⇐* t v⇒*u t≡u = t ≡⟨ t≡u ⟩⊩∷⇐* v⇒*u

  finally-⊩≡∷:⇒*: :
    ∀ t → Γ ⊢ u :⇒*: v ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷:⇒*: _ u⇒*v t≡u =
    case wf-⊩≡∷ t≡u of λ
      (_ , ⊩u) →
    trans-⊩≡∷ t≡u (⊩∷-⇒* u⇒*v ⊩u .proj₂)

  syntax finally-⊩≡∷:⇒*: t u⇒*v t≡u = t ≡⟨ t≡u ⟩⊩∷:⇒*: u⇒*v

opaque

  -- Equational reasoning combinators for _⊩⟨_⟩_≡_∷_ with explicit
  -- types.

  infix -1
    _∷_∎⟨_⟩⊩∷∷ finally-⊩≡∷∷ finally-⊩≡∷∷˘
  infix -2
    step-⊩≡∷∷-conv step-⊩≡∷∷-conv˘ step-⊩≡∷∷-conv-≡ step-⊩≡∷∷-conv-≡˘
  infixr -2
    step-⊩≡∷∷ step-⊩≡∷∷˘ step-⊩≡∷∷≡ step-⊩≡∷∷≡˘ step-⊩≡∷∷⇒* step-⊩≡∷∷⇒
    step-⊩≡∷∷⇐* step-⊩≡∷∷⇐ _∷_≡⟨⟩⊩∷∷_ finally-⊩≡∷∷≡ finally-⊩≡∷∷≡˘
    finally-⊩≡∷∷⇐* finally-⊩≡∷∷:⇒*:

  step-⊩≡∷∷ :
    ∀ t A →
    Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷ _ _ = step-⊩≡∷ _

  syntax step-⊩≡∷∷ t A u≡v t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷ u≡v

  step-⊩≡∷∷˘ :
    ∀ t A →
    Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊩⟨ l′ ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷˘ _ _ = step-⊩≡∷˘ _

  syntax step-⊩≡∷∷˘ t A u≡v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∷ u≡v

  step-⊩≡∷∷≡ :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → t PE.≡ u → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷≡ _ _ = step-⊩≡∷≡ _

  syntax step-⊩≡∷∷≡ t A u≡v t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷≡ u≡v

  step-⊩≡∷∷≡˘ :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → u PE.≡ t → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷≡˘ _ _ = step-⊩≡∷≡˘ _

  syntax step-⊩≡∷∷≡˘ t A u≡v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∷≡ u≡v

  step-⊩≡∷∷⇒* :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ t ⇒* u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷⇒* _ _ = step-⊩≡∷⇒* _

  syntax step-⊩≡∷∷⇒* t A u≡v t⇒*u = t ∷ A ⇒*⟨ t⇒*u ⟩⊩∷∷ u≡v

  step-⊩≡∷∷⇒ :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ t ⇒ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷⇒ _ _ = step-⊩≡∷⇒ _

  syntax step-⊩≡∷∷⇒ t A u≡v t⇒u = t ∷ A ⇒⟨ t⇒u ⟩⊩∷∷ u≡v

  step-⊩≡∷∷⇐* :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u :⇒*: t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷⇐* _ _ = step-⊩≡∷⇐* _

  syntax step-⊩≡∷∷⇐* t A u≡v u⇒*t = t ∷ A ⇐*⟨ u⇒*t ⟩⊩∷∷ u≡v

  step-⊩≡∷∷⇐ :
    ∀ t A → Γ ⊩⟨ l ⟩ u ≡ v ∷ A → Γ ⊢ u ⇒ t ∷ A → Γ ⊢ t ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  step-⊩≡∷∷⇐ _ _ = step-⊩≡∷⇐ _

  syntax step-⊩≡∷∷⇐ t A u≡v u⇒t ⊢t = t ∷ A ⇐⟨ u⇒t , ⊢t ⟩⊩∷∷ u≡v

  _∷_≡⟨⟩⊩∷∷_ : ∀ t A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  _ ∷ _ ≡⟨⟩⊩∷∷ t≡u = t≡u

  step-⊩≡∷∷-conv :
    ∀ A → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B → Γ ⊩⟨ l ⟩ A ≡ B → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷∷-conv _ = step-⊩≡∷-conv

  syntax step-⊩≡∷∷-conv A t≡u A≡B = ∷ A ⟨ A≡B ⟩⊩∷∷ t≡u

  step-⊩≡∷∷-conv˘ :
    ∀ A → Γ ⊩⟨ l′ ⟩ t ≡ u ∷ B → Γ ⊩⟨ l ⟩ B ≡ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷∷-conv˘ _ = step-⊩≡∷-conv˘

  syntax step-⊩≡∷∷-conv˘ A t≡u B≡A = ∷ A ˘⟨ B≡A ⟩⊩∷∷ t≡u

  step-⊩≡∷∷-conv-≡ :
    ∀ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ B → A PE.≡ B → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷∷-conv-≡ _ = step-⊩≡∷-conv-≡

  syntax step-⊩≡∷∷-conv-≡ A t≡u A≡B = ∷ A ⟨ A≡B ⟩⊩∷∷≡ t≡u

  step-⊩≡∷∷-conv-≡˘ :
    ∀ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ B → B PE.≡ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  step-⊩≡∷∷-conv-≡˘ _ = step-⊩≡∷-conv-≡˘

  syntax step-⊩≡∷∷-conv-≡˘ A t≡u B≡A = ∷ A ˘⟨ B≡A ⟩⊩∷∷≡ t≡u

  _∷_∎⟨_⟩⊩∷∷ : ∀ t A → Γ ⊩⟨ l ⟩ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ t ∷ A
  _ ∷ _ ∎⟨ ⊩t ⟩⊩∷∷ = refl-⊩≡∷ ⊩t

  finally-⊩≡∷∷ : ∀ t A u → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  finally-⊩≡∷∷ _ _ _ t≡u = t≡u

  syntax finally-⊩≡∷∷ t A u t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∎∷ u ∎

  finally-⊩≡∷∷˘ : ∀ t A u → Γ ⊩⟨ l ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  finally-⊩≡∷∷˘ _ _ _ t≡u = sym-⊩≡∷ t≡u

  syntax finally-⊩≡∷∷˘ t A u u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∎∷ u ∎

  finally-⊩≡∷∷≡ :
    ∀ t A → u PE.≡ v → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷∷≡ _ _ = finally-⊩≡∷≡ _

  syntax finally-⊩≡∷∷≡ t A u≡v t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∎∷≡ u≡v

  finally-⊩≡∷∷≡˘ :
    ∀ t A → u PE.≡ v → Γ ⊩⟨ l ⟩ u ≡ t ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷∷≡˘ _ _ = finally-⊩≡∷≡˘ _

  syntax finally-⊩≡∷∷≡˘ t A u≡v u≡t = t ∷ A ≡˘⟨ u≡t ⟩⊩∷∎∷≡ u≡v

  finally-⊩≡∷∷⇐* :
    ∀ t A → Γ ⊢ v ⇒* u ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷∷⇐* _ _ = finally-⊩≡∷⇐* _

  syntax finally-⊩≡∷∷⇐* t A v⇒*u t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷⇐* v⇒*u

  finally-⊩≡∷∷:⇒*: :
    ∀ t A → Γ ⊢ u :⇒*: v ∷ A → Γ ⊩⟨ l ⟩ t ≡ u ∷ A → Γ ⊩⟨ l ⟩ t ≡ v ∷ A
  finally-⊩≡∷∷:⇒*: _ _ = finally-⊩≡∷:⇒*: _

  syntax finally-⊩≡∷∷:⇒*: t A v⇒*u t≡u = t ∷ A ≡⟨ t≡u ⟩⊩∷∷:⇒*: v⇒*u

------------------------------------------------------------------------
-- Embedding

private opaque

  -- A lemma used below.

  emb-⊩∷-lemma :
    {l<l′ : l < l′} {⊩A : LogRelKit._⊩_ k Γ A}
    (eq : k PE.≡ kit′ l<l′) →
    LogRelKit._⊩_∷_/_ k Γ t A ⊩A →
    LogRelKit._⊩_∷_/_ (kit′ l<l′) Γ t A
      (PE.subst (λ k → LogRelKit._⊩_ k _ _) eq ⊩A)
  emb-⊩∷-lemma PE.refl ⊩t = ⊩t

opaque
  unfolding _⊩⟨_⟩_∷_

  -- Embedding for _⊩⟨_⟩_∷_.

  emb-⊩∷ :
    l ≤ l′ →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l′ ⟩ t ∷ A
  emb-⊩∷  ≤′-refl ⊩t        = ⊩t
  emb-⊩∷ (≤′-step  l<l′) (⊩A , ⊩t) =
      emb (≤→< l<l′) (PE.subst (λ k → LogRelKit._⊩_ k _ _) (kit≡kit′ (≤→< l<l′)) ⊩A)
    , emb-⊩∷-lemma {l<l′ = ≤→< l<l′} {⊩A = ⊩A} (kit≡kit′ (≤→< l<l′)) ⊩t

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Embedding for _⊩⟨_⟩_≡_.

  emb-⊩≡ :
    l ≤ l′ →
    Γ ⊩⟨ l ⟩ A ≡ B →
    Γ ⊩⟨ l′ ⟩ A ≡ B
  emb-⊩≡     ≤′-refl    A≡B             = A≡B
  emb-⊩≡ {Γ} (≤′-step l<l′) (⊩A , ⊩B , A≡B) =
      emb (≤→< l<l′) (PE.subst (λ k → LogRelKit._⊩_ k _ _) (kit≡kit′ (≤→< l<l′)) ⊩A)
    , emb (≤→< l<l′) (PE.subst (λ k → LogRelKit._⊩_ k _ _) (kit≡kit′ (≤→< l<l′)) ⊩B)
    , lemma (kit≡kit′ (≤→< l<l′)) A≡B
    where
    lemma :
      {⊩A : LogRelKit._⊩_ k Γ A}
      (eq : k PE.≡ kit′ (≤→< l<l′)) →
      LogRelKit._⊩_≡_/_ k Γ A B ⊩A →
      LogRelKit._⊩_≡_/_ (kit′ (≤→< l<l′)) Γ A B
        (PE.subst (λ k → LogRelKit._⊩_ k _ _) eq ⊩A)
    lemma PE.refl A≡B = A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Embedding for _⊩⟨_⟩_≡_∷_.

  emb-⊩≡∷ :
    l ≤ l′ →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A
  emb-⊩≡∷     ≤′-refl   t≡u                  = t≡u
  emb-⊩≡∷ {Γ} (≤′-step l<l′) (⊩A , ⊩t , ⊩u , t≡u) =
      emb (≤→< l<l′) (PE.subst (λ k → LogRelKit._⊩_ k _ _) (kit≡kit′ (≤→< l<l′)) ⊩A)
    , emb-⊩∷-lemma {l<l′ = ≤→< l<l′} {⊩A = ⊩A} (kit≡kit′ (≤→< l<l′)) ⊩t
    , emb-⊩∷-lemma {l<l′ = ≤→< l<l′} {⊩A = ⊩A} (kit≡kit′ (≤→< l<l′)) ⊩u
    , lemma (kit≡kit′ (≤→< l<l′)) t≡u
    where
    lemma :
      {⊩A : LogRelKit._⊩_ k Γ A}
      (eq : k PE.≡ kit′ (≤→< l<l′)) →
      LogRelKit._⊩_≡_∷_/_ k Γ t u A ⊩A →
      LogRelKit._⊩_≡_∷_/_ (kit′ (≤→< l<l′)) Γ t u A
        (PE.subst (λ k → LogRelKit._⊩_ k _ _) eq ⊩A)
    lemma PE.refl t≡u = t≡u

opaque
  unfolding _⊩ᵛ⟨_⟩_

  -- Embedding for _⊩ᵛ⟨_⟩_.

  emb-⊩ᵛ :
    l ≤ l′ →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ⊩ᵛ⟨ l′ ⟩ A
  emb-⊩ᵛ ≤′-refl      ⊩A       = ⊩A
  emb-⊩ᵛ (≤′-step l<) (_ , ⊩A) =
    _ , C.cumul _ (≤→< l<) ⊩A

opaque

  -- Embedding for _⊩ᵛ⟨_⟩_∷_.

  emb-⊩ᵛ∷ :
    l ≤ l′ →
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A
  emb-⊩ᵛ∷ l≤l′ ⊩t =
    level-⊩ᵛ∷ (emb-⊩ᵛ l≤l′ (wf-⊩ᵛ∷ ⊩t)) ⊩t

------------------------------------------------------------------------
-- Some introduction lemmas

opaque
  unfolding _⊩⟨_⟩_∷_

  -- An introduction lemma for _⊩⟨_⟩_∷_.

  ⊩∷-intro :
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ t ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ t ∷ A
  ⊩∷-intro = _,_

opaque
  unfolding _⊩⟨_⟩_≡_

  -- An introduction lemma for _⊩⟨_⟩_≡_.

  ⊩≡-intro :
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ B →
    Γ ⊩⟨ l ⟩ A ≡ B / ⊩A →
    Γ ⊩⟨ l ⟩ A ≡ B
  ⊩≡-intro ⊩A ⊩B A≡B = ⊩A , ⊩B , A≡B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- An introduction lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷-intro :
    (⊩A : Γ ⊩⟨ l ⟩ A) →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  ⊩≡∷-intro ⊩A ⊩t ⊩u t≡u =
    ⊩A , ⊩∷→⊩∷/ ⊩A ⊩t , ⊩∷→⊩∷/ ⊩A ⊩u , t≡u

opaque
  unfolding _⊩ᵛ⟨_⟩_

  -- An introduction lemma for ⊩ᵛ_.

  ⊩ᵛ-∙-intro : Γ ⊩ᵛ⟨ l ⟩ A → ⊩ᵛ Γ ∙ A
  ⊩ᵛ-∙-intro (_ , ⊩A) = _ ∙ ⊩A

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩⟨_⟩_≡_ _⊩ˢ_∷_ _⊩ˢ_≡_∷_

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ⇔ :
    Γ ⊩ᵛ⟨ l ⟩ A ⇔
    (⊩ᵛ Γ ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩⟨ l ⟩ A [ σ₁ ] ≡ A [ σ₂ ]))
  ⊩ᵛ⇔ =
      (λ (⊩Γ , ⊩A) →
           ⊩Γ
         , λ (_ , ⊢Δ , ⊩σ₁ , ⊩σ₂ , σ₁≡σ₂) →
             case ⊩A .unwrap ⊢Δ (Irr.irrelevanceSubst _ _ _ _ ⊩σ₁) of λ
               (⊩A[σ₁] , A[σ₁]≡) →
             case Irr.irrelevanceSubst _ _ _ _ ⊩σ₂ of λ
               ⊩σ₂ →
               ⊩A[σ₁]
             , ⊩A .unwrap ⊢Δ ⊩σ₂ .proj₁
             , A[σ₁]≡ ⊩σ₂ (Irr.irrelevanceSubstEq _ _ _ _ _ _ σ₁≡σ₂))
    , (λ (⊩Γ , A≡A) →
           ⊩Γ
         , wrap λ ⊢Δ ⊩σ →
             case wf-⊩≡ (A≡A (refl-⊩ˢ≡∷ (_ , _ , ⊩σ))) of λ
               (⊩A[σ] , _) →
               ⊩A[σ]
             , λ {σ′ = _} ⊩σ′ σ≡σ′ →
                 ⊩≡→⊩≡/ ⊩A[σ] (A≡A (_ , _ , _ , ⊩σ′ , σ≡σ′)))

opaque

  -- A corollary.

  ⊩ᵛ→⊩ˢ∷→⊩[] :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ A [ σ ]
  ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩σ =
    wf-⊩≡ (⊩ᵛ⇔ .proj₁ ⊩A .proj₂ (refl-⊩ˢ≡∷ ⊩σ)) .proj₁

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_∷_ _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_ _⊩ˢ_∷_ _⊩ˢ_≡_∷_

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷⇔ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A ⇔
    (Γ ⊩ᵛ⟨ l ⟩ A ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩⟨ l ⟩ t [ σ₁ ] ≡ t [ σ₂ ] ∷ A [ σ₁ ]))
  ⊩ᵛ∷⇔ =
      (λ (_ , ⊩A , ⊩t) →
           (_ , ⊩A)
         , λ (_ , ⊢Δ , ⊩σ₁ , ⊩σ₂ , σ₁≡σ₂) →
             case Irr.irrelevanceSubst _ _ _ _ ⊩σ₁ of λ
               ⊩σ₁ →
             case Irr.irrelevanceSubst _ _ _ _ ⊩σ₂ of λ
               ⊩σ₂ →
             case Irr.irrelevanceSubstEq _ _ _ _ _ _ σ₁≡σ₂ of λ
               σ₁≡σ₂ →
             let ⊩A[σ₁] , A[σ₁]≡ = ⊩A .unwrap ⊢Δ ⊩σ₁ in
             case ⊩t _ ⊩σ₁ of λ
               (⊩t[σ₁] , t[σ₁]≡) →
               ⊩A[σ₁]
             , ⊩t[σ₁]
             , convTerm₂ ⊩A[σ₁] (⊩A .unwrap ⊢Δ ⊩σ₂ .proj₁)
                 (A[σ₁]≡ ⊩σ₂ σ₁≡σ₂) (⊩t _ ⊩σ₂ .proj₁)
             , t[σ₁]≡ ⊩σ₂ σ₁≡σ₂)
    , (λ ((_ , ⊩A) , t≡t) →
           _
         , ⊩A
         , λ _ ⊩σ →
             let ⊩A[σ] , _ = ⊩A .unwrap _ ⊩σ in
             case wf-⊩≡∷ (t≡t (refl-⊩ˢ≡∷ (_ , _ , ⊩σ))) of λ
               ((⊩A[σ]′ , ⊩t[σ]) , _) →
               irrelevanceTerm ⊩A[σ]′ ⊩A[σ] ⊩t[σ]
             , λ {σ′ = _} ⊩σ′ σ≡σ′ →
                 ⊩≡∷→⊩≡∷/ ⊩A[σ] (t≡t (_ , _ , _ , ⊩σ′ , σ≡σ′)))

opaque

  -- A corollary.

  ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ :
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ t [ σ ] ∷ A [ σ ]
  ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩t ⊩σ =
    wf-⊩≡∷ (⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ (refl-⊩ˢ≡∷ ⊩σ)) .proj₁

opaque
  unfolding _⊩ˢ_∷_

  -- A characterisation lemma for _⊩ˢ_∷_.

  ⊩ˢ∷ε⇔ : Δ ⊩ˢ σ ∷ ε ⇔ ⊢ Δ
  ⊩ˢ∷ε⇔ =
      (λ (_ , ⊢Δ , _) → ⊢Δ)
    , (λ ⊢Δ → ε , ⊢Δ , _)

opaque
  unfolding _⊩ˢ_∷_ _⊩ᵛ⟨_⟩_ _⊩⟨_⟩_∷_

  -- Another characterisation lemma for _⊩ˢ_∷_.

  ⊩ˢ∷∙⇔′ :
    Δ ⊩ˢ σ ∷ Γ ∙ A ⇔
    ((∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A) ×
     (∃ λ l → Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
     Δ ⊩ˢ tail σ ∷ Γ)
  ⊩ˢ∷∙⇔′ =
      (λ { (_ ∙ ⊩A , _ , ⊩tail , ⊩head) →
             (_ , _ , ⊩A) , (_ , ⊩A .unwrap _ _ .proj₁ , ⊩head)
           , (_ , _ , ⊩tail) })
    , (λ ((_ , _ , ⊩A) , (_ , ⊩A[tail] , ⊩head) , (_ , ⊢Δ , ⊩tail)) →
         case Irr.irrelevanceSubst _ _ _ _ ⊩tail of λ
           ⊩tail →
           _ ∙ ⊩A , ⊢Δ
         , ( ⊩tail
           , irrelevanceTerm ⊩A[tail] (⊩A .unwrap _ ⊩tail .proj₁) ⊩head
           ))

opaque

  -- A variant of the previous lemma.

  ⊩ˢ∷∙⇔ :
    Δ ⊩ˢ σ ∷ Γ ∙ A ⇔
    ((∃ λ l → (Γ ⊩ᵛ⟨ l ⟩ A) × Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
     Δ ⊩ˢ tail σ ∷ Γ)
  ⊩ˢ∷∙⇔ {Δ} {σ} {Γ} {A} =
    Δ ⊩ˢ σ ∷ Γ ∙ A                                              ⇔⟨ ⊩ˢ∷∙⇔′ ⟩

    (∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A) ×
    (∃ λ l → Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
    Δ ⊩ˢ tail σ ∷ Γ                                             ⇔⟨ (λ ((l₁ , ⊩A) , (_ , ⊩head) , ⊩tail) →
                                                                      (l₁ , ⊩A , level-⊩∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A ⊩tail) ⊩head) , ⊩tail)
                                                                 , (λ ((l , ⊩A , ⊩head) , ⊩tail) →
                                                                      (l , ⊩A) , (l , ⊩head) , ⊩tail)
                                                                 ⟩
    (∃ λ l → (Γ ⊩ᵛ⟨ l ⟩ A) × Δ ⊩⟨ l ⟩ head σ ∷ A [ tail σ ]) ×
    Δ ⊩ˢ tail σ ∷ Γ                                             □⇔

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_ _⊩⟨_⟩_≡_ _⊩ˢ_∷_

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_≡_.

  ⊩ᵛ≡⇔ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B ⇔
    (Γ ⊩ᵛ⟨ l ⟩ A ×
     Γ ⊩ᵛ⟨ l ⟩ B ×
     (∀ {m Δ} {σ : Subst m n} →
      Δ ⊩ˢ σ ∷ Γ →
      Δ ⊩⟨ l ⟩ A [ σ ] ≡ B [ σ ]))
  ⊩ᵛ≡⇔ =
      (λ (_ , ⊩A , ⊩B , A≡B) →
           (_ , ⊩A)
         , (_ , ⊩B)
         , λ (_ , ⊢Δ , ⊩σ) →
             case Irr.irrelevanceSubst _ _ _ _ ⊩σ of λ
               ⊩σ →
               ⊩A .unwrap ⊢Δ ⊩σ .proj₁
             , ⊩B .unwrap ⊢Δ ⊩σ .proj₁
             , A≡B ⊢Δ ⊩σ)
    , (λ ((_ , ⊩A) , (_ , ⊩B) , A≡B) →
           _
         , ⊩A
         , Irr.irrelevance _ _ ⊩B
         , (λ _ ⊩σ → ⊩≡→⊩≡/ (⊩A .unwrap _ _ .proj₁) (A≡B (_ , _ , ⊩σ))))

opaque

  -- A variant of ⊩ᵛ≡⇔.

  ⊩ᵛ≡⇔′ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B ⇔
    (Γ ⊩ᵛ⟨ l ⟩ A ×
     Γ ⊩ᵛ⟨ l ⟩ B ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
      Δ ⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ]))
  ⊩ᵛ≡⇔′ {n} {Γ} {l} {A} {B} =
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B                 ⇔⟨ ⊩ᵛ≡⇔ ⟩

    Γ ⊩ᵛ⟨ l ⟩ A ×
    Γ ⊩ᵛ⟨ l ⟩ B ×
    (∀ {m Δ} {σ : Subst m n} →
     Δ ⊩ˢ σ ∷ Γ →
     Δ ⊩⟨ l ⟩ A [ σ ] ≡ B [ σ ])    ⇔⟨ (Σ-cong-⇔ λ ⊩A → Σ-cong-⇔ λ _ →
                                          (λ hyp {m = _} {Δ = _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
      A [ σ₁ ]                                 ≡⟨ ⊩ᵛ⇔ .proj₁ ⊩A .proj₂ σ₁≡σ₂ ⟩⊩
      A [ σ₂ ]                                 ≡⟨ hyp (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₂) ⟩⊩∎
      B [ σ₂ ]                                 ∎)
                                        , (λ hyp {_ _ _} ⊩σ →
                                             hyp (refl-⊩ˢ≡∷ ⊩σ))) ⟩
    Γ ⊩ᵛ⟨ l ⟩ A ×
    Γ ⊩ᵛ⟨ l ⟩ B ×
    (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
     Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
     Δ ⊩⟨ l ⟩ A [ σ₁ ] ≡ B [ σ₂ ])  □⇔

opaque
  unfolding _⊩ᵛ⟨_⟩_∷_ _⊩ᵛ⟨_⟩_≡_∷_ _⊩⟨_⟩_≡_∷_ _⊩ˢ_∷_

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷⇔ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ⇔
    (Γ ⊩ᵛ⟨ l ⟩ t ∷ A ×
     Γ ⊩ᵛ⟨ l ⟩ u ∷ A ×
     (∀ {m Δ} {σ : Subst m n} →
      Δ ⊩ˢ σ ∷ Γ →
      Δ ⊩⟨ l ⟩ t [ σ ] ≡ u [ σ ] ∷ A [ σ ]))
  ⊩ᵛ≡∷⇔ {u} =
      (λ (_ , modelsTermEq ⊩A ⊩t ⊩u t≡u) →
           (_ , ⊩A , ⊩t)
         , (_ , ⊩A , ⊩u)
         , λ (_ , ⊢Δ , ⊩σ) →
             case Irr.irrelevanceSubst _ _ _ _ ⊩σ of λ
               ⊩σ →
             let ⊩A[σ] , _ = ⊩A .unwrap ⊢Δ ⊩σ in
               ⊩A[σ]
             , ⊩t ⊢Δ ⊩σ .proj₁
             , ⊩u ⊢Δ ⊩σ .proj₁
             , t≡u ⊢Δ ⊩σ)
    , (λ ((_ , ⊩A , ⊩t) , (_ , ⊩A′ , ⊩u) , hyp) →
           _
         , modelsTermEq ⊩A ⊩t
             (Irr.irrelevanceTerm {t = u} _ _ ⊩A′ ⊩A ⊩u)
             (λ _ ⊩σ →
                ⊩≡∷→⊩≡∷/ (⊩A .unwrap _ _ .proj₁) (hyp (_ , _ , ⊩σ))))

opaque

  -- A variant of ⊩ᵛ≡∷⇔.

  ⊩ᵛ≡∷⇔′ :
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A ⇔
    (Γ ⊩ᵛ⟨ l ⟩ t ∷ A ×
     Γ ⊩ᵛ⟨ l ⟩ u ∷ A ×
     (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
      Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
      Δ ⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ]))
  ⊩ᵛ≡∷⇔′ {n} {Γ} {l} {t} {u} {A} =
    Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A                        ⇔⟨ ⊩ᵛ≡∷⇔ ⟩

    Γ ⊩ᵛ⟨ l ⟩ t ∷ A ×
    Γ ⊩ᵛ⟨ l ⟩ u ∷ A ×
    (∀ {m Δ} {σ : Subst m n} →
     Δ ⊩ˢ σ ∷ Γ →
     Δ ⊩⟨ l ⟩ t [ σ ] ≡ u [ σ ] ∷ A [ σ ])     ⇔⟨ (Σ-cong-⇔ λ ⊩t → Σ-cong-⇔ λ _ →
                                                     (λ hyp {m = _} {Δ = _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
      t [ σ₁ ]                                            ≡⟨ ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ σ₁≡σ₂ ⟩⊩∷
      t [ σ₂ ]                                            ≡⟨ conv-⊩≡∷
                                                               (⊩ᵛ⇔ .proj₁ (wf-⊩ᵛ∷ ⊩t) .proj₂ (sym-⊩ˢ≡∷ σ₁≡σ₂))
                                                               (hyp (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₂)) ⟩⊩∷∎
      u [ σ₂ ]                                            ∎)
                                                   , (λ hyp {_ _ _} ⊩σ →
                                                        hyp (refl-⊩ˢ≡∷ ⊩σ))) ⟩
    Γ ⊩ᵛ⟨ l ⟩ t ∷ A ×
    Γ ⊩ᵛ⟨ l ⟩ u ∷ A ×
    (∀ {m Δ} {σ₁ σ₂ : Subst m n} →
     Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
     Δ ⊩⟨ l ⟩ t [ σ₁ ] ≡ u [ σ₂ ] ∷ A [ σ₁ ])  □⇔

opaque
  unfolding _⊩ˢ_≡_∷_

  -- A characterisation lemma for _⊩ˢ_≡_∷_.

  ⊩ˢ≡∷ε⇔ : Δ ⊩ˢ σ₁ ≡ σ₂ ∷ ε ⇔ ⊢ Δ
  ⊩ˢ≡∷ε⇔ =
      (λ (_ , ⊢Δ , _) → ⊢Δ)
    , (λ ⊢Δ → ε , ⊢Δ , _)

opaque
  unfolding _⊩ˢ_≡_∷_ _⊩ᵛ⟨_⟩_ _⊩⟨_⟩_≡_∷_

  -- Another characterisation lemma for _⊩ˢ_≡_∷_.

  ⊩ˢ≡∷∙⇔′ :
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A ⇔
    ((∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A) ×
     (∃ λ l → Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
     Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ)
  ⊩ˢ≡∷∙⇔′ =
      (λ { (_ ∙ ⊩A , _ , (⊩tail₁ , ⊩head₁) , (⊩tail₂ , ⊩head₂) ,
            (tail₁≡tail₂ , head₁≡head₂)) →
           let ⊩A[tail₁] , A[tail₁]≡ = ⊩A .unwrap _ ⊩tail₁ in
             (_ , _ , ⊩A)
           , ( _ , ⊩A[tail₁] , ⊩head₁
             , convTerm₂ ⊩A[tail₁] (⊩A .unwrap _ ⊩tail₂ .proj₁)
                 (A[tail₁]≡ ⊩tail₂ tail₁≡tail₂) ⊩head₂
             , head₁≡head₂
             )
           , (_ , _ , ⊩tail₁ , ⊩tail₂ , tail₁≡tail₂) })
    , (λ ((_ , _ , ⊩A) ,
          (_ , ⊩A[tail₁] , ⊩head₁ , ⊩head₂ , head₁≡head₂) ,
          (_ , ⊢Δ , ⊩tail₁ , ⊩tail₂ , tail₁≡tail₂)) →
        case Irr.irrelevanceSubst _ _ _ _ ⊩tail₁ of λ
          ⊩tail₁′ →
        case Irr.irrelevanceSubst _ _ _ _ ⊩tail₂ of λ
          ⊩tail₂′ →
        case Irr.irrelevanceSubstEq _ _ _ _ ⊩tail₁ ⊩tail₁′
               tail₁≡tail₂ of λ
          tail₁≡tail₂ →
        let ⊩A[tail₁]′ , _ = ⊩A .unwrap _ ⊩tail₁′ in
          _ ∙ ⊩A , ⊢Δ
        , ( ⊩tail₁′
          , irrelevanceTerm ⊩A[tail₁] ⊩A[tail₁]′ ⊩head₁
          )
        , ( ⊩tail₂′
          , convTerm₁ ⊩A[tail₁] (⊩A .unwrap _ ⊩tail₂′ .proj₁)
              (irrelevanceEq ⊩A[tail₁]′ ⊩A[tail₁]
                 (⊩A .unwrap _ ⊩tail₁′ .proj₂ ⊩tail₂′ tail₁≡tail₂))
              ⊩head₂
          )
        , ( tail₁≡tail₂
          , irrelevanceEqTerm ⊩A[tail₁] ⊩A[tail₁]′ head₁≡head₂
          ))

opaque

  -- A variant of the previous lemma.

  ⊩ˢ≡∷∙⇔ :
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A ⇔
    ((∃ λ l →
      (Γ ⊩ᵛ⟨ l ⟩ A) ×
      Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
     Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ)
  ⊩ˢ≡∷∙⇔ {Δ} {σ₁} {σ₂} {Γ} {A} =
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ ∙ A                                                  ⇔⟨ ⊩ˢ≡∷∙⇔′ ⟩

    (∃ λ l → Γ ⊩ᵛ⟨ l ⟩ A) ×
    (∃ λ l → Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                                            ⇔⟨ (λ ((l₁ , ⊩A) , (_ , head≡head) , tail≡tail) →
                                                                                  ( l₁ , ⊩A
                                                                                  , level-⊩≡∷ (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A (wf-⊩ˢ≡∷ tail≡tail .proj₁))
                                                                                      head≡head
                                                                                  )
                                                                                , tail≡tail)
                                                                           , (λ ((l , ⊩A , head≡head) , tail≡tail) →
                                                                                (l , ⊩A) , (l , head≡head) , tail≡tail)
                                                                           ⟩
    (∃ λ l → (Γ ⊩ᵛ⟨ l ⟩ A) × Δ ⊩⟨ l ⟩ head σ₁ ≡ head σ₂ ∷ A [ tail σ₁ ]) ×
    Δ ⊩ˢ tail σ₁ ≡ tail σ₂ ∷ Γ                                            □⇔

------------------------------------------------------------------------
-- A lemma related to variables

opaque

  -- Well-typed variables in valid contexts are valid.

  varᵛ :
    x ∷ A ∈ Γ →
    ⊩ᵛ Γ →
    ∃ λ l → Γ ⊩ᵛ⟨ l ⟩ var x ∷ A
  varᵛ (here {A}) ⊩Γ∙A =
    case wf-⊩ᵛ-∙ ⊩Γ∙A of λ
      (l , ⊩A) →
    case wk1-⊩ᵛ ⊩A ⊩A of λ
      ⊩wk1-A →
      l
    , ⊩ᵛ∷⇔ .proj₂
        ( ⊩wk1-A
        , λ σ₁≡σ₂ →
            case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
              ((_ , _ , σ₁₀≡σ₂₀) , _) →
            level-⊩≡∷
              (⊩ᵛ→⊩ˢ∷→⊩[] ⊩wk1-A (wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₁))
              (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ wk1-tail A)
                 σ₁₀≡σ₂₀)
        )
  varᵛ (there x∈Γ) ⊩Γ∙B =
    case wf-⊩ᵛ-∙ ⊩Γ∙B .proj₂ of λ
      ⊩B →
    Σ.map idᶠ (wk1-⊩ᵛ∷ ⊩B) (varᵛ x∈Γ (wf-⊩ᵛ ⊩B))

------------------------------------------------------------------------
-- Some lemmas related to _⊩ˢ_∷_ and _⊩ˢ_≡_∷_

opaque
  unfolding _⊩ˢ_∷_

  -- A lemma related to idSubst.

  ⊩ˢ∷-idSubst :
    ⊩ᵛ Γ →
    Γ ⊩ˢ idSubst ∷ Γ
  ⊩ˢ∷-idSubst ⊩Γ =
    _ , _ , idSubstS ⊩Γ

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩⟨_⟩_≡_∷_ _⊩ˢ_≡_∷_

  -- A lemma related to sgSubst.

  ⊩ˢ≡∷-sgSubst :
    Γ ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A →
    Γ ⊩ˢ sgSubst t ≡ sgSubst u ∷ Γ ∙ A
  ⊩ˢ≡∷-sgSubst (_ , ⊩ᵛA) (⊩A , ⊩t , ⊩u , t≡u) =
      (_ ∙ ⊩ᵛA) , _ , sgSubstS ⊩ᵛA ⊩A ⊩t , sgSubstS ⊩ᵛA ⊩A ⊩u
    , sgSubstSEq t≡u

opaque

  -- Another lemma related to sgSubst.

  ⊩ˢ∷-sgSubst :
    Γ ⊩ᵛ⟨ l′ ⟩ A →
    Γ ⊩⟨ l ⟩ t ∷ A →
    Γ ⊩ˢ sgSubst t ∷ Γ ∙ A
  ⊩ˢ∷-sgSubst ⊩A ⊩t =
    wf-⊩ˢ≡∷ (⊩ˢ≡∷-sgSubst ⊩A (refl-⊩≡∷ ⊩t)) .proj₁

opaque
  unfolding _⊩ˢ_≡_∷_

  -- A lemma related to wk1Subst.

  ⊩ˢ≡∷-wk1Subst :
    Δ ⊢ A →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A ⊩ˢ wk1Subst σ₁ ≡ wk1Subst σ₂ ∷ Γ
  ⊩ˢ≡∷-wk1Subst ⊢A (_ , _ , _ , ⊩σ₂ , σ₁≡σ₂) =
    _ , _ , _ , wk1SubstS _ _ _ ⊩σ₂ , wk1SubstSEq _ _ ⊢A _ σ₁≡σ₂

opaque

  -- Another lemma related to wk1Subst.

  ⊩ˢ∷-wk1Subst :
    Δ ⊢ A →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ∙ A ⊩ˢ wk1Subst σ ∷ Γ
  ⊩ˢ∷-wk1Subst ⊢A ⊩σ =
    wf-⊩ˢ≡∷ (⊩ˢ≡∷-wk1Subst ⊢A (refl-⊩ˢ≡∷ ⊩σ)) .proj₁

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ˢ_∷_

  -- A lemma related to liftSubst.

  ⊩ˢ∷-liftSubst :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ∙ A [ σ ] ⊩ˢ liftSubst σ ∷ Γ ∙ A
  ⊩ˢ∷-liftSubst (_ , ⊩A) (_ , ⊢Δ , ⊩σ) =
    _ ∙ ⊩A , _ , liftSubstS _ ⊢Δ ⊩A (Irr.irrelevanceSubst _ _ _ _ ⊩σ)

opaque

  -- Another lemma related to liftSubst.

  ⊩ˢ≡∷-liftSubst′ :
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A₁ [ σ₁ ] ⊩ˢ liftSubst σ₁ ≡ liftSubst σ₂ ∷ Γ ∙ A₂
  ⊩ˢ≡∷-liftSubst′ {A₁} {A₂} {σ₁} A₁≡A₂ σ₁≡σ₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , _) →
    case escape $ ⊩ᵛ→⊩ˢ∷→⊩[] ⊩A₁ ⊩σ₁ of λ
      ⊢A₁[σ₁] →
    ⊩ˢ≡∷∙⇔′ .proj₂
      ( (_ , ⊩A₂)
      , ( _
        , conv-⊩≡∷
            (wk1 A₁ [ σ₁ ⇑ ]     ≡⟨ wk1-tail A₁ ⟩⊩≡
             A₁ [ wk1Subst σ₁ ]  ≡⟨ ⊩ᵛ≡⇔′ .proj₁ A₁≡A₂ .proj₂ .proj₂ $ refl-⊩ˢ≡∷ $
                                    ⊩ˢ∷-wk1Subst ⊢A₁[σ₁] ⊩σ₁ ⟩⊩∎
             A₂ [ wk1Subst σ₁ ]  ∎)
            (refl-⊩≡∷ $
             ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ (varᵛ here (⊩ᵛ-∙-intro ⊩A₁) .proj₂) $
             ⊩ˢ∷-liftSubst ⊩A₁ ⊩σ₁)
        )
      , ⊩ˢ≡∷-wk1Subst ⊢A₁[σ₁] σ₁≡σ₂
      )

opaque

  -- A variant of ⊩ˢ≡∷-liftSubst′.

  ⊩ˢ≡∷-liftSubst :
    Γ ⊩ᵛ⟨ l ⟩ A →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A [ σ₁ ] ⊩ˢ liftSubst σ₁ ≡ liftSubst σ₂ ∷ Γ ∙ A
  ⊩ˢ≡∷-liftSubst ⊩A =
    ⊩ˢ≡∷-liftSubst′ (refl-⊩ᵛ≡ ⊩A)

opaque

  -- A variant of ⊩ˢ∷-liftSubst.

  ⊩ˢ∷-liftSubst′ :
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ∙ A₁ [ σ ] ⊩ˢ liftSubst σ ∷ Γ ∙ A₂
  ⊩ˢ∷-liftSubst′ A₁≡A₂ ⊩σ =
    wf-⊩ˢ≡∷ (⊩ˢ≡∷-liftSubst′ A₁≡A₂ (refl-⊩ˢ≡∷ ⊩σ)) .proj₁

opaque
  unfolding _⊩ˢ_≡_∷_

  -- A lemma related to _•ₛ_.

  ⊩ˢ≡∷-•ₛ :
    ⊢ Η →
    ρ ∷ Η ⊇ Δ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Η ⊩ˢ ρ •ₛ σ₁ ≡ ρ •ₛ σ₂ ∷ Γ
  ⊩ˢ≡∷-•ₛ ⊢Η ρ⊇ (_ , _ , _ , ⊩σ₂ , σ₁≡σ₂) =
    _ , _ , _ , wkSubstS _ _ ⊢Η ρ⊇ ⊩σ₂ , wkSubstSEq _ _ ⊢Η ρ⊇ _ σ₁≡σ₂

opaque

  -- Another lemma related to _•ₛ_.

  ⊩ˢ∷-•ₛ :
    ⊢ Η →
    ρ ∷ Η ⊇ Δ →
    Δ ⊩ˢ σ ∷ Γ →
    Η ⊩ˢ ρ •ₛ σ ∷ Γ
  ⊩ˢ∷-•ₛ ⊢Η ρ⊇ ⊩σ =
    wf-⊩ˢ≡∷ (⊩ˢ≡∷-•ₛ ⊢Η ρ⊇ (refl-⊩ˢ≡∷ ⊩σ)) .proj₁

opaque

  -- A lemma related to _ₛ•_.

  ⊩ˢ≡∷-ₛ• :
    ρ ∷ Δ ⊇ Γ → ⊩ᵛ Γ → Η ⊩ˢ σ₁ ≡ σ₂ ∷ Δ →
    Η ⊩ˢ σ₁ ₛ• ρ ≡ σ₂ ₛ• ρ ∷ Γ
  ⊩ˢ≡∷-ₛ• TW.id _ σ₁≡σ₂ =
    σ₁≡σ₂
  ⊩ˢ≡∷-ₛ• (TW.step ρ⊇) ⊩Γ σ₁≡σ₂ =
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
      ((_ , ⊩A , head≡head) , tail≡tail) →
    ⊩ˢ≡∷-ₛ• ρ⊇ ⊩Γ tail≡tail
  ⊩ˢ≡∷-ₛ• (TW.lift {A} ρ⊇) ⊩Γ∙A σ₁≡σ₂ =
    case wf-⊩ᵛ-∙ ⊩Γ∙A of λ
      (_ , ⊩A) →
    case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
      ((_ , _ , head≡head) , tail≡tail) →
    ⊩ˢ≡∷∙⇔′ .proj₂
      ( (_ , ⊩A)
      , (_ , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (subst-wk A) head≡head)
      , ⊩ˢ≡∷-ₛ• ρ⊇ (wf-⊩ᵛ ⊩A) tail≡tail
      )

opaque

  -- Another lemma related to _ₛ•_.

  ⊩ˢ∷-ₛ• : ρ ∷ Δ ⊇ Γ → ⊩ᵛ Γ → Η ⊩ˢ σ ∷ Δ → Η ⊩ˢ σ ₛ• ρ ∷ Γ
  ⊩ˢ∷-ₛ• ρ⊇ ⊩Γ ⊩σ =
    wf-⊩ˢ≡∷ (⊩ˢ≡∷-ₛ• ρ⊇ ⊩Γ (refl-⊩ˢ≡∷ ⊩σ)) .proj₁

------------------------------------------------------------------------
-- More weakening lemmas

opaque

  -- A weakening lemma for _⊩ᵛ⟨_⟩_.

  wk-⊩ᵛ : ρ ∷ Δ ⊇ Γ → ⊩ᵛ Δ → Γ ⊩ᵛ⟨ l ⟩ A → Δ ⊩ᵛ⟨ l ⟩ wk ρ A
  wk-⊩ᵛ {ρ} {A} ρ⊇ ⊩Δ ⊩A =
    ⊩ᵛ⇔ .proj₂
      ( ⊩Δ
      , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
          wk ρ A [ σ₁ ]  ≡⟨ subst-wk A ⟩⊩≡
          A [ σ₁ ₛ• ρ ]  ≡⟨ ⊩ᵛ≡⇔′ .proj₁ (refl-⊩ᵛ≡ ⊩A) .proj₂ .proj₂ $
                            ⊩ˢ≡∷-ₛ• ρ⊇ (wf-⊩ᵛ ⊩A) σ₁≡σ₂ ⟩⊩∎≡
          A [ σ₂ ₛ• ρ ]  ≡˘⟨ subst-wk A ⟩
          wk ρ A [ σ₂ ]  ∎
      )

opaque

  -- A weakening lemma for _⊩ᵛ⟨_⟩_∷_.

  wk-⊩ᵛ∷ :
    ρ ∷ Δ ⊇ Γ → ⊩ᵛ Δ → Γ ⊩ᵛ⟨ l ⟩ t ∷ A → Δ ⊩ᵛ⟨ l ⟩ wk ρ t ∷ wk ρ A
  wk-⊩ᵛ∷ {ρ} {t} {A} ρ⊇ ⊩Δ ⊩t =
    case wf-⊩ᵛ∷ ⊩t of λ
      ⊩A →
    ⊩ᵛ∷⇔ .proj₂
      ( wk-⊩ᵛ ρ⊇ ⊩Δ ⊩A
      , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
          wk ρ t [ σ₁ ] ∷ wk ρ A [ σ₁ ]  ≡⟨ subst-wk t ⟩⊩∷∷≡
                                          ⟨ subst-wk A ⟩⊩∷≡
          t [ σ₁ ₛ• ρ ] ∷ A [ σ₁ ₛ• ρ ]  ≡⟨ ⊩ᵛ≡∷⇔′ .proj₁ (refl-⊩ᵛ≡∷ ⊩t) .proj₂ .proj₂ $
                                            ⊩ˢ≡∷-ₛ• ρ⊇ (wf-⊩ᵛ ⊩A) σ₁≡σ₂ ⟩⊩∷∎∷≡
          t [ σ₂ ₛ• ρ ]                  ≡˘⟨ subst-wk t ⟩
          wk ρ t [ σ₂ ]                  ∎
      )

opaque

  -- A weakening lemma for _⊩ᵛ⟨_⟩_≡_.

  wk-⊩ᵛ≡ :
    ρ ∷ Δ ⊇ Γ → ⊩ᵛ Δ → Γ ⊩ᵛ⟨ l ⟩ A ≡ B → Δ ⊩ᵛ⟨ l ⟩ wk ρ A ≡ wk ρ B
  wk-⊩ᵛ≡ {ρ} {A} {B} ρ⊇ ⊩Δ A≡B =
    case wf-⊩ᵛ≡ A≡B of λ
      (⊩A , ⊩B) →
    ⊩ᵛ≡⇔ .proj₂
      ( wk-⊩ᵛ ρ⊇ ⊩Δ ⊩A
      , wk-⊩ᵛ ρ⊇ ⊩Δ ⊩B
      , λ {_ _} {σ = σ} ⊩σ →
          wk ρ A [ σ ]  ≡⟨ subst-wk A ⟩⊩≡
          A [ σ ₛ• ρ ]  ≡⟨ ⊩ᵛ≡⇔ .proj₁ A≡B .proj₂ .proj₂ $
                           ⊩ˢ∷-ₛ• ρ⊇ (wf-⊩ᵛ ⊩A) ⊩σ ⟩⊩∎≡
          B [ σ ₛ• ρ ]  ≡˘⟨ subst-wk B ⟩
          wk ρ B [ σ ]  ∎
      )

opaque

  -- A weakening lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  wk-⊩ᵛ≡∷ :
    ρ ∷ Δ ⊇ Γ → ⊩ᵛ Δ → Γ ⊩ᵛ⟨ l ⟩ t ≡ u ∷ A →
    Δ ⊩ᵛ⟨ l ⟩ wk ρ t ≡ wk ρ u ∷ wk ρ A
  wk-⊩ᵛ≡∷ {ρ} {t} {u} {A} ρ⊇ ⊩Δ t≡u =
    case wf-⊩ᵛ≡∷ t≡u of λ
      (⊩t , ⊩u) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( wk-⊩ᵛ∷ ρ⊇ ⊩Δ ⊩t
      , wk-⊩ᵛ∷ ρ⊇ ⊩Δ ⊩u
      , λ {_ _} {σ = σ} ⊩σ →
          wk ρ t [ σ ] ∷ wk ρ A [ σ ]  ≡⟨ subst-wk t ⟩⊩∷∷≡
                                        ⟨ subst-wk A ⟩⊩∷≡
          t [ σ ₛ• ρ ] ∷ A [ σ ₛ• ρ ]  ≡⟨ ⊩ᵛ≡∷⇔ .proj₁ t≡u .proj₂ .proj₂ $
                                          ⊩ˢ∷-ₛ• ρ⊇ (wf-⊩ᵛ $ wf-⊩ᵛ∷ ⊩t) ⊩σ ⟩⊩∷∎∷≡
          u [ σ ₛ• ρ ]                 ≡˘⟨ subst-wk u ⟩
          wk ρ u [ σ ]                 ∎
      )

------------------------------------------------------------------------
-- Neutral types and terms

opaque

  -- Neutral types that satisfy certain properties are reducible.

  neutral-⊩ :
    Neutral A →
    Γ ⊢ A →
    Γ ⊢ A ≅ A →
    Γ ⊩⟨ l ⟩ A
  neutral-⊩ = neu

opaque
  unfolding _⊩⟨_⟩_∷_

  -- Neutral terms that satisfy certain properties are reducible.

  neutral-⊩∷ :
    Γ ⊩⟨ l ⟩ A →
    Neutral t →
    Γ ⊢ t ∷ A →
    Γ ⊢ t ~ t ∷ A →
    Γ ⊩⟨ l ⟩ t ∷ A
  neutral-⊩∷ ⊩A t-ne ⊢t t~t =
    ⊩A , neuTerm ⊩A t-ne ⊢t t~t

opaque
  unfolding _⊩⟨_⟩_≡_

  -- Reducible equality holds between neutral types that satisfy
  -- certain properties.

  neutral-⊩≡ :
    Γ ⊩⟨ l ⟩ A →
    Γ ⊩⟨ l ⟩ B →
    Neutral A →
    Neutral B →
    Γ ⊢ A ≅ B →
    Γ ⊩⟨ l ⟩ A ≡ B
  neutral-⊩≡ ⊩A ⊩B A-ne B-ne A≅B =
    ⊩A , ⊩B , neuEq ⊩A A-ne B-ne (escape ⊩A) (escape ⊩B) A≅B

opaque
  unfolding _⊩⟨_⟩_≡_∷_

  -- Reducible equality holds between neutral terms that satisfy
  -- certain properties.

  neutral-⊩≡∷ :
    Γ ⊩⟨ l ⟩ A →
    Neutral t →
    Neutral u →
    Γ ⊢ t ∷ A →
    Γ ⊢ u ∷ A →
    Γ ⊢ t ~ u ∷ A →
    Γ ⊩⟨ l ⟩ t ≡ u ∷ A
  neutral-⊩≡∷ ⊩A t-ne u-ne ⊢t ⊢u t~u =
      ⊩A
    , neuTerm ⊩A t-ne ⊢t (~-trans t~u (~-sym t~u))
    , neuTerm ⊩A u-ne ⊢u (~-trans (~-sym t~u) t~u)
    , neuEqTerm ⊩A t-ne u-ne ⊢t ⊢u t~u

------------------------------------------------------------------------
-- Substitution lemmas

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_ _⊩ᵛ⟨_⟩_≡_∷_

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B ≡ C →
    Γ ⊩ᵛ⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ B [ t ]₀ ≡ C [ u ]₀
  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀
    {C} {t} {u}
    (⊩Γ ∙ _ , ⊩B , ⊩C , B≡C) (_ , modelsTermEq ⊩A ⊩t ⊩u t≡u) =
    case Irr.irrelevance _ _ ⊩A of λ
      ⊩A′ →
    case Irr.irrelevance _ _ ⊩B of λ
      ⊩B′ →
    case Irr.irrelevance _ _ ⊩C of λ
      ⊩C →
    case (λ {k Δ σ} →
            Irr.irrelevanceTerm {t = t} _ _ ⊩A ⊩A′ ⊩t
              {k = k} {Δ = Δ} {σ = σ}) of λ
      ⊩t →
    case (λ {k Δ σ} →
            Irr.irrelevanceTerm {t = u} _ _ ⊩A ⊩A′ ⊩u
              {k = k} {Δ = Δ} {σ = σ}) of λ
      ⊩u →
      ⊩Γ
    , substS _ ⊩A′ ⊩B′ ⊩t
    , substS _ ⊩A′ ⊩C ⊩u
    , substSEq _ ⊩A′ ⊩A′ (reflᵛ _ ⊩A′) ⊩B′ ⊩C
        (Irr.irrelevanceEq {B = C} _ _ ⊩B ⊩B′ B≡C) ⊩t ⊩u
        (Irr.irrelevanceEqTerm {t = t} {u = u} _ _ ⊩A ⊩A′ t≡u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l′ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ B [ t ]₀
  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]₀ ⊩B ⊩t =
    wf-⊩ᵛ≡ (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ (refl-⊩ᵛ≡ ⊩B) (refl-⊩ᵛ≡∷ ⊩t)) .proj₁

opaque
  unfolding _⊩ᵛ⟨_⟩_∷_

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₀∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l ⟩ t [ u ]₀ ∷ B [ u ]₀
  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₀∷ {t} (_ , ⊩B , ⊩t) (_ , ⊩A , ⊩u) =
    case Irr.irrelevance _ _ ⊩B of λ
      ⊩B′ →
      _
    , substS _ ⊩A ⊩B′ ⊩u
    , substSTerm {f = t} _ ⊩A ⊩B′
        (Irr.irrelevanceTerm {t = t} _ _ ⊩B ⊩B′ ⊩t) ⊩u

opaque
  unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_ _⊩ᵛ⟨_⟩_≡_∷_

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ →
    Γ ⊩ᵛ⟨ l″ ⟩ t₁ ≡ t₂ ∷ A →
    Γ ⊩ᵛ⟨ l‴ ⟩ u₁ ≡ u₂ ∷ B [ t₁ ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ C₁ [ t₁ , u₁ ]₁₀ ≡ C₂ [ t₂ , u₂ ]₁₀
  ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀
    {C₂} {t₁} {t₂} {u₁} {u₂} C₁≡C₂′@(_ , ⊩C₁ , ⊩C₂ , C₁≡C₂)
    (⊩Γ , modelsTermEq ⊩A ⊩t₁ ⊩t₂ t₁≡t₂)
    (_ , modelsTermEq ⊩B[t₁] ⊩u₁ ⊩u₂ u₁≡u₂) =
    case Irr.irrelevance _ (_ ∙ ⊩A)
           (wf-∙-⊩ᵛ (wf-⊩ᵛ≡ C₁≡C₂′ .proj₁) .proj₂ .proj₂) of λ
      ⊩B →
    let ⊩B[t₁]′ = substS {t = t₁} _ ⊩A ⊩B ⊩t₁ in
    case substS {t = t₂} _ ⊩A ⊩B ⊩t₂ of λ
      ⊩B[t₂] →
    case (λ {k Δ σ} →
            Irr.irrelevanceTerm {t = u₁} _ _ ⊩B[t₁] ⊩B[t₁]′ ⊩u₁
              {k = k} {Δ = Δ} {σ = σ}) of λ
      ⊩u₁′ →
    case (λ {k Δ σ} →
              (convᵛ {t = u₂} _ ⊩B[t₁]′ ⊩B[t₂]
                 (substSEq _ ⊩A ⊩A (reflᵛ _ ⊩A) ⊩B ⊩B (reflᵛ _ ⊩B)
                    ⊩t₁ ⊩t₂ t₁≡t₂)
                 (Irr.irrelevanceTerm {t = u₂} _ _ ⊩B[t₁] ⊩B[t₁]′ ⊩u₂))
              {k = k} {Δ = Δ} {σ = σ}) of λ
      ⊩u₂′ →
    case Irr.irrelevance _ (_ ∙ ⊩B) ⊩C₁ of λ
      ⊩C₁′ →
    case Irr.irrelevance _ (_ ∙ ⊩B) ⊩C₂ of λ
      ⊩C₂′ →
    case substD {u = u₁} ⊩t₁ ⊩B[t₁]′ ⊩u₁′ ⊩C₁′ of λ
      ⊩C₁[t₁,u₁] →
      ⊩Γ
    , ⊩C₁[t₁,u₁]
    , substD ⊩t₂ ⊩B[t₂] ⊩u₂′ ⊩C₂′
    , substDEq
        {⊩t₁ = ⊩t₁} {⊩B₁[t₁] = ⊩B[t₁]′} {⊩u₁ = ⊩u₁′} {⊩C₁ = ⊩C₁′}
        (reflᵛ _ ⊩A) (reflᵛ _ ⊩B) ⊩t₂
        (Irr.irrelevanceEqTerm {t = t₁} {u = t₂} _ _ ⊩A ⊩A t₁≡t₂) ⊩B[t₂]
        ⊩u₂′
        (Irr.irrelevanceEqTerm {t = u₁} {u = u₂} _ _ ⊩B[t₁] ⊩B[t₁]′
           u₁≡u₂)
        ⊩C₁[t₁,u₁] ⊩C₂′ (Irr.irrelevanceEq {B = C₂} _ _ ⊩C₁ ⊩C₁′ C₁≡C₂)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C →
    Γ ⊩ᵛ⟨ l″ ⟩ t ∷ A →
    Γ ⊩ᵛ⟨ l‴ ⟩ u ∷ B [ t ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ C [ t , u ]₁₀
  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀ ⊩C ⊩t ⊩u =
    proj₁ $ wf-⊩ᵛ≡ $
    ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀ (refl-⊩ᵛ≡ ⊩C) (refl-⊩ᵛ≡∷ ⊩t)
      (refl-⊩ᵛ≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t ∷ C →
    Γ ⊩ᵛ⟨ l′ ⟩ u ∷ A →
    Γ ⊩ᵛ⟨ l″ ⟩ v ∷ B [ u ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ t [ u , v ]₁₀ ∷ C [ u , v ]₁₀
  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ {B} {t} {C} ⊩t ⊩u ⊩v =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ∷ ⊩t) of λ
      (_ , ⊩B) →
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀ (wf-⊩ᵛ∷ ⊩t) ⊩u ⊩v
      , λ σ₁≡σ₂ →
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (PE.sym $ [,]-[]-fusion t)
            (PE.sym $ [,]-[]-fusion t) (PE.sym $ [,]-[]-fusion C) $
          ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( (_ , ⊩B)
            , ( _
              , (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
                   (PE.sym $ substConsId B) $
                 ⊩ᵛ∷⇔ .proj₁ ⊩v .proj₂ σ₁≡σ₂)
              )
            , ⊩ˢ≡∷∙⇔′ .proj₂
                ( wf-∙-⊩ᵛ ⊩B
                , (_ , ⊩ᵛ∷⇔ .proj₁ ⊩u .proj₂ σ₁≡σ₂)
                , σ₁≡σ₂
                )
            )
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ C →
    Γ ⊩ᵛ⟨ l″ ⟩ u₁ ≡ u₂ ∷ A →
    Γ ⊩ᵛ⟨ l‴ ⟩ v₁ ≡ v₂ ∷ B [ u₁ ]₀ →
    Γ ⊩ᵛ⟨ l ⟩ t₁ [ u₁ , v₁ ]₁₀ ≡ t₂ [ u₂ , v₂ ]₁₀ ∷ C [ u₁ , v₁ ]₁₀
  ⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀∷ {B} {t₁} {t₂} {C} t₁≡t₂ u₁≡u₂ v₁≡v₂ =
    case wf-⊩ᵛ≡∷ t₁≡t₂ of λ
      (⊩t₁ , ⊩t₂) →
    case wf-⊩ᵛ∷ ⊩t₁ of λ
      ⊩C →
    case wf-∙-⊩ᵛ ⊩C of λ
      (_ , ⊩B) →
    case wf-⊩ᵛ≡∷ u₁≡u₂ of λ
      (⊩u₁ , ⊩u₂) →
    case wf-⊩ᵛ≡∷ v₁≡v₂ of λ
      (⊩v₁ , ⊩v₂) →
    case conv-⊩ᵛ∷ (⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ[]₀≡[]₀ (refl-⊩ᵛ≡ ⊩B) u₁≡u₂) ⊩v₂ of λ
      ⊩v₂ →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ ⊩t₁ ⊩u₁ ⊩v₁
      , conv-⊩ᵛ∷
          (sym-⊩ᵛ≡ $
           ⊩ᵛ≡→⊩ᵛ≡∷→⊩ᵛ≡∷→⊩ᵛ[]₁₀≡[]₁₀ (refl-⊩ᵛ≡ ⊩C) u₁≡u₂ v₁≡v₂)
          (⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]₁₀∷ ⊩t₂ ⊩u₂ ⊩v₂)
      , λ ⊩σ →
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (PE.sym $ [,]-[]-fusion t₁)
            (PE.sym $ [,]-[]-fusion t₂) (PE.sym $ [,]-[]-fusion C) $
          ⊩ᵛ≡∷⇔′ .proj₁ t₁≡t₂ .proj₂ .proj₂ $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( (_ , ⊩B)
            , ( _
              , (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _)
                   (PE.sym $ substConsId B) $
                 ⊩ᵛ≡∷⇔ .proj₁ v₁≡v₂ .proj₂ .proj₂ ⊩σ)
              )
            , ⊩ˢ≡∷∙⇔′ .proj₂
                ( wf-∙-⊩ᵛ ⊩B
                , (_ , ⊩ᵛ≡∷⇔ .proj₁ u₁≡u₂ .proj₂ .proj₂ ⊩σ)
                , refl-⊩ˢ≡∷ ⊩σ
                )
            )

      )

opaque
  unfolding _⊩ᵛ⟨_⟩_≡_ _⊩ᵛ⟨_⟩_∷_

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑² :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ D ≡ E →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l′ ⟩ t ∷ wk2 A →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l ⟩ D [ t ]↑² ≡ E [ t ]↑²
  ⊩ᵛ≡→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑²
    {t} (_ ∙ ⊩A , ⊩D , ⊩E , D≡E) (_ ∙ ⊩B′ ∙ ⊩C′ , ⊩A′ , ⊩t′) =
    case (λ {k Δ σ} →
            Irr.irrelevanceTerm {t = t} _ _ ⊩A′
              (wk1ᵛ _ (Irr.irrelevance _ _ ⊩C′) $
               wk1ᵛ _ (Irr.irrelevance _ _ ⊩B′) ⊩A)
              ⊩t′
              {k = k} {Δ = Δ} {σ = σ}) of λ
      ⊩t →
      _
    , subst↑²S _ _ _ _ ⊩D ⊩t
    , subst↑²S _ _ _ _ ⊩E ⊩t
    , subst↑²SEq _ _ _ _ ⊩D ⊩E D≡E ⊩t

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]↑² :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ D →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l′ ⟩ t ∷ wk2 A →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l ⟩ D [ t ]↑²
  ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]↑² ⊩D ⊩t =
    proj₁ $ wf-⊩ᵛ≡ $ ⊩ᵛ≡→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑² (refl-⊩ᵛ≡ ⊩D) ⊩t

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]↑²∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ D →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l′ ⟩ u ∷ wk2 A →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l ⟩ t [ u ]↑² ∷ D [ u ]↑²
  ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]↑²∷ {A} {t} {D} ⊩t ⊩u =
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛ→⊩ᵛ∷→⊩ᵛ[]↑² (wf-⊩ᵛ∷ ⊩t) ⊩u
      , λ σ₁≡σ₂ →
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (substComp↑² t _) (substComp↑² t _)
            (substComp↑² D _) $
          ⊩ᵛ∷⇔ .proj₁ ⊩t .proj₂ $
          ⊩ˢ≡∷∙⇔′ .proj₂
            ( wf-∙-⊩ᵛ (wf-⊩ᵛ∷ ⊩t)
            , ( _
              , (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk2-tail A) $
                 ⊩ᵛ≡∷⇔′ .proj₁ (refl-⊩ᵛ≡∷ ⊩u) .proj₂ .proj₂ σ₁≡σ₂)
              )
            , ⊩ˢ≡∷∙⇔ .proj₁ (⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ .proj₂) .proj₂
            )
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑²∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ≡ u ∷ D →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l′ ⟩ v ∷ wk2 A →
    Γ ∙ B ∙ C ⊩ᵛ⟨ l ⟩ t [ v ]↑² ≡ u [ v ]↑² ∷ D [ v ]↑²
  ⊩ᵛ≡∷→⊩ᵛ∷→⊩ᵛ[]↑²≡[]↑²∷ {A} {t} {u} {D} t≡u ⊩v =
    case wf-⊩ᵛ≡∷ t≡u of λ
      (⊩t , ⊩u) →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]↑²∷ ⊩t ⊩v
      , ⊩ᵛ∷→⊩ᵛ∷→⊩ᵛ[]↑²∷ ⊩u ⊩v
      , λ ⊩σ →
          PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (substComp↑² t _) (substComp↑² u _)
            (substComp↑² D _) $
          ⊩ᵛ≡∷⇔ .proj₁ t≡u .proj₂ .proj₂ $
          ⊩ˢ∷∙⇔′ .proj₂
            ( wf-∙-⊩ᵛ (wf-⊩ᵛ∷ ⊩t)
            , ( _
              , (PE.subst (_⊩⟨_⟩_∷_ _ _ _) (wk2-tail A) $
                 ⊩ᵛ∷→⊩ˢ∷→⊩[]∷ ⊩v ⊩σ)
              )
            , ⊩ˢ∷∙⇔ .proj₁ (⊩ˢ∷∙⇔ .proj₁ ⊩σ .proj₂) .proj₂
            )
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩≡∷→⊩[]₀≡[]₀ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B ≡ C →
    Γ ⊩⟨ l′ ⟩ t ≡ u ∷ A →
    Γ ⊩⟨ l ⟩ B [ t ]₀ ≡ C [ u ]₀
  ⊩ᵛ≡→⊩≡∷→⊩[]₀≡[]₀ B≡C t≡u =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ≡ B≡C .proj₁) of λ
      (_ , ⊩A) →
    ⊩ᵛ≡⇔′ .proj₁ B≡C .proj₂ .proj₂
      (⊩ˢ≡∷-sgSubst ⊩A (level-⊩≡∷ (⊩ᵛ→⊩ ⊩A) t≡u))

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩∷→⊩[]₀ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩⟨ l′ ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ B [ t ]₀
  ⊩ᵛ→⊩∷→⊩[]₀ ⊩B ⊩t =
    proj₁ $ wf-⊩≡ $
    ⊩ᵛ≡→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩ᵛ≡ ⊩B) (refl-⊩≡∷ ⊩t)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩≡∷→⊩[]₀≡[]₀∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ≡ u ∷ B →
    Γ ⊩⟨ l′ ⟩ v ≡ w ∷ A →
    Γ ⊩⟨ l ⟩ t [ v ]₀ ≡ u [ w ]₀ ∷ B [ v ]₀
  ⊩ᵛ≡∷→⊩≡∷→⊩[]₀≡[]₀∷ t≡u v≡w =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t≡u .proj₁)) of λ
      (_ , ⊩A) →
    ⊩ᵛ≡∷⇔′ .proj₁ t≡u .proj₂ .proj₂
      (⊩ˢ≡∷-sgSubst ⊩A (level-⊩≡∷ (⊩ᵛ→⊩ ⊩A) v≡w))

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩∷→⊩[]₀∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Γ ⊩⟨ l′ ⟩ u ∷ A →
    Γ ⊩⟨ l ⟩ t [ u ]₀ ∷ B [ u ]₀
  ⊩ᵛ∷→⊩∷→⊩[]₀∷ ⊩t ⊩u =
    proj₁ $ wf-⊩≡∷ $ ⊩ᵛ≡∷→⊩≡∷→⊩[]₀≡[]₀∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A [ σ₁ ] →
    Δ ⊩⟨ l ⟩ B₁ [ consSubst σ₁ t₁ ] ≡ B₂ [ consSubst σ₂ t₂ ]
  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] B₁≡B₂ σ₁≡σ₂ t₁≡t₂ =
    ⊩ᵛ≡⇔′ .proj₁ B₁≡B₂ .proj₂ .proj₂ $
    ⊩ˢ≡∷∙⇔′ .proj₂ (wf-∙-⊩ᵛ (wf-⊩ᵛ≡ B₁≡B₂ .proj₁) , (_ , t₁≡t₂) , σ₁≡σ₂)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[,] :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t ∷ A [ σ ] →
    Δ ⊩⟨ l ⟩ B [ consSubst σ t ]
  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[,] ⊩B ⊩σ ⊩t =
    proj₁ $ wf-⊩≡ $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ) (refl-⊩≡∷ ⊩t)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u₁ ≡ u₂ ∷ A [ σ₁ ] →
    Δ ⊩⟨ l ⟩ t₁ [ consSubst σ₁ u₁ ] ≡ t₂ [ consSubst σ₂ u₂ ] ∷
      B [ consSubst σ₁ u₁ ]
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ t₁≡t₂ σ₁≡σ₂ u₁≡u₂ =
    ⊩ᵛ≡∷⇔′ .proj₁ t₁≡t₂ .proj₂ .proj₂ $
    ⊩ˢ≡∷∙⇔′ .proj₂
      (wf-∙-⊩ᵛ (wf-⊩ᵛ∷ $ wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁) , (_ , u₁≡u₂) , σ₁≡σ₂)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[,]∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u ∷ A [ σ ] →
    Δ ⊩⟨ l ⟩ t [ consSubst σ u ] ∷ B [ consSubst σ u ]
  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[,]∷ ⊩t ⊩σ ⊩u =
    proj₁ $ wf-⊩≡∷ $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ) (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A [ σ₁ ] ⊩⟨ l ⟩ B₁ [ σ₁ ⇑ ] ≡ B₂ [ σ₂ ⇑ ]
  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] B₁≡B₂ σ₁≡σ₂ =
    ⊩ᵛ≡⇔′ .proj₁ B₁≡B₂ .proj₂ .proj₂ $
    ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ (wf-⊩ᵛ≡ B₁≡B₂ .proj₁) .proj₂) σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩[⇑] :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ∙ A [ σ ] ⊩⟨ l ⟩ B [ σ ⇑ ]
  ⊩ᵛ→⊩ˢ∷→⊩[⇑] ⊩B ⊩σ =
    proj₁ $ wf-⊩≡ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑]≡[⇑] (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A [ σ₁ ] ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ] ≡ t₂ [ σ₂ ⇑ ] ∷ B [ σ₁ ⇑ ]
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ t₁≡t₂ σ₁≡σ₂ =
    ⊩ᵛ≡∷⇔′ .proj₁ t₁≡t₂ .proj₂ .proj₂ $
    ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)) .proj₂)
      σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ∙ A [ σ ] ⊩⟨ l ⟩ t [ σ ⇑ ] ∷ B [ σ ⇑ ]
  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ ⊩t ⊩σ =
    proj₁ $ wf-⊩≡∷ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑] :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A [ σ₁ ] ∙ B [ σ₁ ⇑ ] ⊩⟨ l ⟩ C₁ [ σ₁ ⇑ ⇑ ] ≡ C₂ [ σ₂ ⇑ ⇑ ]
  ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑] C₁≡C₂ σ₁≡σ₂ =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ≡ C₁≡C₂ .proj₁) of λ
      (_ , ⊩B) →
    ⊩ᵛ≡⇔′ .proj₁ C₁≡C₂ .proj₂ .proj₂ $
    ⊩ˢ≡∷-liftSubst ⊩B $ ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ ⊩B .proj₂) σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩[⇑⇑] :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ∙ A [ σ ] ∙ B [ σ ⇑ ] ⊩⟨ l ⟩ C [ σ ⇑ ⇑ ]
  ⊩ᵛ→⊩ˢ∷→⊩[⇑⇑] ⊩C ⊩σ =
    proj₁ $ wf-⊩≡ $ ⊩ᵛ≡→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑] (refl-⊩ᵛ≡ ⊩C) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ C →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ∙ A [ σ₁ ] ∙ B [ σ₁ ⇑ ] ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ⇑ ] ≡ t₂ [ σ₂ ⇑ ⇑ ] ∷
      C [ σ₁ ⇑ ⇑ ]
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ t₁≡t₂ σ₁≡σ₂ =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)) of λ
      (_ , ⊩B) →
    ⊩ᵛ≡∷⇔′ .proj₁ t₁≡t₂ .proj₂ .proj₂ $
    ⊩ˢ≡∷-liftSubst ⊩B $ ⊩ˢ≡∷-liftSubst (wf-∙-⊩ᵛ ⊩B .proj₂) σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t ∷ C →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ∙ A [ σ ] ∙ B [ σ ⇑ ] ⊩⟨ l ⟩ t [ σ ⇑ ⇑ ] ∷ C [ σ ⇑ ⇑ ]
  ⊩ᵛ∷→⊩ˢ∷→⊩[⇑⇑]∷ ⊩t ⊩σ =
    proj₁ $ wf-⊩≡∷ $ ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑⇑]≡[⇑⇑]∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A [ σ₁ ] →
    Δ ⊩⟨ l ⟩ B₁ [ σ₁ ⇑ ] [ t₁ ]₀ ≡ B₂ [ σ₂ ⇑ ] [ t₂ ]₀
  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ {B₁} {B₂} B₁≡B₂ σ₁≡σ₂ t₁≡t₂ =
    PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
      (PE.sym $ singleSubstComp _ _ B₁)
      (PE.sym $ singleSubstComp _ _ B₂) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] B₁≡B₂ σ₁≡σ₂ t₁≡t₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑][]₀ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t ∷ A [ σ ] →
    Δ ⊩⟨ l ⟩ B [ σ ⇑ ] [ t ]₀
  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑][]₀ ⊩B ⊩σ ⊩t =
    proj₁ $ wf-⊩≡ $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ (refl-⊩ᵛ≡ ⊩B) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩t)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u₁ ≡ u₂ ∷ A [ σ₁ ] →
    Δ ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ] [ u₁ ]₀ ≡ t₂ [ σ₂ ⇑ ] [ u₂ ]₀ ∷
      B [ σ₁ ⇑ ] [ u₁ ]₀
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ {t₁} {t₂} {B} t₁≡t₂ σ₁≡σ₂ u₁≡u₂ =
    PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _)
      (PE.sym $ singleSubstComp _ _ t₁)
      (PE.sym $ singleSubstComp _ _ t₂)
      (PE.sym $ singleSubstComp _ _ B) $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,]∷ t₁≡t₂ σ₁≡σ₂ u₁≡u₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[⇑][]₀∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u ∷ A [ σ ] →
    Δ ⊩⟨ l ⟩ t [ σ ⇑ ] [ u ]₀ ∷ B [ σ ⇑ ] [ u ]₀
  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩[⇑][]₀∷ ⊩t ⊩σ ⊩u =
    proj₁ $ wf-⊩≡∷ $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Δ ⊩⟨ l′ ⟩ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ] →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ B₁ [ t₁ ]₀ [ σ₁ ] ≡ B₂ [ t₂ ]₀ [ σ₂ ]
  ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] {B₁} {B₂} B₁≡B₂ t₁[σ₁]≡t₂[σ₂] σ₁≡σ₂ =
    PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
      (PE.sym $ singleSubstLift B₁ _)
      (PE.sym $ singleSubstLift B₂ _) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀ B₁≡B₂ σ₁≡σ₂ t₁[σ₁]≡t₂[σ₂]

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩∷→⊩ˢ∷→⊩[]₀[] :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Δ ⊩⟨ l′ ⟩ t [ σ ] ∷ A [ σ ] →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ B [ t ]₀ [ σ ]
  ⊩ᵛ→⊩∷→⊩ˢ∷→⊩[]₀[] {t} ⊩B ⊩t[σ] ⊩σ =
    proj₁ $ wf-⊩≡ $
    ⊩ᵛ≡→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[] {t₂ = t} (refl-⊩ᵛ≡ ⊩B) (refl-⊩≡∷ ⊩t[σ])
      (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[]∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ B →
    Δ ⊩⟨ l′ ⟩ u₁ [ σ₁ ] ≡ u₂ [ σ₂ ] ∷ A [ σ₁ ] →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ t₁ [ u₁ ]₀ [ σ₁ ] ≡ t₂ [ u₂ ]₀ [ σ₂ ] ∷ B [ u₁ ]₀ [ σ₁ ]
  ⊩ᵛ≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[]∷ {t₁} {t₂} {B} t₁≡t₂ σ₁≡σ₂ u₁[σ₁]≡u₂[σ₂] =
    PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (PE.sym $ singleSubstLift t₁ _)
      (PE.sym $ singleSubstLift t₂ _) (PE.sym $ singleSubstLift B _) $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩[⇑][]₀≡[⇑][]₀∷ t₁≡t₂ u₁[σ₁]≡u₂[σ₂] σ₁≡σ₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩∷→⊩ˢ∷→⊩[]₀[]∷ :
    Γ ∙ A ⊩ᵛ⟨ l ⟩ t ∷ B →
    Δ ⊩⟨ l′ ⟩ u [ σ ] ∷ A [ σ ] →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ t [ u ]₀ [ σ ] ∷ B [ u ]₀ [ σ ]
  ⊩ᵛ∷→⊩∷→⊩ˢ∷→⊩[]₀[]∷ {u} ⊩t ⊩u[σ] ⊩σ =
    proj₁ $ wf-⊩≡∷ $
    ⊩ᵛ≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₀[]≡[]₀[]∷ {u₂ = u} (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩≡∷ ⊩u[σ])
      (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A [ σ₁ ] →
    Δ ⊩⟨ l″ ⟩ u₁ ≡ u₂ ∷ B [ σ₁ ⇑ ] [ t₁ ]₀ →
    Δ ⊩⟨ l ⟩ C₁ [ σ₁ ⇑ ⇑ ] [ t₁ , u₁ ]₁₀ ≡ C₂ [ σ₂ ⇑ ⇑ ] [ t₂ , u₂ ]₁₀
  ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀
    {B} {C₁} {C₂} C₁≡C₂ σ₁≡σ₂ t₁≡t₂ u₁≡u₂ =
    PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
      (PE.sym $ doubleSubstComp C₁ _ _ _)
      (PE.sym $ doubleSubstComp C₂ _ _ _) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩[,]≡[,] C₁≡C₂
      (⊩ˢ≡∷∙⇔′ .proj₂
         ( wf-∙-⊩ᵛ (wf-∙-⊩ᵛ (wf-⊩ᵛ≡ C₁≡C₂ .proj₁) .proj₂)
         , (_ , t₁≡t₂)
         , σ₁≡σ₂
         )) $
    PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstComp _ _ B) u₁≡u₂

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑⇑][]₁₀ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ t ∷ A [ σ ] →
    Δ ⊩⟨ l″ ⟩ u ∷ B [ σ ⇑ ] [ t ]₀ →
    Δ ⊩⟨ l ⟩ C [ σ ⇑ ⇑ ] [ t , u ]₁₀
  ⊩ᵛ→⊩ˢ∷→⊩∷→⊩[⇑⇑][]₁₀ ⊩C ⊩σ ⊩t ⊩u =
    proj₁ $ wf-⊩≡ $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ (refl-⊩ᵛ≡ ⊩C) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩t) (refl-⊩≡∷ ⊩u)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ C →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u₁ ≡ u₂ ∷ A [ σ₁ ] →
    Δ ⊩⟨ l″ ⟩ v₁ ≡ v₂ ∷ B [ σ₁ ⇑ ] [ u₁ ]₀ →
    Δ ⊩⟨ l ⟩ t₁ [ σ₁ ⇑ ⇑ ] [ u₁ , v₁ ]₁₀ ≡ t₂ [ σ₂ ⇑ ⇑ ] [ u₂ , v₂ ]₁₀ ∷
      C [ σ₁ ⇑ ⇑ ] [ u₁ , v₁ ]₁₀
  ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷
    {B} {t₁} {t₂} {C} t₁≡t₂ σ₁≡σ₂ u₁≡u₂ v₁≡v₂ =
    case wf-∙-⊩ᵛ (wf-⊩ᵛ∷ (wf-⊩ᵛ≡∷ t₁≡t₂ .proj₁)) of λ
      (_ , ⊩B) →
    PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _)
      (PE.sym $ doubleSubstComp t₁ _ _ _)
      (PE.sym $ doubleSubstComp t₂ _ _ _)
      (PE.sym $ doubleSubstComp C _ _ _) $
    ⊩ᵛ≡∷⇔′ .proj₁ t₁≡t₂ .proj₂ .proj₂ $
    ⊩ˢ≡∷∙⇔′ .proj₂
      ( (_ , ⊩B)
      , ( _
        , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstComp _ _ B) v₁≡v₂
        )
      , ⊩ˢ≡∷∙⇔′ .proj₂ (wf-∙-⊩ᵛ ⊩B , (_ , u₁≡u₂) , σ₁≡σ₂)
      )

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩∷→⊩[⇑⇑][]₁₀∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t ∷ C →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l′ ⟩ u ∷ A [ σ ] →
    Δ ⊩⟨ l″ ⟩ v ∷ B [ σ ⇑ ] [ u ]₀ →
    Δ ⊩⟨ l ⟩ t [ σ ⇑ ⇑ ] [ u , v ]₁₀ ∷ C [ σ ⇑ ⇑ ] [ u , v ]₁₀
  ⊩ᵛ∷→⊩ˢ∷→⊩∷→⊩∷→⊩[⇑⇑][]₁₀∷ ⊩t ⊩σ ⊩u ⊩v =
    proj₁ $ wf-⊩≡∷ $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷ (refl-⊩ᵛ≡∷ ⊩t) (refl-⊩ˢ≡∷ ⊩σ)
      (refl-⊩≡∷ ⊩u) (refl-⊩≡∷ ⊩v)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_ and _⊩⟨_⟩_≡_.

  ⊩ᵛ≡→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[] :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C₁ ≡ C₂ →
    Δ ⊩⟨ l′ ⟩ t₁ [ σ₁ ] ≡ t₂ [ σ₂ ] ∷ A [ σ₁ ] →
    Δ ⊩⟨ l″ ⟩ u₁ [ σ₁ ] ≡ u₂ [ σ₂ ] ∷ B [ t₁ ]₀ [ σ₁ ] →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ C₁ [ t₁ , u₁ ]₁₀ [ σ₁ ] ≡ C₂ [ t₂ , u₂ ]₁₀ [ σ₂ ]
  ⊩ᵛ≡→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[]
    {B} {C₁} {C₂} C₁≡C₂ t₁[σ₁]≡t₂[σ₂] u₁[σ₁]≡u₂[σ₂] σ₁≡σ₂ =
    PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
      (PE.sym $ [,]-[]-commute C₁)
      (PE.sym $ [,]-[]-commute C₂) $
    ⊩ᵛ≡→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀ C₁≡C₂ σ₁≡σ₂ t₁[σ₁]≡t₂[σ₂]
      (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstLift B _)
         u₁[σ₁]≡u₂[σ₂])

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_ and _⊩⟨_⟩_.

  ⊩ᵛ→⊩∷→⊩∷→⊩ˢ∷→⊩[]₁₀[] :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ C →
    Δ ⊩⟨ l′ ⟩ t [ σ ] ∷ A [ σ ] →
    Δ ⊩⟨ l″ ⟩ u [ σ ] ∷ B [ t ]₀ [ σ ] →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ C [ t , u ]₁₀ [ σ ]
  ⊩ᵛ→⊩∷→⊩∷→⊩ˢ∷→⊩[]₁₀[] {t} {u} ⊩C ⊩t[σ] ⊩u[σ] ⊩σ =
    proj₁ $ wf-⊩≡ $
    ⊩ᵛ≡→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[] {t₂ = t} {u₂ = u} (refl-⊩ᵛ≡ ⊩C)
      (refl-⊩≡∷ ⊩t[σ]) (refl-⊩≡∷ ⊩u[σ]) (refl-⊩ˢ≡∷ ⊩σ)

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_≡_∷_ and _⊩⟨_⟩_≡_∷_.

  ⊩ᵛ≡∷→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[]∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t₁ ≡ t₂ ∷ C →
    Δ ⊩⟨ l′ ⟩ u₁ [ σ₁ ] ≡ u₂ [ σ₂ ] ∷ A [ σ₁ ] →
    Δ ⊩⟨ l″ ⟩ v₁ [ σ₁ ] ≡ v₂ [ σ₂ ] ∷ B [ u₁ ]₀ [ σ₁ ] →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ t₁ [ u₁ , v₁ ]₁₀ [ σ₁ ] ≡ t₂ [ u₂ , v₂ ]₁₀ [ σ₂ ] ∷
      C [ u₁ , v₁ ]₁₀ [ σ₁ ]
  ⊩ᵛ≡∷→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[]∷
    {B} {t₁} {t₂} {C} t₁≡t₂ u₁[σ₁]≡u₂[σ₂] v₁[σ₁]≡v₂[σ₂] σ₁≡σ₂ =
    PE.subst₃ (_⊩⟨_⟩_≡_∷_ _ _) (PE.sym $ [,]-[]-commute t₁)
      (PE.sym $ [,]-[]-commute t₂) (PE.sym $ [,]-[]-commute C) $
    ⊩ᵛ≡∷→⊩ˢ≡∷→⊩≡∷→⊩≡∷→⊩[⇑⇑][]₁₀≡[⇑⇑][]₁₀∷ t₁≡t₂ σ₁≡σ₂ u₁[σ₁]≡u₂[σ₂]
      (PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (singleSubstLift B _)
         v₁[σ₁]≡v₂[σ₂])

opaque

  -- A substitution lemma for _⊩ᵛ⟨_⟩_∷_ and _⊩⟨_⟩_∷_.

  ⊩ᵛ∷→⊩∷→⊩∷→⊩ˢ∷→⊩[]₁₀[]∷ :
    Γ ∙ A ∙ B ⊩ᵛ⟨ l ⟩ t ∷ C →
    Δ ⊩⟨ l′ ⟩ u [ σ ] ∷ A [ σ ] →
    Δ ⊩⟨ l″ ⟩ v [ σ ] ∷ B [ u ]₀ [ σ ] →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ t [ u , v ]₁₀ [ σ ] ∷ C [ u , v ]₁₀ [ σ ]
  ⊩ᵛ∷→⊩∷→⊩∷→⊩ˢ∷→⊩[]₁₀[]∷ {u} {v} ⊩t ⊩u[σ] ⊩v[σ] ⊩σ =
    proj₁ $ wf-⊩≡∷ $
    ⊩ᵛ≡∷→⊩≡∷→⊩≡∷→⊩ˢ≡∷→⊩[]₁₀[]≡[]₁₀[]∷ {u₂ = u} {v₂ = v} (refl-⊩ᵛ≡∷ ⊩t)
      (refl-⊩≡∷ ⊩u[σ]) (refl-⊩≡∷ ⊩v[σ]) (refl-⊩ˢ≡∷ ⊩σ)
