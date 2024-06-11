------------------------------------------------------------------------
-- Cumulativity lemmata for the logical relation
------------------------------------------------------------------------

{-# OPTIONS --hidden-argument-puns #-}

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Cumulativity
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}

open import Definition.Untyped M
open import Definition.Typed R
open import Definition.LogicalRelation R
import Definition.LogicalRelation.Properties.Cumulativity R as LR
open import Definition.LogicalRelation.Substitution R

open import Tools.Level
open import Tools.Nat hiding (_<_; _≤_)
open import Tools.Product
open import Tools.Unit
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    Γ : Con Term n
    A A₁ A₂ A′ B₁ B₂ C t u : Term _
    σ : Subst m n
    l l′ : TypeLevel
    ⊩Γ ⊩Γ′ : ⊩ᵛ _

opaque mutual

  -- Well-formness is cumulative
  cumul : ∀ {l l′ A} → ([Γ] : ⊩ᵛ Γ) → l < l′ → Γ ⊩ᵛ⟨ l ⟩ A / [Γ] →  Γ ⊩ᵛ⟨ l′ ⟩ A / [Γ]
  cumul [Γ] l< (wrap unwrap) =
    wrap (λ ⊢Δ [σ] → (LR.cumul l< (proj₁ (unwrap ⊢Δ [σ]))) ,
    (λ [σ′] [σ≡σ′] → LR.cumulEq l< (proj₁ (unwrap ⊢Δ [σ]))
            ((proj₂ (unwrap ⊢Δ [σ])) [σ′] [σ≡σ′])))

  -- Well-formness is cumulative
  cumul≤ : ∀ {l l′ A} → ([Γ] : ⊩ᵛ Γ) → l ≤ l′ → Γ ⊩ᵛ⟨ l ⟩ A / [Γ] →  Γ ⊩ᵛ⟨ l′ ⟩ A / [Γ]
  cumul≤ [Γ] ≤′-refl [A] = [A]
  cumul≤ [Γ] (≤′-step l<) (wrap unwrap) =
    wrap (λ ⊢Δ [σ] → (LR.cumul (≤→< l<) (proj₁ (unwrap ⊢Δ [σ]))) ,
    (λ [σ′] [σ≡σ′] → LR.cumulEq (≤→< l<) (proj₁ (unwrap ⊢Δ [σ]))
            ((proj₂ (unwrap ⊢Δ [σ])) [σ′] [σ≡σ′])))
