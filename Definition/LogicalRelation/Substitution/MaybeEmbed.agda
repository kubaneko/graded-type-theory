------------------------------------------------------------------------
-- Embedding of the logical relation into higher type levels
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.MaybeEmbed
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}


open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.Untyped M using (Con ; Term; U)

open import Tools.Nat
open import Tools.Product

private
  variable
    n : Nat
    Γ : Con Term n

-- The lowest level can be embedded in any level (validity variant).
maybeEmbₛ′ : ∀ {l A}
             ([Γ] : ⊩ᵛ Γ)
           → Γ ⊩ᵛ⟨ 0 ⟩ A / [Γ]
           → Γ ⊩ᵛ⟨ l ⟩ A / [Γ]
maybeEmbₛ′ {l = 0} [Γ] [A] = [A]
maybeEmbₛ′ {l = 1+ l} [Γ] [A] = wrap λ ⊢Δ [σ] →
  let [σA]  = proj₁ (unwrap [A] ⊢Δ [σ])
      [σA]′ = maybeEmb′ (proj₁ (unwrap [A] ⊢Δ [σ]))
  in  [σA]′
  ,   (λ [σ′] [σ≡σ′] → irrelevanceEq [σA] [σA]′ (proj₂ (unwrap [A] ⊢Δ [σ]) [σ′] [σ≡σ′]))
