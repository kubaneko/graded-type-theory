------------------------------------------------------------------------
-- Properties of the reduction relation.
------------------------------------------------------------------------

open import Definition.Typed.Restrictions

module Definition.Typed.Consequences.Reduction
  {a} {M : Set a}
  (R : Type-restrictions M)
  where

open import Definition.Untyped M hiding (_∷_)
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.EqRelInstance R
open import Definition.Typed.Consequences.Inequality R
open import Definition.Typed.Consequences.Injectivity R
open import Definition.Typed.Consequences.Inversion R
open import Definition.Typed.Consequences.Syntactic R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Fundamental.Reducibility R

open import Tools.Empty
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    p q : M

-- Helper function where all reducible types can be reduced to WHNF.
whNorm′ : ∀ {A l} ([A] : Γ ⊩⟨ l ⟩ A)
                → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B
whNorm′ (Uᵣ′ .⁰ 0<1 ⊢Γ) = U , Uₙ , idRed:*: (Uⱼ ⊢Γ)
whNorm′ (ℕᵣ D) = ℕ , ℕₙ , D
whNorm′ (Emptyᵣ D) = Empty , Emptyₙ , D
whNorm′ (Unitᵣ (Unitₜ D _)) = Unit , Unitₙ , D
whNorm′ (ne′ K D neK K≡K) = K , ne neK , D
whNorm′ (Πᵣ′ F G D _ _ _ _ _ _ _) = Π _ , _ ▷ F ▹ G , ΠΣₙ , D
whNorm′ (Σᵣ′ F G D _ _ _ _ _ _ _) = Σ _ , _ ▷ F ▹ G , ΠΣₙ , D
whNorm′ (emb 0<1 [A]) = whNorm′ [A]

-- Well-formed types can all be reduced to WHNF.
whNorm : ∀ {A} → Γ ⊢ A → ∃ λ B → Whnf B × Γ ⊢ A :⇒*: B
whNorm A = whNorm′ (reducible A)

ΠNorm : ∀ {A F G} → Γ ⊢ A → Γ ⊢ A ≡ Π p , q ▷ F ▹ G
      → ∃₂ λ F′ G′ → Γ ⊢ A ⇒* Π p , q ▷ F′ ▹ G′ × Γ ⊢ F ≡ F′
         × Γ ∙ F ⊢ G ≡ G′
ΠNorm {A = A} ⊢A A≡ΠFG with whNorm ⊢A
... | _ , Uₙ , D = ⊥-elim (U≢Π (trans (sym (subset* (red D))) A≡ΠFG))
... | _ , ΠΣₙ {b = BMΠ} , D =
  let Π≡Π′ = trans (sym A≡ΠFG) (subset* (red D))
      F≡F′ , G≡G′ , p≡p′ , q≡q′ = injectivity Π≡Π′
      D′ = PE.subst₂ (λ p q → _ ⊢ A ⇒* Π p , q ▷ _ ▹ _) (PE.sym p≡p′) (PE.sym q≡q′) (red D)
  in  _ , _ , D′ , F≡F′ , G≡G′
... | _ , ΠΣₙ {b = BMΣ s} , D = ⊥-elim (Π≢Σⱼ (trans (sym A≡ΠFG) (subset* (red D))))
... | _ , ℕₙ , D = ⊥-elim (ℕ≢Π (trans (sym (subset* (red D))) A≡ΠFG))
... | _ , Unitₙ , D = ⊥-elim (Unit≢Πⱼ (trans (sym (subset* (red D))) A≡ΠFG))
... | _ , Emptyₙ , D = ⊥-elim (Empty≢Πⱼ (trans (sym (subset* (red D))) A≡ΠFG))
... | _ , lamₙ , [ ⊢A , univ ⊢B , A⇒B ] =
  let _ , _ , _ , _ , _ , U≡Π , _ = inversion-lam ⊢B
  in  ⊥-elim (U≢Π U≡Π)
... | _ , zeroₙ , [ ⊢A , univ ⊢B , A⇒B ] = ⊥-elim (U≢ℕ (inversion-zero ⊢B))
... | _ , sucₙ , [ ⊢A , univ ⊢B , A⇒B ] = ⊥-elim (U≢ℕ (proj₂ (inversion-suc ⊢B)))
... | _ , starₙ , [ _ , univ ⊢B , _ ] =
  ⊥-elim (U≢Unitⱼ (inversion-star ⊢B .proj₁))
... | _ , prodₙ , [ _ , univ ⊢B , _ ] =
  let _ , _ , _ , _ , _ , _ , _ , U≡Σ , _ = inversion-prod ⊢B
  in  ⊥-elim (U≢Σ U≡Σ)
... | _ , ne x , D = ⊥-elim (Π≢ne x (trans (sym A≡ΠFG) (subset* (red D))))

ΣNorm : ∀ {A F G m} → Γ ⊢ A → Γ ⊢ A ≡ Σ⟨ m ⟩ p , q ▷ F ▹ G
      → ∃₂ λ F′ G′ → Γ ⊢ A ⇒* Σ⟨ m ⟩ p , q ▷ F′ ▹ G′
         × Γ ⊢ F ≡ F′ × Γ ∙ F ⊢ G ≡ G′
ΣNorm {A = A} ⊢A A≡ΣFG with whNorm ⊢A
... | _ , Uₙ , D = ⊥-elim (U≢Σ (trans (sym (subset* (red D))) A≡ΣFG))
... | _ , (ΠΣₙ {b = BMΠ}) , D = ⊥-elim (Π≢Σⱼ (trans (sym (subset* (red D))) A≡ΣFG))
... | _ , (ΠΣₙ {b = BMΣ m}) , D =
  let Σ≡Σ′ = trans (sym A≡ΣFG) (subset* (red D))
      F≡F′ , G≡G′ , p≡p′ , q≡q′ , m≡m′ = Σ-injectivity Σ≡Σ′
      D′ = PE.subst₃ (λ m p q → _ ⊢ A ⇒* Σ⟨ m ⟩ p , q ▷ _ ▹ _)
                     (PE.sym m≡m′) (PE.sym p≡p′) (PE.sym q≡q′) (red D)
  in  _ , _ , D′ , F≡F′ , G≡G′
... | _ , ℕₙ , D = ⊥-elim (ℕ≢Σ (trans (sym (subset* (red D))) A≡ΣFG))
... | _ , Unitₙ , D = ⊥-elim (Unit≢Σⱼ (trans (sym (subset* (red D))) A≡ΣFG))
... | _ , Emptyₙ , D = ⊥-elim (Empty≢Σⱼ (trans (sym (subset* (red D))) A≡ΣFG))
... | _ , lamₙ , [ ⊢A , univ ⊢B , A⇒B ] =
  let _ , _ , _ , _ , _ , U≡Π , _ = inversion-lam ⊢B
  in  ⊥-elim (U≢Π U≡Π)
... | _ , zeroₙ , [ ⊢A , univ ⊢B , A⇒B ] = ⊥-elim (U≢ℕ (inversion-zero ⊢B))
... | _ , sucₙ , [ ⊢A , univ ⊢B , A⇒B ] = ⊥-elim (U≢ℕ (proj₂ (inversion-suc ⊢B)))
... | _ , starₙ , [ _ , univ ⊢B , _ ] =
  ⊥-elim (U≢Unitⱼ (inversion-star ⊢B .proj₁))
... | _ , prodₙ , [ _ , univ ⊢B , _ ] =
  let _ , _ , _ , _ , _ , _ , _ , U≡Σ , _ = inversion-prod ⊢B
  in  ⊥-elim (U≢Σ U≡Σ)
... | _ , ne x , D = ⊥-elim (Σ≢ne x (trans (sym A≡ΣFG) (subset* (red D))))

-- Helper function where reducible all terms can be reduced to WHNF.
whNormTerm′ : ∀ {a A l} ([A] : Γ ⊩⟨ l ⟩ A) → Γ ⊩⟨ l ⟩ a ∷ A / [A]
                → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A
whNormTerm′ (Uᵣ x) (Uₜ A d typeA A≡A [t]) = A , typeWhnf typeA , d
whNormTerm′ (ℕᵣ x) (ℕₜ n d n≡n prop) =
  let natN = natural prop
  in  n , naturalWhnf natN , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (Emptyᵣ x) (Emptyₜ n d n≡n prop) =
  let emptyN = empty prop
  in  n , ne emptyN , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (Unitᵣ (Unitₜ x _)) (Unitₜ n d prop) =
  n , prop , convRed:*: d (sym (subset* (red x)))
whNormTerm′ (ne (ne K D neK K≡K)) (neₜ k d (neNfₜ neK₁ ⊢k k≡k)) =
  k , ne neK₁ , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (Πᵣ′ _ _ D _ _ _ _ _ _ _) (Πₜ f d funcF _ _ _) =
  f , functionWhnf funcF , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (Σᵣ′ _ _ D _ _ _ _ _ _ _) (Σₜ p d _ pProd _) =
  p , productWhnf pProd , convRed:*: d (sym (subset* (red D)))
whNormTerm′ (emb 0<1 [A]) [a] = whNormTerm′ [A] [a]

-- Well-formed terms can all be reduced to WHNF.
whNormTerm : ∀ {a A} → Γ ⊢ a ∷ A → ∃ λ b → Whnf b × Γ ⊢ a :⇒*: b ∷ A
whNormTerm {a} {A} ⊢a =
  let [A] , [a] = reducibleTerm ⊢a
  in  whNormTerm′ [A] [a]

redMany : ∀ {t u A} → Γ ⊢ t ⇒ u ∷ A → Γ ⊢ t ⇒* u ∷ A
redMany d =
  let _ , _ , ⊢u = syntacticEqTerm (subsetTerm d)
  in  d ⇨ id ⊢u
