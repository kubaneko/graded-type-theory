------------------------------------------------------------------------
-- Validity for Π- and Σ-types
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Pi-Sigma
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  ⦃ eqrel : EqRelSet R ⦄
  where

open EqRelSet eqrel
open Type-restrictions R

open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import
  Definition.LogicalRelation.Substitution.Introductions.Universe R
open import Definition.LogicalRelation.Substitution.Introductions.Var R
import Definition.LogicalRelation.Substitution.Irrelevance R as S
import Definition.LogicalRelation.Weakening R as W

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Typed.Weakening R as TW using (_∷_⊇_)

open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.Untyped.Properties M

open import Tools.Function
open import Tools.Nat using (Nat; 1+; ≤′-trans; ≤′-refl; ≤′-step)
open import Tools.Product
import Tools.PropositionalEquality as PE
import Tools.Reasoning.PropositionalEquality

private variable
  n                       : Nat
  Γ Δ                     : Con Term _
  A A₁ A₂ B B₁ B₂ t t₁ t₂ : Term _
  σ σ₁ σ₂                 : Subst _ _
  p q                     : M
  l l′ l″ l‴              : TypeLevel
  b                       : BinderMode

------------------------------------------------------------------------
-- Some characterisation lemmas

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩ΠΣ⇔ :
    {A : Term n} {B : Term (1+ n)} →
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ⇔
    (ΠΣ-allowed b p q ×
     ⊢ Γ ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ Δ ⊇ Γ → ⊢ Δ →
      Δ ⊩⟨ l ⟩ wk ρ A ×
      (∀ {t u} →
       Δ ⊩⟨ l ⟩ t ≡ u ∷ wk ρ A →
       Δ ⊩⟨ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B [ u ]₀)))
  ⊩ΠΣ⇔ {n} {b} {p} {q} {A} {B} =
      lemma ∘→ B-elim _
    , (λ (ok , ⊢Γ , rest) →
         case PE.subst (_⊩⟨_⟩_ _ _) (wk-id _) $
              rest TW.id ⊢Γ .proj₁ of λ
           ⊩A →
         case escape ⊩A of λ
           ⊢A →
         case ⊢Γ ∙ ⊢A of λ
           ⊢Γ∙A →
         case var ⊢Γ∙A here of λ
           ⊢x0 →
         case PE.subst (λ B → _ ⊩⟨ _ ⟩ B ≡ B) (wkSingleSubstId _) $
              rest (TW.step TW.id) ⊢Γ∙A .proj₂ $
              refl-⊩≡∷ $
              neutral-⊩∷ (W.wk (TW.step TW.id) ⊢Γ∙A ⊩A) (var _) ⊢x0
                (~-var ⊢x0) of λ
           B≡B →
         case escape $ wf-⊩≡ B≡B .proj₁ of λ
           ⊢B →
         Bᵣ (BM b p q)
           (Bᵣ _ _ (idRed:*: (ΠΣⱼ ⊢A ⊢B ok)) ⊢A ⊢B
              (≅-ΠΣ-cong ⊢A (escape-⊩≡ $ refl-⊩≡ ⊩A) (escape-⊩≡ B≡B) ok)
              (λ ρ⊇ ⊢Δ → rest ρ⊇ ⊢Δ .proj₁)
              (λ ρ⊇ ⊢Δ ⊩t →
                 wf-⊩≡
                   (rest ρ⊇ ⊢Δ .proj₂ $
                    refl-⊩≡∷ (rest _ _ .proj₁ , ⊩t))
                   .proj₁)
              (λ ρ⊇ ⊢Δ ⊩t ⊩u t≡u →
                 ⊩≡→⊩≡/
                   (wf-⊩≡
                      (rest ρ⊇ ⊢Δ .proj₂ $
                       refl-⊩≡∷ (rest _ _ .proj₁ , ⊩t))
                      .proj₁) $
                 rest ρ⊇ ⊢Δ .proj₂ (rest _ _ .proj₁ , ⊩t , ⊩u , t≡u))
              ok))
    where
    lemma :
      Γ ⊩⟨ l ⟩B⟨ BM b p q ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
      ΠΣ-allowed b p q ×
      ⊢ Γ ×
      (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
       ρ ∷ Δ ⊇ Γ → ⊢ Δ →
       Δ ⊩⟨ l ⟩ wk ρ A ×
       (∀ {t u} →
        Δ ⊩⟨ l ⟩ t ≡ u ∷ wk ρ A →
        Δ ⊩⟨ l ⟩ wk (lift ρ) B [ t ]₀ ≡ wk (lift ρ) B [ u ]₀))
    lemma (emb 0<1 ⊩ΠΣ) =
      case lemma ⊩ΠΣ of λ
        (ok , ⊢Γ , rest) →
        ok , ⊢Γ
      , λ ρ⊇ ⊢Δ →
          case rest ρ⊇ ⊢Δ of λ
            (⊩A , B≡B) →
          emb 0<1 (PE.subst (λ k → LogRelKit._⊩_ k _ _) (kit≡kit′ 0<1) ⊩A)  ,  emb-⊩≡ (<→≤ 0<1) ∘→ B≡B ∘→ level-⊩≡∷ ⊩A
    lemma (noemb (Bᵣ _ _ ⇒*ΠΣ ⊢A _ _ ⊩wk-A ⊩wk-B wk-B≡wk-B ok)) =
      case B-PE-injectivity _ _ $ whnfRed* (red ⇒*ΠΣ) ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
        ok , wf ⊢A
      , λ ρ⊇ ⊢Δ →
          let ⊩wk-ρ-A = ⊩wk-A ρ⊇ ⊢Δ in
            ⊩wk-ρ-A
          , λ (⊩wk-ρ-A′ , ⊩t , ⊩u , t≡u) →
              case irrelevanceTerm ⊩wk-ρ-A′ ⊩wk-ρ-A ⊩t of λ
                ⊩t →
              case irrelevanceTerm ⊩wk-ρ-A′ ⊩wk-ρ-A ⊩u of λ
                ⊩u →
                ⊩wk-B ρ⊇ ⊢Δ ⊩t
              , ⊩wk-B ρ⊇ ⊢Δ ⊩u
              , wk-B≡wk-B ρ⊇ ⊢Δ ⊩t ⊩u
                  (irrelevanceEqTerm ⊩wk-ρ-A′ ⊩wk-ρ-A t≡u) }

opaque

  -- A variant of ⊩ΠΣ⇔.

  ⊩ΠΣ→ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    ΠΣ-allowed b p q × Γ ⊩⟨ l ⟩ A × Γ ∙ A ⊩⟨ l ⟩ B
  ⊩ΠΣ→ ⊩ΠΣ =
    case ⊩ΠΣ⇔ .proj₁ ⊩ΠΣ of λ
      (ok , ⊢Γ , rest) →
    case rest TW.id ⊢Γ of λ
      (⊩wk-id-A , _) →
    case PE.subst (_⊩⟨_⟩_ _ _) (wk-id _) ⊩wk-id-A of λ
      ⊩A →
    case rest (TW.step TW.id) (⊢→⊢∙ $ escape-⊩ ⊩A) of λ
      (⊩wk₁-A , wk-lift-step-id-B[]₀≡wk-lift-step-id-B[]₀) →
      ok , ⊩A
    , PE.subst (_⊩⟨_⟩_ _ _) (wkSingleSubstId _)
        (proj₁ $ wf-⊩≡ $
         wk-lift-step-id-B[]₀≡wk-lift-step-id-B[]₀ $
         refl-⊩≡∷ (⊩var here ⊩wk₁-A))

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_∷_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩ΠΣ≡ΠΣ⇔ :
    {A₁ A₂ : Term n} {B₁ B₂ : Term (1+ n)} →
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ⇔
    (Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ×
     Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ×
     (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ Δ ⊇ Γ → ⊢ Δ →
      Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
      (∀ {t} →
       Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
       Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B₂ [ t ]₀)))
  ⊩ΠΣ≡ΠΣ⇔ {n} {b} {p} {q} {A₁} {A₂} {B₁} {B₂} =
      (λ (⊩ΠΣ₁ , ⊩ΠΣ₂ , ΠΣ≡ΠΣ) →
           ⊩ΠΣ₁ , ⊩ΠΣ₂
         , lemma₁ ≤′-refl (B-elim _ ⊩ΠΣ₁) ⊩ΠΣ₂
             (irrelevanceEq ⊩ΠΣ₁ (B-intr _ (B-elim _ ⊩ΠΣ₁)) ΠΣ≡ΠΣ))
    , (λ (⊩ΠΣ₁ , ⊩ΠΣ₂ , rest) →
           B-intr _ (B-elim _ ⊩ΠΣ₁) , ⊩ΠΣ₂
         , lemma₂ (B-elim _ ⊩ΠΣ₁) ⊩ΠΣ₂ rest)
    where
    lemma₁ :
      l′ ≤ l →
      (⊩ΠΣ₁ : Γ ⊩⟨ l′ ⟩B⟨ BM b p q ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) →
      Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ →
      Γ ⊩⟨ l′ ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ /
        B-intr _ ⊩ΠΣ₁ →
      ∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
      ρ ∷ Δ ⊇ Γ → ⊢ Δ →
      Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
      (∀ {t} →
       Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
       Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B₂ [ t ]₀)
    lemma₁ ¹≤l (emb l< ⊩ΠΣ₁) ⊩ΠΣ₂ ΠΣ≡ΠΣ =
                    lemma₁ (≤′-trans (<→≤ l<) ¹≤l) ⊩ΠΣ₁ ⊩ΠΣ₂
                    (irrelevanceEq (B-intr _ (emb l< ⊩ΠΣ₁)) (B-intr _ ⊩ΠΣ₁) ΠΣ≡ΠΣ)
    lemma₁
      l′≤l (noemb (Bᵣ _ _ ⇒*ΠΣ₁ ⊢A₁ _ _ ⊩wk-A₁ ⊩wk-B₁ _ ok)) ⊩ΠΣ₂
      (B₌ _ _ ⇒*ΠΣ₂ _ wk-A₁≡wk-A₂ wk-B₁≡wk-B₂) ρ⊇ ⊢Δ =
      case B-PE-injectivity _ _ $ whnfRed* (red ⇒*ΠΣ₁) ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
      case B-PE-injectivity _ _ $ whnfRed* ⇒*ΠΣ₂ ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
      case ⊩ΠΣ⇔ .proj₁ ⊩ΠΣ₂ .proj₂ .proj₂ ρ⊇ ⊢Δ of λ
        (⊩wk-ρ-A₂ , wk-ρ⇑-B₂≡wk-ρ⇑-B₂) →
      case   emb-≤-⊩ l′≤l (⊩wk-A₁ ρ⊇ ⊢Δ)
           , ⊩wk-ρ-A₂
           , emb-≤-≡ (wk-A₁≡wk-A₂ ρ⊇ ⊢Δ) of λ
        wk-ρ-A₁≡wk-ρ-A₂ →
        wk-ρ-A₁≡wk-ρ-A₂
      , λ ⊩t@(⊩wk-ρ-A₁ , ⊩t′) →
          let ⊩wk-ρ⇑-B₁[t] =
                ⊩wk-B₁ ρ⊇ ⊢Δ
                  (irrelevanceTerm ⊩wk-ρ-A₁ (⊩wk-A₁ ρ⊇ ⊢Δ) ⊩t′)
              ⊩wk-ρ⇑-B₁[t]′ = emb-≤-⊩ l′≤l ⊩wk-ρ⇑-B₁[t]
          in
            ⊩wk-ρ⇑-B₁[t]′
          , wf-⊩≡
              (wk-ρ⇑-B₂≡wk-ρ⇑-B₂ $
               refl-⊩≡∷ (conv-⊩∷ wk-ρ-A₁≡wk-ρ-A₂ ⊩t))
              .proj₁
          , irrelevanceEq ⊩wk-ρ⇑-B₁[t] ⊩wk-ρ⇑-B₁[t]′
              (wk-B₁≡wk-B₂ ρ⊇ ⊢Δ $
               irrelevanceTerm ⊩wk-ρ-A₁ (⊩wk-A₁ ρ⊇ ⊢Δ) ⊩t′) }}

    lemma₂ :
      (⊩ΠΣ₁ : Γ ⊩⟨ l′ ⟩B⟨ BM b p q ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) →
      Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ →
      (∀ {m} {ρ : Wk m n} {Δ : Con Term m} →
       ρ ∷ Δ ⊇ Γ → ⊢ Δ →
       Δ ⊩⟨ l ⟩ wk ρ A₁ ≡ wk ρ A₂ ×
       (∀ {t} →
        Δ ⊩⟨ l ⟩ t ∷ wk ρ A₁ →
        Δ ⊩⟨ l ⟩ wk (lift ρ) B₁ [ t ]₀ ≡ wk (lift ρ) B₂ [ t ]₀)) →
      Γ ⊩⟨ l′ ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ /
        B-intr _ ⊩ΠΣ₁
    lemma₂ (emb ≤′-refl ⊩ΠΣ₁) ⊩ΠΣ₂ rest = lemma₂ ⊩ΠΣ₁ ⊩ΠΣ₂ rest
    lemma₂ (emb (≤′-step l<) ⊩ΠΣ₁) ⊩ΠΣ₂ rest = lemma₂ (emb l< ⊩ΠΣ₁) ⊩ΠΣ₂ rest
    lemma₂
      (noemb ⊩ΠΣ₁@(Bᵣ _ _ ⇒*ΠΣ₁ ⊢A₁ _ _ ⊩wk-A ⊩wk-B _ ok)) ⊩ΠΣ₂ rest =
      case extractMaybeEmb′ (B-elim _ ⊩ΠΣ₂) of λ
        (_ , _ , Bᵣ _ _ ⇒*ΠΣ₂ ⊢A₂ ⊢B₂ _ _ _ _ _) →
      case B-PE-injectivity _ _ $ whnfRed* (red ⇒*ΠΣ₁) ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
      case B-PE-injectivity _ _ $ whnfRed* (red ⇒*ΠΣ₂) ΠΣₙ of λ {
        (PE.refl , PE.refl , _) →
      case wf ⊢A₁ of λ
        ⊢Γ →
      case PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wk-id _) (wk-id _) $
           rest TW.id ⊢Γ .proj₁ of λ
        A₁≡A₂ →
      case ⊢Γ ∙ ⊢A₁ of λ
        ⊢Γ∙A₁ →
      case var ⊢Γ∙A₁ here of λ
        ⊢x0 →
      case PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wkSingleSubstId _)
             (wkSingleSubstId _) $
           rest (TW.step TW.id) ⊢Γ∙A₁ .proj₂ $
           neutral-⊩∷ (W.wk (TW.step TW.id) ⊢Γ∙A₁ (wf-⊩≡ A₁≡A₂ .proj₁))
             (var _) ⊢x0 (~-var ⊢x0) of λ
        B₁≡B₂ →
      _ ⊩⟨ _ ⟩ _ ≡ _ / Bᵣ _ ⊩ΠΣ₁ ∋
      B₌ _ _ (id (ΠΣⱼ ⊢A₂ ⊢B₂ ok))
        (≅-ΠΣ-cong ⊢A₁ (escape-⊩≡ A₁≡A₂) (escape-⊩≡ B₁≡B₂) ok)
        (λ ρ⊇ ⊢Δ → ⊩≡→⊩≡/ (⊩wk-A ρ⊇ ⊢Δ) (rest ρ⊇ ⊢Δ .proj₁))
        (λ ρ⊇ ⊢Δ ⊩t →
           case rest ρ⊇ ⊢Δ of λ
             (wk-ρ-A₁≡wk-ρ-A₂ , wk-ρ⇑-B₁≡wk-ρ⇑-B₂) →
           case wf-⊩≡ wk-ρ-A₁≡wk-ρ-A₂ .proj₁ of λ
             ⊩wk-ρ-A₁ →
           ⊩≡→⊩≡/ (⊩wk-B ρ⊇ ⊢Δ ⊩t) $
           wk-ρ⇑-B₁≡wk-ρ⇑-B₂
             ( ⊩wk-ρ-A₁
             , irrelevanceTerm (⊩wk-A ρ⊇ ⊢Δ) ⊩wk-ρ-A₁ ⊩t
             )) }}

opaque

  -- A variant of ⊩ΠΣ≡ΠΣ⇔.

  ⊩ΠΣ≡ΠΣ→ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ →
    ΠΣ-allowed b p q × Γ ⊩⟨ l ⟩ A₁ ≡ A₂ × Γ ∙ A₁ ⊩⟨ l ⟩ B₁ ≡ B₂
  ⊩ΠΣ≡ΠΣ→ ΠΣ≡ΠΣ =
    case ⊩ΠΣ≡ΠΣ⇔ .proj₁ ΠΣ≡ΠΣ of λ
      (⊩ΠΣ₁ , _ , rest) →
    case ⊩ΠΣ⇔ .proj₁ ⊩ΠΣ₁ of λ
      (ok , ⊢Γ , _) →
    case rest TW.id ⊢Γ of λ
      (wk-id-A₁≡wk-id-A₂ , _) →
    case PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wk-id _) (wk-id _)
           wk-id-A₁≡wk-id-A₂ of λ
      A₁≡A₂ →
    case rest (TW.step TW.id)
           (⊢→⊢∙ $ escape-⊩ $ wf-⊩≡ A₁≡A₂ .proj₁) of λ
      (wk₁-A₁≡wk₁-A₂ , wk-lift-step-id-B₁[]₀≡wk-lift-step-id-B₂[]₀) →
      ok , A₁≡A₂
    , PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (wkSingleSubstId _) (wkSingleSubstId _)
        (wk-lift-step-id-B₁[]₀≡wk-lift-step-id-B₂[]₀ $
         ⊩var here (wf-⊩≡ wk₁-A₁≡wk₁-A₂ .proj₁))

-- See also ⊩ᵛΠΣ⇔ below.

------------------------------------------------------------------------
-- Some substitution lemmas

opaque

  -- A substitution lemma for _⊩⟨_⟩_≡_.

  ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ →
    Γ ⊩⟨ l′ ⟩ t₁ ≡ t₂ ∷ A₁ →
    Γ ⊩⟨ l ⟩ B₁ [ t₁ ]₀ ≡ B₂ [ t₂ ]₀
  ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ {B₁} {B₂} {t₁} {t₂} ΠΣ≡ΠΣ t₁≡t₂ =
    case ⊩ΠΣ≡ΠΣ⇔ .proj₁ ΠΣ≡ΠΣ of λ
      (⊩ΠΣ₁ , _ , rest) →
    case ⊩ΠΣ→ ⊩ΠΣ₁ of λ
      (_ , ⊩A₁ , _) →
    case ⊩ΠΣ⇔ .proj₁ ⊩ΠΣ₁ of λ
      (_ , ⊢Γ , rest₁) →
    B₁ [ t₁ ]₀  ≡⟨ PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁) $
                   rest₁ TW.id ⊢Γ .proj₂ $
                   PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (PE.sym $ wk-id _) $
                   level-⊩≡∷ ⊩A₁ t₁≡t₂ ⟩⊩
    B₁ [ t₂ ]₀  ≡⟨ PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₁)
                     (PE.cong _[ _ ]₀ $ wk-lift-id B₂) $
                   rest TW.id ⊢Γ .proj₂ $
                   PE.subst (_⊩⟨_⟩_∷_ _ _ _) (PE.sym $ wk-id _) $
                   level-⊩∷ ⊩A₁ $
                   wf-⊩≡∷ t₁≡t₂ .proj₂ ⟩⊩∎
    B₂ [ t₂ ]₀  ∎

opaque

  -- A substitution lemma for _⊩⟨_⟩_.

  ⊩ΠΣ→⊩∷→⊩[]₀ :
    Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
    Γ ⊩⟨ l′ ⟩ t ∷ A →
    Γ ⊩⟨ l ⟩ B [ t ]₀
  ⊩ΠΣ→⊩∷→⊩[]₀ ⊩ΠΣ ⊩t =
    wf-⊩≡ (⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (refl-⊩≡ ⊩ΠΣ) (refl-⊩≡∷ ⊩t)) .proj₁

------------------------------------------------------------------------
-- Validity of Π and Σ, seen as type formers

opaque

  -- Reducibility for Π and Σ, seen as type formers.

  ⊩ΠΣ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Δ ⊩ˢ σ ∷ Γ →
    Δ ⊩⟨ l ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A ▹ B) [ σ ]
  ⊩ΠΣ {A} {B} ok ⊩A ⊩B ⊩σ =
    ⊩ΠΣ⇔ .proj₂
      ( ok
      , escape-⊩ˢ∷ ⊩σ .proj₁
      , λ ρ⊇ ⊢Η →
            PE.subst (_⊩⟨_⟩_ _ _) (PE.sym $ wk-subst A)
              (⊩ᵛ→⊩ˢ∷→⊩[] ⊩A $ ⊩ˢ∷-•ₛ ⊢Η ρ⊇ ⊩σ)
          , λ t≡u →
              PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                (PE.sym $ singleSubstWkComp _ _ B)
                (PE.sym $ singleSubstWkComp _ _ B) $
              ⊩ᵛ⇔ .proj₁ ⊩B .proj₂ $
              ⊩ˢ≡∷∙⇔ .proj₂
                ( ( _ , ⊩A
                  , PE.subst (_⊩⟨_⟩_≡_∷_ _ _ _ _) (wk-subst A) t≡u
                  )
                , refl-⊩ˢ≡∷ (⊩ˢ∷-•ₛ ⊢Η ρ⊇ ⊩σ)
                )
      )

opaque

  -- Reducibility of equality between Π and Π or Σ and Σ, seen as type
  -- formers.

  ⊩ΠΣ≡ΠΣ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) [ σ₁ ] ≡
      (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂) [ σ₂ ]
  ⊩ΠΣ≡ΠΣ {A₁} {A₂} {B₁} {B₂} ok A₁≡A₂ B₁≡B₂ σ₁≡σ₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wf-⊩ᵛ≡ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂) →
    case conv-∙-⊩ᵛ A₁≡A₂ ⊩B₂ of λ
      ⊩B₂ →
    case wf-⊩ˢ≡∷ σ₁≡σ₂ of λ
      (⊩σ₁ , ⊩σ₂) →
    ⊩ΠΣ≡ΠΣ⇔ .proj₂
      ( ⊩ΠΣ ok ⊩A₁ ⊩B₁ ⊩σ₁
      , ⊩ΠΣ ok ⊩A₂ ⊩B₂ ⊩σ₂
      , λ ρ⊇ ⊢Η →
            PE.subst₂ (_⊩⟨_⟩_≡_ _ _) (PE.sym $ wk-subst A₁)
              (PE.sym $ wk-subst A₂)
              (⊩ᵛ≡⇔′ .proj₁ A₁≡A₂ .proj₂ .proj₂ $
               ⊩ˢ≡∷-•ₛ ⊢Η ρ⊇ σ₁≡σ₂)
          , λ ⊩t →
              PE.subst₂ (_⊩⟨_⟩_≡_ _ _)
                (PE.sym $ singleSubstWkComp _ _ B₁)
                (PE.sym $ singleSubstWkComp _ _ B₂) $
              ⊩ᵛ≡⇔′ .proj₁ B₁≡B₂ .proj₂ .proj₂ $
              ⊩ˢ≡∷∙⇔ .proj₂
                ( ( _ , ⊩A₁
                  , refl-⊩≡∷
                      (PE.subst (_⊩⟨_⟩_∷_ _ _ _) (wk-subst A₁) ⊩t)
                  )
                , ⊩ˢ≡∷-•ₛ ⊢Η ρ⊇ σ₁≡σ₂
                )
      )

opaque

  -- Validity of Π and Σ, seen as type formers.

  ΠΣᵛ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A →
    Γ ∙ A ⊩ᵛ⟨ l ⟩ B →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B
  ΠΣᵛ ok ⊩A ⊩B =
    ⊩ᵛ⇔ .proj₂
      ( wf-⊩ᵛ ⊩A
      , ⊩ΠΣ≡ΠΣ ok (refl-⊩ᵛ≡ ⊩A) (refl-⊩ᵛ≡ ⊩B)
      )

opaque

  -- Validity of equality preservation for Π and Σ, seen as type
  -- formers.

  ΠΣ-congᵛ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ →
    Γ ∙ A₁ ⊩ᵛ⟨ l ⟩ B₁ ≡ B₂ →
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂
  ΠΣ-congᵛ ok A₁≡A₂ B₁≡B₂ =
    case wf-⊩ᵛ≡ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wf-⊩ᵛ≡ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂) →
    case conv-∙-⊩ᵛ A₁≡A₂ ⊩B₂ of λ
      ⊩B₂ →
    ⊩ᵛ≡⇔ .proj₂
      ( ΠΣᵛ ok ⊩A₁ ⊩B₁
      , ΠΣᵛ ok ⊩A₂ ⊩B₂
      , ⊩ΠΣ≡ΠΣ ok A₁≡A₂ B₁≡B₂ ∘→ refl-⊩ˢ≡∷
      )

opaque

  -- A characterisation lemma for _⊩ᵛ⟨_⟩_.

  ⊩ᵛΠΣ⇔ :
    Γ ⊩ᵛ⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ⇔
    (ΠΣ-allowed b p q × Γ ⊩ᵛ⟨ l ⟩ A × Γ ∙ A ⊩ᵛ⟨ l ⟩ B)
  ⊩ᵛΠΣ⇔ {B} =
      (λ ⊩ΠΣAB →
         case ⊩ᵛ⇔ .proj₁ ⊩ΠΣAB of λ
           (⊩Γ , ΠΣAB≡ΠΣAB) →
         case ⊩ᵛ⇔ .proj₂
                (⊩Γ , proj₁ ∘→ proj₂ ∘→ ⊩ΠΣ≡ΠΣ→ ∘→ ΠΣAB≡ΠΣAB) of λ
           ⊩A →
           ⊩ΠΣ⇔ .proj₁
             (wf-⊩≡ (ΠΣAB≡ΠΣAB (refl-⊩ˢ≡∷ $ ⊩ˢ∷-idSubst ⊩Γ)) .proj₁)
             .proj₁
         , ⊩A
         , ⊩ᵛ⇔ .proj₂
             ( ⊩ᵛ-∙-intro ⊩A
             , λ {_ _} {σ₁ = σ₁} {σ₂ = σ₂} σ₁≡σ₂ →
                 case ⊩ˢ≡∷∙⇔ .proj₁ σ₁≡σ₂ of λ
                   ((_ , _ , head-σ₁≡head-σ₂) , tail-σ₁≡tail-σ₂) →
                 B [ σ₁ ]                             ≡˘⟨ substVar-to-subst consSubst-η B ⟩⊩≡
                 B [ consSubst (tail σ₁) (head σ₁) ]  ≡˘⟨ singleSubstComp _ _ B ⟩⊩≡
                 B [ tail σ₁ ⇑ ] [ head σ₁ ]₀         ≡⟨ ⊩ΠΣ≡ΠΣ→⊩≡∷→⊩[]₀≡[]₀ (ΠΣAB≡ΠΣAB tail-σ₁≡tail-σ₂) head-σ₁≡head-σ₂ ⟩⊩∎≡
                 B [ tail σ₂ ⇑ ] [ head σ₂ ]₀         ≡⟨ singleSubstComp _ _ B ⟩
                 B [ consSubst (tail σ₂) (head σ₂) ]  ≡⟨ substVar-to-subst consSubst-η B ⟩
                 B [ σ₂ ]                             ∎
             ))
    , (λ (ok , ⊩A , ⊩B) → ΠΣᵛ ok ⊩A ⊩B)
    where
    open Tools.Reasoning.PropositionalEquality

------------------------------------------------------------------------
-- Validity of Π and Σ, seen as term formers

-- opaque

  -- Reducibility of equality between Π and Π or Σ and Σ, seen as term
  -- formers.

  ⊩ΠΣ≡ΠΣ∷U :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ ∷ U l″ →
    Γ ∙ A₁ ⊩ᵛ⟨ l′ ⟩ B₁ ≡ B₂ ∷ U l‴ →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ →
    Δ ⊩⟨ l ⊔T l′ ⟩ (ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁) [ σ₁ ] ≡
      (ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂) [ σ₂ ] ∷ U (l″ ⊔T l‴)
  ⊩ΠΣ≡ΠΣ∷U {l″ = l″} {l‴ = l‴} ok A₁≡A₂∷U B₁≡B₂∷U σ₁≡σ₂ =
    case ⊩∷U⇔ .proj₁ (⊩ᵛ∷→⊩∷ (wf-⊩ᵛ≡∷ A₁≡A₂∷U .proj₁)) of λ
      (l″<l , _ , _ , _) →
    case ⊩∷U⇔ .proj₁ (⊩ᵛ∷→⊩∷ (wf-⊩ᵛ≡∷ B₁≡B₂∷U .proj₁)) of λ
      (l‴<l′ , _ , _ , _) →
    case ⊩ᵛ≡∷U→⊩ᵛ≡ A₁≡A₂∷U of λ
      A₁≡A₂ → 
    case ⊩ᵛ≡∷U→⊩ᵛ≡ B₁≡B₂∷U of λ
      B₁≡B₂ →
    case ⊩ᵛ≡∷⇔′ .proj₁ A₁≡A₂∷U .proj₂ .proj₂ σ₁≡σ₂ of λ
      A₁[σ₁]≡A₂[σ₂]∷U →
    case ⊩ᵛ≡∷→⊩ˢ≡∷→⊩[⇑]≡[⇑]∷ B₁≡B₂∷U σ₁≡σ₂ of λ
      B₁[σ₁⇑]≡B₂[σ₂⇑]∷U →
    case wf-⊩≡∷ A₁[σ₁]≡A₂[σ₂]∷U of λ
      (⊩A₁[σ₁] , ⊩A₂[σ₂]) →
    case wf-⊩≡∷ B₁[σ₁⇑]≡B₂[σ₂⇑]∷U of λ
      (⊩B₁[σ₁] , _) →
    case ⊩ᵛ∷→⊩ˢ∷→⊩[⇑]∷ (conv-∙-⊩ᵛ∷ A₁≡A₂ (wf-⊩ᵛ≡∷ B₁≡B₂∷U .proj₂)) $
         wf-⊩ˢ≡∷ σ₁≡σ₂ .proj₂ of λ
      ⊩B₂[σ₂] →
    case escape-⊩∷ ⊩A₁[σ₁] of λ
      ⊢A₁[σ₁] →
    case escape-⊩∷ ⊩B₁[σ₁] of λ
      ⊢B₁[σ₁] →
     Type→⊩≡∷U⇔ ΠΣₙ ΠΣₙ .proj₂
     ({!!} , ⊩ᵛ≡⇔′ .proj₁
        (ΠΣ-congᵛ ok
        (emb-⊩ᵛ≡ (m≤n⇒m≤n⊔oT l‴ ≤′-refl) A₁≡A₂)
        (emb-⊩ᵛ≡ (m≤n⇒m≤o⊔nT l″ ≤′-refl) B₁≡B₂))
        .proj₂ .proj₂ σ₁≡σ₂
     , ΠΣⱼ ⊢A₁[σ₁] ⊢B₁[σ₁] ok
     , ΠΣⱼ (escape-⊩∷ ⊩A₂[σ₂]) (escape-⊩∷ ⊩B₂[σ₂]) ok ,
     ≅ₜ-ΠΣ-cong (univ ⊢A₁[σ₁]) (escape-⊩≡∷ A₁[σ₁]≡A₂[σ₂]∷U)
      (escape-⊩≡∷ B₁[σ₁⇑]≡B₂[σ₂⇑]∷U) ok)

opaque

  -- Validity of Π and Σ, seen as term formers.

  ΠΣᵗᵛ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A ∷ U l″ →
    Γ ∙ A ⊩ᵛ⟨ l′ ⟩ B ∷ U l‴ →
    Γ ⊩ᵛ⟨ l ⊔T l′ ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B ∷ U (l″ ⊔T l‴)
  ΠΣᵗᵛ ok ⊩A ⊩B =
    ⊩ᵛ∷⇔ .proj₂
      ( ⊩ᵛ∷⇔ .proj₁ {! ⊩A !} .proj₁
      , ⊩ΠΣ≡ΠΣ∷U ok (refl-⊩ᵛ≡∷ ⊩A) (refl-⊩ᵛ≡∷ ⊩B)
      )

opaque

  -- Validity of equality preservation for Π and Σ, seen as term
  -- formers.

  ΠΣ-congᵗᵛ :
    ΠΣ-allowed b p q →
    Γ ⊩ᵛ⟨ l ⟩ A₁ ≡ A₂ ∷ U l″ →
    Γ ∙ A₁ ⊩ᵛ⟨ l′ ⟩ B₁ ≡ B₂ ∷ U l‴ →
    Γ ⊩ᵛ⟨ l ⊔T l′ ⟩ ΠΣ⟨ b ⟩ p , q ▷ A₁ ▹ B₁ ≡ ΠΣ⟨ b ⟩ p , q ▷ A₂ ▹ B₂ ∷ U (l″ ⊔T l‴)
  ΠΣ-congᵗᵛ {l} ok A₁≡A₂ B₁≡B₂ =
    case wf-⊩ᵛ≡∷ A₁≡A₂ of λ
      (⊩A₁ , ⊩A₂) →
    case wf-⊩ᵛ≡∷ B₁≡B₂ of λ
      (⊩B₁ , ⊩B₂) →
    case conv-∙-⊩ᵛ∷ (⊩ᵛ≡∷U→⊩ᵛ≡ A₁≡A₂) ⊩B₂ of λ
      ⊩B₂ →
    ⊩ᵛ≡∷⇔ .proj₂
      ( ΠΣᵗᵛ ok ⊩A₁ ⊩B₁
      , ΠΣᵗᵛ ok ⊩A₂ ⊩B₂
      , ⊩ΠΣ≡ΠΣ∷U ok A₁≡A₂ B₁≡B₂ ∘→ refl-⊩ˢ≡∷
      )
