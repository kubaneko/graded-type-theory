------------------------------------------------------------------------
-- Validity of the universe type.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Substitution.Introductions.Universe
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.Untyped M
open import Definition.Untyped.Neutral M type-variant
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.ShapeView R
open import Definition.LogicalRelation.Substitution R

open import Tools.Function
open import Tools.Nat using (Nat; ≤′-step; ≤′-refl; 1+)
open import Tools.Product
open import Tools.Empty
import Tools.PropositionalEquality as PE

private
  variable
    n       : Nat
    Γ       : Con Term n
    A B     : Term n
    l l′ l″ : TypeLevel
    k       : LogRelKit

------------------------------------------------------------------------
-- Some characterisation lemmas

lem : {l< : l′ < l} → {D : Γ ⊢ U l″ :⇒*: U l′} →  (⊩U : Γ ⊩⟨ l ⟩U U l″) → ⊩U PE.≡ noemb (Uᵣ l′ l< D) → l″ PE.≡ l′
lem (noemb (Uᵣ l′ l< [ ⊢A , ⊢B , id x ])) PE.refl = PE.refl
lem (noemb (Uᵣ l′ l< [ ⊢A , ⊢B , x ⇨ D ])) e = ⊥-elim (whnfRed x Uₙ)

opaque

  -- A characterisation lemma for _⊩⟨_⟩_.

  ⊩U⇔ :
    Γ ⊩⟨ l ⟩ U l″ ⇔
    ((l″ < l) × ⊢ Γ)
  ⊩U⇔ =
      (λ ⊩U → lemma (U-elim (id (escape ⊩U)) ⊩U))
    , (λ (l′<l , ⊢Γ) →
        Uᵣ (Uᵣ _ l′<l (idRed:*: (Uⱼ ⊢Γ))))
    where
    lemma :
      Γ ⊩⟨ l ⟩U U l″ →
      (l″ < l) × ⊢ Γ
    lemma ⊩U@(noemb (Uᵣ l′ l′<l ([ ⊢A , ⊢B , D ]))) =
      case lem ⊩U PE.refl of λ {
         PE.refl → l′<l , wf ⊢A
         }
    lemma (emb ≤′-refl ⊩U) =
      case lemma ⊩U of λ where
         (l< , ⊢Γ) → ≤′-step l< , ⊢Γ
    lemma (emb (≤′-step s) ⊩U) =
      case lemma (emb s ⊩U) of λ where
         (l< , ⊢Γ) → ≤′-step l< , ⊢Γ

opaque
  unfolding _⊩⟨_⟩_∷_

  -- A characterisation lemma for _⊩⟨_⟩_∷_.

  ⊩∷U⇔ :
    Γ ⊩⟨ l ⟩ A ∷ U l″ ⇔
    (l″ < l × Γ ⊩⟨ l″ ⟩ A ×
      (∃ λ B → Γ ⊢ A :⇒*: B ∷ U l″ × Type B × Γ ⊢ B ≅ B ∷ U l″))
  ⊩∷U⇔ =
      (λ (⊩U , ⊩A) →
         lemma (U-elim (id (escape ⊩U)) ⊩U) (irrelevanceTerm ⊩U (U-intr (U-elim (id (escape ⊩U)) ⊩U)) ⊩A))
    , (λ (l′<l , ⊩A , B , A⇒*B , B-type , B≅B) →
         Uᵣ (Uᵣ _ l′<l (idRed:*: (Uⱼ (wfTerm (⊢t-redₜ A⇒*B)))))
         , (Uₜ B A⇒*B B-type B≅B
             (PE.subst (λ k → LogRelKit._⊩_ k _ _) (kit≡kit′ l′<l) ⊩A)))
    where
    lemma :
      (⊩U : Γ ⊩⟨ l ⟩U U l″) →
      Γ ⊩⟨ l ⟩ A ∷ U l″ / U-intr ⊩U →
      (l″ < l × Γ ⊩⟨ l″ ⟩ A ×
      (∃ λ B → Γ ⊢ A :⇒*: B ∷ U l″ × Type B × Γ ⊢ B ≅ B ∷ U l″))
    lemma ⊩U@(noemb (Uᵣ l′ l′<l _)) (Uₜ B A⇒*B B-type B≅B ⊩A) =
      case lem ⊩U PE.refl of λ {
         PE.refl →
              l′<l
              , PE.subst (λ k → LogRelKit._⊩_ k _ _) (PE.sym (kit≡kit′ l′<l)) ⊩A
              , B , A⇒*B , B-type , B≅B
         }
    lemma (emb ≤′-refl ⊩U) ⊩A =
        case lemma ⊩U ⊩A of λ where
            (l< , ⊩A′ , B , D , B-type , B≡B) → ≤′-step l< , ⊩A′ , B , D , B-type , B≡B
    lemma (emb (≤′-step 0<1) ⊩U) ⊩A =
        case lemma (emb 0<1 ⊩U) ⊩A of λ where
            (l< , ⊩A′ , B , D , B-type , B≡B) → ≤′-step l< , ⊩A′ , B , D , B-type , B≡B

opaque

  -- A variant of ⊩∷U⇔.

  Type→⊩∷U⇔ : {l″ : TypeLevel} →
    Type A →
    (Γ ⊩⟨ l ⟩ A ∷ U l″ ⇔
    ((l″ < l) × (Γ ⊩⟨ l″ ⟩ A) ×
     Γ ⊢ A ∷ U l″ ×
     Γ ⊢ A ≅ A ∷ U l″))
  Type→⊩∷U⇔ {A} {Γ} {l} {l″ = l″} A-type =
    (Γ ⊩⟨ l ⟩ A ∷ U l″)                               ⇔⟨ ⊩∷U⇔ ⟩

    (l″ < l × Γ ⊩⟨ l″ ⟩ A ×
    (∃ λ B → Γ ⊢ A :⇒*: B ∷ U l″ × Type B × Γ ⊢ B ≅ B ∷ U l″)) ⇔⟨ id⇔ ×-cong-⇔ id⇔ ×-cong-⇔
                                                                ( (λ (_ , A⇒*B , _ , B≅B) →
                                                                    case whnfRed*Term (redₜ A⇒*B) (typeWhnf A-type) of λ {
                                                                      PE.refl →
                                                                    ⊢t-redₜ A⇒*B , B≅B })
                                                                , (λ (⊢A , A≅A) → _ , idRedTerm:*: ⊢A , A-type , A≅A)
                                                                )
                                                          ⟩

    ((l″  < l) × (Γ ⊩⟨ l″ ⟩ A) ×
     Γ ⊢ A ∷ U l″ ×
     Γ ⊢ A ≅ A ∷ U l″)                                         □⇔

opaque
  unfolding _⊩⟨_⟩_≡_

  -- A characterisation lemma for _⊩⟨_⟩_≡_.

  ⊩U≡⇔ :
    Γ ⊩⟨ l ⟩ U l″ ≡ A ⇔
    (l″ < l × ⊢ Γ × Γ ⊢ A :⇒*: U l″ × Γ ⊩⟨ l ⟩ A)
  ⊩U≡⇔ =
      (λ (⊩U , ⊩A , U≡A) →
         lemma (U-elim (id (escape ⊩U)) ⊩U)
         (irrelevanceEq ⊩U (U-intr (U-elim (id (escape ⊩U)) ⊩U)) U≡A) ⊩A)
    , (λ where
         (l′<l , ⊢Γ , D , ⊩A) →
           let ⊩U = Uᵣ (Uᵣ _ l′<l (idRed:*: (Uⱼ ⊢Γ))) in
           ⊩U , ⊩A , D)
    where
    lemma2 :
      (⊩U : Γ ⊩⟨ l ⟩U U l″) →
      Γ ⊩⟨ l ⟩ U l″ ≡ A / U-intr ⊩U →
      (l″ < l × ⊢ Γ × Γ ⊢ A :⇒*: U l″)
    lemma2 ⊩U@(noemb (Uᵣ l′ l′<l ([ ⊢A , ⊢U , d ]))) A≡U =
      case lem ⊩U PE.refl of λ {
         PE.refl →
              l′<l , wf ⊢A , A≡U
         }
    lemma2 (emb ≤′-refl ⊩U) A≡U =
      case lemma2 ⊩U A≡U of λ where
        (l< , ⊢Γ , D) → ≤′-step l< , ⊢Γ , D
    lemma2 (emb (≤′-step l<) ⊩U) A≡U =
      case lemma2 (emb l< ⊩U) A≡U of λ where
        (l< , ⊢Γ , D) → ≤′-step l< , ⊢Γ , D
    lemma :
      (⊩U : Γ ⊩⟨ l ⟩U U l″) →
      Γ ⊩⟨ l ⟩ U l″ ≡ A / U-intr ⊩U →
      (Γ ⊩⟨ l ⟩ A) →
      (l″ < l × ⊢ Γ × Γ ⊢ A :⇒*: U l″ × Γ ⊩⟨ l ⟩ A)
    lemma ⊩U@(noemb (Uᵣ l′ l′<l ([ ⊢A , ⊢U , d ]))) A≡U ⊩A =
      case lem ⊩U PE.refl of λ {
         PE.refl →
              l′<l , wf ⊢A , A≡U , ⊩A
         }
    lemma (emb l< ⊩U) A≡U ⊩A =
      case lemma2 (emb l< ⊩U) A≡U of λ where
        (l< , ⊢Γ , D) → l< , ⊢Γ , D , ⊩A

opaque
  unfolding _⊩⟨_⟩_≡_ _⊩⟨_⟩_≡_∷_

  -- A characterisation lemma for _⊩⟨_⟩_≡_∷_.

  ⊩≡∷U⇔ :
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U l″ ⇔
    (∃ λ (l′<l : l″ < l) → Γ ⊩⟨ l″ ⟩ A ≡ B ×
     (∃₂ λ A′ B′ →
      Γ ⊢ A :⇒*: A′ ∷ U l″ ×
      Γ ⊢ B :⇒*: B′ ∷ U l″ ×
      Type A′ ×
      Type B′ ×
      Γ ⊢ A′ ≅ B′ ∷ U l″))
  ⊩≡∷U⇔ =
      (λ (⊩U , _ , _ , A≡B) →
          lemma₃ (U-elim (id (escape ⊩U)) ⊩U)
           (irrelevanceEqTerm ⊩U (U-intr (U-elim (id (escape ⊩U)) ⊩U)) A≡B) )
    , (λ (l′<l , (⊩A , ⊩B , A≡B) , A′ , B′
         , (DA , DB , A′-type , B′-type , A′≅B′)) →
         let ⊩A =
               PE.subst (λ k → LogRelKit._⊩_ k _ _) (kit≡kit′ l′<l) ⊩A
             ⊩B =
               PE.subst (λ k → LogRelKit._⊩_ k _ _) (kit≡kit′ l′<l) ⊩B
         in
         Uᵣ (Uᵣ _ l′<l (idRed:*: (Uⱼ (wfTerm (⊢t-redₜ DA)))))
         , Uₜ A′ DA A′-type (≅ₜ-trans A′≅B′ (≅ₜ-sym A′≅B′)) ⊩A
         , Uₜ B′ DB B′-type (≅ₜ-trans (≅ₜ-sym A′≅B′) A′≅B′) ⊩B
         , Uₜ₌ A′ B′ DA DB A′-type B′-type A′≅B′ ⊩A ⊩B
             (lemma₂ {l′<l = l′<l} (kit≡kit′ l′<l) A≡B))
    where
    lemma₁ :
      {l′<l : l′ < l}
      {⊩A : LogRelKit._⊩_ (kit′ l′<l) Γ A}
      (eq : k PE.≡ kit′ l′<l) →
      LogRelKit._⊩_≡_/_ (kit′ l′<l) Γ A B ⊩A →
      LogRelKit._⊩_≡_/_ k Γ A B
        (PE.subst (λ k → LogRelKit._⊩_ k _ _) (PE.sym eq) ⊩A)
    lemma₁ PE.refl A≡B = A≡B

    lemma₂ :
      {l′<l : l′ < l}
      {⊩A : LogRelKit._⊩_ k Γ A}
      (eq : k PE.≡ kit′ l′<l) →
      LogRelKit._⊩_≡_/_ k Γ A B ⊩A →
      LogRelKit._⊩_≡_/_ (kit′ l′<l) Γ A B
        (PE.subst (λ k → LogRelKit._⊩_ k _ _) eq ⊩A)
    lemma₂ PE.refl A≡B = A≡B

    lemma₃ :
      (⊩U : Γ ⊩⟨ l ⟩U U l″) →
      Γ ⊩⟨ l ⟩ A ≡ B ∷ U l″ / U-intr ⊩U →
      (∃ λ (l′<l : l″ < l) → Γ ⊩⟨ l″ ⟩ A ≡ B ×
      (∃₂ λ A′ B′ →
       Γ ⊢ A :⇒*: A′ ∷ U l″ ×
       Γ ⊢ B :⇒*: B′ ∷ U l″ ×
       Type A′ ×
       Type B′ ×
       Γ ⊢ A′ ≅ B′ ∷ U l″))
    lemma₃
      ⊩U@(noemb (Uᵣ l′ l′<l _))
      (Uₜ₌ A′ B′ A⇒*A′ B⇒*B′ A′-type B′-type A′≅B′ ⊩A ⊩B A≡B) =
        case lem ⊩U PE.refl of λ {
            PE.refl →
                (l′<l
                , ( PE.subst (λ k → LogRelKit._⊩_ k _ _)
                    (PE.sym (kit≡kit′ l′<l)) ⊩A
                , PE.subst (λ k → LogRelKit._⊩_ k _ _)
                    (PE.sym (kit≡kit′ l′<l)) ⊩B
                , lemma₁ {l′<l = l′<l} (kit≡kit′ l′<l) A≡B
                )
            , A′ , B′ , (A⇒*A′ , B⇒*B′ , A′-type , B′-type , A′≅B′)) 
            }
    lemma₃ (emb ≤′-refl ⊩U) A≡B =
      case lemma₃ ⊩U A≡B of λ where
        (l′<l , (⊩A , ⊩B , A≡B) , A′ , B′
         , (DA , DB , A′-type , B′-type , A′≅B′)) ->
         (≤′-step l′<l , (⊩A , ⊩B , A≡B) , A′ , B′
         , (DA , DB , A′-type , B′-type , A′≅B′))
    lemma₃ (emb (≤′-step l<) ⊩U) A≡B =
      case lemma₃ (emb l< ⊩U) A≡B of λ where
        (l′<l , (⊩A , ⊩B , A≡B) , A′ , B′
         , (DA , DB , A′-type , B′-type , A′≅B′)) ->
         (≤′-step l′<l , (⊩A , ⊩B , A≡B) , A′ , B′
         , (DA , DB , A′-type , B′-type , A′≅B′))

opaque

  -- A variant of ⊩≡∷U⇔.

  Type→⊩≡∷U⇔ :
    {l″ : TypeLevel} →
    Type A →
    Type B →
    Γ ⊩⟨ l ⟩ A ≡ B ∷ U l″ ⇔
    (∃ λ (l′<l : l″ < l) → (Γ ⊩⟨ l″ ⟩ A ≡ B) ×
     Γ ⊢ A ∷ U l″ ×
     Γ ⊢ B ∷ U l″ ×
     Γ ⊢ A ≅ B ∷ U l″)
  Type→⊩≡∷U⇔ {A} {B} {Γ} {l} {l″ = l″} A-type B-type =
    (Γ ⊩⟨ l ⟩ A ≡ B ∷ U l″)                           ⇔⟨ ⊩≡∷U⇔ ⟩

    (∃ λ (l′<l : l″ < l) → Γ ⊩⟨ l″ ⟩ A ≡ B ×
     (∃₂ λ A′ B′ →
      Γ ⊢ A :⇒*: A′ ∷ U l″ ×
      Γ ⊢ B :⇒*: B′ ∷ U l″ ×
      Type A′ ×
      Type B′ ×
      Γ ⊢ A′ ≅ B′ ∷ U l″))                            ⇔⟨ (λ ( l′<l , A≡B , A′ , B′ , (DA , DB , A′-type , B′-type , A′≅B′)) →
                                                       case whnfRed*Term (redₜ DA) (typeWhnf A-type) of λ {
                                                         PE.refl →
                                                       case whnfRed*Term (redₜ DB) (typeWhnf B-type) of λ {
                                                         PE.refl →
                                                       ( l′<l , A≡B , ⊢t-redₜ DA , ⊢t-redₜ DB , A′≅B′)}})
                                                  , (λ ( l′<l , A≡B , ⊢A , ⊢B , A≅B) →
                                                       ( l′<l , A≡B , _ , _ ,
                                                       (idRedTerm:*: ⊢A , idRedTerm:*: ⊢B ,
                                                       A-type , B-type , A≅B)))
                                                  ⟩
    (∃ λ (l′<l : l″ < l) → (Γ ⊩⟨ l″ ⟩ A ≡ B) ×
     Γ ⊢ A ∷ U l″ ×
     Γ ⊢ B ∷ U l″ ×
     Γ ⊢ A ≅ B ∷ U l″)                            □⇔

------------------------------------------------------------------------
-- Validity

opaque

  -- Validity of U.

  ⊩ᵛU : ⊩ᵛ Γ → Γ ⊩ᵛ⟨ 1+ l ⟩ U l
  ⊩ᵛU {Γ} {l = l} ⊩Γ =
    ⊩ᵛ⇔ .proj₂ (⊩Γ , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂}  →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ                                      →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
    ⊢ Δ                                                   →⟨ (λ ⊢Δ → ≤′-refl , ⊢Δ , idRed:*: (Uⱼ ⊢Δ)
                                                                      , ⊩U⇔ .proj₂ (≤′-refl , ⊢Δ)) ⟩
    (l < 1+ l × ⊢ Δ × Δ ⊢ U l :⇒*: U l × Δ ⊩⟨ 1+ l ⟩ U l) ⇔˘⟨ ⊩U≡⇔  ⟩→
    Δ ⊩⟨ 1+ l ⟩ U l ≡ U l                                 □
    )

opaque

  -- Validity of U.

  ⊩ᵛU< : ⊩ᵛ Γ → l < l′ → Γ ⊩ᵛ⟨ l′ ⟩ U l
  ⊩ᵛU< {Γ} {l = l} {l′ = l′} ⊩Γ l< =
    ⊩ᵛ⇔ .proj₂ (⊩Γ , λ {_} {Δ = Δ} {σ₁ = σ₁} {σ₂ = σ₂}  →
    Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ                                      →⟨ proj₁ ∘→ escape-⊩ˢ≡∷ ⟩
    ⊢ Δ                                                   →⟨ (λ ⊢Δ → l< , ⊢Δ , idRed:*: (Uⱼ ⊢Δ)
                                                                      , ⊩U⇔ .proj₂ (l< , ⊢Δ)) ⟩
    (l < l′ × ⊢ Δ × Δ ⊢ U l :⇒*: U l × Δ ⊩⟨ l′ ⟩ U l)     ⇔˘⟨ ⊩U≡⇔  ⟩→
    Δ ⊩⟨ l′ ⟩ U l ≡ U l                                   □
    )

-- TODO continue with this if needed
-- opaque
--   univInUniv : (1+ l < l′) → ([U] : Γ ⊩ᵛ⟨ l′ ⟩ U (1+ l)) → Γ ⊩ᵛ⟨ l′ ⟩ U l ∷ U (1+ l)
--   univInUniv {l = l} l< [U] = ⊩ᵛ∷⇔ .proj₂ ([U] , λ ⊩σ →
--     case escape-⊩ˢ∷ ⊩σ of λ
--       (⊢Δ , _) → (
--         let [U]′ =  Uᵣ (Uᵣ l ≤′-refl (idRed:*: (Uⱼ ⊢Δ)))
--         in (⊩∷U⇔ .proj₂ (l< , [U]′ ,
--         (U l , idRedTerm:*: (Uⱼ ⊢Δ) , Uₙ , ≅-Urefl ⊢Δ ))) ,
--         λ _ → Type→⊩≡∷U⇔ Uₙ Uₙ .proj₂
--           (l< , ⊩U≡⇔ .proj₂ (≤′-refl , ⊢Δ , idRed:*: (Uⱼ ⊢Δ) , [U]′)
--           , Uⱼ ⊢Δ , Uⱼ ⊢Δ , ≅-Urefl ⊢Δ)))

opaque

  -- Validity of one of the typing rules called univ.

  ⊩ᵛ∷U→⊩ᵛ :
    Γ ⊩ᵛ⟨ l ⟩ A ∷ U l″ →
    Γ ⊩ᵛ⟨ l″ ⟩ A
  ⊩ᵛ∷U→⊩ᵛ ⊩A∷U =
    -- TODO change
    case ⊩ᵛ∷⇔ .proj₁ ⊩A∷U of λ
      (⊩U , A≡A∷U) →
    emb-⊩ᵛ ≤′-refl $
    ⊩ᵛ⇔ .proj₂
      ( wf-⊩ᵛ ⊩U
      , λ σ₁≡σ₂ →
          case ⊩≡∷U⇔ .proj₁ $ A≡A∷U σ₁≡σ₂ of λ {
            (0<1 , ⊩A[σ₁]≡A[σ₂] , _) →
          ⊩A[σ₁]≡A[σ₂] }
      )

opaque

  -- Validity of another of the typing rules called univ.

  ⊩ᵛ≡∷U→⊩ᵛ≡ :
    Γ ⊩ᵛ⟨ l ⟩ A ≡ B ∷ U l″ →
    Γ ⊩ᵛ⟨ l″ ⟩ A ≡ B
  ⊩ᵛ≡∷U→⊩ᵛ≡ A≡B∷U =
    case ⊩ᵛ≡∷⇔ .proj₁ A≡B∷U of λ
      (⊩A∷U , ⊩B∷U , A≡B∷U) →
    ⊩ᵛ≡⇔ .proj₂
      ( ⊩ᵛ∷U→⊩ᵛ ⊩A∷U
      , ⊩ᵛ∷U→⊩ᵛ ⊩B∷U
      , λ ⊩σ →
          case ⊩≡∷U⇔ .proj₁ $ A≡B∷U ⊩σ of λ {
            (l< , A≡B , _) →
          emb-⊩≡ ≤′-refl A≡B }
      )

------------------------------------------------------------------------
-- Non-opaque validity lemmas

-- Validity of the universe type.
Uᵛ : ([Γ] : ⊩ᵛ Γ) → Γ ⊩ᵛ⟨ 1+ l ⟩ U l / [Γ]
Uᵛ {l = l} [Γ] = wrap λ ⊢Δ [σ] → Uᵣ′ l  ≤′-refl ([ Uⱼ ⊢Δ , Uⱼ ⊢Δ , id (Uⱼ ⊢Δ) ]) , λ x₁ x₂ → [ (Uⱼ ⊢Δ) , (Uⱼ ⊢Δ) , (id (Uⱼ ⊢Δ)) ]

-- Validity of the universe type.
Uᵛ< : ([Γ] : ⊩ᵛ Γ) → l < l′ → Γ ⊩ᵛ⟨ l′ ⟩ U l / [Γ]
Uᵛ< {l = l} [Γ] l< = wrap λ ⊢Δ [σ] → Uᵣ′ l  l< ([ Uⱼ ⊢Δ , Uⱼ ⊢Δ , id (Uⱼ ⊢Δ) ]) , λ x₁ x₂ → [ (Uⱼ ⊢Δ) , (Uⱼ ⊢Δ) , (id (Uⱼ ⊢Δ)) ]

-- Valid terms of type U are valid types.
univᵛ : ∀ {A l l′} ([Γ] : ⊩ᵛ Γ)
        ([U] : Γ ⊩ᵛ⟨ l ⟩ U l′ / [Γ])
      → Γ ⊩ᵛ⟨ l ⟩ A ∷ U l′ / [Γ] / [U]
      → Γ ⊩ᵛ⟨ l′ ⟩ A / [Γ]
univᵛ {l′ = l′} [Γ] [U] [A] = wrap λ ⊢Δ [σ] →
      let [A]₁ = univEq (proj₁ (unwrap [U] ⊢Δ [σ])) (proj₁ ([A] ⊢Δ [σ]))
  in  [A]₁ , (λ [σ′] [σ≡σ′] → univEqEq (proj₁ (unwrap [U] ⊢Δ [σ])) [A]₁
                                       ((proj₂ ([A] ⊢Δ [σ])) [σ′] [σ≡σ′]))

-- Valid term equality of type U is valid type equality.
univEqᵛ : ∀ {A B l l′ l″} ([Γ] : ⊩ᵛ Γ)
          ([U] : Γ ⊩ᵛ⟨ l′ ⟩ U l″ / [Γ])
          ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
        → Γ ⊩ᵛ⟨ l′ ⟩ A ≡ B ∷ U l″ / [Γ] / [U]
        → Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A]
univEqᵛ {A} [Γ] [U] [A] [t≡u] ⊢Δ [σ] =
  univEqEq (proj₁ (unwrap [U] ⊢Δ [σ])) (proj₁ (unwrap [A] ⊢Δ [σ])) ([t≡u] ⊢Δ [σ])
