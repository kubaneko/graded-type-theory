------------------------------------------------------------------------
-- The fundamental lemma of the logical relation for validity.
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Fundamental
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M
open import Definition.Untyped.Properties M

open import Definition.Typed R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Hidden R
open import Definition.LogicalRelation.Irrelevance R
open import Definition.LogicalRelation.Properties R
open import Definition.LogicalRelation.Substitution R
open import Definition.LogicalRelation.Substitution.Escape R
open import Definition.LogicalRelation.Substitution.Properties R
open import Definition.LogicalRelation.Substitution.Introductions R
import Definition.LogicalRelation.Substitution.Introductions.Erased R
  as Erased
import Definition.LogicalRelation.Substitution.Irrelevance R as S
import Definition.LogicalRelation.Substitution.Cumulativity R as C
open import Definition.LogicalRelation.Substitution.Weakening R

import Graded.Derived.Erased.Untyped 𝕄 as E

open import Tools.Function
open import Tools.Level
open import Tools.Product
open import Tools.Unit
open import Tools.Sum
open import Tools.Nat using (Nat; 1+; ≤′-refl; ≤′-step; m≤n⇒m≤n⊔o; m≤n⇒m≤o⊔n; ≤⇒≤′; ≤′⇒≤)
import Tools.PropositionalEquality as PE

private
  variable
    m n : Nat
    Γ : Con Term n
    Δ : Con Term m
    σ σ₁ σ₂ σ′ : Subst m n
    A A₁ A₂ B t t₁ t₂ u : Term _
    ⊩Γ : ⊩ᵛ _

opaque
  m≤n⇒m≤n⊔oT : {l l′ : TypeLevel} → (l″ : TypeLevel) → l ≤ l′ → l ≤ (l′ ⊔T l″)
  m≤n⇒m≤n⊔oT l l< = ≤⇒≤′ (m≤n⇒m≤n⊔o l (≤′⇒≤ l<))

  m≤n⇒m≤o⊔nT : {l l′ : TypeLevel} → (l″ : TypeLevel) → l ≤ l′ → l ≤ (l″ ⊔T l′)
  m≤n⇒m≤o⊔nT l l< = ≤⇒≤′ (m≤n⇒m≤o⊔n l (≤′⇒≤ l<))

  lem1 : (l′ l : TypeLevel) → (l′ PE.≡ (l′ ⊔T l)) ⊎ (l PE.≡ (l′ ⊔T l))
  lem1 0 l = inj₂ PE.refl
  lem1 (1+ l) 0 = inj₁ PE.refl
  lem1 (1+ l) (1+ l′) = case lem1 l l′ of λ {
             (inj₁ eq) -> inj₁ (PE.cong 1+ eq) ;
             (inj₂ eq) -> inj₂ (PE.cong 1+ eq)
          }

  univLift : {[Γ] : ⊩ᵛ Γ} → {l₁ l₂ l′ l″ : TypeLevel} → Γ ⊩ᵛ⟨ l₁ ⟩ U l′ / [Γ] → Γ ⊩ᵛ⟨ l₂ ⟩ U l″ / [Γ] → Γ ⊩ᵛ⟨ l₁ ⊔T l₂ ⟩ U (l′ ⊔T l″) / [Γ]
  univLift {[Γ]} {l₁} {l₂} {l′} {l″} [U₁] [U₂] = case lem1 l′ l″ of λ {
                (inj₁ eq) ->  C.cumul≤ _ ( m≤n⇒m≤n⊔oT  l₂ ≤′-refl) (PE.subst (λ x → _ ⊩ᵛ⟨ _ ⟩ U x / _) eq [U₁])  ;
                (inj₂ eq) ->  C.cumul≤ _ ( m≤n⇒m≤o⊔nT  l₁ ≤′-refl) (PE.subst (λ x → _ ⊩ᵛ⟨ _ ⟩ U x / _) eq [U₂])
           }

opaque
 unfolding _⊩ᵛ⟨_⟩_ _⊩ᵛ⟨_⟩_≡_ _⊩ᵛ⟨_⟩_∷_ _⊩ᵛ⟨_⟩_≡_∷_


 mutual
  -- Fundamental theorem for contexts.
  valid : ⊢ Γ → ⊩ᵛ Γ
  valid ε = ε
  valid (⊢Γ ∙ A) = let l , [Γ] , [A] = fundamental A in [Γ] ∙ [A]

  -- Fundamental theorem for types.
  fundamental : ∀ {A} (⊢A : Γ ⊢ A) →
    ∃ λ l →
    ∃ λ ([Γ] : ⊩ᵛ Γ) →
    Γ ⊩ᵛ⟨ l ⟩ A / [Γ]
  fundamental (ℕⱼ ⊢Γ) =
    0 , ℕᵛ (valid ⊢Γ)
  fundamental (Emptyⱼ x) = 0 , Emptyᵛ (valid x)
  fundamental (Unitⱼ ⊢Γ ok) =
  -- TODO check
  --   Unitᵛ (valid ⊢Γ) ok
  -- fundamental (Uⱼ ⊢Γ) =
  --   ⊩ᵛU (valid ⊢Γ)
  -- fundamental (ΠΣⱼ ⊢A ⊢B ok) =
  --   ΠΣᵛ ok (fundamental ⊢A) (fundamental ⊢B)
    0 , Unitᵛ (valid ⊢Γ) ok
  fundamental (Uⱼ {l} ⊢Γ) = _ , ⊩ᵛU (valid ⊢Γ)
  fundamental (ΠΣⱼ ⊢F ⊢G ok)
    with fundamental ⊢F | fundamental ⊢G
  … | l₁ , [Γ] , [F] | l₂ , [Γ∙F] , [G] =
    let [F]′ = C.cumul≤ [Γ] (m≤n⇒m≤n⊔oT l₂ ≤′-refl) [F]
        [G]′ = C.cumul≤ [Γ∙F] (m≤n⇒m≤o⊔nT l₁ ≤′-refl) [G]
    in l₁ ⊔T l₂ , [Γ] , (ΠΣᵛ [Γ] [F]′ (S.irrelevance [Γ∙F] ([Γ] ∙ [F]′) [G]′) ok)
  fundamental (Idⱼ ⊢t ⊢u) =
    let (_ , [t]) = fundamentalTerm ⊢t
        (_ , [u]) = fundamentalTerm ⊢u
    in _ , Idᵛ [t] [u]
  fundamental (univ ⊢A) =
    let (_ , [A]) = fundamentalTerm ⊢A
        a = ⊩ᵛ∷U→⊩ᵛ [A]
    in _ , a

  -- Fundamental theorem for type equality.
  fundamentalEq : ∀ {A B} → Γ ⊢ A ≡ B
    → ∃  λ l
    → ∃  λ ([Γ] : ⊩ᵛ Γ)
    → ∃₂ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ]) ([B] : Γ ⊩ᵛ⟨ l ⟩ B / [Γ])
    → Γ ⊩ᵛ⟨ l ⟩ A ≡ B / [Γ] / [A]
  fundamentalEq (univ A≡B) =
    let a = ⊩ᵛ≡∷U→⊩ᵛ≡ (proj₂ (fundamentalTermEq A≡B))
    in _ , a
  fundamentalEq (refl ⊢A) =
    let [refl] = refl-⊩ᵛ≡ (proj₂ (fundamental ⊢A))
    in _ , [refl]
  fundamentalEq (sym A≡B) =
    let [sym] = sym-⊩ᵛ≡ (proj₂ (fundamentalEq A≡B))
    in _ , [sym]
  fundamentalEq (trans {B} {C} A≡B B≡C) =
    let (l₁ , [Γ] , A , [BB] , [A≡B]) = fundamentalEq A≡B
        (l₂ , [Γ]′ , [B] , [C] , [B≡C]) = fundamentalEq B≡C
        [A]′ = C.cumul≤ _ (m≤n⇒m≤n⊔oT l₂ ≤′-refl) A
        [B]′ = C.cumul≤ _ (m≤n⇒m≤o⊔nT l₁ ≤′-refl) [B]
        [A≡B]′ =  S.irrelevanceEq {B = B} _ _ A [A]′ [A≡B]
        [B≡C]′ =  S.irrelevanceEq {B = C} _ _ [B] [B]′ [B≡C]
    in (l₁ ⊔T l₂) , trans-⊩ᵛ≡
    ([Γ] , [A]′ , C.cumul≤ _ (m≤n⇒m≤n⊔oT l₂ ≤′-refl) [BB] , [A≡B]′)
    (_ , [B]′ , C.cumul≤ _ (m≤n⇒m≤o⊔nT l₁ ≤′-refl) [C] , [B≡C]′)
  -- fundamentalEq (ΠΣ-cong _ A₁≡A₂ B₁≡B₂ ok) =
  --   ΠΣ-congᵛ ok (fundamentalEq A₁≡A₂) (fundamentalEq B₁≡B₂)
  fundamentalEq (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    let l₁ , [A₁≡A₂] = fundamentalEq A₁≡A₂
    in l₁ , (Id-congᵛ [A₁≡A₂] (proj₂ (fundamentalTermEq t₁≡t₂)) (proj₂ (fundamentalTermEq u₁≡u₂)))

--   -- Fundamental theorem for terms.
  fundamentalTerm : ∀ {A t} → Γ ⊢ t ∷ A
    → ∃ λ l
    → ∃ λ ([Γ] : ⊩ᵛ Γ)
    → ∃ λ ([A] : Γ ⊩ᵛ⟨ l ⟩ A / [Γ])
    → Γ ⊩ᵛ⟨ l ⟩ t ∷ A / [Γ] / [A]
  fundamentalTerm (ℕⱼ ⊢Γ) =
    1 , ℕᵗᵛ (valid ⊢Γ)
  fundamentalTerm (Emptyⱼ x) =
    1 , Emptyᵗᵛ (valid x)
  fundamentalTerm (Unitⱼ ⊢Γ ok) =
    1 , Unitᵗᵛ (valid ⊢Γ) ok
  -- fundamentalTerm (ΠΣⱼ {G = B} ⊢A ⊢B ok) =
  --   ΠΣᵗᵛ {B = B} ok (fundamentalTerm ⊢A) (fundamentalTerm ⊢B)
  -- fundamentalTerm (var ⊢Γ x∈Γ) =
  --   emb-⊩ᵛ∷ ≤¹ (varᵛ x∈Γ (valid ⊢Γ) .proj₂)
  -- fundamentalTerm (lamⱼ {t} ⊢A ⊢t ok) =
  --   lamᵛ {t = t} ok (fundamental ⊢A) (fundamentalTerm ⊢t)
  -- fundamentalTerm (_∘ⱼ_ {t = t} ⊢t ⊢u) =
  --   ∘ᵛ {t = t} (fundamentalTerm ⊢t) (fundamentalTerm ⊢u)
  -- fundamentalTerm (prodⱼ {u} _ ⊢B ⊢t ⊢u ok) =
  --   prodᵛ {u = u} ok (fundamental ⊢B) (fundamentalTerm ⊢t)
  --     (fundamentalTerm ⊢u)
  -- fundamentalTerm (fstⱼ {t} _ _ ⊢t) =
  --   fstᵛ {t = t} (fundamentalTerm ⊢t)
  -- fundamentalTerm (sndⱼ _ _ ⊢t) =
  --   sndᵛ (fundamentalTerm ⊢t)
  fundamentalTerm (zeroⱼ ⊢Γ) =
    0 , zeroᵛ (valid ⊢Γ)
  fundamentalTerm (sucⱼ {n = t} ⊢t) =
    proj₁ (fundamentalTerm ⊢t) , sucᵛ {t = t} (proj₂ (fundamentalTerm ⊢t))
  fundamentalTerm (natrecⱼ {z = t} {s = u} ⊢A ⊢t ⊢u ⊢v) =
    _ , natrecᵛ {t = t} {u = u} (proj₂ (fundamental ⊢A)) (proj₂ (fundamentalTerm ⊢t))
      (proj₂ (fundamentalTerm ⊢u)) (proj₂ (fundamentalTerm ⊢v))
  fundamentalTerm (emptyrecⱼ {t = t} ⊢A ⊢t) =
    let l₁ , [A] = fundamental ⊢A
        _ , [t] = fundamentalTerm ⊢t
    in l₁ , emptyrecᵛ {t = t} [A] [t]
  fundamentalTerm (starⱼ ⊢Γ ok) =
    0 , starᵛ (valid ⊢Γ) ok
  fundamentalTerm (conv {t} ⊢t A≡B) =
    let l , [A≡B] = fundamentalEq A≡B
    in l , conv-⊩ᵛ∷ {t = t} [A≡B] (proj₂ (fundamentalTerm ⊢t))
  fundamentalTerm (prodrecⱼ {u} _ _ ⊢C ⊢t ⊢u _) =
    prodrecᵛ {u = u} (fundamental ⊢C) (fundamentalTerm ⊢t)
      (fundamentalTerm ⊢u)
  fundamentalTerm (unitrecⱼ {u} ⊢A ⊢t ⊢u _) =
    _ , unitrecᵛ {u = u} (proj₂ (fundamental ⊢A)) (proj₂ (fundamentalTerm ⊢t))
      (proj₂ (fundamentalTerm ⊢u))
  fundamentalTerm (Idⱼ {t} {u} ⊢A ⊢t ⊢u) with
    fundamentalTerm ⊢A | fundamentalTerm ⊢t | fundamentalTerm ⊢u
  ... | l₁ , [A] | l₂ , [t] | l₃ , [U] =
    _ , Idᵗᵛ {t = t} {u = u} (proj₂ (fundamentalTerm ⊢A))
      (proj₂ (fundamentalTerm ⊢t)) (proj₂ (fundamentalTerm ⊢u))
  fundamentalTerm (rflⱼ ⊢t) =
    _ , rflᵛ (proj₂ (fundamentalTerm ⊢t))
  fundamentalTerm (Jⱼ {u} _ _ ⊢B ⊢u _ ⊢w) =
    _ , Jᵛ {u = u} (proj₂ (fundamental ⊢B)) (proj₂ (fundamentalTerm ⊢u))
      (proj₂ (fundamentalTerm ⊢w))
  fundamentalTerm (Kⱼ {u} _ ⊢B ⊢u ⊢v ok) =
    _ , Kᵛ {u = u} ok (proj₂ (fundamental ⊢B)) (proj₂ (fundamentalTerm ⊢u))
      (proj₂ (fundamentalTerm ⊢v))
  fundamentalTerm ([]-congⱼ {v} ⊢t ⊢u ⊢v ok) =
    _ , []-congᵛ {v = v} ok (proj₂ (fundamentalTerm ⊢v))
  fundamentalTerm (Uⱼ ⊢Γ) =
    _ , univInUniv ≤′-refl (valid ⊢Γ , Uᵛ (valid ⊢Γ))

--   -- Fundamental theorem for term equality.
  fundamentalTermEq : ∀ {A t t′} → Γ ⊢ t ≡ t′ ∷ A
                    → ∃ λ l
                    → ∃ λ ([Γ] : ⊩ᵛ Γ)
                    → [ Γ ⊩ᵛ⟨ l ⟩ t ≡ t′ ∷ A / [Γ] ]
  fundamentalTermEq (refl ⊢t) =
    _ , refl-⊩ᵛ≡∷ (proj₂ (fundamentalTerm ⊢t))
  fundamentalTermEq (sym t≡u) =
    _ , sym-⊩ᵛ≡∷ (proj₂ (fundamentalTermEq t≡u))
  fundamentalTermEq (trans t≡u u≡v) =
    let l , [u≡v] = fundamentalTermEq u≡v
    in l , trans-⊩ᵛ≡∷ (proj₂ (fundamentalTermEq t≡u)) [u≡v]
  fundamentalTermEq (conv t≡u A≡B) =
    _ , conv-⊩ᵛ≡∷ (proj₂ (fundamentalEq A≡B)) (proj₂ (fundamentalTermEq t≡u))
  -- fundamentalTermEq (ΠΣ-cong _ A₁≡A₂ B₁≡B₂ ok) =
  --   ΠΣ-congᵗᵛ ok (fundamentalTermEq A₁≡A₂) (fundamentalTermEq B₁≡B₂)
  -- fundamentalTermEq (app-cong t₁≡t₂ u₁≡u₂) =
  --   ∘-congᵛ (fundamentalTermEq t₁≡t₂) (fundamentalTermEq u₁≡u₂)
  -- fundamentalTermEq (β-red _ _ ⊢t ⊢u PE.refl ok) =
  --   β-redᵛ ok (fundamentalTerm ⊢t) (fundamentalTerm ⊢u)
  -- fundamentalTermEq (η-eq _ ⊢t₁ ⊢t₂ wk1-t₁∘0≡wk1-t₂∘0) =
  --   η-eqᵛ (fundamentalTerm ⊢t₁) (fundamentalTerm ⊢t₂)
  --     (fundamentalTermEq wk1-t₁∘0≡wk1-t₂∘0)
  fundamentalTermEq (suc-cong t≡u) =
    _ , suc-congᵛ (proj₂ (fundamentalTermEq t≡u))
  fundamentalTermEq (natrec-cong _ A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂) = _ ,
    natrec-congᵛ (proj₂ (fundamentalEq A₁≡A₂)) (proj₂ (fundamentalTermEq t₁≡t₂))
      (proj₂ (fundamentalTermEq u₁≡u₂)) (proj₂ (fundamentalTermEq v₁≡v₂))
  fundamentalTermEq (natrec-zero ⊢A ⊢t ⊢u) = _ ,
    natrec-zeroᵛ (proj₂ (fundamental ⊢A)) (proj₂ (fundamentalTerm ⊢t))
      (proj₂ (fundamentalTerm ⊢u))
  fundamentalTermEq (natrec-suc ⊢A ⊢t ⊢u ⊢v) = _ ,
    natrec-sucᵛ (proj₂ (fundamental ⊢A)) (proj₂ (fundamentalTerm ⊢t))
      (proj₂ (fundamentalTerm ⊢u)) (proj₂ (fundamentalTerm ⊢v))
  fundamentalTermEq (emptyrec-cong F≡F′ n≡n′) = _ ,
    emptyrec-congᵛ (proj₂ (fundamentalEq F≡F′)) (proj₂ (fundamentalTermEq n≡n′))
  fundamentalTermEq (η-unit ⊢t ⊢u η) = _ ,
    η-unitᵛ (proj₂ (fundamentalTerm ⊢t)) (proj₂ (fundamentalTerm ⊢u)) η
  -- fundamentalTermEq (fst-cong _ _ t₁≡t₂) =
  --   fst-congᵛ (fundamentalTermEq t₁≡t₂)
  -- fundamentalTermEq (snd-cong _ _ t₁≡t₂) =
  --   snd-congᵛ (fundamentalTermEq t₁≡t₂)
  -- fundamentalTermEq (prod-cong _ ⊢B t₁≡t₂ u₁≡u₂ ok) =
  --   prod-congᵛ ok (fundamental ⊢B) (fundamentalTermEq t₁≡t₂)
  --     (fundamentalTermEq u₁≡u₂)
  -- fundamentalTermEq (Σ-β₁ _ ⊢B ⊢t ⊢u PE.refl ok) =
  --   Σ-β₁ᵛ ok (fundamental ⊢B) (fundamentalTerm ⊢t) (fundamentalTerm ⊢u)
  -- fundamentalTermEq (Σ-β₂ _ ⊢B ⊢t ⊢u PE.refl ok) =
  --   Σ-β₂ᵛ ok (fundamental ⊢B) (fundamentalTerm ⊢t) (fundamentalTerm ⊢u)
  -- fundamentalTermEq (Σ-η _ _ ⊢t₁ ⊢t₂ fst-t₁≡fst-t₂ snd-t₁≡snd-t₂) =
  --   Σ-ηᵛ (fundamentalTerm ⊢t₁) (fundamentalTerm ⊢t₂)
  --     (fundamentalTermEq fst-t₁≡fst-t₂)
  --     (fundamentalTermEq snd-t₁≡snd-t₂)
  -- fundamentalTermEq (prodrec-cong _ _ C₁≡C₂ t₁≡t₂ u₁≡u₂ _) =
  --   prodrec-congᵛ (fundamentalEq C₁≡C₂) (fundamentalTermEq t₁≡t₂)
  --     (fundamentalTermEq u₁≡u₂)
  -- fundamentalTermEq (prodrec-β _ _ ⊢C ⊢t ⊢u ⊢v PE.refl _) =
  --   prodrec-βᵛ (fundamental ⊢C) (fundamentalTerm ⊢t)
  --     (fundamentalTerm ⊢u) (fundamentalTerm ⊢v)
  fundamentalTermEq (unitrec-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ _ _) = _ ,
    unitrec-congᵛ (proj₂ (fundamentalEq A₁≡A₂)) (proj₂ (fundamentalTermEq t₁≡t₂))
      (proj₂ (fundamentalTermEq u₁≡u₂))
  fundamentalTermEq (unitrec-β ⊢A ⊢u _ no-η) = _ ,
    unitrec-βᵛ (proj₂ (fundamental ⊢A)) (proj₂ (fundamentalTerm ⊢u)) no-η
  -- fundamentalTermEq (unitrec-β-η ⊢A ⊢t ⊢u _ η) =
  --   unitrec-β-ηᵛ (fundamental ⊢A) (fundamentalTerm ⊢t)
  --     (fundamentalTerm ⊢u) η
  fundamentalTermEq (Id-cong A₁≡A₂ t₁≡t₂ u₁≡u₂) =
    _ , Id-congᵗᵛ (proj₂ (fundamentalTermEq A₁≡A₂)) (proj₂ (fundamentalTermEq t₁≡t₂))
      (proj₂ (fundamentalTermEq u₁≡u₂))
  fundamentalTermEq (J-cong _ A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ w₁≡w₂) = _ ,
    J-congᵛ (proj₂ (fundamentalEq A₁≡A₂)) (proj₂ (fundamentalTermEq t₁≡t₂))
      (proj₂ (fundamentalEq B₁≡B₂)) (proj₂ (fundamentalTermEq u₁≡u₂))
      (proj₂ (fundamentalTermEq v₁≡v₂)) (proj₂ (fundamentalTermEq w₁≡w₂))
  fundamentalTermEq (K-cong A₁≡A₂ _ t₁≡t₂ B₁≡B₂ u₁≡u₂ v₁≡v₂ ok) = _ ,
    K-congᵛ ok (proj₂ (fundamentalEq A₁≡A₂)) (proj₂ (fundamentalTermEq t₁≡t₂))
      (proj₂ (fundamentalEq B₁≡B₂)) (proj₂ (fundamentalTermEq u₁≡u₂))
      (proj₂ (fundamentalTermEq v₁≡v₂))
  fundamentalTermEq ([]-cong-cong A₁≡A₂ t₁≡t₂ u₁≡u₂ v₁≡v₂ ok) = _ ,
    []-cong-congᵛ ok (proj₂ (fundamentalEq A₁≡A₂)) (proj₂ (fundamentalTermEq t₁≡t₂))
      (proj₂ (fundamentalTermEq u₁≡u₂)) (proj₂ (fundamentalTermEq v₁≡v₂))
  fundamentalTermEq (J-β _ ⊢t ⊢B ⊢u PE.refl) = _ ,
    J-βᵛ (proj₂ (fundamentalTerm ⊢t)) (proj₂ (fundamental ⊢B))
    (proj₂ (fundamentalTerm ⊢u))
  fundamentalTermEq (K-β _ ⊢B ⊢u ok) = _ ,
    K-βᵛ ok (proj₂ (fundamental ⊢B)) (proj₂ (fundamentalTerm ⊢u))
  fundamentalTermEq ([]-cong-β ⊢t PE.refl ok) = _ ,
    []-cong-βᵛ ok (proj₂ (fundamentalTerm ⊢t))

-- -- Fundamental theorem for substitutions.
-- fundamentalSubst : (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
--       → Δ ⊢ˢ σ ∷ Γ
--       → ∃ λ [Γ] → Δ ⊩ˢ σ ∷ Γ / [Γ] / ⊢Δ
-- fundamentalSubst ε ⊢Δ [σ] = ε , lift tt
-- fundamentalSubst (⊢Γ ∙ ⊢A) ⊢Δ ([tailσ] , [headσ]) =
--   let [Γ] , [A] = fundamental ⊢A
--       [Δ] , [A]′ , [t] = fundamentalTerm [headσ]
--       [Γ]′ , [σ] = fundamentalSubst ⊢Γ ⊢Δ [tailσ]
--       [tailσ]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [σ]
--       [idA]  = proj₁ (unwrap [A]′ (soundContext [Δ]) (idSubstS [Δ]))
--       [idA]′ = proj₁ (unwrap [A] ⊢Δ [tailσ]′)
--       [idt]  = proj₁ ([t] (soundContext [Δ]) (idSubstS [Δ]))
--   in  [Γ] ∙ [A] , ([tailσ]′
--   ,   irrelevanceTerm″ (subst-id _) (subst-id _) [idA] [idA]′ [idt])

-- -- Fundamental theorem for substitution equality.
-- fundamentalSubstEq : (⊢Γ : ⊢ Γ) (⊢Δ : ⊢ Δ)
--       → Δ ⊢ˢ σ ≡ σ′ ∷ Γ
--       → ∃₂ λ [Γ] [σ]
--       → ∃  λ ([σ′] : Δ ⊩ˢ σ′ ∷ Γ / [Γ] / ⊢Δ)
--       → Δ ⊩ˢ σ ≡ σ′ ∷ Γ / [Γ] / ⊢Δ / [σ]
-- fundamentalSubstEq ε ⊢Δ σ = ε , lift tt , lift tt , lift tt
-- fundamentalSubstEq (⊢Γ ∙ ⊢A) ⊢Δ (tailσ≡σ′ , headσ≡σ′) =
--   let [Γ] , [A] = fundamental ⊢A
--       [Γ]′ , [tailσ] , [tailσ′] , [tailσ≡σ′] = fundamentalSubstEq ⊢Γ ⊢Δ tailσ≡σ′
--       [Δ] , modelsTermEq [A]′ [t] [t′] [t≡t′] = fundamentalTermEq headσ≡σ′
--       [tailσ]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ]
--       [tailσ′]′ = S.irrelevanceSubst [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ′]
--       [tailσ≡σ′]′ = S.irrelevanceSubstEq [Γ]′ [Γ] ⊢Δ ⊢Δ [tailσ] [tailσ]′ [tailσ≡σ′]
--       [idA]  = proj₁ (unwrap [A]′ (soundContext [Δ]) (idSubstS [Δ]))
--       [idA]′ = proj₁ (unwrap [A] ⊢Δ [tailσ]′)
--       [idA]″ = proj₁ (unwrap [A] ⊢Δ [tailσ′]′)
--       [idt]  = proj₁ ([t] (soundContext [Δ]) (idSubstS [Δ]))
--       [idt′] = proj₁ ([t′] (soundContext [Δ]) (idSubstS [Δ]))
--       [idt≡t′]  = [t≡t′] (soundContext [Δ]) (idSubstS [Δ])
--   in  [Γ] ∙ [A]
--   ,   ([tailσ]′ , irrelevanceTerm″ (subst-id _) (subst-id _) [idA] [idA]′ [idt])
--   ,   ([tailσ′]′ , convTerm₁ [idA]′ [idA]″
--                              (proj₂ (unwrap [A] ⊢Δ [tailσ]′) [tailσ′]′ [tailσ≡σ′]′)
--                              (irrelevanceTerm″ (subst-id _) (subst-id _)
--                                                 [idA] [idA]′ [idt′]))
--   ,   ([tailσ≡σ′]′ , irrelevanceEqTerm″ (subst-id _) (subst-id _) (subst-id _)
--                                          [idA] [idA]′ [idt≡t′])

-- opaque
--   unfolding _⊩ᵛ⟨_⟩_

--   -- A variant of fundamental.

--   fundamental-⊩ᵛ : Γ ⊢ A → Γ ⊩ᵛ⟨ ¹ ⟩ A
--   fundamental-⊩ᵛ = fundamental

-- opaque
--   unfolding _⊩ᵛ⟨_⟩_≡_

--   -- A variant of fundamentalEq.

--   fundamental-⊩ᵛ≡ : Γ ⊢ A ≡ B → Γ ⊩ᵛ⟨ ¹ ⟩ A ≡ B
--   fundamental-⊩ᵛ≡ = fundamentalEq

-- opaque
--   unfolding _⊩ᵛ⟨_⟩_∷_

--   -- A variant of fundamentalTerm.

--   fundamental-⊩ᵛ∷ : Γ ⊢ t ∷ A → Γ ⊩ᵛ⟨ ¹ ⟩ t ∷ A
--   fundamental-⊩ᵛ∷ = fundamentalTerm

-- opaque
--   unfolding _⊩ᵛ⟨_⟩_≡_∷_

--   -- A variant of fundamentalTermEq.

--   fundamental-⊩ᵛ≡∷ : Γ ⊢ t ≡ u ∷ A → Γ ⊩ᵛ⟨ ¹ ⟩ t ≡ u ∷ A
--   fundamental-⊩ᵛ≡∷ = fundamentalTermEq

-- opaque
--   unfolding _⊩ˢ_∷_

--   -- A variant of fundamentalSubst.

--   fundamental-⊩ˢ∷ : ⊢ Δ → ⊢ Γ → Δ ⊢ˢ σ ∷ Γ → Δ ⊩ˢ σ ∷ Γ
--   fundamental-⊩ˢ∷ ⊢Δ ⊢Γ ⊢σ =
--     case fundamentalSubst ⊢Γ ⊢Δ ⊢σ of λ
--       (_ , ⊩σ) →
--     _ , _ , ⊩σ

-- opaque
--   unfolding _⊩ˢ_≡_∷_

--   -- A variant of fundamentalSubstEq.

--   fundamental-⊩ˢ≡∷ : ⊢ Δ → ⊢ Γ → Δ ⊢ˢ σ₁ ≡ σ₂ ∷ Γ → Δ ⊩ˢ σ₁ ≡ σ₂ ∷ Γ
--   fundamental-⊩ˢ≡∷ ⊢Δ ⊢Γ σ₁≡σ₂ =
--     case fundamentalSubstEq ⊢Γ ⊢Δ σ₁≡σ₂ of λ
--       (_ , σ₁≡σ₂) →
--     _ , _ , σ₁≡σ₂
