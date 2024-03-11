------------------------------------------------------------------------
-- If the extraction function uses strict applications and removes
-- erasable arguments entirely, then it may be the case that
-- well-typed and well-resourced terms extract to terms that do not
-- terminate
------------------------------------------------------------------------

-- In "A New Extraction for Coq" Letouzey points out that uses of the
-- eliminator for the empty type False can lead to problems similar to
-- the one presented below if all logical arguments are removed
-- entirely, given that the eliminator is replaced with code that
-- throws an exception. However, the example discussed below does not
-- rely on how emptyrec is extracted, but is more similar to one in
-- Mishra-Linger's PhD thesis (see Figure 5.1).
--
-- The example looks roughly like this:
--
--   (λ^ω _. zero)
--     (λ⁰ (bot : ⊥).
--        (λ^ω x. cast bot x x) (cast bot (λ^ω x. cast bot x x)))
--
-- If erased arguments are removed entirely, then we end up with a
-- term like the following one:
--
--   (λ _. zero) ((λ x. x x) (λ x. x x))
--
-- If strict applications are used, then this program does not
-- terminate.

{-# OPTIONS --hidden-argument-puns #-}

open import Graded.Modality
open import Graded.Usage.Restrictions
open import Definition.Typed.Restrictions

module Graded.Erasure.Extraction.Non-terminating
  {a} {M : Set a}
  {𝕄 : Modality M}
  (TR : Type-restrictions 𝕄)
  (UR : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Type-restrictions TR

open import Definition.Typed TR
open import Definition.Typed.Consequences.DerivedRules TR
open import Definition.Typed.Properties TR
open import Definition.Untyped M hiding (_∷_)
open import Definition.Untyped.Identity 𝕄

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Derived.Identity UR
open import Graded.Erasure.Extraction 𝕄
open import Graded.Erasure.Extraction.Properties 𝕄
open import Graded.Erasure.Target as T using (Strictness; strict)
open import Graded.Erasure.Target.Non-terminating
open import Graded.Erasure.Target.Properties
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄
open import Graded.Usage 𝕄 UR
open import Graded.Usage.Properties 𝕄 UR

open import Tools.Bool using (Bool; true)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality as PE using (_≡_; _≢_)
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum

private variable
  b           : Bool
  n           : Nat
  Γ           : Con Term _
  A B t u     : Term _
  γ₁ γ₂ γ₃ γ₄ : Conₘ _
  p q         : M
  v           : T.Term _
  s           : Strictness

-- Some lemmas used below.

private module Lemmas (⊢Γ : ⊢ Γ) where opaque

  Empty⊢ℕ∷U : Γ ∙ Empty ⊢ ℕ ∷ U
  Empty⊢ℕ∷U = ℕⱼ (⊢Γ ∙[ Emptyⱼ ])

  Empty⊢ℕ : Γ ∙ Empty ⊢ ℕ
  Empty⊢ℕ = univ Empty⊢ℕ∷U

  Empty∙ℕ⊢ℕ∷U : Γ ∙ Empty ∙ ℕ ⊢ ℕ ∷ U
  Empty∙ℕ⊢ℕ∷U = ℕⱼ (⊢Γ ∙[ Emptyⱼ ] ∙[ ℕⱼ ])

  Empty∙ℕ∙ℕ⊢ℕ∷U : Γ ∙ Empty ∙ ℕ ∙ ℕ ⊢ ℕ ∷ U
  Empty∙ℕ∙ℕ⊢ℕ∷U = ℕⱼ (⊢Γ ∙[ Emptyⱼ ] ∙[ ℕⱼ ] ∙[ ℕⱼ ])

opaque

  -- Another lemma used below.

  ▸Πℕℕ : p ≤ 𝟘 → 𝟘ᶜ {n = n} ▸[ 𝟙ᵐ ] Π ω , p ▷ ℕ ▹ ℕ
  ▸Πℕℕ {p} p≤𝟘 = sub
    (ΠΣₘ ℕₘ $ sub ℕₘ $ begin
        𝟘ᶜ ∙ 𝟙 · p  ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ⟩
        𝟘ᶜ ∙ p      ≤⟨ ≤ᶜ-refl ∙ p≤𝟘 ⟩
        𝟘ᶜ          ∎)
    (begin
       𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
       𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
    where
    open ≤ᶜ-reasoning

------------------------------------------------------------------------
-- The term former cast

opaque

  -- A cast lemma.

  cast : Term n → Term n → Term n → Term n → Term n
  cast t A B u =
    subst 𝟙 U (var x0) A B (emptyrec 𝟘 (Id U A B) t) u

opaque
  unfolding cast subst

  -- An extraction lemma for cast.

  erase-cast : erase′ b s (cast t A B u) ≡ erase′ b s u
  erase-cast = PE.refl

opaque
  unfolding cast

  -- A typing rule for cast.

  ⊢cast :
    Γ ⊢ t ∷ Empty →
    Γ ⊢ A ∷ U →
    Γ ⊢ B ∷ U →
    Γ ⊢ u ∷ A →
    Γ ⊢ cast t A B u ∷ B
  ⊢cast ⊢t ⊢A ⊢B =
    ⊢subst (univ $ var₀ $ Uⱼ $ wfTerm ⊢t) (emptyrecⱼ (Idⱼ ⊢A ⊢B) ⊢t)

opaque
  unfolding cast

  -- A usage rule for cast.

  ▸cast :
    γ₁ ▸[ 𝟘ᵐ? ] t →
    γ₂ ▸[ 𝟙ᵐ ] A →
    γ₃ ▸[ 𝟙ᵐ ] B →
    γ₄ ▸[ 𝟙ᵐ ] u →
    𝟘ᶜ ∧ᶜ ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄) ▸[ 𝟙ᵐ ] cast t A B u
  ▸cast {γ₁} {γ₂} {γ₃} {γ₄} ▸t ▸A ▸B ▸u =
    sub (▸subst Uₘ
           (sub var $ begin
              𝟘ᶜ ∙ 𝟙 · 𝟙   ≈⟨ ≈ᶜ-refl ∙ ·-identityʳ _ ⟩
              𝟘ᶜ , x0 ≔ 𝟙  ∎)
           ▸A ▸B
           (emptyrecₘ (▸-cong (PE.sym ⌞𝟘⌟≡𝟘ᵐ?) ▸t) $
            Idₘ-generalised Uₘ (▸-𝟘ᵐ? ▸A .proj₂) (▸-𝟘ᵐ? ▸B .proj₂)
              (λ _ → ∧ᶜ-decreasingˡ 𝟘ᶜ _)
              (λ _ → ∧ᶜ-decreasingʳ _ _))
           ▸u)
    (begin
       𝟘ᶜ ∧ᶜ ω ·ᶜ (γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄)             ≈˘⟨ ≈ᶜ-trans (·ᶜ-distribˡ-∧ᶜ _ _ _) $
                                                   ∧ᶜ-congʳ $ ·ᶜ-zeroʳ _ ⟩
       ω ·ᶜ (𝟘ᶜ ∧ᶜ γ₂ ∧ᶜ γ₃ ∧ᶜ γ₄)             ≈˘⟨ ·ᶜ-congˡ $
                                                   ≈ᶜ-trans
                                                     (∧ᶜ-congˡ $
                                                      ≈ᶜ-trans
                                                        (∧ᶜ-congˡ $
                                                         ≈ᶜ-trans (∧ᶜ-congˡ $ ∧ᶜ-congʳ $ ·ᶜ-zeroˡ _) $
                                                         ≈ᶜ-trans (≈ᶜ-sym $ ∧ᶜ-assoc _ _ _) $
                                                         ∧ᶜ-congʳ $ ∧ᶜ-comm _ _) $
                                                      ≈ᶜ-trans (∧ᶜ-congˡ $ ∧ᶜ-assoc _ _ _) $
                                                      ≈ᶜ-trans (≈ᶜ-sym $ ∧ᶜ-assoc _ _ _) $
                                                      ≈ᶜ-trans (∧ᶜ-congʳ $ ∧ᶜ-comm _ _) $
                                                      ∧ᶜ-assoc _ _ _) $
                                                   ≈ᶜ-trans (≈ᶜ-sym $ ∧ᶜ-assoc _ _ _) $
                                                   ∧ᶜ-congʳ $ ∧ᶜ-idem _ ⟩
       ω ·ᶜ (𝟘ᶜ ∧ᶜ γ₂ ∧ᶜ γ₃ ∧ᶜ 𝟘 ·ᶜ γ₁ ∧ᶜ γ₄)  ∎)
    where
    open ≤ᶜ-reasoning

------------------------------------------------------------------------
-- The term former λx∙xx

opaque

  -- A term that is roughly "λ x. x x".

  λx∙xx : M → Term (1+ n)
  λx∙xx p =
    lam ω $ cast (var x1) ℕ (Π ω , p ▷ ℕ ▹ ℕ) (var x0) ∘⟨ ω ⟩ var x0

opaque
  unfolding λx∙xx

  -- An extraction lemma for λx∙xx.

  erase-λx∙xx :
    ω ≢ 𝟘 →
    erase′ b s (λx∙xx {n = n} p) ≡
    T.lam (T.var x0 T.∘⟨ s ⟩ T.var x0)
  erase-λx∙xx {b} {s} {p} ω≢𝟘 =
    erase′ b s (λx∙xx p)                                          ≡⟨ lam-≢𝟘 b ω≢𝟘 ⟩

    T.lam
      (erase′ b s $
       cast (var x1) ℕ (Π ω , p ▷ ℕ ▹ ℕ) (var x0) ∘⟨ ω ⟩ var x0)  ≡⟨ PE.cong T.lam $ ∘-≢𝟘 ω≢𝟘 ⟩

    T.lam
      (erase′ b s
         (cast (var x1) ℕ (Π ω , p ▷ ℕ ▹ ℕ) (var x0))
         T.∘⟨ s ⟩ T.var x0)                                       ≡⟨ PE.cong (λ t → T.lam (t T.∘⟨ _ ⟩ _)) erase-cast ⟩

    T.lam (T.var x0 T.∘⟨ s ⟩ T.var x0)                            ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding λx∙xx

  -- A typing rule for λx∙xx.

  ⊢λx∙xx :
    Π-allowed ω p →
    ⊢ Γ →
    Γ ∙ Empty ⊢ λx∙xx p ∷ Π ω , p ▷ ℕ ▹ ℕ
  ⊢λx∙xx ω-ok ⊢Γ =
    lamⱼ′ ω-ok $
    ⊢cast (var₁ Empty⊢ℕ) Empty∙ℕ⊢ℕ∷U
      (ΠΣⱼ Empty∙ℕ⊢ℕ∷U Empty∙ℕ∙ℕ⊢ℕ∷U ω-ok) (var₀ Empty⊢ℕ) ∘ⱼ
    var₀ Empty⊢ℕ
    where
    open Lemmas ⊢Γ

opaque
  unfolding λx∙xx

  -- A usage rule for λx∙xx.

  ▸λx∙xx :
    ω ≤ 𝟘 →
    ω ≤ ω + ω →
    p ≤ 𝟘 →
    𝟘ᶜ ▸[ 𝟙ᵐ ] λx∙xx {n = n} p
  ▸λx∙xx {p} ω≤𝟘 ω≤ω+ω p≤𝟘 =
    lamₘ $ sub (▸cast var ℕₘ (▸Πℕℕ p≤𝟘) var ∘ₘ var) $ begin
      𝟘ᶜ ∙ 𝟙 · ω                              ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ⟩

      𝟘ᶜ ∙ ω                                  ≤⟨ ≤ᶜ-refl ∙ ω≤ω+ω ⟩

      𝟘ᶜ ∙ ω + ω                              ≈˘⟨ ≈ᶜ-refl ∙ +-congʳ (∧-idem _) ⟩

      𝟘ᶜ ∙ (ω ∧ ω) + ω                        ≤⟨ ≤ᶜ-refl ∙ +-monotoneˡ (∧-monotoneˡ ω≤𝟘) ⟩

      𝟘ᶜ ∙ (𝟘 ∧ ω) + ω                        ≈˘⟨ (≈ᶜ-trans
                                                     (+ᶜ-cong
                                                        (≈ᶜ-trans (∧ᶜ-congˡ $ ·ᶜ-congˡ $ ∧ᶜ-idem _) $
                                                         ≈ᶜ-trans (∧ᶜ-congˡ $ ·ᶜ-zeroʳ _) $
                                                         ∧ᶜ-idem _)
                                                        (·ᶜ-zeroʳ _)) $
                                                   +ᶜ-identityʳ _) ∙
                                                  +-cong
                                                    (PE.trans (∧-congˡ ·[𝟘∧𝟙]≡𝟘∧) $
                                                     PE.trans (PE.sym $ ∧-assoc _ _ _) $
                                                     ∧-congʳ $ ∧-idem _)
                                                    ·⌜⌞⌟⌝ ⟩
      (𝟘ᶜ ∧ᶜ ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ)) +ᶜ ω ·ᶜ 𝟘ᶜ ∙
      (𝟘 ∧ ω · (𝟘 ∧ 𝟙)) + ω · ⌜ ⌞ ω ⌟ ⌝       ≈˘⟨ +ᶜ-congʳ $
                                                  ∧ᶜ-congˡ $ ·ᶜ-congˡ $
                                                  ≈ᶜ-trans (≈ᶜ-sym $ ∧ᶜ-assoc _ _ _) $
                                                  ∧ᶜ-congʳ $ ∧ᶜ-idem _ ⟩
      (𝟘ᶜ ∧ᶜ ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ (𝟘ᶜ ∙ 𝟙))) +ᶜ
      ω ·ᶜ (𝟘ᶜ ∙ ⌜ ⌞ ω ⌟ ⌝)                   ∎
    where
    open ≤ᶜ-reasoning

------------------------------------------------------------------------
-- The term former extracts-to-loop

opaque

  -- A term for which the extraction is loop s (for some s) if
  -- erasable arguments are removed entirely.

  extracts-to-loop : M → Term n
  extracts-to-loop p =
    lam 𝟘 (λx∙xx p ∘⟨ ω ⟩ cast (var x0) (Π ω , p ▷ ℕ ▹ ℕ) ℕ (λx∙xx p))

opaque
  unfolding extracts-to-loop loop

  -- An extraction lemma for extracts-to-loop.

  erase-extracts-to-loop :
    ω ≢ 𝟘 →
    erase′ true s (extracts-to-loop {n = n} p) ≡ loop s
  erase-extracts-to-loop {s} {p} ω≢𝟘 =
    erase′ true s (extracts-to-loop p)                              ≡⟨ lam-𝟘-remove ⟩

    erase′ true s
      (λx∙xx p ∘⟨ ω ⟩ cast (var x0) (Π ω , p ▷ ℕ ▹ ℕ) ℕ (λx∙xx p))
      T.[ T.↯ ]₀                                                    ≡⟨ PE.cong T._[ _ ] $
                                                                       ∘-≢𝟘 ω≢𝟘 ⟩
    erase′ true s (λx∙xx p) T.∘⟨ s ⟩
      erase′ true s
        (cast (var x0) (Π ω , p ▷ ℕ ▹ ℕ) ℕ (λx∙xx p))
      T.[ T.↯ ]₀                                                    ≡⟨ PE.cong
                                                                         (λ t → erase′ _ _ (λx∙xx _) T.∘⟨ _ ⟩ t T.[ _ ])
                                                                         erase-cast ⟩
    erase′ true s (λx∙xx p) T.∘⟨ s ⟩
      erase′ true s (λx∙xx p)
      T.[ T.↯ ]₀                                                    ≡⟨ PE.cong (λ t → t T.∘⟨ _ ⟩ t T.[ _ ]) $
                                                                       erase-λx∙xx ω≢𝟘 ⟩
    loop s                                                          ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque
  unfolding extracts-to-loop

  -- A typing rule for extracts-to-loop.

  ⊢extracts-to-loop :
    Π-allowed 𝟘 p →
    Π-allowed ω q →
    ⊢ Γ →
    Γ ⊢ extracts-to-loop q ∷ Π 𝟘 , p ▷ Empty ▹ ℕ
  ⊢extracts-to-loop 𝟘-ok ω-ok ⊢Γ =
    lamⱼ′ 𝟘-ok $
    ⊢λx∙xx ω-ok ⊢Γ ∘ⱼ
    ⊢cast (var₀ (Emptyⱼ ⊢Γ)) (ΠΣⱼ Empty⊢ℕ∷U Empty∙ℕ⊢ℕ∷U ω-ok) Empty⊢ℕ∷U
      (⊢λx∙xx ω-ok ⊢Γ)
    where
    open Lemmas ⊢Γ

opaque
  unfolding extracts-to-loop

  -- A usage rule for extracts-to-loop.

  ▸extracts-to-loop :
    ω < 𝟘 →
    ω ≤ ω + ω →
    p ≤ 𝟘 →
    𝟘ᶜ ▸[ 𝟙ᵐ ] extracts-to-loop {n = n} p
  ▸extracts-to-loop {p} {n} (ω≤𝟘 , ω≢𝟘) ω≤ω+ω p≤𝟘 = lamₘ $ sub
    (▸λx∙xx′ ∘ₘ
     sub
       (▸-cong (PE.sym $ ≢𝟘→⌞⌟≡𝟙ᵐ ω≢𝟘) $
        ▸cast var (▸Πℕℕ p≤𝟘) ℕₘ ▸λx∙xx′)
     (let open ≤ᶜ-reasoning in begin
        𝟘ᶜ                           ≈˘⟨ ≈ᶜ-trans
                                           (∧ᶜ-congˡ $
                                            ≈ᶜ-trans
                                              (·ᶜ-congˡ $
                                               ≈ᶜ-trans (∧ᶜ-congˡ $ ∧ᶜ-idem _) $
                                               ∧ᶜ-idem _) $
                                            ·ᶜ-zeroʳ _) $
                                         ∧ᶜ-idem _ ⟩
        𝟘ᶜ ∧ᶜ ω ·ᶜ (𝟘ᶜ ∧ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ)  ∎))
    (let open ≤ᶜ-reasoning in begin
       𝟘ᶜ ∙ 𝟙 · 𝟘     ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
       𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
       ω ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
       𝟘ᶜ +ᶜ ω ·ᶜ 𝟘ᶜ  ∎)
    where
    ▸λx∙xx′ : 𝟘ᶜ ▸[ 𝟙ᵐ ] λx∙xx {n = n} p
    ▸λx∙xx′ = ▸λx∙xx ω≤𝟘 ω≤ω+ω p≤𝟘

------------------------------------------------------------------------
-- The term former loops

opaque

  -- A term for which the extraction does not terminate if erasable
  -- arguments are removed entirely and strict applications are used
  -- (if ω is non-zero).

  loops : M → Term n
  loops p = lam ω zero ∘⟨ ω ⟩ extracts-to-loop p

opaque
  unfolding loops

  -- An extraction lemma for loops.

  erase-loops :
    ω ≢ 𝟘 →
    erase′ true s (loops {n = n} p) ≡
    T.lam T.zero T.∘⟨ s ⟩ loop s
  erase-loops {s} {p} ω≢𝟘 =
    erase′ true s (lam ω zero ∘⟨ ω ⟩ extracts-to-loop p)  ≡⟨ ∘-≢𝟘 ω≢𝟘 ⟩

    erase′ true s (lam ω zero) T.∘⟨ s ⟩
    erase′ true s (extracts-to-loop p)                    ≡⟨ PE.cong₂ T._∘⟨ _ ⟩_ (lam-≢𝟘 _ ω≢𝟘) $
                                                             erase-extracts-to-loop ω≢𝟘 ⟩
    T.lam T.zero T.∘⟨ s ⟩ loop s                          ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- If ω is non-zero, erasable arguments are removed entirely, and
  -- strict applications are used, then the extraction of loops p does
  -- not reduce to a value.

  loops-does-not-reduce-to-a-value :
    ω ≢ 𝟘 →
    T.Value v →
    ¬ erase′ true strict (loops p) T.⇒* v
  loops-does-not-reduce-to-a-value {v} {p} ω≢𝟘 v-value =
    erase′ true strict (loops p) T.⇒* v            ≡⟨ PE.cong (T._⇒* _) $ erase-loops ω≢𝟘 ⟩→
    T.lam T.zero T.∘⟨ strict ⟩ loop strict T.⇒* v  →⟨ helper ⟩
    ⊥                                              □
    where
    helper : ¬ T.lam T.zero T.∘⟨ strict ⟩ loop s T.⇒* v
    helper T.refl =
      case v-value of λ ()
    helper (T.trans (T.app-subst ())     _)
    helper (T.trans (T.β-red loop-value) _) =
      ¬loop⇒* loop-value T.refl
    helper (T.trans (T.app-subst-arg _ loop⇒) ⇒*v)
      rewrite redDet _ loop⇒ loop⇒loop =
      helper ⇒*v

opaque
  unfolding loops

  -- A typing rule for loops.

  ⊢loops :
    Π-allowed 𝟘 p →
    Π-allowed ω q →
    ⊢ Γ →
    Γ ⊢ loops q ∷ ℕ
  ⊢loops 𝟘-ok ω-ok ⊢Γ =
    lamⱼ′ ω-ok (zeroⱼ (⊢Γ ∙ ΠΣⱼ′ Empty⊢ℕ 𝟘-ok)) ∘ⱼ
    ⊢extracts-to-loop 𝟘-ok ω-ok ⊢Γ
    where
    open Lemmas ⊢Γ

opaque
  unfolding loops

  -- A usage rule for loops.

  ▸loops :
    ω < 𝟘 →
    ω ≤ ω + ω →
    p ≤ 𝟘 →
    𝟘ᶜ ▸[ 𝟙ᵐ ] loops {n = n} p
  ▸loops ω<𝟘@(ω≤𝟘 , ω≢𝟘) ω≤ω+ω p≤𝟘 = sub
    (lamₘ
       (sub zeroₘ $ begin
          𝟘ᶜ ∙ 𝟙 · ω  ≈⟨ ≈ᶜ-refl ∙ ·-identityˡ _ ⟩
          𝟘ᶜ ∙ ω      ≤⟨ ≤ᶜ-refl ∙ ω≤𝟘 ⟩
          𝟘ᶜ          ∎) ∘ₘ
     ▸-cong (PE.sym $ ≢𝟘→⌞⌟≡𝟙ᵐ ω≢𝟘) (▸extracts-to-loop ω<𝟘 ω≤ω+ω p≤𝟘))
    (begin
       𝟘ᶜ             ≈˘⟨ ≈ᶜ-trans (+ᶜ-identityˡ _) (·ᶜ-zeroʳ _) ⟩
       𝟘ᶜ +ᶜ ω ·ᶜ 𝟘ᶜ  ∎)
    where
    open ≤ᶜ-reasoning
