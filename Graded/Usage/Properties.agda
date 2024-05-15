------------------------------------------------------------------------
-- Properties of the usage relation.
------------------------------------------------------------------------

import Graded.Modality
open import Graded.Usage.Restrictions

module Graded.Usage.Properties
  {a} {M : Set a}
  (open Graded.Modality M)
  (𝕄 : Modality)
  (R : Usage-restrictions 𝕄)
  where

open Modality 𝕄
open Usage-restrictions R

open import Graded.Context 𝕄
open import Graded.Context.Properties 𝕄
open import Graded.Usage 𝕄 R
open import Graded.Usage.Inversion 𝕄 R
open import Graded.Usage.Erased-matches
open import Graded.Modality.Dedicated-nr 𝕄
open import Graded.Modality.Nr-instances
open import Graded.Modality.Properties 𝕄
open import Graded.Mode 𝕄

import Definition.Typed
open import Definition.Typed.Restrictions 𝕄
open import Definition.Untyped M

open import Tools.Bool using (Bool; T)
open import Tools.Empty
open import Tools.Fin
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (Nat; 1+)
open import Tools.Product
open import Tools.PropositionalEquality as PE
open import Tools.Relation
open import Tools.Sum
open import Tools.Unit
import Tools.Reasoning.Equivalence
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality

private
  module CR {n} = Tools.Reasoning.PartialOrder (≤ᶜ-poset {n = n})

private
  variable
    n l : Nat
    Γ : Con Term n
    A B F t u v w : Term n
    G : Term (1+ n)
    γ γ₁ γ₂ γ₃ γ₄ γ₅ γ₆ δ η θ χ : Conₘ n
    p q r s z : M
    m m₁ m₂ m₃ m′ : Mode
    b : Bool
    ok : T b
    x : Fin n
    sem : Some-erased-matches

------------------------------------------------------------------------
-- Lemmas related to _◂_∈_

-- Variables only have one annotation in a context

unique-var-usage : x ◂ p ∈ γ → x ◂ q ∈ γ → p PE.≡ q
unique-var-usage here here = PE.refl
unique-var-usage (there x) (there y) = unique-var-usage x y

-- Variable lookup and the usage relation for variables match

var-usage-lookup : x ◂ p ∈ γ → γ ⟨ x ⟩ ≡ p
var-usage-lookup here = PE.refl
var-usage-lookup (there x) = var-usage-lookup x

-- An alternative characterisation of _◂_∈_.

◂∈⇔ : x ◂ p ∈ γ ⇔ γ ⟨ x ⟩ ≡ p
◂∈⇔ = to , from
  where
  to : x ◂ p ∈ γ → γ ⟨ x ⟩ ≡ p
  to here      = refl
  to (there q) = to q

  from : γ ⟨ x ⟩ ≡ p → x ◂ p ∈ γ
  from {γ = _ ∙ _} {x = x0}   refl = here
  from {γ = _ ∙ _} {x = _ +1} eq   = there (from eq)

------------------------------------------------------------------------
-- Replacing one usage mode with another

-- γ ▸[_] t respects _≡_.

▸-cong : m₁ ≡ m₂ → γ ▸[ m₁ ] t → γ ▸[ m₂ ] t
▸-cong = subst (_ ▸[_] _)

-- If 𝟘ᵐ is not allowed, then one can convert usage modes freely.

▸-without-𝟘ᵐ : ¬ T 𝟘ᵐ-allowed → γ ▸[ m ] t → γ ▸[ m′ ] t
▸-without-𝟘ᵐ not-ok =
  ▸-cong (Mode-propositional-without-𝟘ᵐ not-ok)

-- If the modality is trivial, then one can convert usage modes
-- freely.

▸-trivial : Trivial → γ ▸[ m ] t → γ ▸[ m′ ] t
▸-trivial 𝟙≡𝟘 = ▸-without-𝟘ᵐ (flip 𝟘ᵐ.non-trivial 𝟙≡𝟘)

------------------------------------------------------------------------
-- The lemma ▸-𝟘 and some related results

opaque

  -- If a term is well-resourced with respect to any context and mode,
  -- then it is well-resourced with respect to the zero usage context
  -- and the mode 𝟘ᵐ[ ok ].

  ▸-𝟘 : γ ▸[ m ] t → 𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] t

  -- A variant of ▸-𝟘.

  𝟘ᶜ▸[𝟘ᵐ?] : T 𝟘ᵐ-allowed → γ ▸[ m ] t → 𝟘ᶜ ▸[ 𝟘ᵐ? ] t
  𝟘ᶜ▸[𝟘ᵐ?] ok = ▸-cong (PE.sym $ 𝟘ᵐ?≡𝟘ᵐ {ok = ok}) ∘→ ▸-𝟘

  -- If a term is well-resourced with respect to any context and mode,
  -- then it is well-resourced with respect to some usage context and
  -- the mode 𝟘ᵐ?.

  ▸-𝟘ᵐ? : γ ▸[ m ] t → ∃ λ δ → δ ▸[ 𝟘ᵐ? ] t
  ▸-𝟘ᵐ? {m = 𝟘ᵐ[ ok ]} ▸t =
    _ , ▸-cong (PE.sym $ 𝟘ᵐ?≡𝟘ᵐ {ok = ok}) (▸-𝟘 ▸t)
  ▸-𝟘ᵐ? {m = 𝟙ᵐ} {t} ▸t = 𝟘ᵐ?-elim
    (λ m → ∃ λ δ → δ ▸[ m ] t)
    (_ , ▸-𝟘 ▸t)
    (λ _ → _ , ▸t)

  private

    -- Some lemmas used in the implementation of ▸-𝟘.

    ▸-𝟘-J :
      γ₁ ▸[ 𝟘ᵐ? ] A →
      γ₂ ▸[ m₁ ] t →
      γ₃ ∙ ⌜ m₂ ⌝ · p ∙ ⌜ m₂ ⌝ · q ▸[ m₂ ] B →
      γ₄ ▸[ m₃ ] u →
      γ₅ ▸[ m₁ ] v →
      γ₆ ▸[ m₁ ] w →
      𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] J p q A t B u v w
    ▸-𝟘-J {γ₃} {m₂} {p} {q} {B} {ok} ▸A ▸t ▸B ▸u ▸v ▸w
      with J-view p q 𝟘ᵐ[ ok ]
    … | is-other ≤some ≢𝟘 = sub
      (Jₘ ≤some ≢𝟘 ▸A (▸-𝟘 ▸t)
         (sub (▸-𝟘 ▸B) $ begin
            𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · q  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
            𝟘ᶜ                  ∎)
         (▸-𝟘 ▸u) (▸-𝟘 ▸v) (▸-𝟘 ▸w))
      (begin
         𝟘ᶜ                                 ≈˘⟨ ω·ᶜ+ᶜ⁵𝟘ᶜ ⟩
         ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
      where
      open CR
    … | is-some-yes ≡some (p≡𝟘 , q≡𝟘) = sub
      (J₀ₘ₁ ≡some p≡𝟘 q≡𝟘 ▸A (▸-𝟘ᵐ? ▸t .proj₂) (▸-𝟘 ▸B) (▸-𝟘 ▸u)
         (▸-𝟘ᵐ? ▸v .proj₂) (▸-𝟘ᵐ? ▸w .proj₂))
      (begin
         𝟘ᶜ               ≈˘⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
         ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
      where
      open CR
    … | is-all ≡all = J₀ₘ₂
      ≡all ▸A (𝟘ᶜ▸[𝟘ᵐ?] ok ▸t)
      (𝟘ᵐ?-elim (λ m → ∃ λ δ → δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · q ▸[ m ] B)
         ( 𝟘ᶜ
         , sub (▸-𝟘 ▸B) (begin
             𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · q  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
             𝟘ᶜ                  ∎)
         )
         (λ not-ok →
              γ₃
            , sub (▸-cong (only-𝟙ᵐ-without-𝟘ᵐ not-ok) ▸B) (begin
                γ₃ ∙ 𝟙 · p ∙ 𝟙 · q            ≈⟨ ≈ᶜ-refl ∙
                                                 cong (λ m → ⌜ m ⌝ · p) (Mode-propositional-without-𝟘ᵐ {m₁ = 𝟙ᵐ} {m₂ = m₂} not-ok) ∙
                                                 cong (λ m → ⌜ m ⌝ · q) (Mode-propositional-without-𝟘ᵐ {m₁ = 𝟙ᵐ} {m₂ = m₂} not-ok) ⟩
                γ₃ ∙ ⌜ m₂ ⌝ · p ∙ ⌜ m₂ ⌝ · q  ∎))
         .proj₂)
      (▸-𝟘 ▸u) (𝟘ᶜ▸[𝟘ᵐ?] ok ▸v) (𝟘ᶜ▸[𝟘ᵐ?] ok ▸w)
      where
      open CR

    ▸-𝟘-K :
      γ₁ ▸[ 𝟘ᵐ? ] A →
      γ₂ ▸[ m₁ ] t →
      γ₃ ∙ ⌜ m₂ ⌝ · p ▸[ m₂ ] B →
      γ₄ ▸[ m₃ ] u →
      γ₅ ▸[ m₁ ] v →
      𝟘ᶜ ▸[ 𝟘ᵐ[ ok ] ] K p A t B u v
    ▸-𝟘-K {γ₃} {m₂} {p} {B} {ok} ▸A ▸t ▸B ▸u ▸v with K-view p 𝟘ᵐ[ ok ]
    … | is-other ≤some ≢𝟘 = sub
      (Kₘ ≤some ≢𝟘 ▸A (▸-𝟘 ▸t)
         (sub (▸-𝟘 ▸B) $ begin
            𝟘ᶜ ∙ 𝟘 · p  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
            𝟘ᶜ          ∎)
         (▸-𝟘 ▸u) (▸-𝟘 ▸v))
      (begin
         𝟘ᶜ                           ≈˘⟨ ω·ᶜ+ᶜ⁴𝟘ᶜ ⟩
         ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
      where
      open CR
    … | is-some-yes ≡some p≡𝟘 = sub
      (K₀ₘ₁ ≡some p≡𝟘 ▸A (▸-𝟘ᵐ? ▸t .proj₂) (▸-𝟘 ▸B) (▸-𝟘 ▸u)
         (▸-𝟘ᵐ? ▸v .proj₂))
      (begin
         𝟘ᶜ               ≈˘⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
         ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ∎)
      where
      open CR
    … | is-all ≡all = K₀ₘ₂
      ≡all ▸A (𝟘ᶜ▸[𝟘ᵐ?] ok ▸t)
      (𝟘ᵐ?-elim (λ m → ∃ λ δ → δ ∙ ⌜ m ⌝ · p ▸[ m ] B)
         ( 𝟘ᶜ
         , sub (▸-𝟘 ▸B) (begin
             𝟘ᶜ ∙ 𝟘 · p  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
             𝟘ᶜ          ∎)
         )
         (λ not-ok →
              γ₃
            , sub (▸-cong (only-𝟙ᵐ-without-𝟘ᵐ not-ok) ▸B) (begin
                γ₃ ∙ 𝟙 · p       ≈⟨ ≈ᶜ-refl ∙ cong (λ m → ⌜ m ⌝ · p) (Mode-propositional-without-𝟘ᵐ {m₁ = 𝟙ᵐ} {m₂ = m₂} not-ok) ⟩
                γ₃ ∙ ⌜ m₂ ⌝ · p  ∎))
         .proj₂)
      (▸-𝟘 ▸u) (𝟘ᶜ▸[𝟘ᵐ?] ok ▸v)
      where
      open CR

  ▸-𝟘 Uₘ =
    Uₘ
  ▸-𝟘 ℕₘ =
    ℕₘ
  ▸-𝟘 Emptyₘ =
    Emptyₘ
  ▸-𝟘 Unitₘ =
    Unitₘ
  ▸-𝟘 (ΠΣₘ {q} F G) = sub
    (ΠΣₘ (▸-𝟘 F)
       (sub (▸-𝟘 G) $ begin
          𝟘ᶜ ∙ 𝟘 · q  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
          𝟘ᶜ ∙ 𝟘      ∎))
    (begin
       𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
       𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
    where
    open CR
  ▸-𝟘 (var {x}) = sub var
    (begin
       𝟘ᶜ          ≡˘⟨ 𝟘ᶜ,≔𝟘 ⟩
       𝟘ᶜ , x ≔ 𝟘  ∎)
    where
    open CR
  ▸-𝟘 (lamₘ {p} t) = lamₘ
    (sub (▸-𝟘 t) $ begin
       𝟘ᶜ ∙ 𝟘 · p  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
       𝟘ᶜ          ∎)
    where
    open CR
  ▸-𝟘 (_∘ₘ_ {p} t u) = sub
    (▸-𝟘 t ∘ₘ ▸-𝟘 u)
    (begin
       𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
       p ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
       𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ  ∎)
    where
    open CR
  ▸-𝟘 (prodʷₘ {p} t u) = sub
    (prodʷₘ (▸-𝟘 t) (▸-𝟘 u))
    (begin
       𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
       p ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
       p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
    where
    open CR
  ▸-𝟘 (prodˢₘ {p} t u) = sub
    (prodˢₘ (▸-𝟘 t) (▸-𝟘 u))
    (begin
       𝟘ᶜ             ≈˘⟨ ∧ᶜ-idem _ ⟩
       𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈˘⟨ ∧ᶜ-congʳ $ ·ᶜ-zeroʳ _ ⟩
       p ·ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ  ∎)
    where
    open CR
  ▸-𝟘 {ok} (fstₘ _ t _ _) = fstₘ
    𝟘ᵐ[ ok ]
    (▸-𝟘 t)
    refl
    (λ ())
  ▸-𝟘 (sndₘ t) =
    sndₘ (▸-𝟘 t)
  ▸-𝟘 (prodrecₘ {r} {p} t u A ok) = sub
    (prodrecₘ
       (▸-𝟘 t)
       (sub (▸-𝟘 u) $ begin
          𝟘ᶜ ∙ 𝟘 · r · p ∙ 𝟘 · r  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
          𝟘ᶜ                      ∎)
       A
       (Prodrec-allowed-·ᵐ ok))
    (begin
       𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
       r ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
       r ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
    where
    open CR
  ▸-𝟘 zeroₘ =
    zeroₘ
  ▸-𝟘 (sucₘ t) =
    sucₘ (▸-𝟘 t)
  ▸-𝟘 (natrecₘ {p} {r} ▸z ▸s ▸n ▸A) = sub
    (natrecₘ (▸-𝟘 ▸z)
       (sub (▸-𝟘 ▸s) $ begin
          𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · r  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
          𝟘ᶜ                  ∎)
       (▸-𝟘 ▸n)
       ▸A)
    (begin
       𝟘ᶜ                ≈˘⟨ nrᶜ-𝟘ᶜ ⟩
       nrᶜ p r 𝟘ᶜ 𝟘ᶜ 𝟘ᶜ  ∎)
    where
    open import Graded.Modality.Dedicated-nr.Instance
    open CR
  ▸-𝟘 (natrec-no-nrₘ {p} {r} γ▸z δ▸s η▸n θ▸A χ≤γ χ≤δ χ≤η fix) =
    natrec-no-nrₘ (▸-𝟘 γ▸z)
      (sub (▸-𝟘 δ▸s) $ begin
         𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · r  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
         𝟘ᶜ                  ∎)
      (▸-𝟘 η▸n)
      θ▸A
      ≤ᶜ-refl
      (λ _ → ≤ᶜ-refl)
      ≤ᶜ-refl
      (begin
         𝟘ᶜ                        ≈˘⟨ +ᶜ-identityʳ _ ⟩
         𝟘ᶜ +ᶜ 𝟘ᶜ                  ≈˘⟨ +ᶜ-cong (·ᶜ-zeroʳ _) (·ᶜ-zeroʳ _) ⟩
         p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityˡ _ ⟩
         𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ +ᶜ r ·ᶜ 𝟘ᶜ  ∎)
    where
    open CR
  ▸-𝟘 (emptyrecₘ {p} e A ok) = sub
    (emptyrecₘ (▸-𝟘 e) A (Emptyrec-allowed-·ᵐ ok))
    (begin
       𝟘ᶜ       ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
       p ·ᶜ 𝟘ᶜ  ∎)
    where
    open CR
  ▸-𝟘 starʷₘ =
    starʷₘ
  ▸-𝟘 (starˢₘ {γ} ok) = sub
    (starˢₘ ok)
    (begin
       𝟘ᶜ      ≈˘⟨ ·ᶜ-zeroˡ _ ⟩
       𝟘 ·ᶜ γ  ∎)
    where
    open CR
  ▸-𝟘 (unitrecₘ {p} ▸t ▸u ▸A ok) = sub
    (unitrecₘ (▸-𝟘 ▸t) (▸-𝟘 ▸u) ▸A (Unitrec-allowed-·ᵐ ok))
    (begin
       𝟘ᶜ             ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
       p ·ᶜ 𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
       p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
    where
    open CR
  ▸-𝟘 (Idₘ ok ▸A ▸t ▸u) = sub
    (Idₘ ok ▸A (▸-𝟘 ▸t) (▸-𝟘 ▸u))
    (begin
       𝟘ᶜ        ≈˘⟨ +ᶜ-identityʳ _ ⟩
       𝟘ᶜ +ᶜ 𝟘ᶜ  ∎)
    where
    open CR
  ▸-𝟘 (Id₀ₘ ok ▸A ▸t ▸u) =
    Id₀ₘ ok ▸A ▸t ▸u
  ▸-𝟘 rflₘ =
    rflₘ
  ▸-𝟘 (Jₘ _ _ ▸A ▸t ▸B ▸u ▸v ▸w) =
    ▸-𝟘-J ▸A ▸t ▸B ▸u ▸v ▸w
  ▸-𝟘 {m} (J₀ₘ₁ {γ₃} _ refl refl ▸A ▸t ▸B ▸u ▸v ▸w) =
    ▸-𝟘-J ▸A ▸t
      (sub ▸B $ begin
         γ₃ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
         γ₃ ∙ 𝟘 ∙ 𝟘                  ∎)
      ▸u ▸v ▸w
    where
    open CR
  ▸-𝟘 (J₀ₘ₂ _ ▸A ▸t ▸B ▸u ▸v ▸w) =
    ▸-𝟘-J ▸A ▸t ▸B ▸u ▸v ▸w
  ▸-𝟘 (Kₘ _ _ ▸A ▸t ▸B ▸u ▸v) =
    ▸-𝟘-K ▸A ▸t ▸B ▸u ▸v
  ▸-𝟘 {m} (K₀ₘ₁ {γ₃} _ refl ▸A ▸t ▸B ▸u ▸v) =
    ▸-𝟘-K ▸A ▸t
      (sub ▸B $ begin
         γ₃ ∙ ⌜ m ⌝ · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
         γ₃ ∙ 𝟘          ∎)
      ▸u ▸v
    where
    open CR
  ▸-𝟘 (K₀ₘ₂ _ ▸A ▸t ▸B ▸u ▸v) =
    ▸-𝟘-K ▸A ▸t ▸B ▸u ▸v
  ▸-𝟘 ([]-congₘ ▸A ▸t ▸u ▸v) =
    []-congₘ ▸A ▸t ▸u ▸v
  ▸-𝟘 (sub γ▸t _) =
    ▸-𝟘 γ▸t

opaque

  -- The relation _▸[_]_ respects multiplication (in a certain sense).

  ▸-· : γ ▸[ m ] t → ⌜ m′ ⌝ ·ᶜ γ ▸[ m′ ·ᵐ m ] t
  ▸-· {γ} {m′ = 𝟘ᵐ} ▸t = sub (▸-𝟘 ▸t) $ begin
    𝟘 ·ᶜ γ  ≈⟨ ·ᶜ-zeroˡ _ ⟩
    𝟘ᶜ      ∎
    where
    open CR
  ▸-· {γ} {m′ = 𝟙ᵐ} ▸t = sub ▸t $ begin
    𝟙 ·ᶜ γ  ≈⟨ ·ᶜ-identityˡ _ ⟩
    γ       ∎
    where
    open CR

opaque

  -- A variant of ▸-·.

  ▸-ᵐ· : γ ▸[ m ] t → ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ m ᵐ· p ] t
  ▸-ᵐ· {m} {p}  =
    ▸-cong
      (⌞ p ⌟ ·ᵐ m  ≡⟨ ·ᵐ-comm ⌞ _ ⌟ _ ⟩
       m ·ᵐ ⌞ p ⌟  ≡⟨ ·ᵐ⌞⌟ ⟩
       m ᵐ· p      ∎) ∘→
    ▸-·
    where
    open Tools.Reasoning.PropositionalEquality

-- The relation _▸[_]_ respects multiplication (in a certain sense).

▸-·′ : γ ▸[ m ] t → ⌜ m ⌝ ·ᶜ γ ▸[ m ] t
▸-·′ ▸t = ▸-cong ·ᵐ-idem (▸-· ▸t)

-- If a term does not use any resources, then it is well-resourced
-- with respect to any mode.

𝟘ᶜ▸[𝟙ᵐ]→ : 𝟘ᶜ ▸[ 𝟙ᵐ ] t → 𝟘ᶜ ▸[ m ] t
𝟘ᶜ▸[𝟙ᵐ]→ {m = 𝟘ᵐ} = ▸-𝟘
𝟘ᶜ▸[𝟙ᵐ]→ {m = 𝟙ᵐ} = idᶠ

-- A form of monotonicity for _▸[_]_.

▸-≤ : p ≤ q → ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t → ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
▸-≤ {p = p} {q = q} {γ = γ} {t = t} p≤q = lemma _ _ refl refl
  where
  lemma :
    ∀ m₁ m₂ → ⌞ p ⌟ ≡ m₁ → ⌞ q ⌟ ≡ m₂ →
    ⌜ m₁ ⌝ ·ᶜ γ ▸[ m₁ ] t → ⌜ m₂ ⌝ ·ᶜ γ ▸[ m₂ ] t
  lemma 𝟘ᵐ 𝟘ᵐ _ _ ▸t = ▸-cong 𝟘ᵐ-cong ▸t
  lemma 𝟙ᵐ 𝟙ᵐ _ _ ▸t = ▸t
  lemma 𝟙ᵐ 𝟘ᵐ _ _ ▸t = sub (▸-𝟘 ▸t) (begin
    𝟘 ·ᶜ γ  ≈⟨ ·ᶜ-zeroˡ _ ⟩
    𝟘ᶜ      ∎)
    where
    open Tools.Reasoning.PartialOrder ≤ᶜ-poset
  lemma 𝟘ᵐ[ ok ] 𝟙ᵐ ⌞p⌟≡𝟘ᵐ ⌞q⌟≡𝟙ᵐ ▸t =
    ⊥-elim (⌞⌟≡𝟙ᵐ→≢𝟘 ok ⌞q⌟≡𝟙ᵐ (𝟘ᵐ.𝟘≮ ok (begin
      𝟘  ≈˘⟨ ⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p⌟≡𝟘ᵐ ⟩
      p  ≤⟨ p≤q ⟩
      q  ∎)))
    where
    open Tools.Reasoning.PartialOrder ≤-poset

-- If t is well-resourced with respect to the usage context γ, then t
-- is well-resourced with respect to the mode ⌞ p ⌟ and some usage
-- context δ for which p ·ᶜ γ ≈ᶜ p ·ᶜ δ.

▸[𝟙ᵐ]→▸[⌞⌟] :
  γ ▸[ 𝟙ᵐ ] t →
  ∃ λ δ → δ ▸[ ⌞ p ⌟ ] t × p ·ᶜ γ ≈ᶜ p ·ᶜ δ
▸[𝟙ᵐ]→▸[⌞⌟] {γ = γ} {t = t} {p = p} ▸t = lemma _ refl
  where
  lemma : ∀ m → ⌞ p ⌟ ≡ m → ∃ λ δ → δ ▸[ m ] t × p ·ᶜ γ ≈ᶜ p ·ᶜ δ
  lemma 𝟙ᵐ       _      = _ , ▸t , ≈ᶜ-refl
  lemma 𝟘ᵐ[ ok ] ⌞p⌟≡𝟘ᵐ =
      _
    , ▸-𝟘 ▸t
    , (let open Tools.Reasoning.Equivalence Conₘ-setoid in begin
         p ·ᶜ γ   ≈⟨ ·ᶜ-congʳ (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p⌟≡𝟘ᵐ) ⟩
         𝟘 ·ᶜ γ   ≈⟨ ·ᶜ-zeroˡ _ ⟩
         𝟘ᶜ       ≈˘⟨ ·ᶜ-zeroʳ _ ⟩
         p ·ᶜ 𝟘ᶜ  ∎)

------------------------------------------------------------------------
-- The lemma ▸-𝟘ᵐ

-- If γ ▸[ 𝟘ᵐ[ ok ] ] t, then γ ≤ᶜ 𝟘ᶜ.

▸-𝟘ᵐ : γ ▸[ 𝟘ᵐ[ ok ] ] t → γ ≤ᶜ 𝟘ᶜ
▸-𝟘ᵐ Uₘ =
  ≤ᶜ-refl
▸-𝟘ᵐ ℕₘ =
  ≤ᶜ-refl
▸-𝟘ᵐ Emptyₘ =
  ≤ᶜ-refl
▸-𝟘ᵐ Unitₘ =
  ≤ᶜ-refl
▸-𝟘ᵐ (ΠΣₘ {γ = γ} {δ = δ} γ▸ δ▸) = begin
  γ +ᶜ δ    ≤⟨ +ᶜ-monotone (▸-𝟘ᵐ γ▸) (tailₘ-monotone (▸-𝟘ᵐ δ▸)) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityˡ _ ⟩
  𝟘ᶜ        ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (var {x = x}) = begin
  𝟘ᶜ , x ≔ 𝟘  ≡⟨ 𝟘ᶜ,≔𝟘 ⟩
  𝟘ᶜ          ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (lamₘ γ▸) =
  tailₘ-monotone (▸-𝟘ᵐ γ▸)
▸-𝟘ᵐ (_∘ₘ_ {γ = γ} {δ = δ} {p = p} γ▸ δ▸) = begin
  γ +ᶜ p ·ᶜ δ    ≤⟨ +ᶜ-monotone (▸-𝟘ᵐ γ▸) (·ᶜ-monotoneʳ (▸-𝟘ᵐ δ▸)) ⟩
  𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityˡ _ ⟩
  p ·ᶜ 𝟘ᶜ        ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ             ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (prodʷₘ {γ = γ} {p = p} {δ = δ} γ▸ δ▸) = begin
  p ·ᶜ γ +ᶜ δ    ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ (▸-𝟘ᵐ γ▸)) (▸-𝟘ᵐ δ▸) ⟩
  p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
  p ·ᶜ 𝟘ᶜ        ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ             ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (prodˢₘ {γ = γ} {p = p} {δ = δ} γ▸ δ▸) = begin
  p ·ᶜ γ ∧ᶜ δ    ≤⟨ ∧ᶜ-monotone (·ᶜ-monotoneʳ (▸-𝟘ᵐ γ▸)) (▸-𝟘ᵐ δ▸) ⟩
  p ·ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ  ≈⟨ ∧ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
  𝟘ᶜ ∧ᶜ 𝟘ᶜ       ≈⟨ ∧ᶜ-idem _ ⟩
  𝟘ᶜ             ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (fstₘ _ γ▸ eq _) = lemma γ▸ eq
  where
  lemma : γ ▸[ m ] t → m ≡ 𝟘ᵐ[ ok ] → γ ≤ᶜ 𝟘ᶜ
  lemma γ▸ refl = ▸-𝟘ᵐ γ▸
▸-𝟘ᵐ (sndₘ γ▸) =
  ▸-𝟘ᵐ γ▸
▸-𝟘ᵐ (prodrecₘ {γ = γ} {r = r} {δ = δ} γ▸ δ▸ _ _) = begin
  r ·ᶜ γ +ᶜ δ    ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ (▸-𝟘ᵐ γ▸)) (tailₘ-monotone (tailₘ-monotone (▸-𝟘ᵐ δ▸))) ⟩
  r ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
  r ·ᶜ 𝟘ᶜ        ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ             ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ zeroₘ =
  ≤ᶜ-refl
▸-𝟘ᵐ (sucₘ γ▸) =
  ▸-𝟘ᵐ γ▸
▸-𝟘ᵐ
  (natrecₘ {γ = γ} {δ = δ} {p = p} {r = r} {η = η} γ▸ δ▸ η▸ _) = begin
  nrᶜ p r γ δ η     ≤⟨ nrᶜ-monotone (▸-𝟘ᵐ γ▸) (tailₘ-monotone (tailₘ-monotone (▸-𝟘ᵐ δ▸))) (▸-𝟘ᵐ η▸) ⟩
  nrᶜ p r 𝟘ᶜ 𝟘ᶜ 𝟘ᶜ  ≈⟨ nrᶜ-𝟘ᶜ ⟩
  𝟘ᶜ                ∎
  where
  open import Graded.Modality.Dedicated-nr.Instance
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ
  (natrec-no-nrₘ {γ = γ} {χ = χ} γ▸ _ _ _ χ≤γ _ _ _) = begin
  χ   ≤⟨ χ≤γ ⟩
  γ   ≤⟨ ▸-𝟘ᵐ γ▸ ⟩
  𝟘ᶜ  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (emptyrecₘ {γ = γ} {p = p} γ▸ _ _) = begin
  p ·ᶜ γ   ≤⟨ ·ᶜ-monotoneʳ (▸-𝟘ᵐ γ▸) ⟩
  p ·ᶜ 𝟘ᶜ  ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ       ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ starʷₘ = ≤ᶜ-refl
▸-𝟘ᵐ (starˢₘ prop) = ≤ᶜ-reflexive (·ᶜ-zeroˡ _)
▸-𝟘ᵐ (unitrecₘ {γ = γ} {p = p} {δ = δ} γ▸ δ▸ η▸ ok) = begin
  p ·ᶜ γ +ᶜ δ     ≤⟨ +ᶜ-monotone (·ᶜ-monotoneʳ (▸-𝟘ᵐ γ▸)) (▸-𝟘ᵐ δ▸) ⟩
  p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
  p ·ᶜ 𝟘ᶜ        ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ             ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (Idₘ {δ = δ} {η = η} _ _ δ▸ η▸) = begin
  δ +ᶜ η    ≤⟨ +ᶜ-monotone (▸-𝟘ᵐ δ▸) (▸-𝟘ᵐ η▸) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ  ≈⟨ +ᶜ-identityʳ _ ⟩
  𝟘ᶜ        ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (Id₀ₘ _ _ _ _) =
  ≤ᶜ-refl
▸-𝟘ᵐ rflₘ =
  ≤ᶜ-refl
▸-𝟘ᵐ (Jₘ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} _ _ _ γ₂▸ γ₃▸ γ₄▸ γ₅▸ γ₆▸) = begin
  ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)  ≤⟨ ·ᶜ-monotoneʳ $
                                        +ᶜ-monotone (▸-𝟘ᵐ γ₂▸) $
                                        +ᶜ-monotone (tailₘ-monotone (tailₘ-monotone (▸-𝟘ᵐ γ₃▸))) $
                                        +ᶜ-monotone (▸-𝟘ᵐ γ₄▸) $
                                        +ᶜ-monotone (▸-𝟘ᵐ γ₅▸) (▸-𝟘ᵐ γ₆▸) ⟩
  ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ)  ≈⟨ ω·ᶜ+ᶜ⁵𝟘ᶜ ⟩
  𝟘ᶜ                                 ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (J₀ₘ₁ {γ₃} {γ₄} _ _ _ _ _ γ₃▸ γ₄▸ _ _) = begin
  ω ·ᶜ (γ₃ +ᶜ γ₄)  ≤⟨ ·ᶜ-monotoneʳ $
                      +ᶜ-monotone (tailₘ-monotone (tailₘ-monotone (▸-𝟘ᵐ γ₃▸))) (▸-𝟘ᵐ γ₄▸) ⟩
  ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ≈⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
  𝟘ᶜ               ∎
  where
  open CR
▸-𝟘ᵐ (J₀ₘ₂ _ _ _ _ γ₄▸ _ _) =
  ▸-𝟘ᵐ γ₄▸
▸-𝟘ᵐ (Kₘ {γ₂} {γ₃} {γ₄} {γ₅} _ _ _ γ₂▸ γ₃▸ γ₄▸ γ₅▸) = begin
  ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)  ≤⟨ ·ᶜ-monotoneʳ $
                                  +ᶜ-monotone (▸-𝟘ᵐ γ₂▸) $
                                  +ᶜ-monotone (tailₘ-monotone (▸-𝟘ᵐ γ₃▸)) $
                                  +ᶜ-monotone (▸-𝟘ᵐ γ₄▸) (▸-𝟘ᵐ γ₅▸) ⟩
  ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ)  ≈⟨ ω·ᶜ+ᶜ⁴𝟘ᶜ ⟩
  𝟘ᶜ                           ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset
▸-𝟘ᵐ (K₀ₘ₁ {γ₃} {γ₄} _ _ _ _ γ₃▸ γ₄▸ _) = begin
  ω ·ᶜ (γ₃ +ᶜ γ₄)  ≤⟨ ·ᶜ-monotoneʳ $
                      +ᶜ-monotone (tailₘ-monotone (▸-𝟘ᵐ γ₃▸)) (▸-𝟘ᵐ γ₄▸) ⟩
  ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)  ≈⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
  𝟘ᶜ               ∎
  where
  open CR
▸-𝟘ᵐ (K₀ₘ₂ _ _ _ _ γ₄▸ _) =
  ▸-𝟘ᵐ γ₄▸
▸-𝟘ᵐ ([]-congₘ _ _ _ _) =
  ≤ᶜ-refl
▸-𝟘ᵐ (sub {γ = γ} {δ = δ} γ▸ δ≤γ) = begin
  δ   ≤⟨ δ≤γ ⟩
  γ   ≤⟨ ▸-𝟘ᵐ γ▸ ⟩
  𝟘ᶜ  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

------------------------------------------------------------------------
-- Inversion lemmas

-- A kind of inversion lemma for _▸[_]_ related to multiplication.

▸-⌞·⌟ :
  ⌜ ⌞ p · q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p · q ⌟ ] t →
  (⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t) ⊎ (⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t)
▸-⌞·⌟ {p = p} {q = q} {γ = γ} ▸t =
  lemma _ _ refl refl
    (subst (λ m → ⌜ m ⌝ ·ᶜ _ ▸[ m ] _) (PE.sym ⌞⌟·ᵐ) ▸t)
  where
  lemma :
    ∀ m₁ m₂ → ⌞ p ⌟ ≡ m₁ → ⌞ q ⌟ ≡ m₂ →
    ⌜ m₁ ·ᵐ m₂ ⌝ ·ᶜ γ ▸[ m₁ ·ᵐ m₂ ] t →
    (⌜ m₁ ⌝ ·ᶜ γ ▸[ m₁ ] t) ⊎ (⌜ m₂ ⌝ ·ᶜ γ ▸[ m₂ ] t)
  lemma 𝟘ᵐ _  _ _ ▸t = inj₁ ▸t
  lemma 𝟙ᵐ 𝟘ᵐ _ _ ▸t = inj₂ ▸t
  lemma 𝟙ᵐ 𝟙ᵐ _ _ ▸t = inj₁ ▸t

-- If m₂ is 𝟘ᵐ[ ok ] whenever m₁ is 𝟘ᵐ[ ok ], then one can convert
-- from ⌜ m₁ ⌝ ·ᶜ γ ▸[ m₁ ] t to ⌜ m₂ ⌝ ·ᶜ γ ▸[ m₂ ] t.

▸-conv :
  (∀ ok → m₁ ≡ 𝟘ᵐ[ ok ] → m₂ ≡ 𝟘ᵐ[ ok ]) →
  ⌜ m₁ ⌝ ·ᶜ γ ▸[ m₁ ] t →
  ⌜ m₂ ⌝ ·ᶜ γ ▸[ m₂ ] t
▸-conv {m₁ = 𝟘ᵐ} {m₂ = 𝟘ᵐ} _ ▸t =
  ▸-cong 𝟘ᵐ-cong ▸t
▸-conv {m₁ = 𝟙ᵐ} {m₂ = 𝟙ᵐ} _ ▸t =
  ▸t
▸-conv {m₁ = 𝟘ᵐ} {m₂ = 𝟙ᵐ} 𝟘ᵐ≡𝟘ᵐ→𝟙ᵐ≡𝟘ᵐ ▸t =
  case 𝟘ᵐ≡𝟘ᵐ→𝟙ᵐ≡𝟘ᵐ _ PE.refl of λ ()
▸-conv {m₁ = 𝟙ᵐ} {m₂ = 𝟘ᵐ} {γ = γ} hyp ▸t = sub
  (▸-· {m′ = 𝟘ᵐ} ▸t)
  (begin
    𝟘 ·ᶜ γ       ≈˘⟨ ·ᶜ-congˡ (·ᶜ-identityˡ _) ⟩
    𝟘 ·ᶜ 𝟙 ·ᶜ γ  ∎)
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

-- A kind of inversion lemma for _▸[_]_ related to addition.

▸-⌞+⌟ˡ :
  ⌜ ⌞ p + q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p + q ⌟ ] t →
  ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t
▸-⌞+⌟ˡ = ▸-conv λ ok ⌞p+q⌟≡𝟘ᵐ →
  ≡𝟘→⌞⌟≡𝟘ᵐ (𝟘ᵐ.+-positiveˡ ok (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p+q⌟≡𝟘ᵐ))

-- A kind of inversion lemma for _▸[_]_ related to addition.

▸-⌞+⌟ʳ :
  ⌜ ⌞ p + q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p + q ⌟ ] t →
  ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
▸-⌞+⌟ʳ ▸t =
  ▸-⌞+⌟ˡ (subst (λ m → ⌜ m ⌝ ·ᶜ _ ▸[ m ] _) (⌞⌟-cong (+-comm _ _)) ▸t)

-- A kind of inversion lemma for _▸[_]_ related to the meet operation.

▸-⌞∧⌟ˡ :
  ⌜ ⌞ p ∧ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ∧ q ⌟ ] t →
  ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t
▸-⌞∧⌟ˡ = ▸-conv λ ok ⌞p∧q⌟≡𝟘ᵐ →
  ≡𝟘→⌞⌟≡𝟘ᵐ (𝟘ᵐ.∧-positiveˡ ok (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p∧q⌟≡𝟘ᵐ))

-- A kind of inversion lemma for _▸[_]_ related to the meet operation.

▸-⌞∧⌟ʳ :
  ⌜ ⌞ p ∧ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ∧ q ⌟ ] t →
  ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
▸-⌞∧⌟ʳ ▸t =
  ▸-⌞∧⌟ˡ (subst (λ m → ⌜ m ⌝ ·ᶜ _ ▸[ m ] _) (⌞⌟-cong (∧-comm _ _)) ▸t)

-- A kind of inversion lemma for _▸[_]_ related to the star operation.

▸-⌞⊛⌟ˡ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  ⌜ ⌞ p ⊛ q ▷ r ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⊛ q ▷ r ⌟ ] t →
  ⌜ ⌞ p ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⌟ ] t
▸-⌞⊛⌟ˡ = ▸-conv λ ok ⌞p⊛q▷r⌟≡𝟘ᵐ →
  ≡𝟘→⌞⌟≡𝟘ᵐ (𝟘ᵐ.⊛≡𝟘ˡ ok (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p⊛q▷r⌟≡𝟘ᵐ))

-- A kind of inversion lemma for _▸[_]_ related to the star operation.

▸-⌞⊛⌟ʳ :
  ⦃ has-star : Has-star semiring-with-meet ⦄ →
  ⌜ ⌞ p ⊛ q ▷ r ⌟ ⌝ ·ᶜ γ ▸[ ⌞ p ⊛ q ▷ r ⌟ ] t →
  ⌜ ⌞ q ⌟ ⌝ ·ᶜ γ ▸[ ⌞ q ⌟ ] t
▸-⌞⊛⌟ʳ = ▸-conv λ ok ⌞p⊛q▷r⌟≡𝟘ᵐ →
  ≡𝟘→⌞⌟≡𝟘ᵐ (𝟘ᵐ.⊛≡𝟘ʳ ok (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞p⊛q▷r⌟≡𝟘ᵐ))

-- A kind of inversion lemma for _▸[_]_ related to the nr function.

▸-⌞nr⌟₁ :
  ∀ {n} ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  ⌜ ⌞ nr p r z s n ⌟ ⌝ ·ᶜ γ ▸[ ⌞ nr p r z s n ⌟ ] t →
  ⌜ ⌞ z ⌟ ⌝ ·ᶜ γ ▸[ ⌞ z ⌟ ] t
▸-⌞nr⌟₁ = ▸-conv λ ok ⌞nr-przsn⌟≡𝟘ᵐ →
  ≡𝟘→⌞⌟≡𝟘ᵐ $
  nr-positive ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄
    (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞nr-przsn⌟≡𝟘ᵐ) .proj₁

-- A kind of inversion lemma for _▸[_]_ related to the nr function.

▸-⌞nr⌟₂ :
  ∀ {n} ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  ⌜ ⌞ nr p r z s n ⌟ ⌝ ·ᶜ γ ▸[ ⌞ nr p r z s n ⌟ ] t →
  ⌜ ⌞ s ⌟ ⌝ ·ᶜ γ ▸[ ⌞ s ⌟ ] t
▸-⌞nr⌟₂ = ▸-conv λ ok ⌞nr-przsn⌟≡𝟘ᵐ →
  ≡𝟘→⌞⌟≡𝟘ᵐ $
  nr-positive ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄
    (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞nr-przsn⌟≡𝟘ᵐ) .proj₂ .proj₁

-- A kind of inversion lemma for _▸[_]_ related to the nr function.

▸-⌞nr⌟₃ :
  ∀ {n} ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  ⌜ ⌞ nr p r z s n ⌟ ⌝ ·ᶜ γ ▸[ ⌞ nr p r z s n ⌟ ] t →
  ⌜ ⌞ n ⌟ ⌝ ·ᶜ γ ▸[ ⌞ n ⌟ ] t
▸-⌞nr⌟₃ = ▸-conv λ ok ⌞nr-przsn⌟≡𝟘ᵐ →
  ≡𝟘→⌞⌟≡𝟘ᵐ $
  nr-positive ⦃ 𝟘-well-behaved = 𝟘-well-behaved ok ⦄
    (⌞⌟≡𝟘ᵐ→≡𝟘 ⌞nr-przsn⌟≡𝟘ᵐ) .proj₂ .proj₂

------------------------------------------------------------------------
-- The lemma Conₘ-interchange

private opaque

  -- Some lemmas used below.

  Conₘ-interchange₀₁ :
    ∀ δ₃ δ₄ → ω ·ᶜ (γ₃ +ᶜ γ₄) , x ≔ (ω ·ᶜ (δ₃ +ᶜ δ₄)) ⟨ x ⟩ ≡
    ω ·ᶜ ((γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ (γ₄ , x ≔ δ₄ ⟨ x ⟩))
  Conₘ-interchange₀₁ {γ₃} {γ₄} {x} δ₃ δ₄ =
    ω ·ᶜ (γ₃ +ᶜ γ₄) , x ≔ (ω ·ᶜ (δ₃ +ᶜ δ₄)) ⟨ x ⟩      ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-·ᶜ (δ₃ +ᶜ _) _ _ ⟩
    ω ·ᶜ (γ₃ +ᶜ γ₄) , x ≔ ω · (δ₃ +ᶜ δ₄) ⟨ x ⟩         ≡⟨ update-distrib-·ᶜ _ _ _ _ ⟩
    ω ·ᶜ (γ₃ +ᶜ γ₄ , x ≔ (δ₃ +ᶜ δ₄) ⟨ x ⟩)             ≡⟨ cong (_ ·ᶜ_) $
                                                          trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₃ _ _) $
                                                          update-distrib-+ᶜ _ _ _ _ _ ⟩
    ω ·ᶜ ((γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ (γ₄ , x ≔ δ₄ ⟨ x ⟩))  ∎
    where
    open Tools.Reasoning.PropositionalEquality

  Conₘ-interchange-J :
    ∀ δ₂ δ₃ δ₄ δ₅ δ₆ →
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ,
    x ≔ (ω ·ᶜ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅ +ᶜ δ₆)) ⟨ x ⟩ ≡
    ω ·ᶜ
     ((γ₂ , x ≔ δ₂ ⟨ x ⟩) +ᶜ (γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ
      (γ₄ , x ≔ δ₄ ⟨ x ⟩) +ᶜ (γ₅ , x ≔ δ₅ ⟨ x ⟩) +ᶜ
      (γ₆ , x ≔ δ₆ ⟨ x ⟩))
  Conₘ-interchange-J {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} {x} δ₂ δ₃ δ₄ δ₅ δ₆ =
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ,
    x ≔ (ω ·ᶜ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅ +ᶜ δ₆)) ⟨ x ⟩   ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-·ᶜ (δ₂ +ᶜ _) _ _ ⟩

    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ,
    x ≔ ω · (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅ +ᶜ δ₆) ⟨ x ⟩      ≡⟨ update-distrib-·ᶜ _ _ _ _ ⟩

    ω ·ᶜ
    (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆ ,
     x ≔ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅ +ᶜ δ₆) ⟨ x ⟩)        ≡⟨ cong (ω ·ᶜ_) $
                                                       trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₂ _ _) $
                                                       trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                       cong (_ +ᶜ_) $
                                                       trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₃ _ _) $
                                                       trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                       cong (_ +ᶜ_) $
                                                       trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₄ _ _) $
                                                       trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                       cong (_ +ᶜ_) $
                                                       trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₅ _ _) $
                                                       update-distrib-+ᶜ _ _ _ _ _ ⟩

    ω ·ᶜ
    ((γ₂ , x ≔ δ₂ ⟨ x ⟩) +ᶜ (γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ
     (γ₄ , x ≔ δ₄ ⟨ x ⟩) +ᶜ (γ₅ , x ≔ δ₅ ⟨ x ⟩) +ᶜ
     (γ₆ , x ≔ δ₆ ⟨ x ⟩))                           ∎
    where
    open Tools.Reasoning.PropositionalEquality

  Conₘ-interchange-K :
    ∀ δ₂ δ₃ δ₄ δ₅ →
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ,
    x ≔ (ω ·ᶜ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅)) ⟨ x ⟩ ≡
    ω ·ᶜ
     ((γ₂ , x ≔ δ₂ ⟨ x ⟩) +ᶜ (γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ
      (γ₄ , x ≔ δ₄ ⟨ x ⟩) +ᶜ (γ₅ , x ≔ δ₅ ⟨ x ⟩))
  Conₘ-interchange-K {γ₂} {γ₃} {γ₄} {γ₅} {x} δ₂ δ₃ δ₄ δ₅ =
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ,
    x ≔ (ω ·ᶜ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅)) ⟨ x ⟩                    ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-·ᶜ (δ₂ +ᶜ _) _ _ ⟩

    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ,
    x ≔ ω · (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅) ⟨ x ⟩                       ≡⟨ update-distrib-·ᶜ _ _ _ _ ⟩

    ω ·ᶜ
    (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ , x ≔ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅) ⟨ x ⟩)  ≡⟨ cong (ω ·ᶜ_) $
                                                                  trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₂ _ _) $
                                                                  trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                                  cong (_ +ᶜ_) $
                                                                  trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₃ _ _) $
                                                                  trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                                  cong (_ +ᶜ_) $
                                                                  trans (cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ₄ _ _) $
                                                                  update-distrib-+ᶜ _ _ _ _ _ ⟩
    ω ·ᶜ
    ((γ₂ , x ≔ δ₂ ⟨ x ⟩) +ᶜ (γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ
     (γ₄ , x ≔ δ₄ ⟨ x ⟩) +ᶜ (γ₅ , x ≔ δ₅ ⟨ x ⟩))               ∎
    where
    open Tools.Reasoning.PropositionalEquality

opaque

  -- The contents of two valid modality contexts can be freely
  -- interchanged.

  Conₘ-interchange :
    γ ▸[ m ] t → δ ▸[ m ] t → (x : Fin n) → (γ , x ≔ δ ⟨ x ⟩) ▸[ m ] t
  Conₘ-interchange (sub γ▸t γ≤γ′) δ▸t x = sub
    (Conₘ-interchange γ▸t δ▸t x)
    (update-monotoneˡ x γ≤γ′)

  Conₘ-interchange {m} {δ} (var {x = y}) ▸var x = sub
    var
    (begin
       𝟘ᶜ , y ≔ ⌜ m ⌝ , x ≔ δ ⟨ x ⟩                 ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-var ▸var ⟩
       𝟘ᶜ , y ≔ ⌜ m ⌝ , x ≔ (𝟘ᶜ , y ≔ ⌜ m ⌝) ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ , y ≔ ⌜ m ⌝                               ∎)
    where
    open CR

  Conₘ-interchange {δ} Uₘ ▸U x = sub
    Uₘ
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-U ▸U ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange {δ = η} (ΠΣₘ {γ} {δ} ▸t ▸u) ▸ΠΣ x =
    case inv-usage-ΠΣ ▸ΠΣ of λ
      (invUsageΠΣ {δ = γ′} {η = δ′} ▸t′ ▸u′ η≤γ′+δ′) → sub
    (ΠΣₘ (Conₘ-interchange ▸t ▸t′ x) (Conₘ-interchange ▸u ▸u′ (x +1)))
    (begin
       γ +ᶜ δ , x ≔ η ⟨ x ⟩                      ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤γ′+δ′ ⟩
       γ +ᶜ δ , x ≔ (γ′ +ᶜ δ′) ⟨ x ⟩             ≡⟨ cong (_ , x ≔_) (lookup-distrib-+ᶜ γ′ _ _) ⟩
       γ +ᶜ δ , x ≔ γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩          ≡⟨ update-distrib-+ᶜ γ _ _ _ x ⟩
       (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ∎)
    where
    open CR

  Conₘ-interchange {δ} (lamₘ {γ} ▸t) ▸lam x =
    case inv-usage-lam ▸lam of λ
      (invUsageLam {δ = γ′} ▸t′ δ≤γ′) → sub
    (lamₘ (Conₘ-interchange ▸t ▸t′ (x +1)))
    (begin
       γ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤γ′ ⟩
       γ , x ≔ γ′ ⟨ x ⟩  ∎)
    where
    open CR

  Conₘ-interchange {δ = η} (_∘ₘ_ {γ} {δ} {p} ▸t ▸u) ▸∘ x =
    case inv-usage-app ▸∘ of λ
      (invUsageApp {δ = γ′} {η = δ′} ▸t′ ▸u′ η≤γ′+pδ′) → sub
    (Conₘ-interchange ▸t ▸t′ x ∘ₘ Conₘ-interchange ▸u ▸u′ x)
    (begin
       γ +ᶜ p ·ᶜ δ , x ≔ η ⟨ x ⟩                             ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤γ′+pδ′ ⟩
       (γ +ᶜ p ·ᶜ δ) , x ≔ (γ′ +ᶜ p ·ᶜ δ′) ⟨ x ⟩             ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-+ᶜ γ′ _ _ ⟩
       (γ +ᶜ p ·ᶜ δ) , x ≔ γ′ ⟨ x ⟩ + (p ·ᶜ δ′) ⟨ x ⟩        ≡⟨ update-distrib-+ᶜ _ _ _ _ _ ⟩
       (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (p ·ᶜ δ , x ≔ (p ·ᶜ δ′) ⟨ x ⟩)  ≡⟨ cong (_ +ᶜ_) $ cong (_ , _ ≔_) $ lookup-distrib-·ᶜ δ′ _ _ ⟩
       (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (p ·ᶜ δ , x ≔ p · δ′ ⟨ x ⟩)     ≡⟨ cong (_ +ᶜ_) $ update-distrib-·ᶜ _ _ _ _ ⟩
       (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ p ·ᶜ (δ , x ≔ δ′ ⟨ x ⟩)         ∎)
    where
    open CR

  Conₘ-interchange {δ = η} (prodʷₘ {γ} {p} {δ} ▸t ▸u) ▸prod x =
    case inv-usage-prodʷ ▸prod of λ
      (invUsageProdʷ {δ = γ′} {η = δ′} ▸t′ ▸u′ η≤pγ′+δ′) → sub
    (prodʷₘ (Conₘ-interchange ▸t ▸t′ x) (Conₘ-interchange ▸u ▸u′ x))
    (begin
       p ·ᶜ γ +ᶜ δ , x ≔ η ⟨ x ⟩                          ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤pγ′+δ′ ⟩
       p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′ +ᶜ δ′) ⟨ x ⟩            ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-+ᶜ (_ ·ᶜ γ′) _ _ ⟩
       p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′) ⟨ x ⟩ + δ′ ⟨ x ⟩       ≡⟨ cong (_,_≔_ _ _) $ cong (_+ _) $ lookup-distrib-·ᶜ γ′ _ _ ⟩
       p ·ᶜ γ +ᶜ δ , x ≔ p · γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩          ≡⟨ update-distrib-+ᶜ _ _ _ _ _ ⟩
       (p ·ᶜ γ , x ≔ p · γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡⟨ cong (_+ᶜ _) $ update-distrib-·ᶜ _ _ _ _ ⟩
       p ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)      ∎)
    where
    open CR

  Conₘ-interchange {δ = η} (prodˢₘ {γ} {p} {δ} ▸t ▸u) ▸prod x =
    case inv-usage-prodˢ ▸prod of λ
      (invUsageProdˢ {δ = γ′} {η = δ′} ▸t′ ▸u′ η≤pγ′∧δ′) → sub
    (prodˢₘ (Conₘ-interchange ▸t ▸t′ x) (Conₘ-interchange ▸u ▸u′ x))
    (begin
       p ·ᶜ γ ∧ᶜ δ , x ≔ η ⟨ x ⟩                          ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤pγ′∧δ′ ⟩
       p ·ᶜ γ ∧ᶜ δ , x ≔ (p ·ᶜ γ′ ∧ᶜ δ′) ⟨ x ⟩            ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-∧ᶜ (_ ·ᶜ γ′) _ _ ⟩
       p ·ᶜ γ ∧ᶜ δ , x ≔ (p ·ᶜ γ′) ⟨ x ⟩ ∧ δ′ ⟨ x ⟩       ≡⟨ cong (_,_≔_ _ _) $ cong (_∧ _) $ lookup-distrib-·ᶜ γ′ _ _ ⟩
       p ·ᶜ γ ∧ᶜ δ , x ≔ p · γ′ ⟨ x ⟩ ∧ δ′ ⟨ x ⟩          ≡⟨ update-distrib-∧ᶜ _ _ _ _ _ ⟩
       (p ·ᶜ γ , x ≔ p · γ′ ⟨ x ⟩) ∧ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡⟨ cong (_∧ᶜ _) $ update-distrib-·ᶜ _ _ _ _ ⟩
       p ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) ∧ᶜ (δ , x ≔ δ′ ⟨ x ⟩)      ∎)
    where
    open CR

  Conₘ-interchange {δ} (fstₘ {γ} m ▸t PE.refl ok) ▸fst x =
    case inv-usage-fst ▸fst of λ
      (invUsageFst {δ = γ′} _ _ ▸t′ δ≤γ′ _) → sub
    (fstₘ m (Conₘ-interchange ▸t ▸t′ x) PE.refl ok)
    (begin
       γ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤γ′ ⟩
       γ , x ≔ γ′ ⟨ x ⟩  ∎)
    where
    open CR

  Conₘ-interchange {δ} (sndₘ {γ} ▸t) ▸snd x =
    case inv-usage-snd ▸snd of λ
      (invUsageSnd {δ = γ′} ▸t′ δ≤γ′) → sub
    (sndₘ (Conₘ-interchange ▸t ▸t′ x))
    (begin
       γ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤γ′ ⟩
       γ , x ≔ γ′ ⟨ x ⟩  ∎)
    where
    open CR

  Conₘ-interchange {δ = η} (prodrecₘ {γ} {r} {δ} ▸t ▸u ▸A ok) ▸pr x =
    case inv-usage-prodrec ▸pr of λ
      (invUsageProdrec
         {δ = γ′} {η = δ′} ▸t′ ▸u′ _ _ η≤rγ+δ′) → sub
    (prodrecₘ (Conₘ-interchange ▸t ▸t′ x)
       (Conₘ-interchange ▸u ▸u′ (x +2)) ▸A ok)
    (begin
       r ·ᶜ γ +ᶜ δ , x ≔ η ⟨ x ⟩                          ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤rγ+δ′ ⟩
       r ·ᶜ γ +ᶜ δ , x ≔ (r ·ᶜ γ′ +ᶜ δ′) ⟨ x ⟩            ≡⟨ cong (_,_≔_ _ _) $ lookup-distrib-+ᶜ (_ ·ᶜ γ′) _ _ ⟩
       r ·ᶜ γ +ᶜ δ , x ≔ (r ·ᶜ γ′) ⟨ x ⟩ + δ′ ⟨ x ⟩       ≡⟨ cong (_,_≔_ _ _) $ cong (_+ _) $ lookup-distrib-·ᶜ γ′ _ _ ⟩
       r ·ᶜ γ +ᶜ δ , x ≔ r · γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩          ≡⟨ update-distrib-+ᶜ _ _ _ _ _ ⟩
       (r ·ᶜ γ , x ≔ r · γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡⟨ cong (_+ᶜ _) $ update-distrib-·ᶜ _ _ _ _ ⟩
       r ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)      ∎)
    where
    open CR

  Conₘ-interchange {δ} Emptyₘ ▸Empty x = sub
    Emptyₘ
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-Empty ▸Empty ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange {δ} (emptyrecₘ {γ} {p} ▸t ▸A ok) ▸er x =
    case inv-usage-emptyrec ▸er of λ
      (invUsageEmptyrec {δ = γ′} ▸t′ _ _ δ≤pγ′) → sub
    (emptyrecₘ (Conₘ-interchange ▸t ▸t′ x) ▸A ok)
    (begin
       p ·ᶜ γ , x ≔ δ ⟨ x ⟩          ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤pγ′ ⟩
       p ·ᶜ γ , x ≔ (p ·ᶜ γ′) ⟨ x ⟩  ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-·ᶜ γ′ _ _ ⟩
       p ·ᶜ γ , x ≔ p · (γ′ ⟨ x ⟩)   ≡⟨ update-distrib-·ᶜ _ _ _ _ ⟩
       p ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩)       ∎)
    where
    open CR

  Conₘ-interchange {δ} Unitₘ ▸Unit x = sub
    Unitₘ
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-Unit ▸Unit ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange {δ} starʷₘ ▸star x = sub
    starʷₘ
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-starʷ ▸star ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange {δ} (starˢₘ {γ} {m} ok) ▸star x =
    case inv-usage-starˢ ▸star of λ
      (invUsageStarˢ {δ = γ′} δ≤⌜m⌝γ′ 𝟘≈γ′) → sub
    (let open Tools.Reasoning.Equivalence Conₘ-setoid in
     starˢₘ λ not-sink → begin
       𝟘ᶜ                 ≡˘⟨ update-self _ _ ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≈⟨ update-cong (ok not-sink) (lookup-cong $ 𝟘≈γ′ not-sink) ⟩
       γ , x ≔ γ′ ⟨ x ⟩   ∎)
    (let open CR in begin
       ⌜ m ⌝ ·ᶜ γ , x ≔ δ ⟨ x ⟩              ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤⌜m⌝γ′ ⟩
       ⌜ m ⌝ ·ᶜ γ , x ≔ (⌜ m ⌝ ·ᶜ γ′) ⟨ x ⟩  ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-·ᶜ γ′ _ _ ⟩
       ⌜ m ⌝ ·ᶜ γ , x ≔ ⌜ m ⌝ · γ′ ⟨ x ⟩     ≡⟨ update-distrib-·ᶜ _ _ _ _ ⟩
       ⌜ m ⌝ ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩)           ∎)

  Conₘ-interchange {δ = η} (unitrecₘ {γ} {p} {δ} ▸t ▸u ▸A ok) ▸ur x =
    case inv-usage-unitrec ▸ur of λ
      (invUsageUnitrec {δ = γ′} {η = δ′} ▸t′ ▸u′ _ _ η≤pγ′+δ′) → sub
    (unitrecₘ (Conₘ-interchange ▸t ▸t′ x) (Conₘ-interchange ▸u ▸u′ x) ▸A
       ok)
    (begin
       p ·ᶜ γ +ᶜ δ , x ≔ η ⟨ x ⟩                          ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤pγ′+δ′ ⟩
       p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′ +ᶜ δ′) ⟨ x ⟩            ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-+ᶜ (_ ·ᶜ γ′) _ _ ⟩
       p ·ᶜ γ +ᶜ δ , x ≔ (p ·ᶜ γ′) ⟨ x ⟩ + δ′ ⟨ x ⟩       ≡⟨ cong (_,_≔_ _ _) $ cong (_+ _) $ lookup-distrib-·ᶜ γ′ _ _ ⟩
       p ·ᶜ γ +ᶜ δ , x ≔ p · γ′ ⟨ x ⟩ + δ′ ⟨ x ⟩          ≡⟨ update-distrib-+ᶜ _ _ _ _ _ ⟩
       (p ·ᶜ γ , x ≔ p · γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)  ≡⟨ cong (_+ᶜ _) $ update-distrib-·ᶜ _ _ _ _ ⟩
       p ·ᶜ (γ , x ≔ γ′ ⟨ x ⟩) +ᶜ (δ , x ≔ δ′ ⟨ x ⟩)      ∎)
    where
    open CR

  Conₘ-interchange {δ} ℕₘ ▸ℕ x = sub
    ℕₘ
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-ℕ ▸ℕ ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange {δ} zeroₘ ▸zero x = sub
    zeroₘ
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-zero ▸zero ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange {δ} (sucₘ {γ} ▸t) ▸suc x =
    case inv-usage-suc ▸suc of λ
      (invUsageSuc {δ = γ′} ▸t′ δ≤γ′) → sub
    (sucₘ (Conₘ-interchange ▸t ▸t′ x))
    (begin
       γ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤γ′ ⟩
       γ , x ≔ γ′ ⟨ x ⟩  ∎)
    where
    open CR

  Conₘ-interchange
    {δ = θ}
    (natrecₘ {γ} {δ} {p} {r} {η} ⦃ has-nr = nr₁ ⦄ ▸z ▸s ▸n ▸A) ▸nr x =
    case inv-usage-natrec ▸nr of λ {
      (invUsageNatrec
         {δ = γ′} {η = δ′} {θ = η′} ▸z′ ▸s′ ▸n′ _ θ≤ more) →
    case more of λ where
      (invUsageNatrecNoNr _ _ _ _) →
        ⊥-elim not-nr-and-no-nr
      (invUsageNatrecNr ⦃ has-nr = nr₂ ⦄) →
        case Dedicated-nr-propositional nr₁ nr₂ of λ {
          refl → sub
        (natrecₘ (Conₘ-interchange ▸z ▸z′ x)
           (Conₘ-interchange ▸s ▸s′ (x +2)) (Conₘ-interchange ▸n ▸n′ x)
           ▸A)
        (begin
           nrᶜ p r γ δ η , x ≔ θ ⟨ x ⟩                                  ≤⟨ update-monotoneʳ _ $ lookup-monotone _ θ≤ ⟩

           nrᶜ p r γ δ η , x ≔ nrᶜ p r γ′ δ′ η′ ⟨ x ⟩                   ≡⟨ cong (_ , _ ≔_) $ nrᶜ-⟨⟩ γ′ ⟩

           nrᶜ p r γ δ η , x ≔ nr p r (γ′ ⟨ x ⟩) (δ′ ⟨ x ⟩) (η′ ⟨ x ⟩)  ≡˘⟨ ≈ᶜ→≡ nrᶜ-,≔ ⟩

           nrᶜ p r (γ , x ≔ γ′ ⟨ x ⟩) (δ , x ≔ δ′ ⟨ x ⟩)
             (η , x ≔ η′ ⟨ x ⟩)                                         ∎) }}
    where
    open CR
    open import Graded.Modality.Dedicated-nr.Instance

  Conₘ-interchange
    {δ = θ}
    (natrec-no-nrₘ {γ} {δ} {p} {r} {η} {χ} ⦃ no-nr = ¬nr ⦄
       ▸z ▸s ▸n ▸A χ≤γ χ≤δ χ≤η fix)
    ▸nr x =
    case inv-usage-natrec ▸nr of λ {
      (invUsageNatrec
         {δ = γ′} {η = δ′} {θ = η′} {χ = χ′} ▸z′ ▸s′ ▸n′ _ θ≤χ′ more) →
    case more of λ where
      invUsageNatrecNr →
        ⊥-elim not-nr-and-no-nr
      (invUsageNatrecNoNr χ′≤γ′ χ′≤δ′ χ′≤η′ fix′) → sub
        (natrec-no-nrₘ ⦃ no-nr = ¬nr ⦄ (Conₘ-interchange ▸z ▸z′ x)
           (Conₘ-interchange ▸s ▸s′ (x +2)) (Conₘ-interchange ▸n ▸n′ x)
           ▸A
           (begin
              χ , x ≔ χ′ ⟨ x ⟩  ≤⟨ update-monotone _ χ≤γ $ lookup-monotone _ χ′≤γ′ ⟩
              γ , x ≔ γ′ ⟨ x ⟩  ∎)
           (λ ok → begin
              χ , x ≔ χ′ ⟨ x ⟩  ≤⟨ update-monotone _ (χ≤δ ok) (lookup-monotone _ (χ′≤δ′ ok)) ⟩
              δ , x ≔ δ′ ⟨ x ⟩  ∎)
           (begin
              χ , x ≔ χ′ ⟨ x ⟩  ≤⟨ update-monotone _ χ≤η (lookup-monotone _ χ′≤η′) ⟩
              η , x ≔ η′ ⟨ x ⟩  ∎)
           (begin
              χ , x ≔ χ′ ⟨ x ⟩                                    ≤⟨ update-monotone _ fix (lookup-monotone _ fix′) ⟩

              δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ ,
              x ≔ (δ′ +ᶜ p ·ᶜ η′ +ᶜ r ·ᶜ χ′) ⟨ x ⟩                ≈⟨ update-congʳ $
                                                                     trans (lookup-distrib-+ᶜ δ′ _ _) $
                                                                     cong (_ +_) $
                                                                     trans (lookup-distrib-+ᶜ (_ ·ᶜ η′) _ _) $
                                                                     cong₂ _+_
                                                                       (lookup-distrib-·ᶜ η′ _ _)
                                                                       (lookup-distrib-·ᶜ χ′ _ _) ⟩
              δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ ,
              x ≔ δ′ ⟨ x ⟩ + p · η′ ⟨ x ⟩ + r · χ′ ⟨ x ⟩          ≡⟨ trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                                     cong (_ +ᶜ_) $
                                                                     trans (update-distrib-+ᶜ _ _ _ _ _) $
                                                                     cong₂ _+ᶜ_
                                                                       (update-distrib-·ᶜ _ _ _ _)
                                                                       (update-distrib-·ᶜ _ _ _ _) ⟩
              (δ , x ≔ δ′ ⟨ x ⟩) +ᶜ
              p ·ᶜ (η , x ≔ η′ ⟨ x ⟩) +ᶜ r ·ᶜ (χ , x ≔ χ′ ⟨ x ⟩)  ∎))
        (begin
           χ , x ≔ θ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ θ≤χ′ ⟩
           χ , x ≔ χ′ ⟨ x ⟩  ∎) }
    where
    open CR

  Conₘ-interchange {δ = θ} (Idₘ {δ} {η} not-erased ▸A ▸t ▸u) ▸Id x =
    case inv-usage-Id ▸Id of λ where
      (invUsageId₀ erased _ _ _ _) →
        ⊥-elim $ not-erased erased
      (invUsageId {δ = δ′} {η = η′} _ _ ▸t′ ▸u′ θ≤δ′+η′) → sub
        (Idₘ not-erased ▸A (Conₘ-interchange ▸t ▸t′ x)
           (Conₘ-interchange ▸u ▸u′ x))
        (begin
           δ +ᶜ η , x ≔ θ ⟨ x ⟩                      ≤⟨ update-monotoneʳ _ $ lookup-monotone _ θ≤δ′+η′ ⟩
           δ +ᶜ η , x ≔ (δ′ +ᶜ η′) ⟨ x ⟩             ≡⟨ cong (_ , _ ≔_) $ lookup-distrib-+ᶜ δ′ _ _ ⟩
           δ +ᶜ η , x ≔ δ′ ⟨ x ⟩ + η′ ⟨ x ⟩          ≡⟨ update-distrib-+ᶜ _ _ _ _ _ ⟩
           (δ , x ≔ δ′ ⟨ x ⟩) +ᶜ (η , x ≔ η′ ⟨ x ⟩)  ∎)
    where
    open CR

  Conₘ-interchange {δ} (Id₀ₘ erased ▸A ▸t ▸u) ▸Id x =
    case inv-usage-Id ▸Id of λ where
      (invUsageId not-erased _ _ _ _) →
        ⊥-elim $ not-erased erased
      (invUsageId₀ _ _ ▸t′ ▸u′ γ≤𝟘) → sub
        (Id₀ₘ erased ▸A (Conₘ-interchange ▸t ▸t′ x)
           (Conₘ-interchange ▸u ▸u′ x))
        (begin
           𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ γ≤𝟘 ⟩
           𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
           𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange {δ} rflₘ ▸rfl x = sub
    rflₘ
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ $ inv-usage-rfl ▸rfl ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

  Conₘ-interchange
    {δ = η}
    (Jₘ {γ₂} {γ₃} {γ₄} {γ₅} {γ₆} ≤some ok ▸A ▸t ▸F ▸u ▸v ▸w) ▸J x =
    case inv-usage-J ▸J of λ where
      (invUsageJ₀₁ ≡some p≡𝟘 q≡𝟘 _ _ _ _ _ _ _) →
        ⊥-elim $ ok ≡some (p≡𝟘 , q≡𝟘)
      (invUsageJ₀₂ ≡all _ _ _ _ _ _ _) →
        case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
      (invUsageJ {γ₂ = δ₂} {γ₃ = δ₃} {γ₄ = δ₄} {γ₅ = δ₅} {γ₆ = δ₆}
         _ _ _ ▸t′ ▸F′ ▸u′ ▸v′ ▸w′ η≤ω·) → sub
        (Jₘ ≤some ok ▸A (Conₘ-interchange ▸t ▸t′ x)
           (Conₘ-interchange ▸F ▸F′ (x +2)) (Conₘ-interchange ▸u ▸u′ x)
           (Conₘ-interchange ▸v ▸v′ x) (Conₘ-interchange ▸w ▸w′ x))
        (begin
           ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) , x ≔ η ⟨ x ⟩  ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤ω· ⟩

           ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ,
           x ≔ (ω ·ᶜ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅ +ᶜ δ₆)) ⟨ x ⟩    ≡⟨ Conₘ-interchange-J δ₂ δ₃ δ₄ δ₅ δ₆ ⟩

           ω ·ᶜ
           ((γ₂ , x ≔ δ₂ ⟨ x ⟩) +ᶜ (γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ
            (γ₄ , x ≔ δ₄ ⟨ x ⟩) +ᶜ (γ₅ , x ≔ δ₅ ⟨ x ⟩) +ᶜ
            (γ₆ , x ≔ δ₆ ⟨ x ⟩))                            ∎)
    where
    open CR

  Conₘ-interchange
    {δ = η} (J₀ₘ₁ {γ₃} {γ₄} ≡some p≡𝟘 q≡𝟘 ▸A ▸t ▸F ▸u ▸v ▸w) ▸J x =
    case inv-usage-J ▸J of λ where
      (invUsageJ _ ok _ _ _ _ _ _ _) →
        ⊥-elim $ ok ≡some (p≡𝟘 , q≡𝟘)
      (invUsageJ₀₂ ≡all _ _ _ _ _ _ _) →
        case trans (PE.sym ≡some) ≡all of λ ()
      (invUsageJ₀₁ {γ₃ = δ₃} {γ₄ = δ₄}
         _ _ _ _ ▸t′ ▸F′ ▸u′ ▸v′ ▸w′ η≤ω·) → sub
        (J₀ₘ₁ ≡some p≡𝟘 q≡𝟘 ▸A (Conₘ-interchange ▸t ▸t′ x)
           (Conₘ-interchange ▸F ▸F′ (x +2)) (Conₘ-interchange ▸u ▸u′ x)
           (Conₘ-interchange ▸v ▸v′ x) (Conₘ-interchange ▸w ▸w′ x))
        (begin
           ω ·ᶜ (γ₃ +ᶜ γ₄) , x ≔ η ⟨ x ⟩                      ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤ω· ⟩
           ω ·ᶜ (γ₃ +ᶜ γ₄) , x ≔ (ω ·ᶜ (δ₃ +ᶜ δ₄)) ⟨ x ⟩      ≡⟨ Conₘ-interchange₀₁ δ₃ δ₄ ⟩
           ω ·ᶜ ((γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ (γ₄ , x ≔ δ₄ ⟨ x ⟩))  ∎)
    where
    open CR

  Conₘ-interchange {δ} (J₀ₘ₂ {γ₄} ≡all ▸A ▸t ▸F ▸u ▸v ▸w) ▸J x =
    case inv-usage-J ▸J of λ where
      (invUsageJ ≤some _ _ _ _ _ _ _ _) →
        case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
      (invUsageJ₀₁ ≡some _ _ _ _ _ _ _ _ _) →
        case trans (PE.sym ≡all) ≡some of λ ()
      (invUsageJ₀₂ {γ₄ = γ₄′} _ _ _ _ ▸u′ _ _ δ≤γ₄′) → sub
        (J₀ₘ₂ ≡all ▸A ▸t ▸F (Conₘ-interchange ▸u ▸u′ x) ▸v ▸w)
        (begin
           γ₄ , x ≔ δ ⟨ x ⟩    ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤γ₄′ ⟩
           γ₄ , x ≔ γ₄′ ⟨ x ⟩  ∎)
    where
    open CR

  Conₘ-interchange
    {δ = η} (Kₘ {γ₂} {γ₃} {γ₄} {γ₅} ≤some ok ▸A ▸t ▸F ▸u ▸v) ▸K x =
    case inv-usage-K ▸K of λ where
      (invUsageK₀₁ ≡some p≡𝟘 _ _ _ _ _ _) →
        ⊥-elim $ ok ≡some p≡𝟘
      (invUsageK₀₂ ≡all _ _ _ _ _ _) →
        case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
      (invUsageK {γ₂ = δ₂} {γ₃ = δ₃} {γ₄ = δ₄} {γ₅ = δ₅}
         _ _ _ ▸t′ ▸F′ ▸u′ ▸v′ η≤ω·) → sub
        (Kₘ ≤some ok ▸A (Conₘ-interchange ▸t ▸t′ x)
           (Conₘ-interchange ▸F ▸F′ (x +1)) (Conₘ-interchange ▸u ▸u′ x)
           (Conₘ-interchange ▸v ▸v′ x))
        (begin
           ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) , x ≔ η ⟨ x ⟩       ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤ω· ⟩

           ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ,
           x ≔ (ω ·ᶜ (δ₂ +ᶜ δ₃ +ᶜ δ₄ +ᶜ δ₅)) ⟨ x ⟩         ≡⟨ Conₘ-interchange-K δ₂ δ₃ δ₄ δ₅ ⟩

           ω ·ᶜ
           ((γ₂ , x ≔ δ₂ ⟨ x ⟩) +ᶜ (γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ
            (γ₄ , x ≔ δ₄ ⟨ x ⟩) +ᶜ (γ₅ , x ≔ δ₅ ⟨ x ⟩))    ∎)
    where
    open CR

  Conₘ-interchange
    {δ = η} (K₀ₘ₁ {γ₃} {γ₄} ≡some p≡𝟘 ▸A ▸t ▸F ▸u ▸v) ▸K x =
    case inv-usage-K ▸K of λ where
      (invUsageK _ ok _ _ _ _ _ _) →
        ⊥-elim $ ok ≡some p≡𝟘
      (invUsageK₀₂ ≡all _ _ _ _ _ _) →
        case trans (PE.sym ≡some) ≡all of λ ()
      (invUsageK₀₁ {γ₃ = δ₃} {γ₄ = δ₄} _ _ _ ▸t′ ▸F′ ▸u′ ▸v′ η≤ω·) → sub
        (K₀ₘ₁ ≡some p≡𝟘 ▸A (Conₘ-interchange ▸t ▸t′ x)
           (Conₘ-interchange ▸F ▸F′ (x +1)) (Conₘ-interchange ▸u ▸u′ x)
           (Conₘ-interchange ▸v ▸v′ x))
        (begin
           ω ·ᶜ (γ₃ +ᶜ γ₄) , x ≔ η ⟨ x ⟩                      ≤⟨ update-monotoneʳ _ $ lookup-monotone _ η≤ω· ⟩
           ω ·ᶜ (γ₃ +ᶜ γ₄) , x ≔ (ω ·ᶜ (δ₃ +ᶜ δ₄)) ⟨ x ⟩      ≡⟨ Conₘ-interchange₀₁ δ₃ δ₄ ⟩
           ω ·ᶜ ((γ₃ , x ≔ δ₃ ⟨ x ⟩) +ᶜ (γ₄ , x ≔ δ₄ ⟨ x ⟩))  ∎)
    where
    open CR

  Conₘ-interchange {δ} (K₀ₘ₂ {γ₄} ≡all ▸A ▸t ▸F ▸u ▸v) ▸K x =
    case inv-usage-K ▸K of λ where
      (invUsageK ≤some _ _ _ _ _ _ _) →
        case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
      (invUsageK₀₁ ≡some _ _ _ _ _ _ _) →
        case trans (PE.sym ≡all) ≡some of λ ()
      (invUsageK₀₂ {γ₄ = γ₄′} _ _ _ _ ▸u′ _ δ≤γ₄′) → sub
        (K₀ₘ₂ ≡all ▸A ▸t ▸F (Conₘ-interchange ▸u ▸u′ x) ▸v)
        (begin
           γ₄ , x ≔ δ ⟨ x ⟩    ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤γ₄′ ⟩
           γ₄ , x ≔ γ₄′ ⟨ x ⟩  ∎)
    where
    open CR

  Conₘ-interchange {δ} ([]-congₘ ▸A ▸t ▸u ▸v) ▸bc x =
    case inv-usage-[]-cong ▸bc of λ
      (invUsage-[]-cong _ _ _ _ δ≤𝟘) → sub
    ([]-congₘ ▸A ▸t ▸u ▸v)
    (begin
       𝟘ᶜ , x ≔ δ ⟨ x ⟩   ≤⟨ update-monotoneʳ _ $ lookup-monotone _ δ≤𝟘 ⟩
       𝟘ᶜ , x ≔ 𝟘ᶜ ⟨ x ⟩  ≡⟨ update-self _ _ ⟩
       𝟘ᶜ                 ∎)
    where
    open CR

-- Some variants of Conₘ-interchange

Conₘ-interchange₁ : γ ▸[ m ] t → δ ▸[ m ] t
                  → tailₘ γ ∙ δ ⟨ x0 ⟩ ▸[ m ] t
Conₘ-interchange₁ {γ = γ} {m} {t} {δ} γ▸t δ▸t =
  subst (_▸[ m ] t) (update-head γ (δ ⟨ x0 ⟩))
        (Conₘ-interchange γ▸t δ▸t x0)


Conₘ-interchange₂ : γ ▸[ m ] t → δ ▸[ m ] t
                  → tailₘ (tailₘ γ) ∙ δ ⟨ x1 ⟩ ∙ δ ⟨ x0 ⟩ ▸[ m ] t
Conₘ-interchange₂ {γ = γ} {m} {t} {δ} γ▸t δ▸t =
  subst (_▸[ m ] t) eq
        (Conₘ-interchange (Conₘ-interchange γ▸t δ▸t x1) δ▸t x0)
  where
  open Tools.Reasoning.PropositionalEquality
  δ₁ = δ ⟨ x1 ⟩
  δ₀ = δ ⟨ x0 ⟩
  eq = begin
    γ , x1 ≔ δ₁ , x0 ≔ δ₀ ≡⟨ update-head _ _ ⟩
    tailₘ (γ , x1 ≔ δ₁) ∙ δ₀ ≡⟨ cong (λ x → tailₘ x ∙ δ₀) (update-step γ δ₁ x0) ⟩
    (tailₘ γ , x0 ≔ δ₁) ∙ δ₀ ≡⟨ cong (_∙ _) (update-head (tailₘ γ) δ₁) ⟩
    tailₘ (tailₘ γ) ∙ δ₁ ∙ δ₀ ∎


------------------------------------------------------------------------
-- Variants of some usage rules

module _ where

  open import Graded.Modality.Dedicated-nr.Instance

  -- A variant of natrecₘ and natrec-no-nrₘ.

  natrec-nr-or-no-nrₘ :
    γ ▸[ m ] t →
    δ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · r ▸[ m ] u →
    η ▸[ m ] v →
    θ ∙ ⌜ 𝟘ᵐ? ⌝ · q ▸[ 𝟘ᵐ? ] A →
    (⦃ has-nr : Dedicated-nr ⦄ →
     χ ≤ᶜ nrᶜ p r γ δ η) →
    (⦃ no-nr : No-dedicated-nr ⦄ →
     χ ≤ᶜ γ ×
     (T 𝟘ᵐ-allowed →
      χ ≤ᶜ δ) ×
     (⦃ 𝟘-well-behaved : Has-well-behaved-zero semiring-with-meet ⦄ →
      χ ≤ᶜ η) ×
     χ ≤ᶜ δ +ᶜ p ·ᶜ η +ᶜ r ·ᶜ χ) →
    χ ▸[ m ] natrec p q r A t u v
  natrec-nr-or-no-nrₘ ▸t ▸u ▸v ▸A hyp₁ hyp₂ =
    case dedicated-nr? of λ where
      does-have-nr →
        sub (natrecₘ ▸t ▸u ▸v ▸A) hyp₁
      does-not-have-nr →
        case hyp₂ of λ {
          (χ≤γ , χ≤δ , χ≤η , fix) →
        natrec-no-nrₘ ▸t ▸u ▸v ▸A χ≤γ χ≤δ χ≤η fix }

opaque

  -- A variant of Idₘ and Id₀ₘ.

  Idₘ-generalised :
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ m ] t →
    γ₃ ▸[ m ] u →
    (Id-erased → δ ≤ᶜ 𝟘ᶜ) →
    (¬ Id-erased → δ ≤ᶜ γ₂ +ᶜ γ₃) →
    δ ▸[ m ] Id A t u
  Idₘ-generalised {γ₂} {m} {γ₃} {δ} ▸A ▸t ▸u δ≤𝟘ᶜ δ≤γ₂+γ₃ =
    case Id-erased? of λ where
      (no not-erased) →
        sub (Idₘ not-erased ▸A ▸t ▸u) (δ≤γ₂+γ₃ not-erased)
      (yes erased) → 𝟘ᵐ-allowed-elim
        (λ ok →
           sub (Id₀ₘ erased ▸A (𝟘ᶜ▸[𝟘ᵐ?] ok ▸t) (𝟘ᶜ▸[𝟘ᵐ?] ok ▸u))
             (δ≤𝟘ᶜ erased))
        (λ not-ok →
           sub
             (Id₀ₘ erased ▸A (▸-without-𝟘ᵐ not-ok ▸t)
                (▸-without-𝟘ᵐ not-ok ▸u))
             (δ≤𝟘ᶜ erased))

opaque

  -- A generalisation of the usage rule Jₘ:
  -- erased-matches-for-J m ≡ none and
  -- erased-matches-for-J m ≡ some → ¬ (p ≡ 𝟘 × q ≡ 𝟘) have been
  -- removed.

  Jₘ-generalised :
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ m ] t →
    γ₃ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · q ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ m ] v →
    γ₆ ▸[ m ] w →
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆) ▸[ m ] J p q A t B u v w
  Jₘ-generalised
    {γ₂} {m} {γ₃} {p} {q} {B} {γ₄} {γ₅} {γ₆} ▸A ▸t ▸B ▸u ▸v ▸w
    with J-view p q m
  … | is-other ≤some ≢𝟘 =
    Jₘ ≤some ≢𝟘 ▸A ▸t ▸B ▸u ▸v ▸w
  … | is-some-yes ≡some (refl , refl) = sub
    (J₀ₘ₁ ≡some refl refl ▸A (▸-𝟘ᵐ? ▸t .proj₂)
       (sub ▸B $ begin
          γ₃ ∙ 𝟘 ∙ 𝟘                  ≈˘⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
          γ₃ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘  ∎)
       ▸u (▸-𝟘ᵐ? ▸v .proj₂) (▸-𝟘ᵐ? ▸w .proj₂))
    (begin
       ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)  ≤⟨ ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ $
                                             ≤ᶜ-trans (≤ᶜ-reflexive $ ≈ᶜ-sym $ ·ᶜ-congˡ $ +ᶜ-assoc _ _ _)
                                             ω·ᶜ+ᶜ≤ω·ᶜˡ ⟩
       ω ·ᶜ (γ₃ +ᶜ γ₄)                    ∎)
    where
    open CR
  Jₘ-generalised
    {γ₂} {m} {γ₃} {p} {q} {B} {γ₄} {γ₅} {γ₆} ▸A ▸t ▸B ▸u ▸v ▸w
    | is-all ≡all = sub
    (J₀ₘ₂ ≡all ▸A (▸-𝟘ᵐ? ▸t .proj₂)
       (𝟘ᵐ?-elim (λ m → ∃ λ γ → γ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · q ▸[ m ] B)
          ( 𝟘ᶜ
          , sub (▸-𝟘 ▸B) (begin
              𝟘ᶜ ∙ 𝟘 · p ∙ 𝟘 · q  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ∙ ·-zeroˡ _ ⟩
              𝟘ᶜ                  ∎)
          )
          (λ not-ok →
               γ₃
             , sub (▸-cong (Mode-propositional-without-𝟘ᵐ not-ok) ▸B)
                 (begin
                    γ₃ ∙ 𝟙 · p ∙ 𝟙 · q          ≈˘⟨ ≈ᶜ-refl ∙
                                                    cong (λ m → ⌜ m ⌝ · _) (only-𝟙ᵐ-without-𝟘ᵐ {m = m} not-ok) ∙
                                                    cong (λ m → ⌜ m ⌝ · _) (only-𝟙ᵐ-without-𝟘ᵐ {m = m} not-ok) ⟩
                    γ₃ ∙ ⌜ m ⌝ · p ∙ ⌜ m ⌝ · q  ∎))
          .proj₂)
       ▸u (▸-𝟘ᵐ? ▸v .proj₂) (▸-𝟘ᵐ? ▸w .proj₂))
    (begin
       ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)  ≤⟨ ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ $
                                             ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ
                                             ω·ᶜ+ᶜ≤ω·ᶜˡ ⟩
       ω ·ᶜ γ₄                            ≤⟨ ω·ᶜ-decreasing ⟩
       γ₄                                 ∎)
    where
    open CR

opaque

  -- A generalisation of the usage rule J₀ₘ₁:
  -- erased-matches-for-J m ≡ some has been replaced by
  -- erased-matches-for-J m ≡ not-none sem.

  J₀ₘ₁-generalised :
    erased-matches-for-J m ≡ not-none sem →
    p ≡ 𝟘 →
    q ≡ 𝟘 →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ 𝟘ᵐ? ] t →
    γ₃ ∙ 𝟘 ∙ 𝟘 ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ 𝟘ᵐ? ] v →
    γ₆ ▸[ 𝟘ᵐ? ] w →
    ω ·ᶜ (γ₃ +ᶜ γ₄) ▸[ m ] J p q A t B u v w
  J₀ₘ₁-generalised {m} {γ₃} {B} {γ₄} hyp refl refl ▸A ▸t ▸B ▸u ▸v ▸w
    with erased-matches-for-J m in ok
  … | none = case hyp of λ ()
  … | some = J₀ₘ₁ ok refl refl ▸A ▸t ▸B ▸u ▸v ▸w
  … | all  = sub
    (J₀ₘ₂ ok ▸A (▸-𝟘ᵐ? ▸t .proj₂)
       (𝟘ᵐ?-elim (λ m → ∃ λ γ → γ ∙ ⌜ m ⌝ · 𝟘 ∙ ⌜ m ⌝ · 𝟘 ▸[ m ] B)
          ( 𝟘ᶜ
          , sub (▸-𝟘 ▸B) (begin
              𝟘ᶜ ∙ 𝟘 · 𝟘 ∙ 𝟘 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
              𝟘ᶜ                  ∎)
          )
          (λ not-ok →
               γ₃
             , sub (▸-cong (Mode-propositional-without-𝟘ᵐ not-ok) ▸B)
                 (begin
                    γ₃ ∙ 𝟙 · 𝟘 ∙ 𝟙 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ∙ ·-zeroʳ _ ⟩
                    γ₃ ∙ 𝟘 ∙ 𝟘          ∎))
          .proj₂)
       ▸u (▸-𝟘ᵐ? ▸v .proj₂) (▸-𝟘ᵐ? ▸w .proj₂))
    (begin
       ω ·ᶜ (γ₃ +ᶜ γ₄)  ≤⟨ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
       ω ·ᶜ γ₄          ≤⟨ ω·ᶜ-decreasing ⟩
       γ₄               ∎)
    where
    open CR

opaque

  -- A generalisation of the usage rule Kₘ:
  -- erased-matches-for-K m ≤ᵉᵐ some and
  -- erased-matches-for-K m ≡ some → p ≢ 𝟘 have been removed.

  Kₘ-generalised :
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ m ] t →
    γ₃ ∙ ⌜ m ⌝ · p ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ m ] v →
    ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅) ▸[ m ] K p A t B u v
  Kₘ-generalised {γ₂} {m} {γ₃} {p} {B} {γ₄} {γ₅} ▸A ▸t ▸B ▸u ▸v
    with K-view p m
  … | is-other ≤some ≢𝟘 =
    Kₘ ≤some ≢𝟘 ▸A ▸t ▸B ▸u ▸v
  … | is-some-yes ≡some refl = sub
    (K₀ₘ₁ ≡some refl ▸A (▸-𝟘ᵐ? ▸t .proj₂)
       (sub ▸B $ begin
          γ₃ ∙ 𝟘          ≈˘⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
          γ₃ ∙ ⌜ m ⌝ · 𝟘  ∎)
       ▸u (▸-𝟘ᵐ? ▸v .proj₂))
    (begin
       ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)  ≤⟨ ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ $
                                       ≤ᶜ-trans (≤ᶜ-reflexive $ ≈ᶜ-sym $ ·ᶜ-congˡ $ +ᶜ-assoc _ _ _)
                                       ω·ᶜ+ᶜ≤ω·ᶜˡ ⟩
       ω ·ᶜ (γ₃ +ᶜ γ₄)              ∎)
    where
    open CR
  … | is-all ≡all = sub
    (K₀ₘ₂ ≡all ▸A (▸-𝟘ᵐ? ▸t .proj₂)
       (𝟘ᵐ?-elim (λ m → ∃ λ γ → γ ∙ ⌜ m ⌝ · p ▸[ m ] B)
          ( 𝟘ᶜ
          , sub (▸-𝟘 ▸B) (begin
              𝟘ᶜ ∙ 𝟘 · p  ≈⟨ ≈ᶜ-refl ∙ ·-zeroˡ _ ⟩
              𝟘ᶜ          ∎)
          )
          (λ not-ok →
               γ₃
             , sub (▸-cong (Mode-propositional-without-𝟘ᵐ not-ok) ▸B)
                 (begin
                    γ₃ ∙ 𝟙 · p      ≈˘⟨ ≈ᶜ-refl ∙ cong (λ m → ⌜ m ⌝ · _) (only-𝟙ᵐ-without-𝟘ᵐ {m = m} not-ok) ⟩
                    γ₃ ∙ ⌜ m ⌝ · p  ∎))
          .proj₂)
       ▸u (▸-𝟘ᵐ? ▸v .proj₂))
    (begin
       ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)  ≤⟨ ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ $
                                       ≤ᶜ-trans ω·ᶜ+ᶜ≤ω·ᶜʳ
                                       ω·ᶜ+ᶜ≤ω·ᶜˡ ⟩
       ω ·ᶜ γ₄                      ≤⟨ ω·ᶜ-decreasing ⟩
       γ₄                           ∎)
    where
    open CR

opaque

  -- A generalisation of the usage rule K₀ₘ₁:
  -- erased-matches-for-K m ≡ some has been replaced by
  -- erased-matches-for-K m ≡ not-none sem.

  K₀ₘ₁-generalised :
    erased-matches-for-K m ≡ not-none sem →
    p ≡ 𝟘 →
    γ₁ ▸[ 𝟘ᵐ? ] A →
    γ₂ ▸[ 𝟘ᵐ? ] t →
    γ₃ ∙ 𝟘 ▸[ m ] B →
    γ₄ ▸[ m ] u →
    γ₅ ▸[ 𝟘ᵐ? ] v →
    ω ·ᶜ (γ₃ +ᶜ γ₄) ▸[ m ] K p A t B u v
  K₀ₘ₁-generalised {m} {γ₃} {B} {γ₄} hyp refl ▸A ▸t ▸B ▸u ▸v
    with erased-matches-for-K m in ok
  … | none = case hyp of λ ()
  … | some = K₀ₘ₁ ok refl ▸A ▸t ▸B ▸u ▸v
  … | all  = sub
    (K₀ₘ₂ ok ▸A (▸-𝟘ᵐ? ▸t .proj₂)
       (𝟘ᵐ?-elim (λ m → ∃ λ γ → γ ∙ ⌜ m ⌝ · 𝟘 ▸[ m ] B)
          ( 𝟘ᶜ
          , sub (▸-𝟘 ▸B) (begin
              𝟘ᶜ ∙ 𝟘 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
              𝟘ᶜ          ∎)
          )
          (λ not-ok →
               γ₃
             , sub (▸-cong (Mode-propositional-without-𝟘ᵐ not-ok) ▸B)
                 (begin
                    γ₃ ∙ 𝟙 · 𝟘  ≈⟨ ≈ᶜ-refl ∙ ·-zeroʳ _ ⟩
                    γ₃ ∙ 𝟘      ∎))
          .proj₂)
       ▸u (▸-𝟘ᵐ? ▸v .proj₂))
    (begin
       ω ·ᶜ (γ₃ +ᶜ γ₄)  ≤⟨ ω·ᶜ+ᶜ≤ω·ᶜʳ ⟩
       ω ·ᶜ γ₄          ≤⟨ ω·ᶜ-decreasing ⟩
       γ₄               ∎)
    where
    open CR

------------------------------------------------------------------------
-- Lemmas related to ⌈_⌉

-- The context ⌈ t ⌉ 𝟘ᵐ[ ok ] is equivalent to 𝟘ᶜ.

⌈⌉-𝟘ᵐ :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  (t : Term n) → ⌈ t ⌉ 𝟘ᵐ[ ok ] ≈ᶜ 𝟘ᶜ
⌈⌉-𝟘ᵐ (var x) = begin
  𝟘ᶜ , x ≔ 𝟘  ≡⟨ 𝟘ᶜ,≔𝟘 ⟩
  𝟘ᶜ          ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ (U l) =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ {ok = ok} (ΠΣ⟨ _ ⟩ _ , _ ▷ F ▹ G) = begin
  (⌈ F ⌉ 𝟘ᵐ[ ok ] +ᶜ tailₘ (⌈ G ⌉ 𝟘ᵐ[ ok ]))  ≈⟨ +ᶜ-cong (⌈⌉-𝟘ᵐ F) (tailₘ-cong (⌈⌉-𝟘ᵐ G)) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ                                    ≈⟨ +ᶜ-identityʳ _ ⟩
  𝟘ᶜ                                          ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ (lam _ t) =
  tailₘ-cong (⌈⌉-𝟘ᵐ t)
⌈⌉-𝟘ᵐ {ok = ok} (t ∘⟨ p ⟩ u) = begin
  ⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ p ·ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ]  ≈⟨ +ᶜ-cong (⌈⌉-𝟘ᵐ t) (·ᶜ-congˡ (⌈⌉-𝟘ᵐ u)) ⟩
  𝟘ᶜ +ᶜ p ·ᶜ 𝟘ᶜ                          ≈⟨ +ᶜ-congˡ (·ᶜ-zeroʳ _) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ                               ≈⟨ +ᶜ-identityˡ _ ⟩
  𝟘ᶜ                                     ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ {ok = ok} (prod 𝕨 p t u) = begin
  p ·ᶜ ⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ]  ≈⟨ +ᶜ-cong (·ᶜ-congˡ (⌈⌉-𝟘ᵐ t)) (⌈⌉-𝟘ᵐ u) ⟩
  p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ                          ≈⟨ +ᶜ-identityʳ _ ⟩
  p ·ᶜ 𝟘ᶜ                                ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ                                     ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ {ok = ok} (prod 𝕤 p t u) = begin
  p ·ᶜ ⌈ t ⌉ 𝟘ᵐ[ ok ] ∧ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ]  ≈⟨ ∧ᶜ-cong (·ᶜ-congˡ (⌈⌉-𝟘ᵐ t)) (⌈⌉-𝟘ᵐ u) ⟩
  p ·ᶜ 𝟘ᶜ ∧ᶜ 𝟘ᶜ                          ≈⟨ ∧ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
  𝟘ᶜ ∧ᶜ 𝟘ᶜ                               ≈⟨ ∧ᶜ-idem _ ⟩
  𝟘ᶜ                                     ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ (fst _ t) =
  ⌈⌉-𝟘ᵐ t
⌈⌉-𝟘ᵐ (snd _ t) =
  ⌈⌉-𝟘ᵐ t
⌈⌉-𝟘ᵐ {ok = ok} (prodrec r _ _ _ t u) = begin
  r ·ᶜ ⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ tailₘ (tailₘ (⌈ u ⌉ 𝟘ᵐ[ ok ]))  ≈⟨ +ᶜ-cong (·ᶜ-congˡ (⌈⌉-𝟘ᵐ t)) (tailₘ-cong (tailₘ-cong (⌈⌉-𝟘ᵐ u))) ⟩
  r ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ                                          ≈⟨ +ᶜ-congʳ (·ᶜ-zeroʳ _) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ                                               ≈⟨ +ᶜ-identityˡ _ ⟩
  𝟘ᶜ                                                     ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ {ok = ok} (unitrec p q A t u) = begin
  p ·ᶜ ⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ]  ≈⟨ +ᶜ-cong (·ᶜ-congˡ (⌈⌉-𝟘ᵐ t)) (⌈⌉-𝟘ᵐ u) ⟩
  p ·ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ                          ≈⟨ +ᶜ-identityʳ _ ⟩
  p ·ᶜ 𝟘ᶜ                                ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ                                     ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ ℕ =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ zero =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ (suc t) =
  ⌈⌉-𝟘ᵐ t
⌈⌉-𝟘ᵐ {ok = ok} (natrec p _ r A z s n) = begin
  nrᶜ p r (⌈ z ⌉ 𝟘ᵐ[ ok ]) (tailₘ (tailₘ (⌈ s ⌉ 𝟘ᵐ[ ok ])))
    (⌈ n ⌉ 𝟘ᵐ[ ok ])                                         ≈⟨ nrᶜ-cong (⌈⌉-𝟘ᵐ z) (tailₘ-cong (tailₘ-cong (⌈⌉-𝟘ᵐ s))) (⌈⌉-𝟘ᵐ n) ⟩

  nrᶜ p r 𝟘ᶜ 𝟘ᶜ 𝟘ᶜ                                           ≈⟨ nrᶜ-𝟘ᶜ ⟩

  𝟘ᶜ                                                         ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ Unit! =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ star! = ≈ᶜ-refl
⌈⌉-𝟘ᵐ Empty =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ {ok = ok} (emptyrec p _ t) = begin
  p ·ᶜ ⌈ t ⌉ 𝟘ᵐ[ ok ]  ≈⟨ ·ᶜ-congˡ (⌈⌉-𝟘ᵐ t) ⟩
  p ·ᶜ 𝟘ᶜ              ≈⟨ ·ᶜ-zeroʳ _ ⟩
  𝟘ᶜ                   ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ {ok = ok} (Id _ t u) with Id-erased?
… | yes _ = ≈ᶜ-refl
… | no _  = begin
  ⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ]  ≈⟨ +ᶜ-cong (⌈⌉-𝟘ᵐ t) (⌈⌉-𝟘ᵐ u) ⟩
  𝟘ᶜ +ᶜ 𝟘ᶜ                          ≈⟨ +ᶜ-identityˡ _ ⟩
  𝟘ᶜ                                ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ rfl =
  ≈ᶜ-refl
⌈⌉-𝟘ᵐ {ok} (J p q _ t B u v w) with J-view p q 𝟘ᵐ[ ok ]
… | is-all _        = ⌈⌉-𝟘ᵐ u
… | is-some-yes _ _ = begin
  ω ·ᶜ (tailₘ (tailₘ (⌈ B ⌉ 𝟘ᵐ[ ok ])) +ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ])  ≈⟨ ·ᶜ-congˡ $ +ᶜ-cong (tailₘ-cong (tailₘ-cong (⌈⌉-𝟘ᵐ B))) (⌈⌉-𝟘ᵐ u) ⟩
  ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)                                          ≈⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
  𝟘ᶜ                                                       ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
… | is-other _ _ = begin
  ω ·ᶜ
  (⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ tailₘ (tailₘ (⌈ B ⌉ 𝟘ᵐ[ ok ])) +ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ] +ᶜ
   ⌈ v ⌉ 𝟘ᵐ[ ok ] +ᶜ ⌈ w ⌉ 𝟘ᵐ[ ok ])                                      ≈⟨ ·ᶜ-congˡ $
                                                                             +ᶜ-cong (⌈⌉-𝟘ᵐ t) $
                                                                             +ᶜ-cong (tailₘ-cong (tailₘ-cong (⌈⌉-𝟘ᵐ B))) $
                                                                             +ᶜ-cong (⌈⌉-𝟘ᵐ u) (+ᶜ-cong (⌈⌉-𝟘ᵐ v) (⌈⌉-𝟘ᵐ w)) ⟩

  ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ)                                       ≈⟨ ω·ᶜ+ᶜ⁵𝟘ᶜ ⟩

  𝟘ᶜ                                                                      ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ {ok} (K p _ t B u v) with K-view p 𝟘ᵐ[ ok ]
… | is-all _        = ⌈⌉-𝟘ᵐ u
… | is-some-yes _ _ = begin
  ω ·ᶜ (tailₘ (⌈ B ⌉ 𝟘ᵐ[ ok ]) +ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ])  ≈⟨ ·ᶜ-congˡ $ +ᶜ-cong (tailₘ-cong (⌈⌉-𝟘ᵐ B)) (⌈⌉-𝟘ᵐ u) ⟩
  ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ)                                  ≈⟨ ω·ᶜ+ᶜ²𝟘ᶜ ⟩
  𝟘ᶜ                                               ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
… | is-other _ _ = begin
  ω ·ᶜ
  (⌈ t ⌉ 𝟘ᵐ[ ok ] +ᶜ tailₘ (⌈ B ⌉ 𝟘ᵐ[ ok ]) +ᶜ ⌈ u ⌉ 𝟘ᵐ[ ok ] +ᶜ
   ⌈ v ⌉ 𝟘ᵐ[ ok ])                                                ≈⟨ ·ᶜ-congˡ $
                                                                     +ᶜ-cong (⌈⌉-𝟘ᵐ t) $
                                                                     +ᶜ-cong (tailₘ-cong (⌈⌉-𝟘ᵐ B)) $
                                                                     +ᶜ-cong (⌈⌉-𝟘ᵐ u) (⌈⌉-𝟘ᵐ v) ⟩

  ω ·ᶜ (𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ +ᶜ 𝟘ᶜ)                                     ≈⟨ ω·ᶜ+ᶜ⁴𝟘ᶜ ⟩

  𝟘ᶜ                                                              ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
⌈⌉-𝟘ᵐ ([]-cong _ _ _ _ _) =
  ≈ᶜ-refl

-- The context ⌈ t ⌉ m does not change (up to _≈ᶜ_) if it is
-- multiplied by ⌜ m ⌝.

·-⌈⌉ :
  ⦃ has-nr : Has-nr semiring-with-meet ⦄ →
  (t : Term n) → ⌜ m ⌝ ·ᶜ ⌈ t ⌉ m ≈ᶜ ⌈ t ⌉ m
·-⌈⌉ {m = 𝟘ᵐ} t = begin
  𝟘 ·ᶜ ⌈ t ⌉ 𝟘ᵐ  ≈⟨ ·ᶜ-zeroˡ _ ⟩
  𝟘ᶜ             ≈˘⟨ ⌈⌉-𝟘ᵐ t ⟩
  ⌈ t ⌉ 𝟘ᵐ       ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid
·-⌈⌉ {m = 𝟙ᵐ} t = begin
  𝟙 ·ᶜ ⌈ t ⌉ 𝟙ᵐ  ≈⟨ ·ᶜ-identityˡ _ ⟩
  ⌈ t ⌉ 𝟙ᵐ       ∎
  where
  open Tools.Reasoning.Equivalence Conₘ-setoid

open import Graded.Modality.Dedicated-nr.Instance

-- For dedicated nr functions the function ⌈_⌉ provides upper bounds
-- for valid modality contexts when the strong unit type is not
-- allowed to be used as a sink: if γ ▸[ m ] t, then γ ≤ᶜ ⌈ t ⌉ m.

usage-upper-bound :
  ⦃ has-nr : Dedicated-nr ⦄ →
  ⦃ no-sink : ¬Starˢ-sink ⦄ →
  γ ▸[ m ] t → γ ≤ᶜ ⌈ t ⌉ m
usage-upper-bound Uₘ     = ≤ᶜ-refl
usage-upper-bound ℕₘ     = ≤ᶜ-refl
usage-upper-bound Emptyₘ = ≤ᶜ-refl
usage-upper-bound Unitₘ  = ≤ᶜ-refl

usage-upper-bound (ΠΣₘ {G = G} ▸F ▸G) =
  +ᶜ-monotone (usage-upper-bound ▸F)
              (subst (_ ≈ᶜ_) (tailₘ-distrib-∧ᶜ (_ ∙ _) (⌈ G ⌉ _))
                     (tailₘ-cong (usage-upper-bound ▸G)))

usage-upper-bound var = ≤ᶜ-refl

usage-upper-bound (lamₘ {t = t} ▸t) =
  subst (_ ≈ᶜ_) (tailₘ-distrib-∧ᶜ (_ ∙ _) (⌈ t ⌉ _))
    (tailₘ-cong (usage-upper-bound ▸t))

usage-upper-bound (▸t ∘ₘ ▸u) =
  +ᶜ-monotone (usage-upper-bound ▸t)
    (·ᶜ-monotoneʳ (usage-upper-bound ▸u))

usage-upper-bound (prodʷₘ t u) =
  +ᶜ-monotone (·ᶜ-monotoneʳ (usage-upper-bound t)) (usage-upper-bound u)
usage-upper-bound (prodˢₘ t u) =
  ∧ᶜ-monotone (·ᶜ-monotoneʳ (usage-upper-bound t))
    (usage-upper-bound u)
usage-upper-bound (fstₘ _ t PE.refl _) = usage-upper-bound t
usage-upper-bound (sndₘ t) = usage-upper-bound t
usage-upper-bound (prodrecₘ t u A _) =
  +ᶜ-monotone (·ᶜ-monotoneʳ (usage-upper-bound t))
              (tailₘ-monotone (tailₘ-monotone (usage-upper-bound u)))

usage-upper-bound zeroₘ    = ≤ᶜ-refl
usage-upper-bound (sucₘ t) = usage-upper-bound t

usage-upper-bound
  ⦃ has-nr = nr₁ ⦄
  (natrecₘ {z = z} {s = s} {n = n} ⦃ has-nr = nr₂ ⦄ γ▸z δ▸s η▸n θ▸A) =
  case Dedicated-nr-propositional nr₁ nr₂ of λ {
    refl →
  case usage-upper-bound γ▸z of λ {
    γ≤γ′ →
  case usage-upper-bound δ▸s of λ {
    δ≤δ′ →
  case usage-upper-bound η▸n of λ {
    η≤η′ →
  nrᶜ-monotone γ≤γ′ (tailₘ-monotone (tailₘ-monotone δ≤δ′)) η≤η′ }}}}

usage-upper-bound (natrec-no-nrₘ _ _ _ _ _ _ _ _) =
  ⊥-elim not-nr-and-no-nr

usage-upper-bound (emptyrecₘ e A _) =
  ·ᶜ-monotoneʳ (usage-upper-bound e)

usage-upper-bound starʷₘ = ≤ᶜ-refl
usage-upper-bound ⦃ no-sink = ns ⦄ (starˢₘ prop) =
  ≤ᶜ-reflexive (≈ᶜ-trans (·ᶜ-congˡ (≈ᶜ-sym (prop ns)))
                 (·ᶜ-zeroʳ _))

usage-upper-bound (unitrecₘ t u A ok) =
  +ᶜ-monotone (·ᶜ-monotoneʳ (usage-upper-bound t)) (usage-upper-bound u)

usage-upper-bound {m} (Idₘ {δ} {t} {η} {u} not-ok _ ▸t ▸u)
  with Id-erased?
… | yes ok = ⊥-elim (not-ok ok)
… | no _   = begin
  δ +ᶜ η              ≤⟨ +ᶜ-monotone (usage-upper-bound ▸t) (usage-upper-bound ▸u) ⟩
  ⌈ t ⌉ m +ᶜ ⌈ u ⌉ m  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

usage-upper-bound (Id₀ₘ ok _ _ _) with Id-erased?
… | no not-ok = ⊥-elim (not-ok ok)
… | yes _     = ≤ᶜ-refl

usage-upper-bound rflₘ =
  ≤ᶜ-refl

usage-upper-bound
  {m}
  (Jₘ {p} {q} {γ₂} {t} {γ₃} {B} {γ₄} {u} {γ₅} {v} {γ₆} {w}
     ≤some ok _ ▸t ▸B ▸u ▸v ▸w)
  with J-view p q m
… | is-all ≡all               = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
… | is-some-yes ≡some p≡𝟘×q≡𝟘 = ⊥-elim $ ok ≡some p≡𝟘×q≡𝟘
… | is-other _ _              = begin
  ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅ +ᶜ γ₆)                                      ≤⟨ ·ᶜ-monotoneʳ $
                                                                            +ᶜ-monotone (usage-upper-bound ▸t) $
                                                                            +ᶜ-monotone (tailₘ-monotone (tailₘ-monotone (usage-upper-bound ▸B))) $
                                                                            +ᶜ-monotone (usage-upper-bound ▸u) $
                                                                            +ᶜ-monotone (usage-upper-bound ▸v) $
                                                                            usage-upper-bound ▸w ⟩
  ω ·ᶜ
  (⌈ t ⌉ m +ᶜ tailₘ (tailₘ (⌈ B ⌉ m)) +ᶜ ⌈ u ⌉ m +ᶜ ⌈ v ⌉ m +ᶜ ⌈ w ⌉ m)  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

usage-upper-bound
  {m} (J₀ₘ₁ {p} {q} {γ₃} {B} {γ₄} {u} ≡some p≡𝟘 q≡𝟘 _ ▸t ▸B ▸u ▸v ▸w)
  with J-view p q m
… | is-all ≡all     = case trans (PE.sym ≡some) ≡all of λ ()
… | is-other _ 𝟘≢𝟘  = ⊥-elim $ 𝟘≢𝟘 ≡some (p≡𝟘 , q≡𝟘)
… | is-some-yes _ _ = begin
  ω ·ᶜ (γ₃ +ᶜ γ₄)                            ≤⟨ ·ᶜ-monotoneʳ $
                                                +ᶜ-monotone (tailₘ-monotone (tailₘ-monotone (usage-upper-bound ▸B))) $
                                                usage-upper-bound ▸u ⟩
  ω ·ᶜ (tailₘ (tailₘ (⌈ B ⌉ m)) +ᶜ ⌈ u ⌉ m)  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

usage-upper-bound {m} (J₀ₘ₂ {p} {q} ≡all _ _ _ ▸u _ _) with J-view p q m
… | is-other ≤some _    = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
… | is-some-yes ≡some _ = case trans (PE.sym ≡some) ≡all of λ ()
… | is-all _            = usage-upper-bound ▸u

usage-upper-bound
  {m}
  (Kₘ {p} {γ₂} {t} {γ₃} {B} {γ₄} {u} {γ₅} {v} ≤some ok _ ▸t ▸B ▸u ▸v)
  with K-view p m
… | is-all ≡all           = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
… | is-some-yes ≡some p≡𝟘 = ⊥-elim $ ok ≡some p≡𝟘
… | is-other _ _          = begin
  ω ·ᶜ (γ₂ +ᶜ γ₃ +ᶜ γ₄ +ᶜ γ₅)                              ≤⟨ ·ᶜ-monotoneʳ $
                                                              +ᶜ-monotone (usage-upper-bound ▸t) $
                                                              +ᶜ-monotone (tailₘ-monotone (usage-upper-bound ▸B)) $
                                                              +ᶜ-monotone (usage-upper-bound ▸u) $
                                                              usage-upper-bound ▸v ⟩
  ω ·ᶜ (⌈ t ⌉ m +ᶜ tailₘ (⌈ B ⌉ m) +ᶜ ⌈ u ⌉ m +ᶜ ⌈ v ⌉ m)  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

usage-upper-bound
  {m} (K₀ₘ₁ {p} {γ₃} {B} {γ₄} {u} ≡some p≡𝟘 _ ▸t ▸B ▸u ▸v)
  with K-view p m
… | is-all ≡all     = case trans (PE.sym ≡some) ≡all of λ ()
… | is-other _ 𝟘≢𝟘  = ⊥-elim $ 𝟘≢𝟘 ≡some p≡𝟘
… | is-some-yes _ _ = begin
  ω ·ᶜ (γ₃ +ᶜ γ₄)                    ≤⟨ ·ᶜ-monotoneʳ $
                                        +ᶜ-monotone (tailₘ-monotone (usage-upper-bound ▸B)) $
                                        usage-upper-bound ▸u ⟩
  ω ·ᶜ (tailₘ (⌈ B ⌉ m) +ᶜ ⌈ u ⌉ m)  ∎
  where
  open Tools.Reasoning.PartialOrder ≤ᶜ-poset

usage-upper-bound {m} (K₀ₘ₂ {p} ≡all _ _ _ ▸u _) with K-view p m
… | is-other ≤some _    = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
… | is-some-yes ≡some _ = case trans (PE.sym ≡some) ≡all of λ ()
… | is-all _            = usage-upper-bound ▸u

usage-upper-bound ([]-congₘ _ _ _ _) =
  ≤ᶜ-refl

usage-upper-bound (sub t x) = ≤ᶜ-trans x (usage-upper-bound t)


-- A valid modality context can be computed from a well-resourced term
-- (if there is a dedicated nr functions).

usage-inf :
  ⦃ has-nr : Dedicated-nr ⦄ →
  γ ▸[ m ] t → ⌈ t ⌉ m ▸[ m ] t
usage-inf Uₘ = Uₘ
usage-inf ℕₘ = ℕₘ
usage-inf Emptyₘ = Emptyₘ
usage-inf Unitₘ = Unitₘ
usage-inf (ΠΣₘ {G = G} γ▸F δ▸G) =
  ΠΣₘ (usage-inf γ▸F) (Conₘ-interchange₁ (usage-inf δ▸G) δ▸G)
usage-inf var = var
usage-inf (lamₘ {p = p} {t = t} γ▸t) =
  lamₘ (Conₘ-interchange₁ (usage-inf γ▸t) γ▸t)
usage-inf (γ▸t ∘ₘ γ▸t₁) = usage-inf γ▸t ∘ₘ usage-inf γ▸t₁
usage-inf (prodʷₘ γ▸t γ▸t₁) = prodʷₘ (usage-inf γ▸t) (usage-inf γ▸t₁)
usage-inf (prodˢₘ γ▸t γ▸t₁) = prodˢₘ (usage-inf γ▸t) (usage-inf γ▸t₁)
usage-inf (fstₘ m γ▸t PE.refl ok) =
  fstₘ m (usage-inf γ▸t) PE.refl ok
usage-inf (sndₘ γ▸t) = sndₘ (usage-inf γ▸t)
usage-inf {m = m} (prodrecₘ {r = r} {δ = δ} {p = p} {u = u} γ▸t δ▸u η▸A ok) =
  prodrecₘ (usage-inf γ▸t)
           (Conₘ-interchange₂ (usage-inf δ▸u) δ▸u)
           η▸A
           ok
usage-inf zeroₘ = zeroₘ
usage-inf (sucₘ γ▸t) = sucₘ (usage-inf γ▸t)
usage-inf {m = m}
  ⦃ has-nr = nr₁ ⦄
  (natrecₘ {p = p} {r = r} {s = s} ⦃ has-nr = nr₂ ⦄ γ▸z δ▸s η▸n θ▸A) =
  case Dedicated-nr-propositional nr₁ nr₂ of λ {
    refl →
  natrecₘ (usage-inf γ▸z)
          (Conₘ-interchange₂ (usage-inf δ▸s) δ▸s)
          (usage-inf η▸n)
          θ▸A }
usage-inf (natrec-no-nrₘ _ _ _ _ _ _ _ _) =
  ⊥-elim not-nr-and-no-nr
usage-inf (emptyrecₘ γ▸t δ▸A ok) = emptyrecₘ (usage-inf γ▸t) δ▸A ok
usage-inf starʷₘ = starʷₘ
usage-inf (starˢₘ prop) = starₘ
usage-inf (unitrecₘ γ▸t δ▸u η▸A ok) =
  unitrecₘ (usage-inf γ▸t) (usage-inf δ▸u) η▸A ok
usage-inf (Idₘ not-ok ▸A ▸t ▸u) with Id-erased?
… | yes ok = ⊥-elim (not-ok ok)
… | no _   = Idₘ not-ok ▸A (usage-inf ▸t) (usage-inf ▸u)
usage-inf (Id₀ₘ ok ▸A ▸t ▸u) with Id-erased?
… | no not-ok = ⊥-elim (not-ok ok)
… | yes _     = Id₀ₘ ok ▸A ▸t ▸u
usage-inf rflₘ =
  rflₘ
usage-inf {m} (Jₘ {p} {q} ≤some ok ▸A ▸t ▸B ▸u ▸v ▸w) with J-view p q m
… | is-all ≡all               = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
… | is-some-yes ≡some p≡𝟘×q≡𝟘 = ⊥-elim $ ok ≡some p≡𝟘×q≡𝟘
… | is-other _ _              =
  Jₘ ≤some ok ▸A (usage-inf ▸t) (Conₘ-interchange₂ (usage-inf ▸B) ▸B)
    (usage-inf ▸u) (usage-inf ▸v) (usage-inf ▸w)
usage-inf {m} (J₀ₘ₁ {p} {q} ≡some p≡𝟘 q≡𝟘 ▸A ▸t ▸B ▸u ▸v ▸w)
  with J-view p q m
… | is-all ≡all     = case trans (PE.sym ≡some) ≡all of λ ()
… | is-other _ 𝟘≢𝟘  = ⊥-elim $ 𝟘≢𝟘 ≡some (p≡𝟘 , q≡𝟘)
… | is-some-yes _ _ =
  J₀ₘ₁ ≡some p≡𝟘 q≡𝟘 ▸A (usage-inf ▸t)
    (Conₘ-interchange₂ (usage-inf ▸B) ▸B) (usage-inf ▸u) (usage-inf ▸v)
    (usage-inf ▸w)
usage-inf {m} (J₀ₘ₂ {p} {q} ≡all ▸A ▸t ▸B ▸u ▸v ▸w) with J-view p q m
… | is-other ≤some _    = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
… | is-some-yes ≡some _ = case trans (PE.sym ≡some) ≡all of λ ()
… | is-all _            = J₀ₘ₂ ≡all ▸A ▸t ▸B (usage-inf ▸u) ▸v ▸w
usage-inf {m} (Kₘ {p} ≤some ok ▸A ▸t ▸B ▸u ▸v) with K-view p m
… | is-all ≡all           = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
… | is-some-yes ≡some p≡𝟘 = ⊥-elim $ ok ≡some p≡𝟘
… | is-other _ _          =
  Kₘ ≤some ok ▸A (usage-inf ▸t) (Conₘ-interchange₁ (usage-inf ▸B) ▸B)
    (usage-inf ▸u) (usage-inf ▸v)
usage-inf {m} (K₀ₘ₁ {p} ≡some p≡𝟘 ▸A ▸t ▸B ▸u ▸v) with K-view p m
… | is-all ≡all     = case trans (PE.sym ≡some) ≡all of λ ()
… | is-other _ 𝟘≢𝟘  = ⊥-elim $ 𝟘≢𝟘 ≡some p≡𝟘
… | is-some-yes _ _ =
  K₀ₘ₁ ≡some p≡𝟘 ▸A (usage-inf ▸t) (Conₘ-interchange₁ (usage-inf ▸B) ▸B)
    (usage-inf ▸u) (usage-inf ▸v)
usage-inf {m} (K₀ₘ₂ {p} ≡all ▸A ▸t ▸B ▸u ▸v) with K-view p m
… | is-other ≤some _    = case ≤ᵉᵐ→≡all→≡all ≤some ≡all of λ ()
… | is-some-yes ≡some _ = case trans (PE.sym ≡some) ≡all of λ ()
… | is-all _            = K₀ₘ₂ ≡all ▸A ▸t ▸B (usage-inf ▸u) ▸v
usage-inf ([]-congₘ ▸A ▸t ▸u ▸v) =
  []-congₘ ▸A ▸t ▸u ▸v
usage-inf (sub γ▸t x) = usage-inf γ▸t

------------------------------------------------------------------------
-- A negative result

module _ (TR : Type-restrictions) where

  open Definition.Typed TR

  -- It is always the case that Γ ⊢ t ∷ A implies Γ ⊢ A (see
  -- Definition.Typed.Consequences.Syntactic.syntacticTerm), but if
  -- Γ ⊢ t ∷ A and γ ▸[ 𝟙ᵐ ] t always imply γ ▸[ 𝟙ᵐ ] A, then the
  -- modality is trivial.

  ▸-term→▸-type :
    (∀ {n} {Γ : Con Term n} {t A : Term n} {γ : Conₘ n} →
       Γ ⊢ t ∷ A → γ ▸[ 𝟙ᵐ ] t → γ ▸[ 𝟙ᵐ ] A) →
    Trivial
  ▸-term→▸-type hyp =
    case inv-usage-var (hyp ⊢t ▸t) of λ {
      (ε ∙ 𝟘≤𝟙 ∙ 𝟙≤𝟘) →
    ≤-antisym 𝟙≤𝟘 𝟘≤𝟙 }
    where
    Γ′ = ε ∙ (U l) ∙ var x0
    t′ = var x0
    A′ = var x1
    γ′ = ε ∙ 𝟘 ∙ 𝟙

    ⊢U : ⊢ ε ∙ (U l)
    ⊢U = ε ∙ Uⱼ ε

    ⊢Γ : ⊢ Γ′
    ⊢Γ = ⊢U ∙ univ (var ⊢U here)

    ⊢t : Γ′ ⊢ t′ ∷ A′
    ⊢t = var ⊢Γ here

    ▸t : γ′ ▸[ 𝟙ᵐ ] t′
    ▸t = var
