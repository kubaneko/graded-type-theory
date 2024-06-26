------------------------------------------------------------------------
-- A modality for the natural numbers extended with infinity
------------------------------------------------------------------------

module Graded.Modality.Instances.Nat-plus-infinity where

import Tools.Algebra
open import Tools.Bool using (T)
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat as N using (Nat; 1+)
open import Tools.Product as Σ
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum as ⊎ using (_⊎_; inj₁; inj₂)

open import Graded.FullReduction.Assumptions
import Graded.Modality
import Graded.Modality.Instances.BoundedStar as BoundedStar
import Graded.Modality.Instances.LowerBounded as LowerBounded
import Graded.Modality.Instances.Recursive.Sequences
import Graded.Modality.Properties.Division
import Graded.Modality.Properties.Meet
import Graded.Modality.Properties.PartialOrder
open import Graded.Modality.Variant lzero

open import Definition.Typed.Restrictions
open import Definition.Untyped using (BMΣ; 𝕤)
open import Graded.Usage.Restrictions

-- The grades are the natural numbers extended with ∞.

data ℕ⊎∞ : Set where
  ⌞_⌟ : Nat → ℕ⊎∞
  ∞   : ℕ⊎∞

open Graded.Modality ℕ⊎∞
open Tools.Algebra   ℕ⊎∞

private variable
  m n o   : ℕ⊎∞
  TRs     : Type-restrictions _
  URs     : Usage-restrictions _
  variant : Modality-variant

------------------------------------------------------------------------
-- Operators

-- Meet.
--
-- The meet operation is defined in such a way that
-- ∞ ≤ … ≤ ⌞ 1 ⌟ ≤ ⌞ 0 ⌟.

infixr 40 _∧_

_∧_ : ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞
∞     ∧ _     = ∞
⌞ _ ⌟ ∧ ∞     = ∞
⌞ m ⌟ ∧ ⌞ n ⌟ = ⌞ m N.⊔ n ⌟

-- Addition.

infixr 40 _+_

_+_ : ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞
∞     + _     = ∞
⌞ _ ⌟ + ∞     = ∞
⌞ m ⌟ + ⌞ n ⌟ = ⌞ m N.+ n ⌟

-- Multiplication.

infixr 45 _·_

_·_ : ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞
⌞ 0 ⌟ · _     = ⌞ 0 ⌟
_     · ⌞ 0 ⌟ = ⌞ 0 ⌟
∞     · _     = ∞
⌞ _ ⌟ · ∞     = ∞
⌞ m ⌟ · ⌞ n ⌟ = ⌞ m N.* n ⌟

-- Division.

infixl 45 _/_

_/_ : ℕ⊎∞ → ℕ⊎∞ → ℕ⊎∞
_     / ⌞ 0 ⌟    = ∞
⌞ m ⌟ / ⌞ 1+ n ⌟ = ⌞ m N./ 1+ n ⌟
∞     / ⌞ 1+ _ ⌟ = ∞
∞     / ∞        = ∞
⌞ _ ⌟ / ∞        = ⌞ 0 ⌟

-- A star operator.

infix 50 _*

_* : ℕ⊎∞ → ℕ⊎∞
⌞ 0 ⌟ * = ⌞ 1 ⌟
_     * = ∞

-- The inferred ordering relation.

infix 10 _≤_

_≤_ : ℕ⊎∞ → ℕ⊎∞ → Set
m ≤ n = m ≡ m ∧ n

------------------------------------------------------------------------
-- Some properties

-- The grade ∞ is the least one.

∞≤ : ∀ n → ∞ ≤ n
∞≤ _ = refl

-- The grade ⌞ 0 ⌟ is the greatest one.

≤0 : n ≤ ⌞ 0 ⌟
≤0 {n = ∞}     = refl
≤0 {n = ⌞ n ⌟} = cong ⌞_⌟ (
  n        ≡˘⟨ N.⊔-identityʳ _ ⟩
  n N.⊔ 0  ∎)
  where
  open Tools.Reasoning.PropositionalEquality

-- Multiplication is commutative.

·-comm : Commutative _·_
·-comm = λ where
  ⌞ 0 ⌟    ⌞ 0 ⌟    → refl
  ⌞ 1+ _ ⌟ ⌞ 0 ⌟    → refl
  ⌞ 0 ⌟    ⌞ 1+ _ ⌟ → refl
  ⌞ 1+ m ⌟ ⌞ 1+ _ ⌟ → cong ⌞_⌟ (N.*-comm (1+ m) _)
  ⌞ 0 ⌟    ∞        → refl
  ⌞ 1+ _ ⌟ ∞        → refl
  ∞        ⌞ 0 ⌟    → refl
  ∞        ⌞ 1+ _ ⌟ → refl
  ∞        ∞        → refl

-- The function ⌞_⌟ is injective.

⌞⌟-injective : ∀ {m n} → ⌞ m ⌟ ≡ ⌞ n ⌟ → m ≡ n
⌞⌟-injective refl = refl

-- The function ⌞_⌟ is antitone.

⌞⌟-antitone : ∀ {m n} → m N.≤ n → ⌞ n ⌟ ≤ ⌞ m ⌟
⌞⌟-antitone {m = m} {n = n} m≤n =
  ⌞ n ⌟        ≡˘⟨ cong ⌞_⌟ (N.m≥n⇒m⊔n≡m m≤n) ⟩
  ⌞ n N.⊔ m ⌟  ∎
  where
  open Tools.Reasoning.PropositionalEquality

-- An inverse to ⌞⌟-antitone.

⌞⌟-antitone⁻¹ : ∀ {m n} → ⌞ n ⌟ ≤ ⌞ m ⌟ → m N.≤ n
⌞⌟-antitone⁻¹ {m = m} {n = n} =
  ⌞ n ⌟ ≤ ⌞ m ⌟  →⟨ ⌞⌟-injective ⟩
  n ≡ n N.⊔ m    →⟨ N.m⊔n≡m⇒n≤m ∘→ sym ⟩
  m N.≤ n        □

-- The function ⌞_⌟ is homomorphic with respect to _·_/N._*_.

⌞⌟·⌞⌟≡⌞*⌟ : ∀ {m n} → ⌞ m ⌟ · ⌞ n ⌟ ≡ ⌞ m N.* n ⌟
⌞⌟·⌞⌟≡⌞*⌟ {m = 0}               = refl
⌞⌟·⌞⌟≡⌞*⌟ {m = 1+ _} {n = 1+ _} = refl
⌞⌟·⌞⌟≡⌞*⌟ {m = 1+ m} {n = 0}    = cong ⌞_⌟ (sym (N.*-zeroʳ m))

-- Addition is decreasing for the left argument.

+-decreasingˡ : m + n ≤ m
+-decreasingˡ {m = ∞}                 = refl
+-decreasingˡ {m = ⌞ _ ⌟} {n = ∞}     = refl
+-decreasingˡ {m = ⌞ _ ⌟} {n = ⌞ n ⌟} = ⌞⌟-antitone (N.m≤m+n _ n)

-- One of the two characteristic properties of the star operator of a
-- star semiring.

*≡+·* : n * ≡ ⌞ 1 ⌟ + n · n *
*≡+·* {n = ∞}        = refl
*≡+·* {n = ⌞ 0 ⌟}    = refl
*≡+·* {n = ⌞ 1+ _ ⌟} = refl

-- One of the two characteristic properties of the star operator of a
-- star semiring.

*≡+*· : n * ≡ ⌞ 1 ⌟ + n * · n
*≡+*· {n = ∞}        = refl
*≡+*· {n = ⌞ 0 ⌟}    = refl
*≡+*· {n = ⌞ 1+ _ ⌟} = refl

-- Equality is decidable.

_≟_ : Decidable (_≡_ {A = ℕ⊎∞})
_≟_ = λ where
  ∞     ∞     → yes refl
  ⌞ _ ⌟ ∞     → no (λ ())
  ∞     ⌞ _ ⌟ → no (λ ())
  ⌞ m ⌟ ⌞ n ⌟ → case m N.≟ n of λ where
    (yes refl) → yes refl
    (no m≢n)   → no (λ { refl → m≢n refl })

-- The relation _≤_ is total.

≤-total : ∀ m n → m ≤ n ⊎ n ≤ m
≤-total ∞     _     = inj₁ refl
≤-total _     ∞     = inj₂ refl
≤-total ⌞ m ⌟ ⌞ n ⌟ = case N.≤-total m n of λ where
  (inj₁ m≤n) → inj₂ (⌞⌟-antitone m≤n)
  (inj₂ n≤m) → inj₁ (⌞⌟-antitone n≤m)

-- The type ℕ⊎∞ is a set.

ℕ⊎∞-set : Is-set ℕ⊎∞
ℕ⊎∞-set {x = ∞}     {y = ∞}     {x = refl} {y = refl} = refl
ℕ⊎∞-set {x = ⌞ m ⌟} {y = ⌞ n ⌟} {x = p}    {y = q}    =
                                                         $⟨ N.Nat-set ⟩
  ⌞⌟-injective p ≡ ⌞⌟-injective q                        →⟨ cong (cong ⌞_⌟) ⟩
  cong ⌞_⌟ (⌞⌟-injective p) ≡ cong ⌞_⌟ (⌞⌟-injective q)  →⟨ (λ hyp → trans (sym (lemma _)) (trans hyp (lemma _))) ⟩
  p ≡ q                                                  □
  where
  lemma : (p : ⌞ m ⌟ ≡ ⌞ n ⌟) → cong ⌞_⌟ (⌞⌟-injective p) ≡ p
  lemma refl = refl

opaque

  -- The grade ∞ · (m + n) is bounded by ∞ · n.

  ∞·+≤∞·ʳ : ∞ · (m + n) ≤ ∞ · n
  ∞·+≤∞·ʳ {m = ∞}                       = refl
  ∞·+≤∞·ʳ {m = ⌞ _ ⌟}    {n = ∞}        = refl
  ∞·+≤∞·ʳ {m = ⌞ 0 ⌟}    {n = ⌞ 0 ⌟}    = refl
  ∞·+≤∞·ʳ {m = ⌞ 1+ _ ⌟} {n = ⌞ 0 ⌟}    = refl
  ∞·+≤∞·ʳ {m = ⌞ 0 ⌟}    {n = ⌞ 1+ _ ⌟} = refl
  ∞·+≤∞·ʳ {m = ⌞ 1+ _ ⌟} {n = ⌞ 1+ _ ⌟} = refl

------------------------------------------------------------------------
-- The modality

-- A "semiring with meet" for ℕ⊎∞.

ℕ⊎∞-semiring-with-meet : Semiring-with-meet
ℕ⊎∞-semiring-with-meet = record
  { _+_          = _+_
  ; _·_          = _·_
  ; _∧_          = _∧_
  ; 𝟘            = ⌞ 0 ⌟
  ; 𝟙            = ⌞ 1 ⌟
  ; ω            = ∞
  ; ω≤𝟙          = refl
  ; ω·+≤ω·ʳ      = ∞·+≤∞·ʳ
  ; is-𝟘?        = _≟ ⌞ 0 ⌟
  ; +-·-Semiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = PE.isEquivalence
              ; ∙-cong        = cong₂ _+_
              }
            ; assoc = +-assoc
            }
          ; identity =
                (λ where
                   ⌞ _ ⌟ → refl
                   ∞     → refl)
              , (λ where
                   ⌞ _ ⌟ → cong ⌞_⌟ (N.+-identityʳ _)
                   ∞     → refl)
          }
        ; comm = +-comm
        }
      ; *-cong = cong₂ _·_
      ; *-assoc = ·-assoc
      ; *-identity =
            (λ where
               ⌞ 0 ⌟    → refl
               ⌞ 1+ _ ⌟ → cong ⌞_⌟ (N.+-identityʳ _)
               ∞        → refl)
          , (λ where
               ⌞ 0 ⌟    → refl
               ⌞ 1+ _ ⌟ → cong (⌞_⌟ ∘→ 1+) (N.*-identityʳ _)
               ∞        → refl)
      ; distrib = ·-distrib-+
      }
    ; zero =
          (λ _ → refl)
        , (λ where
             ⌞ 0 ⌟    → refl
             ⌞ 1+ _ ⌟ → refl
             ∞        → refl)
    }
  ; ∧-Semilattice = record
    { isBand = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = PE.isEquivalence
          ; ∙-cong        = cong₂ _∧_
          }
        ; assoc = ∧-assoc
        }
      ; idem = λ where
          ⌞ _ ⌟ → cong ⌞_⌟ (N.⊔-idem _)
          ∞     → refl
      }
    ; comm = ∧-comm
    }
  ; ·-distrib-∧ = ·-distrib-∧
  ; +-distrib-∧ = +-distrib-∧
  }
  where
  open Tools.Reasoning.PropositionalEquality

  +-assoc : Associative _+_
  +-assoc = λ where
    ⌞ m ⌟ ⌞ _ ⌟ ⌞ _ ⌟ → cong ⌞_⌟ (N.+-assoc m _ _)
    ⌞ _ ⌟ ⌞ _ ⌟ ∞     → refl
    ⌞ _ ⌟ ∞     _     → refl
    ∞     _     _     → refl

  +-comm : Commutative _+_
  +-comm = λ where
    ⌞ 0 ⌟    ⌞ 0 ⌟    → refl
    ⌞ 1+ _ ⌟ ⌞ 0 ⌟    → cong ⌞_⌟ (N.+-identityʳ _)
    ⌞ 0 ⌟    ⌞ 1+ _ ⌟ → cong ⌞_⌟ (sym (N.+-identityʳ _))
    ⌞ 1+ m ⌟ ⌞ 1+ _ ⌟ → cong ⌞_⌟ (N.+-comm (1+ m) _)
    ⌞ 0 ⌟    ∞        → refl
    ⌞ 1+ _ ⌟ ∞        → refl
    ∞        ⌞ 0 ⌟    → refl
    ∞        ⌞ 1+ _ ⌟ → refl
    ∞        ∞        → refl

  ·-assoc : Associative _·_
  ·-assoc = λ where
    ⌞ 0 ⌟    _        _        → refl
    ⌞ 1+ _ ⌟ ⌞ 0    ⌟ _        → refl
    ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ ⌞ 0 ⌟    → refl
    ⌞ 1+ m ⌟ ⌞ 1+ n ⌟ ⌞ 1+ _ ⌟ → cong ⌞_⌟ $
                                 N.*-assoc (1+ m) (1+ n) (1+ _)
    ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ ∞        → refl
    ⌞ 1+ _ ⌟ ∞        ⌞ 0  ⌟   → refl
    ⌞ 1+ _ ⌟ ∞        ⌞ 1+ _ ⌟ → refl
    ⌞ 1+ _ ⌟ ∞        ∞        → refl
    ∞        ⌞ 0    ⌟ _        → refl
    ∞        ⌞ 1+ _ ⌟ ⌞ 0 ⌟    → refl
    ∞        ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ → refl
    ∞        ⌞ 1+ _ ⌟ ∞        → refl
    ∞        ∞        ⌞ 0  ⌟   → refl
    ∞        ∞        ⌞ 1+ _ ⌟ → refl
    ∞        ∞        ∞        → refl

  ·-distribˡ-+ : _·_ DistributesOverˡ _+_
  ·-distribˡ-+ = λ where
    ⌞ 0 ⌟    _        _        → refl
    ⌞ 1+ _ ⌟ ⌞ 0    ⌟ ⌞ 0 ⌟    → refl
    ⌞ 1+ _ ⌟ ⌞ 0    ⌟ ⌞ 1+ _ ⌟ → refl
    ⌞ 1+ _ ⌟ ⌞ 0    ⌟ ∞        → refl
    ⌞ 1+ m ⌟ ⌞ 1+ n ⌟ ⌞ 0 ⌟    →
      ⌞ 1+ m ⌟ · (⌞ 1+ n ⌟ + ⌞ 0 ⌟)           ≡⟨⟩
      ⌞ 1+ m N.* (1+ n N.+ 0) ⌟               ≡⟨ cong ⌞_⌟ (N.*-distribˡ-+ (1+ m) (1+ _) 0) ⟩
      ⌞ 1+ m N.* 1+ n N.+ 1+ m N.* 0 ⌟        ≡⟨ cong (λ o → ⌞ 1+ m N.* 1+ n N.+ o ⌟) (N.*-zeroʳ (1+ m)) ⟩
      ⌞ 1+ m N.* 1+ n N.+ 0 ⌟                 ≡⟨⟩
      ⌞ 1+ m ⌟ · ⌞ 1+ n ⌟ + ⌞ 1+ m ⌟ · ⌞ 0 ⌟  ∎
    ⌞ 1+ m ⌟ ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ → cong ⌞_⌟ $
                                 N.*-distribˡ-+ (1+ m) (1+ _) (1+ _)
    ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ ∞        → refl
    ⌞ 1+ _ ⌟ ∞        ⌞ 0  ⌟   → refl
    ⌞ 1+ _ ⌟ ∞        ⌞ 1+ _ ⌟ → refl
    ⌞ 1+ _ ⌟ ∞        ∞        → refl
    ∞        ⌞ 0    ⌟ ⌞ 0 ⌟    → refl
    ∞        ⌞ 0    ⌟ ⌞ 1+ _ ⌟ → refl
    ∞        ⌞ 0    ⌟ ∞        → refl
    ∞        ⌞ 1+ _ ⌟ ⌞ 0 ⌟    → refl
    ∞        ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ → refl
    ∞        ⌞ 1+ _ ⌟ ∞        → refl
    ∞        ∞        ⌞ 0  ⌟   → refl
    ∞        ∞        ⌞ 1+ _ ⌟ → refl
    ∞        ∞        ∞        → refl

  ·-distrib-+ : _·_ DistributesOver _+_
  ·-distrib-+ =
    ·-distribˡ-+ , comm∧distrˡ⇒distrʳ ·-comm ·-distribˡ-+

  ∧-assoc : Associative _∧_
  ∧-assoc = λ where
    ⌞ m ⌟ ⌞ _ ⌟ ⌞ _ ⌟ → cong ⌞_⌟ (N.⊔-assoc m _ _)
    ⌞ _ ⌟ ⌞ _ ⌟ ∞     → refl
    ⌞ _ ⌟ ∞     _     → refl
    ∞     _     _     → refl

  ∧-comm : Commutative _∧_
  ∧-comm = λ where
    ⌞ 0 ⌟    ⌞ 0 ⌟    → refl
    ⌞ 1+ _ ⌟ ⌞ 0 ⌟    → refl
    ⌞ 0 ⌟    ⌞ 1+ _ ⌟ → refl
    ⌞ 1+ m ⌟ ⌞ 1+ _ ⌟ → cong ⌞_⌟ (N.⊔-comm (1+ m) (1+ _))
    ⌞ 0 ⌟    ∞        → refl
    ⌞ 1+ _ ⌟ ∞        → refl
    ∞        ⌞ 0 ⌟    → refl
    ∞        ⌞ 1+ _ ⌟ → refl
    ∞        ∞        → refl

  ·-distribˡ-∧ : _·_ DistributesOverˡ _∧_
  ·-distribˡ-∧ = λ where
    ⌞ 0 ⌟    _        _        → refl
    ⌞ 1+ _ ⌟ ⌞ 0    ⌟ ⌞ 0 ⌟    → refl
    ⌞ 1+ _ ⌟ ⌞ 0    ⌟ ⌞ 1+ _ ⌟ → refl
    ⌞ 1+ _ ⌟ ⌞ 0    ⌟ ∞        → refl
    ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ ⌞ 0 ⌟    → refl
    ⌞ 1+ m ⌟ ⌞ 1+ n ⌟ ⌞ 1+ _ ⌟ → cong ⌞_⌟ $
                                 N.*-distribˡ-⊔ (1+ m) (1+ n) (1+ _)
    ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ ∞        → refl
    ⌞ 1+ _ ⌟ ∞        ⌞ 0  ⌟   → refl
    ⌞ 1+ _ ⌟ ∞        ⌞ 1+ _ ⌟ → refl
    ⌞ 1+ _ ⌟ ∞        ∞        → refl
    ∞        ⌞ 0    ⌟ ⌞ 0 ⌟    → refl
    ∞        ⌞ 0    ⌟ ⌞ 1+ _ ⌟ → refl
    ∞        ⌞ 0    ⌟ ∞        → refl
    ∞        ⌞ 1+ _ ⌟ ⌞ 0 ⌟    → refl
    ∞        ⌞ 1+ _ ⌟ ⌞ 1+ _ ⌟ → refl
    ∞        ⌞ 1+ _ ⌟ ∞        → refl
    ∞        ∞        ⌞ 0  ⌟   → refl
    ∞        ∞        ⌞ 1+ _ ⌟ → refl
    ∞        ∞        ∞        → refl

  ·-distrib-∧ : _·_ DistributesOver _∧_
  ·-distrib-∧ =
    ·-distribˡ-∧ , comm∧distrˡ⇒distrʳ ·-comm ·-distribˡ-∧

  +-distribˡ-∧ : _+_ DistributesOverˡ _∧_
  +-distribˡ-∧ = λ where
    ⌞ m ⌟ ⌞ _ ⌟ ⌞ _ ⌟ → cong ⌞_⌟ (N.+-distribˡ-⊔ m _ _)
    ⌞ _ ⌟ ⌞ _ ⌟ ∞     → refl
    ⌞ _ ⌟ ∞     _     → refl
    ∞     _     _     → refl

  +-distrib-∧ : _+_ DistributesOver _∧_
  +-distrib-∧ =
    +-distribˡ-∧ , comm∧distrˡ⇒distrʳ +-comm +-distribˡ-∧

instance

  -- The semiring has a well-behaved zero.

  ℕ⊎∞-has-well-behaved-zero :
    Has-well-behaved-zero ℕ⊎∞-semiring-with-meet
  ℕ⊎∞-has-well-behaved-zero = record
    { non-trivial  = λ ()
    ; zero-product = λ where
        {p = ⌞ 0 ⌟} {q = ⌞ _ ⌟} _ → inj₁ refl
        {p = ⌞ 0 ⌟} {q = ∞}     _ → inj₁ refl
        {p = ⌞ _ ⌟} {q = ⌞ 0 ⌟} _ → inj₂ refl
        {p = ∞}     {q = ⌞ 0 ⌟} _ → inj₂ refl
    ; +-positiveˡ  = λ where
        {p = ⌞ 0 ⌟} {q = ⌞ _ ⌟} _ → refl
    ; ∧-positiveˡ  = λ where
        {p = ⌞ 0 ⌟}    {q = ⌞ _ ⌟} _  → refl
        {p = ⌞ 1+ _ ⌟} {q = ⌞ 0 ⌟} ()
    }

private
  module BS =
    BoundedStar
      ℕ⊎∞-semiring-with-meet _* (λ _ → *≡+·*) (λ _ → inj₁ ≤0)

-- A natrec-star operator for ℕ⊎∞ defined using the construction in
-- Graded.Modality.Instances.BoundedStar.

ℕ⊎∞-has-star-bounded-star : Has-star ℕ⊎∞-semiring-with-meet
ℕ⊎∞-has-star-bounded-star = BS.has-star

-- A natrec-star operator for ℕ⊎∞ defined using the construction in
-- Graded.Modality.Instances.LowerBounded.

ℕ⊎∞-has-star-lower-bounded : Has-star ℕ⊎∞-semiring-with-meet
ℕ⊎∞-has-star-lower-bounded =
  LowerBounded.has-star ℕ⊎∞-semiring-with-meet ∞ ∞≤

-- The _⊛_▷_ operator of the second modality is equal to the _⊛_▷_
-- operator of the first modality for non-zero last arguments.

≢𝟘→⊛▷≡⊛▷ :
  let module HS₁ = Has-star ℕ⊎∞-has-star-bounded-star
      module HS₂ = Has-star ℕ⊎∞-has-star-lower-bounded
  in
  o ≢ ⌞ 0 ⌟ →
  m HS₁.⊛ n ▷ o ≡ m HS₂.⊛ n ▷ o
≢𝟘→⊛▷≡⊛▷ {o = ∞}        _   = refl
≢𝟘→⊛▷≡⊛▷ {o = ⌞ 1+ _ ⌟} _   = refl
≢𝟘→⊛▷≡⊛▷ {o = ⌞ 0 ⌟}    0≢0 = ⊥-elim (0≢0 refl)

-- The _⊛_▷_ operator of the second modality is bounded strictly by
-- the _⊛_▷_ operator of the first modality.

⊛▷<⊛▷ :
  let module HS₁ = Has-star ℕ⊎∞-has-star-bounded-star
      module HS₂ = Has-star ℕ⊎∞-has-star-lower-bounded
  in
  (∀ m n o → m HS₂.⊛ n ▷ o ≤ m HS₁.⊛ n ▷ o) ×
  (∃₃ λ m n o → m HS₂.⊛ n ▷ o ≢ m HS₁.⊛ n ▷ o)
⊛▷<⊛▷ =
    BS.LowerBounded.⊛′≤⊛ ∞ (λ _ → refl)
  , ⌞ 1 ⌟ , ⌞ 1 ⌟ , ⌞ 0 ⌟ , (λ ())

-- A modality (of any kind) for ℕ⊎∞ defined using the construction in
-- Graded.Modality.Instances.BoundedStar.

ℕ⊎∞-modality : Modality-variant → Modality
ℕ⊎∞-modality variant =
  BS.isModality variant (λ _ → ℕ⊎∞-has-well-behaved-zero)

------------------------------------------------------------------------
-- A property related to division

private
  module D = Graded.Modality.Properties.Division ℕ⊎∞-semiring-with-meet

-- The division operator is correctly defined.

/≡/ : m D./ n ≡ m / n
/≡/ {m = ∞}     {n = ∞}        = refl , λ _ _ → refl
/≡/ {m = ⌞ _ ⌟} {n = ∞}        = ≤0   , λ { ⌞ 0 ⌟ _ → refl }
/≡/             {n = ⌞ 0 ⌟}    = ≤0   , λ _ _ → refl
/≡/ {m = ∞}     {n = ⌞ 1+ _ ⌟} = refl , λ _ _ → refl
/≡/ {m = ⌞ m ⌟} {n = ⌞ 1+ n ⌟} =
    (begin
       ⌞ m ⌟                      ≤⟨ ⌞⌟-antitone (N.m/n*n≤m _ (1+ _)) ⟩
       ⌞ (m N./ 1+ n) N.* 1+ n ⌟  ≡⟨ cong ⌞_⌟ (N.*-comm _ (1+ n)) ⟩
       ⌞ 1+ n N.* (m N./ 1+ n) ⌟  ≡˘⟨ ⌞⌟·⌞⌟≡⌞*⌟ ⟩
       ⌞ 1+ n ⌟ · ⌞ m N./ 1+ n ⌟  ∎)
  , λ where
      ⌞ o ⌟ →
        ⌞ m ⌟ ≤ ⌞ 1+ n ⌟ · ⌞ o ⌟  ≡⟨ cong (_ ≤_) ⌞⌟·⌞⌟≡⌞*⌟ ⟩→
        ⌞ m ⌟ ≤ ⌞ 1+ n N.* o ⌟    →⟨ ⌞⌟-antitone⁻¹ ⟩
        1+ n N.* o N.≤ m          →⟨ N.*≤→≤/ ⟩
        o N.≤ m N./ 1+ n          →⟨ ⌞⌟-antitone ⟩
        ⌞ m N./ 1+ n ⌟ ≤ ⌞ o ⌟    □
  where
  open Graded.Modality.Properties.PartialOrder ℕ⊎∞-semiring-with-meet
  open Tools.Reasoning.PartialOrder ≤-poset

------------------------------------------------------------------------
-- A lemma related to Graded.Modality.Instances.Recursive

open Graded.Modality.Instances.Recursive.Sequences
       ℕ⊎∞-semiring-with-meet

-- The family of sequences that Graded.Modality.Instances.Recursive is
-- about does not have the required fixpoints.

¬-Has-fixpoints-nr : ¬ Has-fixpoints-nr
¬-Has-fixpoints-nr =
  (∀ r → ∃ λ n → ∀ p q → nr (1+ n) p q r ≡ nr n p q r)  →⟨ (λ hyp → Σ.map idᶠ (λ f → f p q) (hyp r)) ⟩
  (∃ λ n → nr (1+ n) p q r ≡ nr n p q r)                →⟨ Σ.map idᶠ (λ {x = n} → trans (sym (increasing n))) ⟩
  (∃ λ n → ⌞ 1 ⌟ + nr n p q r ≡ nr n p q r)             →⟨ (λ (n , hyp) →
                                                                _
                                                              , subst (λ n → ⌞ 1 ⌟ + n ≡ n) (always-⌞⌟ n .proj₂) hyp) ⟩
  (∃ λ n → ⌞ 1+ n ⌟ ≡ ⌞ n ⌟)                            →⟨ (λ { (_ , ()) }) ⟩
  ⊥                                                     □
  where
  open module S = Semiring-with-meet ℕ⊎∞-semiring-with-meet using (𝟘; 𝟙)
  open Graded.Modality.Properties.Meet ℕ⊎∞-semiring-with-meet
  open Tools.Reasoning.PropositionalEquality

  r = 𝟙
  p = 𝟘
  q = 𝟙

  increasing : ∀ n → nr (1+ n) p q r ≡ 𝟙 + nr n p q r
  increasing 0      = refl
  increasing (1+ n) =
    p ∧ (q + r · nr (1+ n) p q r)   ≡⟨ largest→∧≡ʳ (λ _ → ≤0) ⟩
    q + r · nr (1+ n) p q r         ≡⟨ cong (λ n → q + r · n) (increasing n) ⟩
    q + r · (𝟙 + nr n p q r)        ≡⟨ cong (q +_) (S.·-identityˡ _) ⟩
    q + (𝟙 + nr n p q r)            ≡˘⟨ S.+-assoc _ _ _ ⟩
    (q + 𝟙) + nr n p q r            ≡⟨ cong (_+ nr n p q r) (S.+-comm q _) ⟩
    (𝟙 + q) + nr n p q r            ≡⟨ S.+-assoc _ _ _ ⟩
    𝟙 + (q + nr n p q r)            ≡˘⟨ cong ((𝟙 +_) ∘→ (q +_)) (S.·-identityˡ _) ⟩
    𝟙 + (q + r · nr n p q r)        ≡˘⟨ cong (𝟙 +_) (largest→∧≡ʳ (λ _ → ≤0)) ⟩
    𝟙 + (p ∧ (q + r · nr n p q r))  ∎

  always-⌞⌟ : ∀ m → ∃ λ n → nr m p q r ≡ ⌞ n ⌟
  always-⌞⌟ 0      = _ , refl
  always-⌞⌟ (1+ m) =
    case always-⌞⌟ m of λ {
      (n , eq) →
      1+ n
    , (nr (1+ m) p q r  ≡⟨ increasing m ⟩
       𝟙 + nr m p q r   ≡⟨ cong (𝟙 +_) eq ⟩
       ⌞ 1+ n ⌟         ∎) }

------------------------------------------------------------------------
-- Instances of Full-reduction-assumptions

-- An instance of Type-restrictions (ℕ⊎∞-modality variant) is suitable
-- for the full reduction theorem if whenever Σˢ-allowed m n holds,
-- then m is ⌞ 1 ⌟, or m is ⌞ 0 ⌟ and 𝟘ᵐ is allowed.

Suitable-for-full-reduction :
  ∀ variant → Type-restrictions (ℕ⊎∞-modality variant) → Set
Suitable-for-full-reduction variant TRs =
  ∀ m n → Σˢ-allowed m n → m ≡ ⌞ 1 ⌟ ⊎ m ≡ ⌞ 0 ⌟ × T 𝟘ᵐ-allowed
  where
  open Modality-variant variant
  open Type-restrictions TRs

-- Given an instance of Type-restrictions (ℕ⊎∞-modality variant) one
-- can create a "suitable" instance of Type-restrictions.

suitable-for-full-reduction :
  Type-restrictions (ℕ⊎∞-modality variant) →
  ∃ (Suitable-for-full-reduction variant)
suitable-for-full-reduction {variant = variant} TRs =
    record TRs
      { ΠΣ-allowed = λ b m n →
          ΠΣ-allowed b m n ×
          (b ≡ BMΣ 𝕤 → m ≡ ⌞ 1 ⌟ ⊎ m ≡ ⌞ 0 ⌟ × T 𝟘ᵐ-allowed)
      ; []-cong-allowed = λ s →
          []-cong-allowed s × T 𝟘ᵐ-allowed
      ; []-cong→Erased = λ (ok₁ , ok₂) →
            []-cong→Erased ok₁ .proj₁ , []-cong→Erased ok₁ .proj₂
          , (λ _ → inj₂ (refl , ok₂))
      ; []-cong→¬Trivial =
          λ _ ()
      }
  , (λ _ _ → (_$ refl) ∘→ proj₂)
  where
  open Modality-variant variant
  open Type-restrictions TRs

-- The full reduction assumptions hold for ℕ⊎∞-modality variant and
-- any "suitable" instance of Type-restrictions.

full-reduction-assumptions :
  Suitable-for-full-reduction variant TRs →
  Full-reduction-assumptions TRs URs
full-reduction-assumptions ok = record
  { sink⊎𝟙≤𝟘    = λ _ _ → inj₂ refl
  ; ≡𝟙⊎𝟙≤𝟘 = ⊎.map idᶠ (λ (p≡⌞0⌟ , ok) → p≡⌞0⌟ , ok , refl) ∘→ ok _ _
  }

-- Type and usage restrictions that satisfy the full reduction
-- assumptions are "suitable".

full-reduction-assumptions-suitable :
  Full-reduction-assumptions TRs URs →
  Suitable-for-full-reduction variant TRs
full-reduction-assumptions-suitable as =
  λ m n Σ-ok →
    case ≡𝟙⊎𝟙≤𝟘 Σ-ok of λ where
      (inj₁ m≡𝟙) → inj₁ m≡𝟙
      (inj₂ (m≡𝟘 , 𝟘ᵐ-ok , _)) → inj₂ (m≡𝟘 , 𝟘ᵐ-ok)
  where
  open Full-reduction-assumptions as
