------------------------------------------------------------------------
-- The erasure modality semiring.
------------------------------------------------------------------------

module Graded.Modality.Instances.Erasure where

open import Tools.Product
open import Tools.PropositionalEquality
open import Tools.Relation

-- The set of erasure annotations with 𝟘 corresponding to no usage
-- and ω to any usage.

data Erasure : Set where
  𝟘 ω : Erasure

open import Tools.Algebra Erasure

private variable
  q : Erasure

infixl 40 _+_
infixl 40 _∧_
infixl 45 _·_ _/_
infix  10 _≤_ _≟_
infix  50 _⊛_▷_

---------------------------------------
-- Operations for erasure anntations --
---------------------------------------

-- Addition of erasure annotations

_+_ : Op₂ Erasure
𝟘 + q = q
ω + q = ω

-- Multiplication of erasure annotations

_·_ : Op₂ Erasure
𝟘 · q = 𝟘
ω · q = q

-- Meet for erasure annotations coincides with addition

_∧_ : Op₂ Erasure
_∧_ = _+_

-- Natrec-star operators

_⊛_▷_ : Op₃ Erasure
p ⊛ q ▷ r = p + q

-- Division.

_/_ : Op₂ Erasure
p / ω = p
_ / 𝟘 = ω

-- Ordering relation for erasure
-- Reflexive closure of ω ≤ 𝟘

_≤_ : (p q : Erasure) → Set
p ≤ q = p ≡ p ∧ q

-- A decision procedure for equality.

_≟_ : Decidable (_≡_ {A = Erasure})
𝟘 ≟ 𝟘 = yes refl
𝟘 ≟ ω = no (λ ())
ω ≟ 𝟘 = no (λ ())
ω ≟ ω = yes refl

---------------------------------------
-- Properties of addition (and meet) --
---------------------------------------

-- Addition is commutative
-- p + q ≡ q + p

+-Commutative : Commutative _+_
+-Commutative 𝟘 𝟘 = refl
+-Commutative 𝟘 ω = refl
+-Commutative ω 𝟘 = refl
+-Commutative ω ω = refl

-- Addition is associative
-- p + (q + r) ≡ (p + q) + r

+-Associative : Associative _+_
+-Associative 𝟘 q r = refl
+-Associative ω q r = refl

-- Addition is idempotent

+-Idempotent : Idempotent _+_
+-Idempotent 𝟘 = refl
+-Idempotent ω = refl

-- 𝟘 is a left identity of addition
-- 𝟘 + p ≡ p

+-LeftIdentity : LeftIdentity 𝟘 _+_
+-LeftIdentity p = refl

-- 𝟘 is a right identity of addition
-- p + 𝟘 ≡ p

+-RightIdentity : RightIdentity 𝟘 _+_
+-RightIdentity 𝟘 = refl
+-RightIdentity ω = refl

-- 𝟘 is an identity of addition
-- 𝟘 + p ≡ p ≡ p + 𝟘

+-Identity : Identity 𝟘 _+_
+-Identity = +-LeftIdentity , +-RightIdentity

-- Addition is decreasing for the left argument.

+-decreasingˡ : (p q : Erasure) → (p + q) ≤ p
+-decreasingˡ 𝟘 𝟘 = refl
+-decreasingˡ 𝟘 ω = refl
+-decreasingˡ ω 𝟘 = refl
+-decreasingˡ ω ω = refl

opaque

  -- The function p +_ is decreasing.

  +-decreasingʳ : (p : Erasure) → p + q ≤ q
  +-decreasingʳ {q = 𝟘} 𝟘 = refl
  +-decreasingʳ {q = 𝟘} ω = refl
  +-decreasingʳ {q = ω} 𝟘 = refl
  +-decreasingʳ {q = ω} ω = refl

----------------------------------
-- Properties of multiplication --
----------------------------------

-- Multiplication is associative
-- p · (q · r) ≡ (p · q) · r

·-Associative : Associative _·_
·-Associative 𝟘 q r = refl
·-Associative ω q r = refl

-- 𝟘 is a left zero for multiplication
-- 𝟘 · p ≡ 𝟘

·-LeftZero : LeftZero 𝟘 _·_
·-LeftZero p = refl

-- 𝟘 is a right zero for multiplication
-- p · 𝟘 ≡ 𝟘

·-RightZero : RightZero 𝟘 _·_
·-RightZero 𝟘 = refl
·-RightZero ω = refl

-- 𝟘 is a zero for multiplication
-- 𝟘 · p ≡ 𝟘 ≡ p · 𝟘

·-zero : Zero 𝟘 _·_
·-zero = ·-LeftZero , ·-RightZero

-- ω is a left identity for multiplication
-- ω · p ≡ p

·-LeftIdentity : LeftIdentity ω _·_
·-LeftIdentity p = refl

-- ω is a right identity for multiplication
-- p · ω ≡ p

·-RightIdentity : RightIdentity ω _·_
·-RightIdentity 𝟘 = refl
·-RightIdentity ω = refl

-- ω is an identity for multiplication
-- ω · p ≡ p ≡ p · ω

·-Identity : Identity ω _·_
·-Identity = ·-LeftIdentity , ·-RightIdentity

----------------------
-- Properties of ⊛  --
----------------------

-- p ⊛ᵣ q is a solution to the inequality x ≤ q + rx
-- p ⊛ᵣ q ≤ q + r · (p ⊛ᵣ q)

⊛-ineq₁ : (p q r : Erasure) → p ⊛ q ▷ r ≤ q + r · p ⊛ q ▷ r
⊛-ineq₁ 𝟘 𝟘 𝟘 = refl
⊛-ineq₁ 𝟘 𝟘 ω = refl
⊛-ineq₁ 𝟘 ω r = refl
⊛-ineq₁ ω q r = refl

-- p ⊛ᵣ q is a solution to the the inequality x ≤ p
-- p ⊛ᵣ q ≤ p

⊛-ineq₂ : (p q r : Erasure) → p ⊛ q ▷ r ≤ p
⊛-ineq₂ 𝟘 𝟘 r = refl
⊛-ineq₂ 𝟘 ω r = refl
⊛-ineq₂ ω q r = refl

-- Addition is sub-interchangeable with ⊛ᵣ
-- (p ⊛ᵣ q) + (p′ ⊛ᵣ q′) ≤ (p + p′) ⊛ᵣ (q + q′)

+-sub-interchangeable-⊛ : (r : Erasure) → _+_ SubInterchangeable (_⊛_▷ r) by _≤_
+-sub-interchangeable-⊛ r 𝟘 𝟘 𝟘 𝟘 = refl
+-sub-interchangeable-⊛ r 𝟘 𝟘 𝟘 ω = refl
+-sub-interchangeable-⊛ r 𝟘 𝟘 ω q′ = refl
+-sub-interchangeable-⊛ r 𝟘 ω p′ q′ = refl
+-sub-interchangeable-⊛ r ω q p′ q′ = refl

-- Multiplation right sub-distributes over ⊛ᵣ
-- (p ⊛ᵣ p′) · q ≤ (p · q) ⊛ᵣ (p′ · q)

·-sub-distribʳ-⊛ : (r : Erasure) → _·_ SubDistributesOverʳ (_⊛_▷ r) by _≤_
·-sub-distribʳ-⊛ r q 𝟘 p′ = sym (+-Idempotent (p′ · q))
·-sub-distribʳ-⊛ r 𝟘 ω 𝟘 = refl
·-sub-distribʳ-⊛ r 𝟘 ω ω = refl
·-sub-distribʳ-⊛ r ω ω p′ = refl

-- ⊛ᵣ left sub-distributes over meet
-- p ⊛ᵣ (q ∧ q′) ≤ (p ⊛ᵣ q) ∧ (p ⊛ᵣ q′)

⊛-sub-distribˡ-∧ : (r : Erasure) → (_⊛_▷ r) SubDistributesOverˡ _∧_ by _≤_
⊛-sub-distribˡ-∧ r 𝟘 q q′ = sym (+-Idempotent (q + q′))
⊛-sub-distribˡ-∧ r ω q q′ = refl

-- ⊛ᵣ left sub-distributes over meet
-- (p ∧ p′) ⊛ᵣ q ≤ (p ⊛ᵣ q) ∧ (p′ ⊛ᵣ q)

⊛-sub-distribʳ-∧ : (r : Erasure) → (_⊛_▷ r) SubDistributesOverʳ _∧_ by _≤_
⊛-sub-distribʳ-∧ r q ω p′ = refl
⊛-sub-distribʳ-∧ r q 𝟘 ω = refl
⊛-sub-distribʳ-∧ r 𝟘 𝟘 𝟘 = refl
⊛-sub-distribʳ-∧ r ω 𝟘 𝟘 = refl

--------------------------------------------------------------------
-- Distributive properties of addition, multiplication (and meet) --
--------------------------------------------------------------------

-- Multiplication is left distributive over addition
-- p · (q + r) ≡ (p · q) + (p · r)

·-distribˡ-+ : _·_ DistributesOverˡ _+_
·-distribˡ-+ 𝟘 q r = refl
·-distribˡ-+ ω q r = refl

-- Multiplication is right distributive over addition
-- (q + r) · p ≡ (q · p) + (r · p)

·-distribʳ-+ : _·_ DistributesOverʳ _+_
·-distribʳ-+ p 𝟘 r = refl
·-distribʳ-+ 𝟘 ω 𝟘 = refl
·-distribʳ-+ 𝟘 ω ω = refl
·-distribʳ-+ ω ω r = refl

-- Multiplication is distributive over addition
-- p · (q + r) ≡ (p · q) + (p · r) and (q + r) · p ≡ (q · p) + (r · p)

·-distrib-+ : _·_ DistributesOver _+_
·-distrib-+ = ·-distribˡ-+ , ·-distribʳ-+

-- Addition is left distributive over addition
-- p + (q + r) ≡ (p + q) + (p + r)

+-distribˡ-+ : _+_ DistributesOverˡ _+_
+-distribˡ-+ 𝟘 q r = refl
+-distribˡ-+ ω q r = refl

-- Addition is right distributive over addition
-- (q + r) + p ≡ (q + p) + (r + p)

+-distribʳ-+ : _+_ DistributesOverʳ _+_
+-distribʳ-+ p ω r = refl
+-distribʳ-+ 𝟘 𝟘 r = refl
+-distribʳ-+ ω 𝟘 𝟘 = refl
+-distribʳ-+ ω 𝟘 ω = refl

-- Addition is distributive over addition
-- p + (q + r) ≡ (p + q) + (p + r) and (q + r) + p ≡ (q + p) + (r + p)

+-distrib-+ : _+_ DistributesOver _+_
+-distrib-+ = +-distribˡ-+ , +-distribʳ-+

-----------------------------------------------------
-- Addition (and meet) form the following algebras --
-----------------------------------------------------

-- Addition forms a magma

+-Magma : IsMagma _+_
+-Magma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _+_
  }

-- Addition forms a semigroup

+-Semigroup : IsSemigroup _+_
+-Semigroup = record
  { isMagma = +-Magma
  ; assoc   = +-Associative
  }

-- Addition forms a monoid for 𝟘 as identity

+-Monoid : IsMonoid _+_ 𝟘
+-Monoid = record
  { isSemigroup = +-Semigroup
  ; identity    = +-Identity
  }

-- Addition forms a commutative monoid with 𝟘 as identity

+-CommutativeMonoid : IsCommutativeMonoid _+_ 𝟘
+-CommutativeMonoid = record
  { isMonoid = +-Monoid
  ; comm     = +-Commutative
  }

-- Addition forms a band

+-Band : IsBand _+_
+-Band = record
  { isSemigroup = +-Semigroup
  ; idem        = +-Idempotent
  }

-- Addition forms a semilattice

+-Semilattice : IsMeetSemilattice _+_
+-Semilattice = record
  { isBand = +-Band
  ; comm   = +-Commutative
  }

-------------------------------------------------
-- Multiplication forms the following algebras --
-------------------------------------------------

-- Multiplication forms a magma

·-Magma : IsMagma _·_
·-Magma = record
  { isEquivalence = isEquivalence
  ; ∙-cong        = cong₂ _·_
  }

-- Multiplication forms a semigroup

·-Semigroup : IsSemigroup _·_
·-Semigroup = record
  { isMagma = ·-Magma
  ; assoc   = ·-Associative
  }

-- Multiplication forms a monoid with ω as identity

·-Monoid : IsMonoid _·_ ω
·-Monoid = record
  { isSemigroup = ·-Semigroup
  ; identity    = ·-Identity
  }

-------------------------------------------------
-- Addition and Multiplication form a semiring --
-------------------------------------------------

+-·-SemiringWithoutAnnihilatingZero : IsSemiringWithoutAnnihilatingZero _+_ _·_ 𝟘 ω
+-·-SemiringWithoutAnnihilatingZero = record
  { +-isCommutativeMonoid = +-CommutativeMonoid
  ; *-cong = cong₂ _·_
  ; *-assoc = ·-Associative
  ; *-identity = ·-Identity
  ; distrib = ·-distrib-+
  }

+-·-Semiring : IsSemiring _+_ _·_ 𝟘 ω
+-·-Semiring = record
  { isSemiringWithoutAnnihilatingZero = +-·-SemiringWithoutAnnihilatingZero
  ; zero = ·-zero
  }
