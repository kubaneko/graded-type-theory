------------------------------------------------------------------------
-- Escaping the logical relation
------------------------------------------------------------------------

open import Definition.Typed.EqualityRelation
open import Definition.Typed.Restrictions
open import Graded.Modality

module Definition.LogicalRelation.Properties.Escape
  {a} {M : Set a}
  {𝕄 : Modality M}
  (R : Type-restrictions 𝕄)
  {{eqrel : EqRelSet R}}
  where

open EqRelSet {{...}}
open Type-restrictions R

open import Definition.Untyped M hiding (K)
open import Definition.Untyped.Neutral M type-variant
open import Definition.Typed R
open import Definition.Typed.Properties R
open import Definition.LogicalRelation R
open import Definition.LogicalRelation.Properties.Reflexivity R
open import Definition.LogicalRelation.Properties.Whnf R

open import Tools.Empty
open import Tools.Function
open import Tools.Nat
open import Tools.Product
import Tools.PropositionalEquality as PE

private
  variable
    n : Nat
    Γ : Con Term n
    A B t u : Term n
    l : TypeLevel
    b : BinderMode
    s : Strength
    p q : M

-- Reducible types are well-formed.
escape : ∀ {l A} → Γ ⊩⟨ l ⟩ A → Γ ⊢ A
escape (Uᵣ′ l′ l< [ ⊢A , ⊢B , D ]) = ⊢A
escape (ℕᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (Emptyᵣ [ ⊢A , ⊢B , D ]) = ⊢A
escape (Unitᵣ (Unitₜ [ ⊢A , ⊢B , D ] _)) = ⊢A
escape (ne′ K [ ⊢A , ⊢B , D ] neK K≡K) = ⊢A
escape (Bᵣ′ _ _ _ [ ⊢A , _ , _ ] _ _ _ _ _ _ _) = ⊢A
escape (Idᵣ ⊩A) = ⊢A-red (_⊩ₗId_.⇒*Id ⊩A)
escape (emb ≤′-refl A) = escape A
escape (emb (≤′-step k) A) = escape (emb k A)

-- Reducible terms are well-formed.
escapeTerm : ∀ {l A t} → ([A] : Γ ⊩⟨ l ⟩ A)
              → Γ ⊩⟨ l ⟩ t ∷ A / [A]
              → Γ ⊢ t ∷ A
escapeTerm (Uᵣ′ l′ l< ⊢Γ) (Uₜ A [ ⊢t , ⊢u , d ] typeA A≡A [A]) =
  conv  ⊢t (sym ( subset* (red  ⊢Γ)))
escapeTerm (ℕᵣ D) (ℕₜ n [ ⊢t , ⊢u , d ] t≡t prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Emptyᵣ D) (Emptyₜ e [ ⊢t , ⊢u , d ] t≡t prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Unitᵣ (Unitₜ D _)) (Unitₜ e [ ⊢t , ⊢u , d ] _ prop) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (ne′ K D neK K≡K) (neₜ k [ ⊢t , ⊢u , d ] nf) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Bᵣ′ BΠ! _ _ D _ _ _ _ _ _ _) (Πₜ _ [ ⊢t , _ , _ ] _ _ _ _) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Bᵣ′ BΣ! _ _ D _ _ _ _ _ _ _) (Σₜ _ [ ⊢t , _ , _ ] _ _ _) =
  conv ⊢t (sym (subset* (red D)))
escapeTerm (Idᵣ ⊩A) (_ , t⇒*u , _) =
  conv (⊢t-redₜ t⇒*u) (sym (subset* (red (_⊩ₗId_.⇒*Id ⊩A))))
escapeTerm (emb ≤′-refl A) t = escapeTerm A t
escapeTerm (emb (≤′-step k) A) t = escapeTerm (emb k A) t

-- Reducible type equality is contained in the equality relation.
escapeEq :
  (⊩A : Γ ⊩⟨ l ⟩ A) →
  Γ ⊩⟨ l ⟩ A ≡ B / ⊩A →
  Γ ⊢ A ≅ B

-- Reducible term equality is contained in the equality relation.
escapeTermEq :
  (⊩A : Γ ⊩⟨ l ⟩ A) →
  Γ ⊩⟨ l ⟩ t ≡ u ∷ A / ⊩A →
  Γ ⊢ t ≅ u ∷ A

-- If there is a well-formed equality between two identity types,
-- then the corresponding reduced identity types are equal.
Id≅Id :
  {⊩A : Γ ⊩′⟨ l ⟩Id A}
  (A≡B : Γ ⊩⟨ l ⟩ A ≡ B / Idᵣ ⊩A) →
  let open _⊩ₗId_ ⊩A
      open _⊩ₗId_≡_/_ A≡B
  in
  Γ ⊢ Id Ty lhs rhs ≅ Id Ty′ lhs′ rhs′
Id≅Id {⊩A = ⊩A} A≡B =
  ≅-Id-cong
    (escapeEq ⊩Ty Ty≡Ty′)
    (escapeTermEq ⊩Ty lhs≡lhs′)
    (escapeTermEq ⊩Ty rhs≡rhs′)
  where
  open _⊩ₗId_ ⊩A
  open _⊩ₗId_≡_/_ A≡B

escapeEq (Uᵣ′ l′ l< [ ⊢A , ⊢B , D ]) [ ⊢A₁ , ⊢B₁ , D₁ ] =
  ≅-red D  D₁ Uₙ Uₙ ((≅-Urefl (wf ⊢A)))
escapeEq (ℕᵣ [ ⊢A , ⊢B , D ]) D′ = ≅-red D D′ ℕₙ ℕₙ (≅-ℕrefl (wf ⊢A))
escapeEq (Emptyᵣ [ ⊢A , ⊢B , D ]) D′ =
  ≅-red D D′ Emptyₙ Emptyₙ (≅-Emptyrefl (wf ⊢A))
escapeEq (Unitᵣ (Unitₜ [ ⊢A , ⊢B , D ] ok)) D′ =
  ≅-red D D′ Unitₙ Unitₙ (≅-Unitrefl (wf ⊢A) ok)
escapeEq (ne′ K D neK K≡K) (ne₌ M D′ neM K≡M) =
  ≅-red (red D) (red D′) (ne neK) (ne neM) K≡M
escapeEq (Bᵣ′ W _ _ D _ _ _ _ _ _ _) (B₌ _ _ D′ A≡B _ _) =
  ≅-red (red D) D′ ⟦ W ⟧ₙ ⟦ W ⟧ₙ A≡B
escapeEq (Idᵣ ⊩A) A≡B =
  ≅-red (red (_⊩ₗId_.⇒*Id ⊩A)) (red (_⊩ₗId_≡_/_.⇒*Id′ A≡B)) Idₙ Idₙ
    (Id≅Id A≡B)
escapeEq (emb ≤′-refl A) A≡B = escapeEq A A≡B
escapeEq (emb (≤′-step k) A) A≡B = escapeEq (emb k A) A≡B

escapeTermEq (Uᵣ′ l′ l< [ ⊢A , ⊢B , D ]) (Uₜ₌ A B d d′ typeA typeB A≡B [A] [B] [A≡B]) =
  ≅ₜ-red D (redₜ d) (redₜ d′) Uₙ (typeWhnf typeA) (typeWhnf typeB)  A≡B
escapeTermEq (ℕᵣ D) (ℕₜ₌ k k′ d d′ k≡k′ prop) =
  let natK , natK′ = split prop
  in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) ℕₙ
             (naturalWhnf natK) (naturalWhnf natK′) k≡k′
escapeTermEq (Emptyᵣ D) (Emptyₜ₌ k k′ d d′ k≡k′ prop) =
  let natK , natK′ = esplit prop
  in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Emptyₙ
             (ne natK) (ne natK′) k≡k′
escapeTermEq (Unitᵣ (Unitₜ D _)) (Unitₜ₌ˢ ⊢t ⊢u ok) =
  let t≅u = ≅ₜ-η-unit ⊢t ⊢u ok
      A≡Unit = subset* (red D)
  in  ≅-conv t≅u (sym A≡Unit)
escapeTermEq (Unitᵣ (Unitₜ D _)) (Unitₜ₌ʷ _ _ d d′ k≡k′ prop _) =
  let whK , whK′ = usplit prop
  in  ≅ₜ-red (red D) (redₜ d) (redₜ d′) Unitₙ
             whK whK′ k≡k′
escapeTermEq (ne′ K D neK K≡K)
                 (neₜ₌ k m d d′ (neNfₜ₌ neT neU t≡u)) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) (ne neK) (ne neT) (ne neU)
         (~-to-≅ₜ t≡u)
escapeTermEq
  (Bᵣ′ BΠ! _ _ D _ _ _ _ _ _ _) (Πₜ₌ _ _ d d′ funcF funcG f≡g _ _ _) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) ΠΣₙ
    (functionWhnf funcF) (functionWhnf funcG) f≡g
escapeTermEq
  (Bᵣ′ BΣ! _ _ D _ _ _ _ _ _ _) (Σₜ₌ _ _ d d′ pProd rProd p≅r _ _ _) =
  ≅ₜ-red (red D) (redₜ d) (redₜ d′) ΠΣₙ
    (productWhnf pProd) (productWhnf rProd) p≅r
escapeTermEq {Γ = Γ} (Idᵣ ⊩A) t≡u@(_ , _ , t⇒*t′ , u⇒*u′ , _) =
  case ⊩Id≡∷-view-inhabited ⊩A t≡u of λ where
    (ne t′-n u′-n t′~u′) →
      lemma (ne t′-n) (ne u′-n) (~-to-≅ₜ t′~u′)
    (rfl₌ lhs≡rhs) →
      lemma rflₙ rflₙ
        (                                   $⟨ ≅-Id-cong
                                                 (escapeEq ⊩Ty (reflEq ⊩Ty))
                                                 (escapeTermEq ⊩Ty (reflEqTerm ⊩Ty ⊩lhs))
                                                 (escapeTermEq ⊩Ty lhs≡rhs) ⟩
         Γ ⊢ Id Ty lhs lhs ≅ Id Ty lhs rhs  →⟨ ≅-eq ⟩
         Γ ⊢ Id Ty lhs lhs ≡ Id Ty lhs rhs  →⟨ ≅-conv (≅ₜ-rflrefl (escapeTerm ⊩Ty ⊩lhs)) ⟩
         (Γ ⊢ rfl ≅ rfl ∷ Id Ty lhs rhs)    □)
  where
  open _⊩ₗId_ ⊩A

  lemma = ≅ₜ-red (red ⇒*Id) (redₜ t⇒*t′) (redₜ u⇒*u′) Idₙ
escapeTermEq (emb ≤′-refl A) t≡u = escapeTermEq A t≡u
escapeTermEq (emb (≤′-step k) A) t≡u = escapeTermEq (emb k A) t≡u

-- If the type Unit (of some mode) is in the logical relation, then the
-- Unit type (of the same mode) is allowed.

⊩Unit→Unit-allowed :
  Γ ⊩⟨ l ⟩ Unit s → Unit-allowed s
⊩Unit→Unit-allowed {Γ = Γ} = λ where
  (Uᵣ′ l′ l< [ ⊢Unit , _ , D ]) →
                  $⟨ D , Uₙ ⟩
    Γ ⊢ Unit! ↘ (U l′)  →⟨ flip whrDet* (id ⊢Unit , Unitₙ) ⟩
    (U l′) PE.≡ Unit!   →⟨ (case_of λ ()) ⟩
    Unit-allowed _  □
  (ℕᵣ [ ⊢Unit , _ , D ]) →
                  $⟨ D , ℕₙ ⟩
    Γ ⊢ Unit! ↘ ℕ  →⟨ flip whrDet* (id ⊢Unit , Unitₙ) ⟩
    ℕ PE.≡ Unit!   →⟨ (case_of λ ()) ⟩
    Unit-allowed _  □
  (Emptyᵣ [ ⊢Unit , _ , D ]) →
                      $⟨ D , Emptyₙ ⟩
    Γ ⊢ Unit! ↘ Empty  →⟨ flip whrDet* (id ⊢Unit , Unitₙ) ⟩
    Empty PE.≡ Unit!   →⟨ (case_of λ ()) ⟩
    Unit-allowed _     □
  (Unitᵣ (Unitₜ [ _ , _ , D ] ok)) → case whnfRed* D Unitₙ of λ where
    PE.refl → ok
  (ne (ne A [ ⊢Unit , _ , D ] neA _)) →
                  $⟨ D , ne neA ⟩
    Γ ⊢ Unit! ↘ A  →⟨ whrDet* (id ⊢Unit , Unitₙ) ⟩
    Unit! PE.≡ A   →⟨ ⊥-elim ∘→ Unit≢ne neA ⟩
    Unit-allowed _  □
  (Bᵣ′ b A B [ ⊢Unit , _ , D ] _ _ _ _ _ _ _) →
                            $⟨ D , ⟦ b ⟧ₙ ⟩
    Γ ⊢ Unit! ↘ ⟦ b ⟧ A ▹ B  →⟨ whrDet* (id ⊢Unit , Unitₙ) ⟩
    Unit! PE.≡ ⟦ b ⟧ A ▹ B   →⟨ ⊥-elim ∘→ Unit≢B b ⟩
    Unit-allowed _           □
  (Idᵣ ⊩A) →
    let open _⊩ₗId_ ⊩A in
                              $⟨ red ⇒*Id , Idₙ ⟩
    Γ ⊢ Unit! ↘ Id Ty lhs rhs  →⟨ whrDet* (id (⊢A-red ⇒*Id) , Unitₙ) ⟩
    Unit! PE.≡ Id Ty lhs rhs   →⟨ (λ ()) ⟩
    Unit-allowed _             □
  (emb ≤′-refl [Unit]) → ⊩Unit→Unit-allowed [Unit]
  (emb (≤′-step k) [Unit]) →  ⊩Unit→Unit-allowed (emb k [Unit])

-- If the type ΠΣ⟨ b ⟩ p , q ▷ A ▹ B is in the logical relation, then
-- it is allowed.

⊩ΠΣ→ΠΣ-allowed :
  Γ ⊩⟨ l ⟩ ΠΣ⟨ b ⟩ p , q ▷ A ▹ B →
  ΠΣ-allowed b p q
⊩ΠΣ→ΠΣ-allowed {b = b} = λ where
  (Uᵣ′ l′ l< [ ⊢ΠAB , _ , D ]) →
     ⊥-elim ( U≢ΠΣ b ( (whrDet* (D , Uₙ) (id ⊢ΠAB , ΠΣₙ))))
  (ℕᵣ [ ⊢ΠAB , _ , D ]) →
    ⊥-elim (ℕ≢ΠΣ b (whrDet* (D , ℕₙ) (id ⊢ΠAB , ΠΣₙ)))
  (Emptyᵣ [ ⊢ΠAB , _ , D ]) →
    ⊥-elim (Empty≢ΠΣ b (whrDet* (D , Emptyₙ) (id ⊢ΠAB , ΠΣₙ)))
  (Unitᵣ (Unitₜ [ ⊢ΠAB , _ , D ] _)) →
    ⊥-elim (Unit≢ΠΣ b (whrDet* (D , Unitₙ) (id ⊢ΠAB , ΠΣₙ)))
  (ne (ne _ [ ⊢ΠAB , _ , D ] neK _)) →
    ⊥-elim (ΠΣ≢ne b neK (whrDet* (id ⊢ΠAB , ΠΣₙ) (D , ne neK)))
  (Bᵣ′ (BM BMΠ _ _) _ _ [ ⊢ΠAB , _ , D ] _ _ _ _ _ _ ok) →
    case whrDet* (id ⊢ΠAB , ΠΣₙ) (D , ΠΣₙ) of λ {
      PE.refl →
    ok }
  (Bᵣ′ (BM (BMΣ _) _ _) _ _ [ ⊢ΠAB , _ , D ] _ _ _ _ _ _ ok) →
    case whrDet* (id ⊢ΠAB , ΠΣₙ) (D , ΠΣₙ) of λ {
      PE.refl →
    ok }
  (Idᵣ ⊩A) →
    let open _⊩ₗId_ ⊩A in
    ⊥-elim (Id≢ΠΣ b (whrDet* (red ⇒*Id , Idₙ) (id (⊢A-red ⇒*Id) , ΠΣₙ)))
  (emb ≤′-refl [ΠΣ]) →  ⊩ΠΣ→ΠΣ-allowed [ΠΣ]
  (emb (≤′-step k) [ΠΣ]) →  ⊩ΠΣ→ΠΣ-allowed (emb k [ΠΣ])
