/-
Coset representatives for a finite-index subgroup, and the elementary identity which expresses a
product of group elements in terms of the "defect" `X_c(σ) = x_c σ x_{cσ}⁻¹ ∈ S` of a coset
representative.

This is the group-theoretic input of the cochain-level transfer (corestriction) identity
`res ≫ cor = [Γ : S] • 𝟙` with coefficients in an arbitrary `Rep k Γ`; the coefficient-level
transfer cochains are defined in `Submission/Work/GCTransfer/Transfer.lean`.
-/
import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory Representation Rep

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u

namespace NK.GCTransfer

section Coset

variable {Γ : Type u} [Group Γ] (S : Subgroup Γ)

/-- A representative of the left coset `S * γ` (chosen using `Quotient.out`). -/
noncomputable def sRep (γ : Γ) : Γ :=
  Quotient.out (Quotient.mk'' γ : Quotient (QuotientGroup.rightRel S))

lemma sRep_eq_of_rel {a b : Γ} (h : QuotientGroup.rightRel S a b) : sRep S a = sRep S b := by
  have h2 : (Quotient.mk'' a : Quotient (QuotientGroup.rightRel S)) = Quotient.mk'' b :=
    Quotient.sound h
  simp [sRep, h2]

lemma sRep_idem (γ : Γ) : sRep S (sRep S γ) = sRep S γ :=
  congrArg Quotient.out (Quotient.out_eq (Quotient.mk'' γ : Quotient (QuotientGroup.rightRel S)))

lemma sRep_mul_left (h : S) (γ : Γ) : sRep S ((h : Γ) * γ) = sRep S γ := by
  apply sRep_eq_of_rel
  rw [QuotientGroup.rightRel_apply]
  have hh : γ * ((h : Γ) * γ)⁻¹ = (h : Γ)⁻¹ := by group
  rw [hh]
  exact S.inv_mem h.2

lemma sRep_mul_right (x γ : Γ) : sRep S (sRep S x * γ) = sRep S (x * γ) := by
  apply sRep_eq_of_rel
  rw [QuotientGroup.rightRel_apply]
  have h := Quotient.out_eq (Quotient.mk'' x : Quotient (QuotientGroup.rightRel S))
  have h2 : QuotientGroup.rightRel S (sRep S x) x := Quotient.exact h
  rw [QuotientGroup.rightRel_apply] at h2
  have hh : x * γ * (sRep S x * γ)⁻¹ = x * (sRep S x)⁻¹ := by group
  rw [hh]
  exact h2

lemma sRep_mul_assoc_rep (x σ τ : Γ) :
    sRep S ((x * σ) * τ) = sRep S (x * (σ * τ)) := by
  rw [mul_assoc]

/-- The "defect" of the coset representative: `t γ (rep (tγ))⁻¹ ∈ S`. -/
noncomputable def sX (t γ : Γ) : Γ := t * γ * (sRep S (t * γ))⁻¹

lemma sX_mem (t γ : Γ) : sX S t γ ∈ S := by
  have h := Quotient.out_eq (Quotient.mk'' (t * γ) : Quotient (QuotientGroup.rightRel S))
  have h2 : QuotientGroup.rightRel S (sRep S (t * γ)) (t * γ) := Quotient.exact h
  rw [QuotientGroup.rightRel_apply] at h2
  simpa [sX] using h2

/-- `sX S t γ` as an element of `S`. -/
noncomputable def sXS (t γ : Γ) : S := ⟨sX S t γ, sX_mem S t γ⟩

@[simp] lemma sXS_coe (t γ : Γ) : (sXS S t γ : Γ) = sX S t γ := rfl

lemma sX_mul_rep (t γ : Γ) : sX S t γ * sRep S (t * γ) = t * γ := by
  simp [sX, mul_assoc]

lemma sX_mul (a σ τ : Γ) : sX S a σ * sX S (sRep S (a * σ)) τ = sX S a (σ * τ) := by
  have h1 : sRep S (sRep S (a * σ) * τ) = sRep S (a * (σ * τ)) := by
    rw [sRep_mul_right]
    congr 1
    group
  simp only [sX]
  rw [h1]
  group

lemma sXS_mul (a σ τ : Γ) :
    sXS S a σ * sXS S (sRep S (a * σ)) τ = sXS S a (σ * τ) := by
  apply Subtype.ext
  simpa using sX_mul S a σ τ

end Coset

section Shift

variable {Γ : Type u} [Group Γ] (S : Subgroup Γ)

/-- The "shift by `σ`" of the coset space: right multiplication by `σ` on the left cosets `S γ`. -/
noncomputable def csShift (σ : Γ) :
    Quotient (QuotientGroup.rightRel S) → Quotient (QuotientGroup.rightRel S) :=
  fun c => Quotient.mk'' (Quotient.out c * σ)

lemma cs_mk_mul_right {a b : Γ}
    (h : (Quotient.mk'' a : Quotient (QuotientGroup.rightRel S)) = Quotient.mk'' b) (γ : Γ) :
    (Quotient.mk'' (a * γ) : Quotient (QuotientGroup.rightRel S)) = Quotient.mk'' (b * γ) := by
  rw [Quotient.eq'']
  rw [QuotientGroup.rightRel_apply]
  have h' : QuotientGroup.rightRel S a b := Quotient.exact h
  rw [QuotientGroup.rightRel_apply] at h'
  have hh : (b * γ) * (a * γ)⁻¹ = b * a⁻¹ := by group
  rw [hh]
  exact h'

lemma csShift_shift (σ : Γ) (c : Quotient (QuotientGroup.rightRel S)) :
    csShift S σ⁻¹ (csShift S σ c) = c := by
  simp only [csShift]
  rw [cs_mk_mul_right S (Quotient.out_eq (Quotient.mk'' (Quotient.out c * σ))) σ⁻¹]
  rw [show (Quotient.out c * σ) * σ⁻¹ = Quotient.out c from by group]
  exact Quotient.out_eq c

/-- The permutation of the coset space induced by right multiplication by `σ`. -/
noncomputable def csShiftEquiv (σ : Γ) :
    Quotient (QuotientGroup.rightRel S) ≃ Quotient (QuotientGroup.rightRel S) where
  toFun := csShift S σ
  invFun := csShift S σ⁻¹
  left_inv c := csShift_shift S σ c
  right_inv c := by simpa using csShift_shift S σ⁻¹ c

variable [Fintype Γ]

noncomputable instance (priority := 10000) csQuotientFintype :
    Fintype (Quotient (QuotientGroup.rightRel S)) := by
  classical
  exact Fintype.ofSurjective (fun γ : Γ => (Quotient.mk'' γ : Quotient (QuotientGroup.rightRel S)))
    (fun q => Quotient.inductionOn q fun γ => ⟨γ, rfl⟩)

lemma csSum_shift (σ : Γ) {M : Type u} [AddCommMonoid M]
    (F : Quotient (QuotientGroup.rightRel S) → M) :
    (∑ c, F (csShift S σ c)) = ∑ c, F c :=
  Equiv.sum_comp (csShiftEquiv S σ) F

lemma cs_card_eq_index : Fintype.card (Quotient (QuotientGroup.rightRel S)) = Subgroup.index S := by
  rw [Fintype.card_eq_nat_card,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel S),
    ← Subgroup.index_eq_card]

/-- The representative of a *shifted* coset, in the `sRep` notation. -/
lemma sRep_shift (c : Quotient (QuotientGroup.rightRel S)) (σ : Γ) :
    Quotient.out (csShift S σ c) = sRep S (Quotient.out c * σ) := rfl

end Shift

end NK.GCTransfer
