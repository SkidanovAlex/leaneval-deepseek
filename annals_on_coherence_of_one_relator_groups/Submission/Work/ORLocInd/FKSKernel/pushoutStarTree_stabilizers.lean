import Mathlib
import Submission.Work.ORLocInd.FKSKernel.PushoutStarTree

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.FKSKernel

open Quiver

variable {ι : Type u} {H : Type u} {G : ι → Type u} [Group H] [∀ i, Group (G i)]

/-- The action on a centre, in `Quotient.mk''`-form. -/
private theorem pst_smul_ctr_mk (φ : ∀ i, H →* G i) (x g : Psh φ) :
    x • ctr φ (Quotient.mk'' g) = ctr φ (Quotient.mk'' (x * g)) := by
  rw [show x • ctr φ (Quotient.mk'' g) = ctr φ (smulCtr φ x (Quotient.mk'' g)) from rfl,
    smulCtr_mk]

/-- The action on a leaf, in `Quotient.mk''`-form. -/
private theorem pst_smul_lf_mk (φ : ∀ i, H →* G i) (i : ι) (x g : Psh φ) :
    x • lf φ i (Quotient.mk'' g) = lf φ i (Quotient.mk'' (x * g)) := by
  rw [show x • lf φ i (Quotient.mk'' g) = smulVtx φ x (lf φ i (Quotient.mk'' g)) from rfl,
    smulVtx_lf]
  simp only [lf]
  rw [smulCtr_mk]

/-- Two leaves with labels in the same `i`-th vertex group coincide exactly when the corresponding
cosets of the `i`-th subgroup coincide. -/
private theorem pst_lf_mk_eq (φ : ∀ i, H →* G i) (i : ι) (a b : Psh φ) :
    lf φ i (Quotient.mk'' a) = lf φ i (Quotient.mk'' b) ↔
      (Quotient.mk'' a : Psh φ ⧸ ofSub φ i) = Quotient.mk'' b := by
  simp only [lf, cosetMap_mk]
  constructor
  · intro h
    exact eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj h)).2
  · intro h
    rw [h]

/-- The stabiliser of a centre is the conjugate of the base subgroup. -/
private theorem pst_stabilizer_ctr (φ : ∀ i, H →* G i) (g : Psh φ) :
    MulAction.stabilizer (Psh φ) (ctr φ (Quotient.mk'' g)) =
      (baseSub φ).map (MulEquiv.toMonoidHom (MulAut.conj g)) := by
  ext x
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_map]
  constructor
  · intro hx
    have h1 : ctr φ (Quotient.mk'' (x * g)) = ctr φ (Quotient.mk'' g) := by
      rw [← pst_smul_ctr_mk (φ := φ) x g]; exact hx
    have h2 : (Quotient.mk'' (x * g) : Psh φ ⧸ baseSub φ) = Quotient.mk'' g :=
      ctr_inj (φ := φ) h1
    rw [QuotientGroup.eq] at h2
    obtain ⟨k, hk⟩ := h2
    refine ⟨(Monoid.PushoutI.base φ k)⁻¹, ⟨k⁻¹, (Monoid.PushoutI.base φ).map_inv k⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    show g * (Monoid.PushoutI.base φ k)⁻¹ * g⁻¹ = x
    rw [hk]
    group
  · rintro ⟨h, hh, hxh⟩
    rw [MulEquiv.coe_toMonoidHom] at hxh
    have hx : x = MulAut.conj g h := hxh.symm
    rw [hx, MulAut.conj_apply]
    show ctr φ (smulCtr φ (g * h * g⁻¹) (Quotient.mk'' g)) = ctr φ (Quotient.mk'' g)
    rw [smulCtr_mk]
    apply congrArg (ctr φ)
    change (Quotient.mk'' ((g * h * g⁻¹) * g) : Psh φ ⧸ baseSub φ) = Quotient.mk'' g
    rw [QuotientGroup.eq]
    have key : ((g * h * g⁻¹) * g)⁻¹ * g = h⁻¹ := by group
    rw [key]
    exact (baseSub φ).inv_mem hh

/-- The stabiliser of a leaf is the conjugate of the corresponding vertex subgroup. -/
private theorem pst_stabilizer_lf (φ : ∀ i, H →* G i) (i : ι) (g : Psh φ) :
    MulAction.stabilizer (Psh φ) (lf φ i (Quotient.mk'' g)) =
      (ofSub φ i).map (MulEquiv.toMonoidHom (MulAut.conj g)) := by
  ext x
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_map]
  constructor
  · intro hx
    have h1 : lf φ i (Quotient.mk'' (x * g)) = lf φ i (Quotient.mk'' g) := by
      rw [← pst_smul_lf_mk (φ := φ) i x g]; exact hx
    have h2 : (Quotient.mk'' (x * g) : Psh φ ⧸ ofSub φ i) = Quotient.mk'' g :=
      (pst_lf_mk_eq φ i (x * g) g).mp h1
    rw [QuotientGroup.eq] at h2
    obtain ⟨k, hk⟩ := h2
    refine ⟨(Monoid.PushoutI.of (φ := φ) i k)⁻¹,
      ⟨k⁻¹, (Monoid.PushoutI.of (φ := φ) i).map_inv k⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    show g * (Monoid.PushoutI.of (φ := φ) i k)⁻¹ * g⁻¹ = x
    rw [hk]
    group
  · rintro ⟨h, hh, hxh⟩
    rw [MulEquiv.coe_toMonoidHom] at hxh
    have hx : x = MulAut.conj g h := hxh.symm
    rw [hx, MulAut.conj_apply]
    show lf φ i (smulCtr φ (g * h * g⁻¹) (Quotient.mk'' g)) = lf φ i (Quotient.mk'' g)
    rw [smulCtr_mk]
    rw [pst_lf_mk_eq]
    rw [QuotientGroup.eq]
    have key : ((g * h * g⁻¹) * g)⁻¹ * g = h⁻¹ := by group
    rw [key]
    exact (ofSub φ i).inv_mem hh

theorem pushoutStarTree_stabilizers {ι : Type u} {H : Type u} {G : ι → Type u} [Group H]
    [∀ i, Group (G i)] (φ : ∀ i, H →* G i) :
    (∀ g : Psh φ, MulAction.stabilizer (Psh φ) (ctr φ (Quotient.mk'' g)) =
      (baseSub φ).map (MulEquiv.toMonoidHom (MulAut.conj g))) ∧
    (∀ (i : ι) (g : Psh φ), MulAction.stabilizer (Psh φ) (lf φ i (Quotient.mk'' g)) =
      (ofSub φ i).map (MulEquiv.toMonoidHom (MulAut.conj g))) :=
  ⟨fun g => pst_stabilizer_ctr φ g, fun i g => pst_stabilizer_lf φ i g⟩

end Work.ORLocInd.FKSKernel
