import Mathlib
import Submission.Work.ThomBordism.Grassmann.RotationDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

/-!
# The rotation carrying one unit vector to another: the geometric properties

For the formula of `Work.ThomBordism.Grassmann.rotMap` (`RotationDefs.lean`) this module proves,
for unit vectors `u`, `e` with `1 + ⟪u,e⟫ ≠ 0`:

* `rotMap u e u = e`;
* `rotMap u e` is an isometry (`⟪rotMap u e x, rotMap u e y⟫ = ⟪x,y⟫`);
* `rotMap e u` is a two-sided inverse of `rotMap u e`;
* `(u,x) ↦ rotMap u e x` is continuous on the region `1 + ⟪u,e⟫ ≠ 0`.

These are the "parallel transport" properties of the incidence fibration of the sphere bundle of the
tautological bundle over the oriented Grassmannian.
-/

open scoped RealInnerProductSpace

namespace Work.ThomBordism.Grassmann

noncomputable section

variable {n : ℕ}

theorem rotMap_inner_self {u e x : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = 1) (he : ‖e‖ = 1)
    (h : 1 + inner ℝ u e ≠ 0) :
    inner ℝ (rotMap u e x) (rotMap u e x) = inner ℝ x x := by
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  simp only [rotMap]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, starRingEnd_apply, star_trivial]
  rw [real_inner_comm u x, real_inner_comm e x, huu, hee]
  field_simp
  rw [real_inner_comm e u]
  ring

/-- **`rotMap u e` sends `u` to `e`.** -/
theorem rotMap_self {u e : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = 1) (he : ‖e‖ = 1) :
    rotMap u e u = e := by
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hnum : inner ℝ u e - inner ℝ u u * inner ℝ u e = 0 := by rw [huu]; ring
  simp only [rotMap, hnum, zero_div, zero_smul, sub_zero]
  rw [huu, one_smul]
  abel_nf

/-- **`rotMap u e` is an isometry.** -/
theorem rotMap_inner {u e x y : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = 1) (he : ‖e‖ = 1)
    (h : 1 + inner ℝ u e ≠ 0) :
    inner ℝ (rotMap u e x) (rotMap u e y) = inner ℝ x y := by
  have hlin : rotMap u e (x + y) = rotMap u e x + rotMap u e y := by
    simpa using rotMap_linear u e 1 1 x y
  have h1 : inner ℝ (rotMap u e (x+y)) (rotMap u e (x+y)) = inner ℝ (x+y) (x+y) :=
    rotMap_inner_self hu he h
  rw [hlin] at h1
  have h2 : inner ℝ (rotMap u e x) (rotMap u e x) = inner ℝ x x := rotMap_inner_self hu he h
  have h3 : inner ℝ (rotMap u e y) (rotMap u e y) = inner ℝ y y := rotMap_inner_self hu he h
  have hpol : ∀ a b : EuclideanSpace ℝ (Fin n),
      inner ℝ (a+b) (a+b) = inner ℝ a a + 2*inner ℝ a b + inner ℝ b b := by
    intro a b
    rw [inner_add_left, inner_add_right, inner_add_right, real_inner_comm b a]
    ring
  rw [hpol (rotMap u e x) (rotMap u e y), hpol x y, h2, h3] at h1
  linarith

/-- **`rotMap e u` is a two-sided inverse of `rotMap u e`.** -/
theorem rotMap_rotMap {u e x : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = 1) (he : ‖e‖ = 1)
    (h : 1 + inner ℝ u e ≠ 0) :
    rotMap e u (rotMap u e x) = x := by
  have hcu : inner ℝ e u = inner ℝ u e := by rw [real_inner_comm]
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hee : inner ℝ e e = 1 := by rw [real_inner_self_eq_norm_sq, he]; norm_num
  have hyval : rotMap u e x
      = x + (inner ℝ x u) • (e - u)
        - ((inner ℝ x e - inner ℝ x u * inner ℝ u e) / (1 + inner ℝ u e)) • (u + e) := by
    simp only [rotMap]
  have hye : inner ℝ (rotMap u e x) e = inner ℝ x u := by
    rw [hyval]
    simp only [inner_add_left, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, starRingEnd_apply, star_trivial, huu, hee]
    field_simp
    ring
  have hyu : inner ℝ (rotMap u e x) u
      = 2 * inner ℝ u e * inner ℝ x u - inner ℝ x e := by
    rw [hyval]
    simp only [inner_add_left, inner_sub_left, inner_sub_right, inner_smul_left,
      inner_smul_right, starRingEnd_apply, star_trivial, huu, hee]
    field_simp
    rw [hcu]
    ring
  rw [rotMap]
  rw [hcu, hye, hyu, hyval]
  module

/-- **`(u,x) ↦ rotMap u e x` is continuous where the denominator does not vanish.** -/
theorem continuous_rotMap {e : EuclideanSpace ℝ (Fin n)} :
    ContinuousOn (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => rotMap p.1 e p.2)
      {p | 1 + inner ℝ p.1 e ≠ 0} := by
  simp only [rotMap]
  have h12 : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => inner ℝ p.1 e)
      {p | 1 + inner ℝ p.1 e ≠ 0} :=
    (continuous_inner.comp (continuous_fst.prodMk continuous_const)).continuousOn
  have hden : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => 1 + inner ℝ p.1 e)
      {p | 1 + inner ℝ p.1 e ≠ 0} := continuousOn_const.add h12
  have hnum : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        inner ℝ p.2 e - inner ℝ p.2 p.1 * inner ℝ p.1 e) {p | 1 + inner ℝ p.1 e ≠ 0} :=
    (continuous_inner.comp (continuous_snd.prodMk continuous_const)).continuousOn.sub
      (((continuous_inner.comp (continuous_snd.prodMk continuous_fst)).continuousOn).mul h12)
  have hquot : ContinuousOn
      (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (inner ℝ p.2 e - inner ℝ p.2 p.1 * inner ℝ p.1 e) / (1 + inner ℝ p.1 e))
      {p | 1 + inner ℝ p.1 e ≠ 0} :=
    hnum.div hden (fun p hp => hp)
  refine ContinuousOn.sub
    (ContinuousOn.add continuousOn_snd ?_)
    (continuous_smul.comp_continuousOn (hquot.prodMk (continuousOn_fst.add continuousOn_const)))
  exact continuous_smul.comp_continuousOn
    (((continuous_inner.comp (continuous_snd.prodMk continuous_fst)).continuousOn).prodMk
      (continuousOn_const.sub continuousOn_fst))


/-- **`rotMap u e` scales along the rotation**: `rotMap u e (c • u) = c • e`. -/
theorem rotMap_smul_self {u e : EuclideanSpace ℝ (Fin n)} (hu : ‖u‖ = 1) (he : ‖e‖ = 1)
    (c : ℝ) : rotMap u e (c • u) = c • e := by
  simpa [rotMap_self hu he] using rotMap_linear u e c 0 u u

end

end Work.ThomBordism.Grassmann
