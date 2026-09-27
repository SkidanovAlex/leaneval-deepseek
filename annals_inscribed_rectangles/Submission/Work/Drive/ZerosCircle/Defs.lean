import Mathlib

/-!
# The circle lemma: basic definitions

Material for `Work.Drive.zeros_finite_on_unitCircle` (zeros of a `C¹` function `h` on the unit
circle of `EuclideanSpace ℝ (Fin 2)` are finite when the gradient of `h` is nowhere parallel to the
radial direction at those zeros).

This file contains

* `Work.Drive.zcTang`, the tangent vector to the unit circle at `z` (the rotation of `z` by `π/2`)
  and its elementary properties: it has the same norm as `z` and is orthogonal to `z`;
* `Work.Drive.zc_expand`: for an orthonormal pair `(z, v)` in the two-dimensional Euclidean space
  `EuclideanSpace ℝ (Fin 2)` and every `w`, `w = ⟪z, w⟫ • z + ⟪v, w⟫ • v`;
* `Work.Drive.zcArcPt`, the arc parametrisation `s ↦ cos s • z + sin s • v` of the unit circle
  through `z`, together with `‖zcArcPt z v s‖ = 1` and `zcArcPt z v 0 = z`.
-/

namespace Work.Drive

open scoped InnerProductSpace

noncomputable section

/-- The tangent vector to the unit circle at `z`: `z` rotated by `π / 2`,
i.e. `(-z₂, z₁)` in coordinates. -/
def zcTang (z : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then -(z 1) else z 0)

lemma zcTang_apply (z : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) :
    zcTang z i = if i = 0 then -(z 1) else z 0 := by
  simp [zcTang]

lemma zcTang_apply_zero (z : EuclideanSpace ℝ (Fin 2)) : zcTang z 0 = -(z 1) := by
  simp [zcTang]

lemma zcTang_apply_one (z : EuclideanSpace ℝ (Fin 2)) : zcTang z 1 = z 0 := by
  simp [zcTang]

/-- The tangent vector has the same norm as `z`. -/
theorem zcTang_norm (z : EuclideanSpace ℝ (Fin 2)) : ‖zcTang z‖ = ‖z‖ := by
  have h1 : ‖zcTang z‖ ^ 2 = (zcTang z 0) ^ 2 + (zcTang z 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have h2 : ‖z‖ ^ 2 = (z 0) ^ 2 + (z 1) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  have h3 : (zcTang z 0) ^ 2 + (zcTang z 1) ^ 2 = (z 0) ^ 2 + (z 1) ^ 2 := by
    rw [zcTang_apply_zero, zcTang_apply_one]
    ring
  nlinarith [norm_nonneg (zcTang z), norm_nonneg z]

/-- The tangent vector is orthogonal to `z`. -/
theorem zcTang_inner (z : EuclideanSpace ℝ (Fin 2)) : ⟪zcTang z, z⟫_ℝ = 0 := by
  have h : (⟪zcTang z, z⟫_ℝ : ℝ) = zcTang z 0 * z 0 + zcTang z 1 * z 1 := by
    simp [PiLp.inner_apply, Fin.sum_univ_two]
    ring
  rw [h, zcTang_apply_zero, zcTang_apply_one]
  ring

/-- `zcTang z` does not vanish when `z` lies on the unit circle. -/
theorem zcTang_ne_zero {z : EuclideanSpace ℝ (Fin 2)} (hz : ‖z‖ = 1) : zcTang z ≠ 0 := by
  intro h
  have := zcTang_norm z
  rw [h, norm_zero, hz] at this
  exact one_ne_zero this.symm

/-- **Orthonormal expansion in the plane.**  If `z` and `v` are unit vectors of
`EuclideanSpace ℝ (Fin 2)` which are orthogonal to each other, they form an orthonormal basis, and
every vector is expanded in it. -/
theorem zc_expand (z v w : EuclideanSpace ℝ (Fin 2)) (hz : ‖z‖ = 1) (hv : ‖v‖ = 1)
    (hzv : ⟪z, v⟫_ℝ = 0) : w = ⟪z, w⟫_ℝ • z + ⟪v, w⟫_ℝ • v := by
  have hon : Orthonormal ℝ (fun i : Fin 2 => if i = 0 then z else v) := by
    rw [orthonormal_iff_ite]
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hz, hv, hzv, real_inner_comm]
  have hli := hon.linearIndependent
  have hcard : Fintype.card (Fin 2) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    simp
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range (fun i : Fin 2 => if i = 0 then z else v)) :=
    (hli.span_eq_top_of_card_eq_finrank hcard).ge
  have hsum := (OrthonormalBasis.mk hon hsp).sum_repr' w
  rw [OrthonormalBasis.coe_mk] at hsum
  rw [Fin.sum_univ_two] at hsum
  simpa using hsum.symm

/-- The point of the unit circle obtained from `z` by rotating towards `v` through the angle `s`,
namely `cos s • z + sin s • v`. -/
def zcArcPt (z v : EuclideanSpace ℝ (Fin 2)) (s : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  Real.cos s • z + Real.sin s • v

@[simp]
theorem zcArcPt_zero (z v : EuclideanSpace ℝ (Fin 2)) : zcArcPt z v 0 = z := by
  simp [zcArcPt]

/-- The arc `s ↦ cos s • z + sin s • v` runs inside the unit circle. -/
theorem zcArcPt_norm (z v : EuclideanSpace ℝ (Fin 2)) (s : ℝ) (hz : ‖z‖ = 1) (hv : ‖v‖ = 1)
    (hzv : ⟪z, v⟫_ℝ = 0) : ‖zcArcPt z v s‖ = 1 := by
  have horth : ⟪Real.cos s • z, Real.sin s • v⟫_ℝ = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, hzv, mul_zero, mul_zero]
  have h2 : ‖Real.cos s • z + Real.sin s • v‖ ^ 2 =
      ‖Real.cos s • z‖ ^ 2 + ‖Real.sin s • v‖ ^ 2 := by
    simpa [pow_two] using (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero
      (Real.cos s • z) (Real.sin s • v)).mpr horth
  have h1 : ‖Real.cos s • z + Real.sin s • v‖ ^ 2 = 1 := by
    rw [h2, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, hz, hv, mul_one, mul_one,
      sq_abs, sq_abs]
    linarith [Real.sin_sq_add_cos_sq s]
  have h3 : ‖zcArcPt z v s‖ ^ 2 = 1 := by simpa [zcArcPt] using h1
  nlinarith [norm_nonneg (zcArcPt z v s)]

end

end Work.Drive
