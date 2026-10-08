/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Auxiliary linear algebra for the centralizer of a semisimple element of `SL(2,F)`

For `x ∈ SL(2,F)` (`F` a field with `(2 : F) ≠ 0`) the *traceless part*
`W = Work.L2F.Torus.conjMat F x = 2 • x - tr(x) • 1` satisfies

* `tr W = 0` (`Work.L2F.Torus.conjMat_trace`),
* `W * W = disc F x • 1` (`Work.L2F.Torus.conjMat_mul_self`), where `disc F x = tr(x) ^ 2 - 4`,
* `W.det = -disc F x` (`conjMat_det` below, from `det (a • 1 + b • X) = a ^ 2 + ab·tr X + b²·det X`),
* `x = (2)⁻¹ • W + ((2)⁻¹ * tr x) • 1` (`Work.L2F.Torus.x_eq_smul_conjMat`),
* `W` commutes with `x` (`conjMat_comm`), and `a • 1 + b • W` commutes with `x` whenever `W` does.

The main results of this file are

* `exists_smul_one_add_of_commute`: a matrix `Y` with `Y.det = 1` commuting with a traceless `X`
  with `X.det ≠ 0` lies in the two-dimensional algebra `F·1 + F·X`, and the coefficients satisfy
  `a ^ 2 + X.det * b ^ 2 = 1` (the case `X.det = 1` is the core of
  `Work.L2F.Mat2.centralizer_sq_neg_one`);
* `mem_centralizer_iff_smul_one_add`: for `(tr x) ^ 2 ≠ 4` the centralizer of `x` in `SL(2,F)` is
  exactly the set of `a • 1 + b • W` with `a ^ 2 - disc F x * b ^ 2 = 1`.

These feed `Work.L2F.Mat2.centralizer_sl2_structure`.
-/
import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.commute_entries
import Submission.Work.L2F.Mat2.det_smul_one_add_smul
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det
import Submission.Work.L2F.Torus.Defs

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Mat2

/-! ## The commutant of a traceless matrix with non-zero determinant -/

/-- **The commutant of a traceless matrix with non-zero determinant.**  Let `F` be a field with
`(2 : F) ≠ 0`, let `X : Matrix (Fin 2) (Fin 2) F` be traceless with `X.det ≠ 0`, and let
`Y : Matrix (Fin 2) (Fin 2) F` have `Y.det = 1` and commute with `X`.  Then `Y = a • 1 + b • X`
with `a ^ 2 + X.det * b ^ 2 = 1`.

Write `X = !![p, q; r, -p]`.  Extracting the `(0,1)` and `(1,0)` entries of `Y * X = X * Y`
(`commute_entries`) gives

* `X 0 1 * (Y 0 0 - Y 1 1) = (2 * X 0 0) * Y 0 1`,
* `X 1 0 * (Y 0 0 - Y 1 1) = (2 * X 0 0) * Y 1 0`.

If `X 0 1 ≠ 0` put `b = Y 0 1 / X 0 1` and `a = Y 0 0 - b * X 0 0`; the two relations above
(plus the `(0,0)`-entry relation for the `(1,0)` slot) show that `Y = a • 1 + b • X`.
If `X 0 1 = 0` then `X 0 0 * X 0 0 = -X.det` (Cayley–Hamilton), so `X 0 0 ≠ 0` and `Y 0 1 = 0`;
put `b = (Y 0 0 - Y 1 1) / (2 * X 0 0)` and `a = Y 0 0 - b * X 0 0` (the `(1,0)` relation gives
`b * X 1 0 = Y 1 0`).

Finally `det (a • 1 + b • X) = a ^ 2 + a * b * X.trace + b ^ 2 * X.det = a ^ 2 + X.det * b ^ 2 =
det Y = 1`. -/
theorem exists_smul_one_add_of_commute (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (X Y : Matrix (Fin 2) (Fin 2) F) (htr : X.trace = 0) (hdetX : X.det ≠ 0) (hdetY : Y.det = 1)
    (hcomm : Y * X = X * Y) :
    ∃ a b : F, a ^ 2 + X.det * b ^ 2 = 1 ∧ Y = a • 1 + b • X := by
  obtain ⟨hC, hD, hE⟩ := commute_entries F X Y htr hcomm
  have hX11 : X 1 1 = - X 0 0 := by
    have h := htr
    rw [Matrix.trace_fin_two] at h
    exact eq_neg_of_add_eq_zero_right h
  by_cases hq : X 0 1 = 0
  · -- `X 0 1 = 0`: then `X 0 0 ≠ 0` (as `X.det ≠ 0`) and `Y 0 1 = 0`.
    have hX00sq : X 0 0 * X 0 0 = -X.det := by
      have h : X.det = X 0 0 * X 1 1 - X 0 1 * X 1 0 := Matrix.det_fin_two X
      rw [h, hX11, hq]
      ring
    have hX00 : X 0 0 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hX00sq
      exact hdetX (neg_eq_zero.mp hX00sq.symm)
    have hY01 : Y 0 1 = 0 := by
      have h := hD
      rw [hq, zero_mul] at h
      exact (mul_eq_zero.mp h.symm).resolve_left (mul_ne_zero h2 hX00)
    have h2X00 : 2 * X 0 0 ≠ 0 := mul_ne_zero h2 hX00
    have hb10 : ((Y 0 0 - Y 1 1) / (2 * X 0 0)) * X 1 0 = Y 1 0 := by
      rw [div_mul_eq_mul_div, mul_comm (Y 0 0 - Y 1 1) (X 1 0), hE, mul_div_cancel_left₀ _ h2X00]
    have hb2 : 2 * (((Y 0 0 - Y 1 1) / (2 * X 0 0)) * X 0 0) = Y 0 0 - Y 1 1 := by
      field_simp
    have hmat : Y = (Y 0 0 - ((Y 0 0 - Y 1 1) / (2 * X 0 0)) * X 0 0) • 1
        + ((Y 0 0 - Y 1 1) / (2 * X 0 0)) • X := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.add_apply, Matrix.smul_apply]
      · simp [Matrix.add_apply, Matrix.smul_apply, hq]
        exact hY01
      · simp [Matrix.add_apply, Matrix.smul_apply]
        exact hb10.symm
      · simp [Matrix.add_apply, Matrix.smul_apply]
        rw [hX11]
        rw [show (Y 0 0 - (Y 0 0 - Y 1 1) / (2 * X 0 0) * X 0 0)
              + (Y 0 0 - Y 1 1) / (2 * X 0 0) * (-X 0 0)
            = Y 0 0 - 2 * (((Y 0 0 - Y 1 1) / (2 * X 0 0)) * X 0 0) from by ring]
        rw [hb2]
        ring
    refine ⟨Y 0 0 - ((Y 0 0 - Y 1 1) / (2 * X 0 0)) * X 0 0,
      (Y 0 0 - Y 1 1) / (2 * X 0 0), ?_, hmat⟩
    have h : ((Y 0 0 - ((Y 0 0 - Y 1 1) / (2 * X 0 0)) * X 0 0) • 1
        + ((Y 0 0 - Y 1 1) / (2 * X 0 0)) • X).det = 1 := by
      rw [← hmat]; exact hdetY
    rw [det_smul_one_add_smul, htr] at h
    linear_combination h
  · -- `X 0 1 ≠ 0`: use `b = Y 0 1 / X 0 1`.
    have hb01 : (Y 0 1 / X 0 1) * X 0 1 = Y 0 1 := div_mul_cancel₀ _ hq
    have hb10 : (Y 0 1 / X 0 1) * X 1 0 = Y 1 0 := by
      rw [div_mul_eq_mul_div, hC, mul_div_cancel_left₀ _ hq]
    have hb2 : 2 * ((Y 0 1 / X 0 1) * X 0 0) = Y 0 0 - Y 1 1 := by
      apply mul_right_cancel₀ hq
      rw [mul_comm (Y 0 0 - Y 1 1) (X 0 1), hD]
      field_simp
    have hmat : Y = (Y 0 0 - (Y 0 1 / X 0 1) * X 0 0) • 1 + (Y 0 1 / X 0 1) • X := by
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.add_apply, Matrix.smul_apply]
      · simp [Matrix.add_apply, Matrix.smul_apply]
        exact hb01.symm
      · simp [Matrix.add_apply, Matrix.smul_apply]
        exact hb10.symm
      · simp [Matrix.add_apply, Matrix.smul_apply]
        rw [hX11]
        rw [show (Y 0 0 - Y 0 1 / X 0 1 * X 0 0) + Y 0 1 / X 0 1 * (-X 0 0)
            = Y 0 0 - 2 * ((Y 0 1 / X 0 1) * X 0 0) from by ring]
        rw [hb2]
        ring
    refine ⟨Y 0 0 - (Y 0 1 / X 0 1) * X 0 0, Y 0 1 / X 0 1, ?_, hmat⟩
    have h : ((Y 0 0 - (Y 0 1 / X 0 1) * X 0 0) • 1 + (Y 0 1 / X 0 1) • X).det = 1 := by
      rw [← hmat]; exact hdetY
    rw [det_smul_one_add_smul, htr] at h
    linear_combination h

/-! ## The algebra generated by `W = conjMat F x` -/

variable {F : Type*} [Field F]

/-- The determinant of the traceless part: `det (2 • x - tr(x) • 1) = 4 - tr(x) ^ 2 = -disc F x`. -/
theorem conjMat_det (h2 : (2 : F) ≠ 0) (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    (Work.L2F.Torus.conjMat F x).det = - Work.L2F.Torus.disc F x := by
  have hdet : ((x : Matrix (Fin 2) (Fin 2) F)).det = 1 := Matrix.SpecialLinearGroup.det_coe x
  have hsplit : (2 : F) • (x : Matrix (Fin 2) (Fin 2) F)
        - (((x : Matrix (Fin 2) (Fin 2) F)).trace) • (1 : Matrix (Fin 2) (Fin 2) F)
      = (-(((x : Matrix (Fin 2) (Fin 2) F)).trace)) • (1 : Matrix (Fin 2) (Fin 2) F)
        + (2 : F) • (x : Matrix (Fin 2) (Fin 2) F) := by
    rw [neg_smul]
    abel
  rw [Work.L2F.Torus.conjMat_apply, hsplit, det_smul_one_add_smul, hdet,
    Work.L2F.Torus.disc_apply]
  ring

/-- The traceless part commutes with `x`. -/
theorem conjMat_comm (_h2 : (2 : F) ≠ 0) (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    Work.L2F.Torus.conjMat F x * (x : Matrix (Fin 2) (Fin 2) F)
      = (x : Matrix (Fin 2) (Fin 2) F) * Work.L2F.Torus.conjMat F x := by
  rw [Work.L2F.Torus.conjMat_apply]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one]

/-- A matrix commuting with `x` commutes with the traceless part `2 • x - tr(x) • 1`. -/
theorem mul_conjMat_comm (h2 : (2 : F) ≠ 0) (x y : Matrix.SpecialLinearGroup (Fin 2) F)
    (h : (y : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F)
      = (x : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F)) :
    (y : Matrix (Fin 2) (Fin 2) F) * Work.L2F.Torus.conjMat F x
      = Work.L2F.Torus.conjMat F x * (y : Matrix (Fin 2) (Fin 2) F) := by
  rw [Work.L2F.Torus.conjMat_apply]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Matrix.one_mul, h]

/-- The product formula in the commutative algebra `F·1 + F·W` generated by a matrix `W` with
`W * W = ρ • 1`. -/
theorem smul_one_add_smul_mul {W : Matrix (Fin 2) (Fin 2) F} {ρ : F}
    (hW : W * W = ρ • (1 : Matrix (Fin 2) (Fin 2) F)) (a b c e : F) :
    (a • 1 + b • W) * (c • 1 + e • W) =
      (a * c + ρ * (b * e)) • (1 : Matrix (Fin 2) (Fin 2) F) + (a * e + b * c) • W := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, hW, smul_smul, add_smul, smul_add]
  module

/-- The algebra `F·1 + F·W` is commutative when `W * W = ρ • 1`. -/
theorem smul_one_add_smul_mul_comm {W : Matrix (Fin 2) (Fin 2) F} {ρ : F}
    (hW : W * W = ρ • (1 : Matrix (Fin 2) (Fin 2) F)) (a b c e : F) :
    (a • 1 + b • W) * (c • 1 + e • W) = (c • 1 + e • W) * (a • 1 + b • W) := by
  rw [smul_one_add_smul_mul hW a b c e, smul_one_add_smul_mul hW c e a b]
  module

/-- `a • 1 + b • W` commutes with `x`, where `W = Work.L2F.Torus.conjMat F x`. -/
theorem mul_smul_one_add_smul_conj (h2 : (2 : F) ≠ 0) (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (a b : F) :
    (a • 1 + b • Work.L2F.Torus.conjMat F x) * (x : Matrix (Fin 2) (Fin 2) F)
      = (x : Matrix (Fin 2) (Fin 2) F) * (a • 1 + b • Work.L2F.Torus.conjMat F x) := by
  rw [add_mul, mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, conjMat_comm h2 x]

/-! ## The centralizer of a semisimple element -/

/-- **The centralizer of a semisimple element of `SL(2,F)`.**  If `(tr x) ^ 2 ≠ 4` then
`C_{SL(2,F)}(x) = {a • 1 + b • W | a ^ 2 - disc F x * b ^ 2 = 1}`, where
`W = conjMat F x = 2 • x - tr(x) • 1` is the traceless part of `x`. -/
theorem mem_centralizer_iff_smul_one_add (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : ((x : Matrix (Fin 2) (Fin 2) F)).trace ^ 2 ≠ 4)
    (y : Matrix.SpecialLinearGroup (Fin 2) F) :
    y ∈ Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ↔
      ∃ a b : F, a ^ 2 - Work.L2F.Torus.disc F x * b ^ 2 = 1 ∧
        (y : Matrix (Fin 2) (Fin 2) F) = a • 1 + b • Work.L2F.Torus.conjMat F x := by
  have hdisc : Work.L2F.Torus.disc F x ≠ 0 := by
    rw [Work.L2F.Torus.disc_apply]
    exact sub_ne_zero.mpr hx
  constructor
  · intro hy
    have hyx : (y : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F)
        = (x : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hy
      exact congrArg (fun t : Matrix.SpecialLinearGroup (Fin 2) F =>
        (t : Matrix (Fin 2) (Fin 2) F)) h
    have hcommW := mul_conjMat_comm h2 x y hyx
    obtain ⟨a, b, hab, hY⟩ := exists_smul_one_add_of_commute F h2 (Work.L2F.Torus.conjMat F x)
      (y : Matrix (Fin 2) (Fin 2) F) (Work.L2F.Torus.conjMat_trace F x)
      (by rw [conjMat_det h2 x]; exact neg_ne_zero.mpr hdisc)
      (Matrix.SpecialLinearGroup.det_coe y) hcommW
    refine ⟨a, b, ?_, hY⟩
    rw [conjMat_det h2 x] at hab
    linear_combination hab
  · rintro ⟨a, b, hab, hy⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hy]
    exact mul_smul_one_add_smul_conj h2 x a b

end Work.L2F.Mat2
