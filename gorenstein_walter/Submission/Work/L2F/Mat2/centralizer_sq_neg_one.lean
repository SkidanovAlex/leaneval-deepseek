import Mathlib
import Submission.Work.L2F.Defs
import Submission.Work.L2F.Mat2.trace_mul_self
import Submission.Work.L2F.Mat2.det_smul_one_add_smul
import Submission.Work.L2F.Mat2.commute_entries

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Mat2

/-- The computational core of `centralizer_sq_neg_one`: if `X : Matrix (Fin 2) (Fin 2) F` is
traceless with determinant `1` (so that `X * X = -1` by Cayley–Hamilton) and `Y` commutes with
`X`, then `Y` lies in the two-dimensional algebra `F[X] = {a • 1 + b • X}`, and (when `Y` is
also in `SL(2,F)`, i.e. `det Y = 1`) the coefficients satisfy `a ^ 2 + b ^ 2 = 1`.

Write `X = !![p, q; r, -p]` (so `-p ^ 2 - q * r = 1`).  Extracting the `(0,1)` and `(1,0)` entries
of `Y * X = X * Y` (`commute_entries`) gives

* `X 0 1 * (Y 0 0 - Y 1 1) = (2 * X 0 0) * Y 0 1`,
* `X 1 0 * (Y 0 0 - Y 1 1) = (2 * X 0 0) * Y 1 0`.

If `X 0 1 ≠ 0` put `b = Y 0 1 / X 0 1` and `a = Y 0 0 - b * X 0 0`; the two relations above
(plus the `(0,0)`-entry relation for the `(1,0)` slot) show that `Y = a • 1 + b • X`.
If `X 0 1 = 0` then `X 0 0 ^ 2 = -1`, so `X 0 0 ≠ 0` and `Y 0 1 = 0`; put
`b = (Y 0 0 - Y 1 1) / (2 * X 0 0)` and `a = Y 0 0 - b * X 0 0` (the `(1,0)` relation gives
`b * X 1 0 = Y 1 0`).

Finally `det (a • 1 + b • X) = a ^ 2 + a * b * X.trace + b ^ 2 * X.det = a ^ 2 + b ^ 2 =
det Y = 1`. -/
private theorem exists_smul_one_add_smul_of_commute (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (X Y : Matrix (Fin 2) (Fin 2) F) (htr : X.trace = 0) (hdetX : X.det = 1) (hdetY : Y.det = 1)
    (hcomm : Y * X = X * Y) :
    ∃ a b : F, a ^ 2 + b ^ 2 = 1 ∧ Y = a • 1 + b • X := by
  obtain ⟨hC, hD, hE⟩ := commute_entries F X Y htr hcomm
  have hX11 : X 1 1 = - X 0 0 := by
    have h := htr
    rw [Matrix.trace_fin_two] at h
    exact eq_neg_of_add_eq_zero_right h
  by_cases hq : X 0 1 = 0
  · -- `X 0 1 = 0`: then `X 0 0 ≠ 0` and `Y 0 1 = 0`.
    have hX00sq : X 0 0 ^ 2 = -1 := by
      have h := hdetX
      rw [Matrix.det_fin_two, hX11, hq] at h
      simp only [zero_mul, sub_zero] at h
      linear_combination -h
    have hX00 : X 0 0 ≠ 0 := by
      intro h0
      rw [h0] at hX00sq
      norm_num at hX00sq
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
    refine ⟨Y 0 0 - ((Y 0 0 - Y 1 1) / (2 * X 0 0)) * X 0 0, (Y 0 0 - Y 1 1) / (2 * X 0 0), ?_, hmat⟩
    have h : ((Y 0 0 - ((Y 0 0 - Y 1 1) / (2 * X 0 0)) * X 0 0) • 1
        + ((Y 0 0 - Y 1 1) / (2 * X 0 0)) • X).det = 1 := by
      rw [← hmat]; exact hdetY
    rw [det_smul_one_add_smul, htr, hdetX] at h
    simpa using h
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
    rw [det_smul_one_add_smul, htr, hdetX] at h
    simpa using h

/-- The centralizer of `x ∈ SL(2,F)` with `x² = -1` (and `(2:F) ≠ 0`) is
`{a • 1 + b • x | a² + b² = 1}`.  Proof: `x` is not scalar (`x = λ • 1` with `x² = -1` gives
`det x = λ² = -1 ≠ 1`), so for some `v ≠ 0` the pair `(v, x v)` is a basis of `F²`; if `y` commutes
with `x` and `y v = a v + b (x v)` then `y (x v) = x (y v) = a (x v) - b v`, so `y` and
`a • 1 + b • x` agree on the basis, hence are equal.  Conversely such a `y` commutes with `x`, and
`det (a • 1 + b • x) = a² + b²` (because `tr x = 0`, from `trace_mul_self` applied to `x² = -1`),
so `y ∈ SL(2,F)` exactly when `a² + b² = 1`. -/
theorem centralizer_sq_neg_one (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (x : Matrix.SpecialLinearGroup (Fin 2) F)
    (hx : (x : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) = -1)
    (y : Matrix.SpecialLinearGroup (Fin 2) F) :
    y ∈ Subgroup.centralizer ({x} : Set (Matrix.SpecialLinearGroup (Fin 2) F)) ↔
      ∃ a b : F, a ^ 2 + b ^ 2 = 1 ∧
        (y : Matrix (Fin 2) (Fin 2) F) = a • 1 + b • (x : Matrix (Fin 2) (Fin 2) F) := by
  constructor
  · intro hy
    -- `y` commuting with `x` becomes an equality of matrices
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    have hcomm : (y : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F)
        = (x : Matrix (Fin 2) (Fin 2) F) * (y : Matrix (Fin 2) (Fin 2) F) := by
      have h := congrArg (fun t : Matrix.SpecialLinearGroup (Fin 2) F =>
        (t : Matrix (Fin 2) (Fin 2) F)) hy
      simpa only [Matrix.SpecialLinearGroup.coe_mul] using h
    -- `tr x = 0` from Newton's identity and `x ^ 2 = -1`, `det x = 1`
    have htr : (x : Matrix (Fin 2) (Fin 2) F).trace = 0 := by
      have h := Work.L2F.Mat2.trace_mul_self F (x : Matrix (Fin 2) (Fin 2) F)
      rw [hx] at h
      rw [Matrix.trace_neg, Matrix.trace_one, Fintype.card_fin,
        Matrix.SpecialLinearGroup.det_coe] at h
      simp only [mul_one] at h
      have h2' : (x : Matrix (Fin 2) (Fin 2) F).trace ^ 2 = 0 := by
        linear_combination -h
      exact mul_self_eq_zero.mp (by rw [← pow_two]; exact h2')
    exact exists_smul_one_add_smul_of_commute F h2 (x : Matrix (Fin 2) (Fin 2) F)
      (y : Matrix (Fin 2) (Fin 2) F) htr (Matrix.SpecialLinearGroup.det_coe x)
      (Matrix.SpecialLinearGroup.det_coe y) hcomm
  · rintro ⟨a, b, _hab, hmat⟩
    -- conversely `a • 1 + b • x` commutes with `x` since `x ^ 2 = -1` is central in `F[x]`
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hmat]
    rw [add_mul, mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      one_mul, mul_one, hx]

end Work.L2F.Mat2
