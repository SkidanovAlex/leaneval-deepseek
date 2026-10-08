import Mathlib
import Submission.Work.L2F.Torus.Defs
import Submission.Work.L2F.Mat2.commute_entries

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Torus

/-! # The commutant of a traceless `2 × 2` matrix with `V * V = D • 1`

Let `F` be a field with `(2 : F) ≠ 0` and `V : Matrix (Fin 2) (Fin 2) F` a traceless matrix with
`V * V = D • 1` for some `D ≠ 0`.  Since `V` is traceless, Cayley–Hamilton forces
`V * V = -det V • 1`, so `det V = -D ≠ 0` and `V` is non-scalar (the latter also directly from
`V = c • 1 ⟹ 0 = tr V = 2c ⟹ c = 0 ⟹ D = 0`): the minimal polynomial of `V` is `X² - D`, which is
separable, and hence the commutant of `V` in `M₂(F)` is exactly the two-dimensional algebra
`F[X]/(X² - D) = F·1 + F·V = algSpan F V`.

The proof extracts the entries of `Y * V = V * Y` (`Work.L2F.Mat2.commute_entries`) and then splits
on whether the `(0,1)`-entry `q = V 0 1` vanishes: if `q ≠ 0` the coefficient `b` is `Y 0 1 / q`, and
if `q = 0` then `V` is `!![p, 0; r, -p]` with `p² = D ≠ 0`, so `trivially` `b` is determined by the
diagonal difference `(Y 0 0 - Y 1 1) / (2p)`. -/

/-- For a traceless `2 × 2` matrix `V` with `V * V = D • 1` we have `det V = -D`.  (Extract the
`(0,0)`-entry of `V * V = D • 1` and use `V 1 1 = -V 0 0`.) -/
theorem det_eq_neg_of_traceless_sq (F : Type*) [Field F] (V : Matrix (Fin 2) (Fin 2) F) (D : F)
    (hVtr : V.trace = 0) (hV2 : V * V = D • 1) : V.det = -D := by
  have hV11 : V 1 1 = - V 0 0 := by
    have h := hVtr
    rw [Matrix.trace_fin_two] at h
    exact eq_neg_of_add_eq_zero_right h
  have h00 : V 0 0 * V 0 0 + V 0 1 * V 1 0 = D := by
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hV2
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  rw [Matrix.det_fin_two, hV11]
  linear_combination -h00

/-- **The commutant of a traceless matrix with non-zero determinant is `F·1 + F·X`.**  If
`X : Matrix (Fin 2) (Fin 2) F` is traceless with `X.det ≠ 0`, and `Y` commutes with `X`, then
`Y = a • 1 + b • X` for some `a b : F`. -/
theorem mem_algSpan_of_commute (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (X Y : Matrix (Fin 2) (Fin 2) F) (htr : X.trace = 0) (hdetX : X.det ≠ 0)
    (hcomm : Y * X = X * Y) : Y ∈ algSpan F X := by
  obtain ⟨hC, hD, hE⟩ := Work.L2F.Mat2.commute_entries F X Y htr hcomm
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
      rw [div_mul_eq_mul_div, mul_comm (Y 0 0 - Y 1 1) (X 1 0), hE,
        mul_div_cancel_left₀ _ h2X00]
    have hb2 : 2 * (((Y 0 0 - Y 1 1) / (2 * X 0 0)) * X 0 0) = Y 0 0 - Y 1 1 := by
      field_simp
    refine ⟨Y 0 0 - ((Y 0 0 - Y 1 1) / (2 * X 0 0)) * X 0 0,
      (Y 0 0 - Y 1 1) / (2 * X 0 0), ?_⟩
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
  · -- `X 0 1 ≠ 0`: use `b = Y 0 1 / X 0 1`.
    have hb01 : (Y 0 1 / X 0 1) * X 0 1 = Y 0 1 := div_mul_cancel₀ _ hq
    have hb10 : (Y 0 1 / X 0 1) * X 1 0 = Y 1 0 := by
      rw [div_mul_eq_mul_div, hC, mul_div_cancel_left₀ _ hq]
    have hb2 : 2 * ((Y 0 1 / X 0 1) * X 0 0) = Y 0 0 - Y 1 1 := by
      apply mul_right_cancel₀ hq
      rw [mul_comm (Y 0 0 - Y 1 1) (X 0 1), hD]
      field_simp
    refine ⟨Y 0 0 - (Y 0 1 / X 0 1) * X 0 0, Y 0 1 / X 0 1, ?_⟩
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

/-- The commutant of a traceless matrix `V` with `V * V = D • 1` (`D ≠ 0`) is the `F`-algebra
`algSpan F V = F·1 + F·V`. -/
theorem commute_iff_mem_algSpan (F : Type*) [Field F] (h2 : (2 : F) ≠ 0)
    (V Y : Matrix (Fin 2) (Fin 2) F) (D : F) (hVtr : V.trace = 0)
    (hV2 : V * V = D • 1) (hD : D ≠ 0) :
    Y * V = V * Y ↔ Y ∈ algSpan F V := by
  have hdetV : V.det ≠ 0 := by
    rw [det_eq_neg_of_traceless_sq F V D hVtr hV2]
    exact neg_ne_zero.mpr hD
  refine ⟨fun hcomm => mem_algSpan_of_commute F h2 V Y hVtr hdetV hcomm, fun hY => ?_⟩
  obtain ⟨a, b, rfl⟩ := hY
  calc (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • V) * V
      = a • V + b • (D • (1 : Matrix (Fin 2) (Fin 2) F)) := by
        rw [add_mul, Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, hV2]
    _ = V * (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • V) := by
        rw [mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, hV2]

end Work.L2F.Torus
