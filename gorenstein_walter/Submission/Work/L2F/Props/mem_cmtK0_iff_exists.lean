import Mathlib
import Submission.Work.L2F.Props.PGL2CommutatorTorusDefs
import Submission.Work.L2F.Mat2.det_smul_one_add_smul
import Submission.Work.L2F.Mat2.sq_eq_trace_smul_sub_det
import Submission.Work.L2F.Mat2.commute_entries

open scoped MatrixGroups
open Matrix

-- `lam ≠ 0` is part of the intended setting but is not needed for the argument (see the docstring
-- of `commutant_sq_scalar`), so no proof step refers to it.
set_option linter.unusedVariables false

namespace Work.L2F.Props

/-! ## Cayley–Hamilton for a non-scalar square root of a scalar matrix

Let `S` be a `2 × 2` matrix over a field with `S * S = lam • 1` which is not a scalar matrix.  Then
the minimal polynomial of `S` is the degree-`2` polynomial `X ^ 2 - lam`, hence equal to the
characteristic polynomial of `S`: this forces `tr S = 0` and `det S = -lam`.  Everything below is
proved by Cayley–Hamilton (`Work.L2F.Mat2.sq_eq_trace_smul_sub_det`), which for `2 × 2` matrices
reads `S * S = S.trace • S - S.det • 1`.

These two facts are stated for an arbitrary field: no hypothesis `(2 : F) ≠ 0` is needed. -/

/-- If `S * S = lam • 1` and `S` is not a scalar matrix then `tr S = 0`.  Indeed Cayley–Hamilton
turns `S * S = lam • 1` into `S.trace • S = (lam + S.det) • 1`; if `S.trace ≠ 0` this displays `S`
as a scalar matrix. -/
lemma trace_eq_zero_of_sq_eq_smul_one (F : Type*) [Field F] (S : Matrix (Fin 2) (Fin 2) F)
    (lam : F) (hS : S * S = lam • 1) (hns : ∀ c : F, S ≠ c • 1) : S.trace = 0 := by
  have hCH := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F S
  rw [hS] at hCH
  have hkey : S.trace • S = (lam + S.det) • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h1 : S.trace • S = lam • 1 + S.det • 1 := (sub_eq_iff_eq_add).mp hCH.symm
    rw [h1, ← add_smul]
  by_contra htr
  refine hns ((lam + S.det) / S.trace) ?_
  calc S = S.trace⁻¹ • (S.trace • S) := by rw [smul_smul, inv_mul_cancel₀ htr, one_smul]
    _ = S.trace⁻¹ • ((lam + S.det) • 1) := by rw [hkey]
    _ = ((lam + S.det) / S.trace) • 1 := by rw [smul_smul, div_eq_inv_mul]

/-- If `S * S = lam • 1` and `tr S = 0` then `det S = -lam`: Cayley–Hamilton now reads
`lam • 1 = -(S.det) • 1`, and the `(0,0)` entry gives `lam = -S.det`. -/
lemma det_eq_neg_of_sq_eq_smul_one (F : Type*) [Field F] (S : Matrix (Fin 2) (Fin 2) F)
    (lam : F) (hS : S * S = lam • 1) (htr : S.trace = 0) : S.det = -lam := by
  have hCH := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F S
  rw [hS, htr, zero_smul, zero_sub] at hCH
  have h := congrFun (congrFun hCH 0) 0
  simp only [Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply_eq] at h
  linear_combination h

/-! ## The commutant of `S` is `F·1 + F·S` -/

/-- **The commutant of a non-scalar square root of a scalar matrix.**  Over any field, if
`S * S = lam • 1` and `S` is not a scalar matrix, then every matrix commuting with `S` lies in the
two-dimensional algebra `F·1 + F·S`.

Note that `lam ≠ 0` is not needed.  The proof is an explicit entry computation.  By the previous
lemma `tr S = 0`, so `S = !![p, q; r, -p]` with `p * p + q * r = lam`; writing `Y = !![α, β; γ, δ]`
the `(0,1)`- and `(1,0)`-entries of `Y * S = S * Y` give

* `β * r = q * γ`,  `q * (α - δ) = 2 * p * β`,  `r * (α - δ) = 2 * p * γ`.

If `r ≠ 0` then `Y = a • 1 + b • S` with `b = γ / r`, `a = α - b * p`; if `q ≠ 0` then with
`b = β / q`; finally if `q = r = 0` then `S = !![p, 0; 0, -p]` and `p = -p` would make `S = p • 1`
scalar, so `(2 : F) ≠ 0`, and one takes `a = (α + δ) / 2`, `b = (α - δ) / (2 * p)`.  Thus `2` is
divided by only in the last case, where its invertibility is forced by the hypotheses. -/
lemma commutant_sq_scalar (F : Type*) [Field F] (S Y : Matrix (Fin 2) (Fin 2) F) (lam : F)
    (hS : S * S = lam • 1) (hns : ∀ c : F, S ≠ c • 1) (hcomm : Y * S = S * Y) :
    ∃ a b : F, Y = a • 1 + b • S := by
  have htr : S.trace = 0 := trace_eq_zero_of_sq_eq_smul_one F S lam hS hns
  have hS11 : S 1 1 = - S 0 0 := by
    have h := htr
    rw [Matrix.trace_fin_two] at h
    exact eq_neg_of_add_eq_zero_right h
  have hS00 : S 0 0 * S 0 0 + S 0 1 * S 1 0 = lam := by
    have h := congrFun (congrFun hS 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using h
  obtain ⟨hC, hD, hE⟩ := Work.L2F.Mat2.commute_entries F S Y htr hcomm
  rcases eq_or_ne (S 1 0) 0 with hr | hr
  · rcases eq_or_ne (S 0 1) 0 with hq | hq
    · -- `S 0 1 = S 1 0 = 0`: `S = !![p, 0; 0, -p]`, and `(2 : F) ≠ 0`.
      have h2p : 2 * S 0 0 ≠ 0 := by
        intro h2p0
        have hpn : S 0 0 = - S 0 0 := by
          have h : S 0 0 + S 0 0 = 0 := by rwa [two_mul] at h2p0
          exact eq_neg_of_add_eq_zero_right h
        refine hns (S 0 0) ?_
        ext i j
        fin_cases i <;> fin_cases j
        · simp [Matrix.smul_apply]
        · simp [Matrix.smul_apply, hq]
        · simp [Matrix.smul_apply, hr]
        · simp [Matrix.smul_apply, hS11]
          rw [← hpn]
      have h2 : (2 : F) ≠ 0 := fun h0 => h2p (by rw [h0, zero_mul])
      have hS0 : S 0 0 ≠ 0 := fun h0 => h2p (by rw [h0, mul_zero])
      have hY01 : Y 0 1 = 0 := by
        have h := hD
        rw [hq, zero_mul] at h
        exact (mul_eq_zero.mp h.symm).resolve_left h2p
      have hY10 : Y 1 0 = 0 := by
        have h := hE
        rw [hr, zero_mul] at h
        exact (mul_eq_zero.mp h.symm).resolve_left h2p
      have hA : (Y 0 0 - Y 1 1) / (2 * S 0 0) * S 0 0 = (Y 0 0 - Y 1 1) / 2 := by
        rw [div_mul_eq_mul_div]
        exact mul_div_mul_right (Y 0 0 - Y 1 1) 2 hS0
      have h00 : Y 0 0 = (Y 0 0 + Y 1 1) / 2 + (Y 0 0 - Y 1 1) / (2 * S 0 0) * S 0 0 := by
        rw [hA, ← add_div, show Y 0 0 + Y 1 1 + (Y 0 0 - Y 1 1) = 2 * Y 0 0 by ring]
        exact (mul_div_cancel_left₀ (Y 0 0) h2).symm
      have h11 : Y 1 1 = (Y 0 0 + Y 1 1) / 2 + - ((Y 0 0 - Y 1 1) / (2 * S 0 0) * S 0 0) := by
        rw [hA, ← sub_eq_add_neg, ← sub_div,
          show Y 0 0 + Y 1 1 - (Y 0 0 - Y 1 1) = 2 * Y 1 1 by ring]
        exact (mul_div_cancel_left₀ (Y 1 1) h2).symm
      refine ⟨(Y 0 0 + Y 1 1) / 2, (Y 0 0 - Y 1 1) / (2 * S 0 0), ?_⟩
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.add_apply, Matrix.smul_apply]
        exact h00
      · simp [Matrix.add_apply, Matrix.smul_apply, hq]
        exact hY01
      · simp [Matrix.add_apply, Matrix.smul_apply, hr]
        exact hY10
      · simp [Matrix.add_apply, Matrix.smul_apply, hS11]
        exact h11
    · -- `S 1 0 = 0`, `S 0 1 ≠ 0`: use `b = Y 0 1 / S 0 1`.
      have hb2 : 2 * ((Y 0 1 / S 0 1) * S 0 0) = Y 0 0 - Y 1 1 := by
        apply mul_right_cancel₀ hq
        rw [mul_comm (Y 0 0 - Y 1 1) (S 0 1), hD]
        field_simp
      have hb11 : Y 1 1 = (Y 0 0 - (Y 0 1 / S 0 1) * S 0 0) - (Y 0 1 / S 0 1) * S 0 0 := by
        linear_combination hb2
      have hY10 : Y 1 0 = 0 := by
        have h := hC
        rw [hr, mul_zero] at h
        exact (mul_eq_zero.mp h.symm).resolve_left hq
      refine ⟨Y 0 0 - (Y 0 1 / S 0 1) * S 0 0, Y 0 1 / S 0 1, ?_⟩
      ext i j
      fin_cases i <;> fin_cases j
      · simp [Matrix.add_apply, Matrix.smul_apply]
      · simp [Matrix.add_apply, Matrix.smul_apply]
        exact (div_mul_cancel₀ (Y 0 1) hq).symm
      · simp [Matrix.add_apply, Matrix.smul_apply, hr]
        exact hY10
      · simp [Matrix.add_apply, Matrix.smul_apply, hS11]
        linear_combination hb11
  · -- `S 1 0 ≠ 0`: use `b = Y 1 0 / S 1 0`.
    have hb01 : Y 0 1 = (Y 1 0 / S 1 0) * S 0 1 := by
      have h' : (Y 1 0 / S 1 0) * S 0 1 = Y 0 1 := by
        rw [div_mul_eq_mul_div, mul_comm (Y 1 0) (S 0 1), ← hC, mul_div_cancel_right₀ _ hr]
      exact h'.symm
    have hb2 : 2 * ((Y 1 0 / S 1 0) * S 0 0) = Y 0 0 - Y 1 1 := by
      apply mul_right_cancel₀ hr
      rw [mul_comm (Y 0 0 - Y 1 1) (S 1 0), hE]
      field_simp
    have hb11 : Y 1 1 = (Y 0 0 - (Y 1 0 / S 1 0) * S 0 0) - (Y 1 0 / S 1 0) * S 0 0 := by
      linear_combination hb2
    refine ⟨Y 0 0 - (Y 1 0 / S 1 0) * S 0 0, Y 1 0 / S 1 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simp [Matrix.add_apply, Matrix.smul_apply]
    · simp [Matrix.add_apply, Matrix.smul_apply]
      exact hb01
    · simp [Matrix.add_apply, Matrix.smul_apply]
      exact (div_mul_cancel₀ (Y 1 0) hr).symm
    · simp [Matrix.add_apply, Matrix.smul_apply, hS11]
      linear_combination hb11

/-! ## The determinant of `a • 1 + b • S` -/

/-- For `S * S = lam • 1` with `S` non-scalar, `det (a • 1 + b • S) = a ^ 2 - lam * b ^ 2`. -/
lemma det_smul_one_add_smul_of_sq_eq_smul_one (F : Type*) [Field F]
    (S : Matrix (Fin 2) (Fin 2) F) (lam a b : F) (hS : S * S = lam • 1)
    (hns : ∀ c : F, S ≠ c • 1) :
    (a • 1 + b • S).det = a ^ 2 - lam * b ^ 2 := by
  have htr : S.trace = 0 := trace_eq_zero_of_sq_eq_smul_one F S lam hS hns
  have hdet : S.det = -lam := det_eq_neg_of_sq_eq_smul_one F S lam hS htr
  rw [Work.L2F.Mat2.det_smul_one_add_smul, htr, hdet]
  ring

/-- `cmtK0 F S` consists of the `a • 1 + b • S` with `a² - lam·b² = 1`.
Hint: `S² = lam • 1` with `S` non-scalar forces `tr S = 0` and `det S = -lam`, so
`det (a • 1 + b • S) = a² - lam b²` (`Work.L2F.Mat2.det_smul_one_add_smul`); the commutant of a
non-scalar matrix satisfying a separable quadratic is `F[S] = {a • 1 + b • S}`. -/
theorem mem_cmtK0_iff_exists (F : Type*) [Field F] (S : Matrix.GeneralLinearGroup (Fin 2) F) (lam : F)
    (hS : (S : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F) = lam • 1)
    (hlam : lam ≠ 0) (hns : ∀ c : F, (S : Matrix (Fin 2) (Fin 2) F) ≠ c • 1)
    (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    x ∈ Work.L2F.Props.cmtK0 F S ↔ ∃ a b : F, a ^ 2 - lam * b ^ 2 = 1 ∧
      (x : Matrix (Fin 2) (Fin 2) F) = a • 1 + b • (S : Matrix (Fin 2) (Fin 2) F) := by
  constructor
  · intro hx
    -- `x` commutes with `S` at the level of matrices
    have hcomm : (x : Matrix (Fin 2) (Fin 2) F) * (S : Matrix (Fin 2) (Fin 2) F)
        = (S : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) := by
      have h := congrArg (fun t : Matrix.GeneralLinearGroup (Fin 2) F =>
        (t : Matrix (Fin 2) (Fin 2) F)) ((mem_cmtK0_iff_comm F S x).mp hx)
      simpa [Matrix.GeneralLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
        using h
    obtain ⟨a, b, hab⟩ := commutant_sq_scalar F (S : Matrix (Fin 2) (Fin 2) F)
      (x : Matrix (Fin 2) (Fin 2) F) lam hS hns hcomm
    refine ⟨a, b, ?_, hab⟩
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M.det) hab
    rw [Matrix.SpecialLinearGroup.det_coe x,
      det_smul_one_add_smul_of_sq_eq_smul_one F (S : Matrix (Fin 2) (Fin 2) F) lam a b hS hns] at h
    linear_combination -h
  · rintro ⟨a, b, -, hmat⟩
    rw [mem_cmtK0_iff_comm]
    apply Units.ext
    simp only [Matrix.GeneralLinearGroup.coe_mul]
    rw [Matrix.SpecialLinearGroup.coe_GL_coe_matrix x, hmat]
    rw [add_mul, mul_add, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hS]

end Work.L2F.Props
