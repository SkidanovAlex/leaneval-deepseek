import Mathlib

namespace Work.TMC14Core

/-- An element `l` of `ℝ` with `l^2 - t*l + 1 = 0` exists whenever `2 < |t|`: the quadratic
`X^2 - t*X + 1` has discriminant `t^2 - 4 > 0`. -/
private lemma exists_root_quadratic (t : ℝ) (ht : 2 < |t|) :
    ∃ l : ℝ, l ^ 2 - t * l + 1 = 0 := by
  refine ⟨(t + Real.sqrt (t ^ 2 - 4)) / 2, ?_⟩
  have hpos : 0 < t ^ 2 - 4 := by
    nlinarith [sq_abs t, abs_nonneg t]
  have hssq : (Real.sqrt (t ^ 2 - 4)) ^ 2 = t ^ 2 - 4 := Real.sq_sqrt hpos.le
  nlinarith [hssq]

/-- A `2 × 2` real matrix with determinant `1` and `|trace| > 2` has a real eigenvalue, hence a
real eigenvector. -/
theorem eigvecDetOne (M : Matrix (Fin 2) (Fin 2) ℝ) (hdet : M.det = 1) (htr : 2 < |M.trace|) :
    ∃ (l : ℝ) (v : Fin 2 → ℝ), v ≠ 0 ∧ M.mulVec v = l • v := by
  -- The characteristic polynomial is `X^2 - trace * X + det`; its discriminant is `trace^2 - 4 > 0`,
  -- so it has a real root `l`.
  obtain ⟨l, hl⟩ := exists_root_quadratic M.trace htr
  -- Thus `l • 1 - M` is singular, i.e. it kills some nonzero vector.
  have hA : (Matrix.scalar (Fin 2) l - M).det = 0 := by
    rw [← Matrix.eval_charpoly M l, Matrix.charpoly_fin_two]
    simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C]
    rw [hdet]
    linarith [hl]
  obtain ⟨v, hv_ne, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hA
  refine ⟨l, v, hv_ne, ?_⟩
  -- `scalar l = l • 1`, so `(l • 1 - M) v = l • v - M v = 0` gives `M v = l • v`.
  have hscalar : Matrix.scalar (Fin 2) l = l • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    ext i j; by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
  rw [hscalar, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
  exact hv.symm

end Work.TMC14Core
