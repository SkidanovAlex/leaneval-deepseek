import Mathlib

/-!
# The real determinant of multiplication by a complex number

For `c : ℂ`, the map `z ↦ z * c` is `ℝ`-linear on `ℂ ≅ ℝ²`; its determinant is `‖c‖²`.  This is the
computation that identifies the *real* Jacobian of a holomorphic map with `‖deriv‖²`, and hence the
missing link in the change-of-variables formula for holomorphic charts.

It is used (via `Mathlib/MeasureTheory/Function/Jacobian.lean`) to prove the conformal invariance of
the Dirichlet density `⟨∇u,∇v⟩ dA`, which is the input of the chart-wise Green-identity proof of the
symmetry of the Green function; see `Submission/Work/Drive/NOTES_energyRoute_chartwise.md`.
-/

open MeasureTheory
open Complex

namespace Work.Analysis.Complex

set_option linter.unusedSimpArgs false

/-- **The determinant of the real-linear map "multiplication by `c`" on `ℂ` is `‖c‖ ^ 2`.** -/
theorem det_smulRight_one_complex (c : ℂ) :
    LinearMap.det ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ :
      ℂ →ₗ[ℝ] ℂ) = ‖c‖ ^ 2 := by
  rw [← LinearMap.det_toMatrix basisOneI]
  have hmat : LinearMap.toMatrix basisOneI basisOneI
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ : ℂ →ₗ[ℝ] ℂ)
      = !![c.re, -c.im; c.im, c.re] := by
    ext i j
    simp only [LinearMap.toMatrix_apply, coe_basisOneI, ContinuousLinearMap.smulRight_apply,
      one_apply_eq_self, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one]
    fin_cases i <;> fin_cases j <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hnorm : ‖c‖ ^ 2 = c.re ^ 2 + c.im ^ 2 := by
    rw [show ‖c‖ = Real.sqrt (normSq c) from rfl, Real.sq_sqrt (normSq_nonneg c), normSq_apply]
    ring
  rw [hmat, Matrix.det_fin_two_of, hnorm]
  ring

end Work.Analysis.Complex
