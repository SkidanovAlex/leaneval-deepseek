import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.fourierCoeff_pdVec

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

/-- Squared norm of the Fourier coefficient of an iterated partial derivative.

Since `∂_{l 0} ⋯ ∂_{l (k-1)}` is the Fourier multiplier `∏ i, 2πi m (l i)`
(`fourierCoeff_pdVec`), the squared norm of the coefficient picks up the product of the
moduli squared of the multipliers, `∏ i, (2π m (l i))²`. -/
theorem fourierCoeff_pdVec_normSq {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ) (l : Fin k → ι)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ k f) (hper : Work.Diff.STE.Periodic1 f) (m : ι → ℤ) :
    ‖Work.Diff.STE.fourierCoeff (Work.Diff.STE.pdVec k l f) m‖ ^ 2
      = (∏ i, (2 * Real.pi * ((m (l i) : ℤ) : ℝ)) ^ 2) * ‖Work.Diff.STE.fourierCoeff f m‖ ^ 2 := by
  rw [Work.Diff.STE.fourierCoeff_pdVec k l f hf hper m]
  rw [norm_mul, mul_pow]
  congr 1
  rw [norm_prod]
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Complex.normSq_eq_norm_sq]
  have hcast : 2 * (Real.pi : ℂ) * Complex.I * ((m (l i) : ℤ) : ℂ)
      = ((2 * Real.pi * ((m (l i) : ℤ) : ℝ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [hcast, map_mul, Complex.normSq_ofReal, Complex.normSq_I, mul_one]
  ring

end Work.Diff.STE
