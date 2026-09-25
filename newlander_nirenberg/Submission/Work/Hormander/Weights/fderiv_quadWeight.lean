import Mathlib
import Submission.Work.Hormander.Weights.Defs

noncomputable section

namespace Work.Hormander.Weights

/-- The derivative of the quadratic weight `φ(z) = K‖z‖²` is
`v ↦ 2K ⟪z, v⟫_ℝ`.  This is the elementary computation behind the fact that the
complex Hessian of `quadWeight` is `K·δ_{ij}`. -/
theorem fderiv_quadWeight {n : ℕ} (K : ℝ) (z v : Cn n) :
    fderiv ℝ (quadWeight n K) z v = 2 * K * inner ℝ z v := by
  change fderiv ℝ (fun y : Cn n => K * ‖y‖ ^ 2) z v = 2 * K * inner ℝ z v
  have h := (hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_mul K
  rw [h.fderiv]
  simp only [smul_apply, innerSL_apply_apply]
  ring

end Work.Hormander.Weights
