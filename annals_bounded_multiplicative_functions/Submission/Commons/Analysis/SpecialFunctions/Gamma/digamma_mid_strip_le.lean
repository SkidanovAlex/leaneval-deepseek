import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_vertical_bound
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_le
import Submission.Commons.Analysis.SpecialFunctions.Gamma.log_z_half_inv_strip_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex
open scoped Real
set_option autoImplicit false
noncomputable section

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- Tightened digamma bound on a mid strip (no real-axis-pole danger, small constant):
`‖digamma (x + y·I)‖ ≤ log (2 + |y|) + 2` for `1/2 ≤ x ≤ 8` and all real `y`.

Proof decomposition (`z = x + y·I`, with `Re z ≥ 1/2`, so `z` and its integer shifts stay in the
right half-plane):

1. Two-term Stirling-type remainder bound, published as
   `Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_le`:
   `‖ψ(z) − log z + 1/(2z)‖ ≤ 1/2` (Binet-formula proof, `|y|`-independent).
2. Logarithmic term bound, published as
   `Commons.Analysis.SpecialFunctions.Gamma.log_z_half_inv_strip_le`:
   `‖log z‖ + 1/(2·‖z‖) ≤ log (2 + |y|) + 3/2`.

Then by the triangle inequality and `‖2⁻¹·z⁻¹‖ = (1/2)·‖z⁻¹‖`:

`‖ψ(z)‖ ≤ ‖ψ(z) − log z + 1/(2z)‖ + ‖log z‖ + 1/(2‖z‖) ≤ 1/2 + log(2+|y|) + 3/2
       = log (2 + |y|) + 2`.

The constant `2` is achievable because the real axis maximum of `|digamma x| − log 2` on
`x ∈ [1/2, 8]` is below `2` and the logarithmic growth gives no larger excess. -/
theorem digamma_mid_strip_le (x y : ℝ) (hx1 : (1 : ℝ) / 2 ≤ x) (hx2 : x ≤ 8) :
    ‖Complex.digamma ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤ Real.log (2 + |y|) + 2 := by
  let z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
  have hA := digamma_logRem_le x y hx1 hx2
  have hB := log_z_half_inv_strip_le x y hx1 hx2
  have hnorm_mul : ‖(((2 : ℂ)⁻¹) * z⁻¹)‖ ≤ ((1 : ℝ) / 2) * ‖z⁻¹‖ := by
    rw [norm_mul]
    norm_num
  have h1 : ‖Complex.digamma z‖ ≤
      ‖Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹‖ +
        ‖Complex.log z - ((2 : ℂ)⁻¹) * z⁻¹‖ := by
    calc
      ‖Complex.digamma z‖
          = ‖(Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹) +
              (Complex.log z - ((2 : ℂ)⁻¹) * z⁻¹)‖ := by
            congr 1
            abel
      _ ≤ ‖Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹‖ +
            ‖Complex.log z - ((2 : ℂ)⁻¹) * z⁻¹‖ := by
            exact norm_add_le _ _
  have h2 : ‖Complex.log z - ((2 : ℂ)⁻¹) * z⁻¹‖ ≤ ‖Complex.log z‖ +
      ((1 : ℝ) / 2) * ‖z⁻¹‖ := by
    calc
      ‖Complex.log z - ((2 : ℂ)⁻¹) * z⁻¹‖ ≤ ‖Complex.log z‖ + ‖((2 : ℂ)⁻¹) * z⁻¹‖ := by
        exact norm_sub_le _ _
      _ ≤ ‖Complex.log z‖ + ((1 : ℝ) / 2) * ‖z⁻¹‖ := by
        simpa [add_comm] using (add_le_add_left hnorm_mul ‖Complex.log z‖)
  have h3 : ‖Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹‖ ≤ (1 : ℝ) / 2 := by
    simpa [z] using hA
  have h4 : ‖Complex.log z‖ + ((1 : ℝ) / 2) * ‖z⁻¹‖ ≤ Real.log (2 + |y|) + (3 : ℝ) / 2 := by
    simpa [z] using hB
  have hstep2 : ‖Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹‖ +
        ‖Complex.log z - ((2 : ℂ)⁻¹) * z⁻¹‖ ≤
      ‖Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹‖ +
        (‖Complex.log z‖ + ((1 : ℝ) / 2) * ‖z⁻¹‖) := by
    simpa [add_comm] using
      (add_le_add_left h2 (‖Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹‖))
  have hfinal : ‖Complex.digamma z‖ ≤ Real.log (2 + |y|) + 2 := by
    calc
      ‖Complex.digamma z‖ ≤ ‖Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹‖ +
          ‖Complex.log z - ((2 : ℂ)⁻¹) * z⁻¹‖ := h1
      _ ≤ ‖Complex.digamma z - Complex.log z + ((2 : ℂ)⁻¹) * z⁻¹‖ +
          (‖Complex.log z‖ + ((1 : ℝ) / 2) * ‖z⁻¹‖) := hstep2
      _ ≤ (1 : ℝ) / 2 + (Real.log (2 + |y|) + (3 : ℝ) / 2) := by
            exact add_le_add h3 h4
      _ ≤ Real.log (2 + |y|) + 2 := by
            have hlog : 0 ≤ Real.log (2 + |y|) := Real.log_nonneg (by linarith [abs_nonneg y])
            nlinarith
  simpa [z] using hfinal

end Commons.Analysis.SpecialFunctions.Gamma
