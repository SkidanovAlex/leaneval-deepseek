import Mathlib
import Submission.Work.Pert.Ksub2.Setup

namespace Work.Pert.Ksub2

/-- Derivative of the "model" map `v ↦ v / (1 + τ₀ v · hF (τ₀ v))`, where `τ₀ v = -1/v`.

Since `τ₀'(w) = 1/w² = τ₀(w)²` and `w = -1/τ₀(w)`, the chain rule plus the quotient rule give
the stated closed form.  The hypotheses are exactly the ones making the expression
differentiable at `w`: `w ≠ 0` (so that `τ₀` is differentiable there), `hF` differentiable at
`τ₀ w`, and nonvanishing of the denominator. -/
theorem deriv_div_tau0_model {hF : ℂ → ℂ} {w : ℂ} (hw : w ≠ 0)
    (hd : DifferentiableAt ℂ hF (MandelDim.tau0 w))
    (hden : 1 + MandelDim.tau0 w * hF (MandelDim.tau0 w) ≠ 0) :
    deriv (fun v : ℂ => v / (1 + MandelDim.tau0 v * hF (MandelDim.tau0 v))) w
      = 1 + MandelDim.tau0 w ^ 2 *
          (deriv hF (MandelDim.tau0 w) - hF (MandelDim.tau0 w) ^ 2) /
          (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) ^ 2 := by
  -- `τ₀ v = -1/v`, so `τ₀'(w) = 1/w²`.
  have hτd : HasDerivAt MandelDim.tau0 (1 / w ^ 2) w := by
    have h : MandelDim.tau0 = fun y : ℂ => (-1 : ℂ) * y⁻¹ := by
      funext y; simp [MandelDim.tau0, div_eq_mul_inv]
    rw [h]
    simpa [one_div] using (hasDerivAt_inv hw).const_mul (-1)
  -- chain rule: derivative of `v ↦ hF (τ₀ v)`.
  have hFd : HasDerivAt hF (deriv hF (MandelDim.tau0 w)) (MandelDim.tau0 w) := hd.hasDerivAt
  have hFt : HasDerivAt (fun v : ℂ => hF (MandelDim.tau0 v))
      (deriv hF (MandelDim.tau0 w) * (1 / w ^ 2)) w := hFd.comp w hτd
  -- product and quotient rules.
  have hprod : HasDerivAt (fun v : ℂ => MandelDim.tau0 v * hF (MandelDim.tau0 v))
      ((1 / w ^ 2) * hF (MandelDim.tau0 w)
        + MandelDim.tau0 w * (deriv hF (MandelDim.tau0 w) * (1 / w ^ 2))) w :=
    hτd.mul hFt
  have hden' : HasDerivAt (fun v : ℂ => 1 + MandelDim.tau0 v * hF (MandelDim.tau0 v))
      ((1 / w ^ 2) * hF (MandelDim.tau0 w)
        + MandelDim.tau0 w * (deriv hF (MandelDim.tau0 w) * (1 / w ^ 2))) w :=
    hprod.const_add 1
  have hquot : HasDerivAt (fun v : ℂ => v / (1 + MandelDim.tau0 v * hF (MandelDim.tau0 v)))
      ((1 * (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w))
        - w * ((1 / w ^ 2) * hF (MandelDim.tau0 w)
          + MandelDim.tau0 w * (deriv hF (MandelDim.tau0 w) * (1 / w ^ 2))))
        / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) ^ 2) w :=
    (hasDerivAt_id w).div hden' hden
  rw [hquot.deriv]
  -- the remaining identity is algebraic: clear `τ₀ w = -1/w` and the two denominators.
  rw [show MandelDim.tau0 w = -1 / w from rfl]
  have hden2 : 1 + (-1 / w) * hF (-1 / w) ≠ 0 := by
    simpa [MandelDim.tau0, one_div] using hden
  have hD2 : (1 + (-1 / w) * hF (-1 / w)) ^ 2 ≠ 0 := pow_ne_zero 2 hden2
  rw [div_eq_iff hD2, add_mul, one_mul, div_mul_cancel₀ _ hD2]
  field_simp
  ring

end Work.Pert.Ksub2
