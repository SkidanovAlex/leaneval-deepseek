import Mathlib
import Submission.Commons.Analysis.Real.integral_poisson_hilbert_kernel
import Submission.Commons.Analysis.Real.poissonExtension_eq_integral_conjugate
import Submission.Commons.Analysis.Real.abs_integral_poisson_mul_hilbert_le
import Submission.Commons.MeasureTheory.Integral.integral_poisson_kernel
import Submission.Commons.MeasureTheory.Integral.abs_integral_poisson_le

set_option autoImplicit false

open Real MeasureTheory Set

namespace Commons.Analysis.Real

/-- **Poisson extension vs. Hilbert transform of the derivative.**

If `φ` is `C²` with compact support and the Hilbert-type transform of `deriv φ`,
`x ↦ (1/π) ∫_0^∞ (φ'(x+t) - φ'(x-t))/t dt`, is bounded by `C₁`, then the Poisson
extension of `φ` at the origin differs from `φ 0` by at most `σ * C₁`:

`|(1/π) ∫_ℝ φ t * σ/(σ²+t²) dt - φ 0| ≤ σ * C₁`.

The proof factors the difference of the Poisson extension and `φ 0` as the integral of the
conjugate-Poisson (Hilbert) transform of `φ'` over the vertical scale `s ∈ (0, σ)`,
`poissonExtension_eq_integral_conjugate`; the integrand is bounded by `C₁` for every scale by
`abs_integral_poisson_mul_hilbert_le`, whence the interval-integral bound. -/
theorem abs_poissonExtension_sub_le {φ : ℝ → ℝ} {C₁ : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hc : HasCompactSupport φ)
    (hH : ∀ x : ℝ, |(1 / π) * ∫ t in Set.Ioi (0 : ℝ),
      (deriv φ (x + t) - deriv φ (x - t)) / t| ≤ C₁) :
    ∀ σ : ℝ, 0 < σ →
      |(1 / π) * (∫ t : ℝ, φ t * (σ / (σ ^ 2 + t ^ 2))) - φ 0| ≤ σ * C₁ := by
  intro σ hσ
  -- Rewrite the difference as an integral over the scale `s ∈ (0, σ)`.
  rw [poissonExtension_eq_integral_conjugate hφ hc hσ]
  -- Bound the interval integral by `C₁ * |σ - 0| = σ * C₁`.
  have hkey := intervalIntegral.norm_integral_le_of_norm_le_const (C := C₁) (by
    intro s hs
    have hs' : s ∈ Set.Ioc (0 : ℝ) σ := by
      rw [Set.uIoc_of_le hσ.le] at hs
      exact hs
    rw [Real.norm_eq_abs]
    exact abs_integral_poisson_mul_hilbert_le hφ hc hH hs'.1)
  rw [Real.norm_eq_abs] at hkey
  refine le_trans hkey ?_
  rw [sub_zero, abs_of_pos hσ]
  exact le_of_eq (mul_comm C₁ σ)

end Commons.Analysis.Real
