import Mathlib
import Submission.Work.BMF.triangle_fourier_pair

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open MeasureTheory
open scoped BigOperators

/-- The inverse Fourier transform of the tent function `τ x = max 0 (1 - |x|)` on `ℝ`:
`∫ x, τ x * exp (2πI x ξ) dx = sinc (π ξ)^2` (with `sinc 0 = 1`).

Proof route: `τ` is even and vanishes off `[-1,1]`, so the integral equals
`2 * ∫_0^1 (1-x) * cos (2π ξ x) dx`; on `0 < x < 1` the function
`x ↦ (1-x) * sin (a x)/a - cos (a x)/a^2` (with `a = 2πξ ≠ 0`) has derivative `(1-x) * cos (a x)`,
so `∫_0^1 (1-x) cos (a x) dx = (1 - cos a)/a^2`, and this rearranges to
`(sin (πξ)/(πξ))^2 = sinc (πξ)^2` using `1 - cos (2θ) = 2 sin θ ^ 2`. For `ξ = 0` the integral is
`∫_{-1}^1 (1 - |x|) dx = 1 = sinc 0 ^ 2`. -/
theorem tent_char_integral (ξ : ℝ) :
    ∫ x : ℝ, ((max 0 (1 - |x|) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (x * ξ))
      = (((Real.sinc (Real.pi * ξ)) ^ 2 : ℝ) : ℂ) := by
  -- The interval-integral form of the statement, proved independently.
  have htri := triangle_fourier_pair.1 ξ
  -- The integrand vanishes off `Ioc (-1) 1`: there `1 - |x| ≤ 0`.
  have hvan : ∀ x : ℝ, x ∉ Set.Ioc (-1 : ℝ) 1 →
      ((max 0 (1 - |x|) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (x * ξ)) = 0 := by
    intro x hx
    have hx' : x ≤ -1 ∨ 1 < x := by
      by_contra h
      rw [not_or, not_le, not_lt] at h
      exact hx ⟨h.1, h.2⟩
    have hmax : max 0 (1 - |x|) = (0 : ℝ) := by
      apply max_eq_left
      rcases hx' with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith
      · rw [abs_of_nonneg (by linarith)]; linarith
    rw [hmax]
    simp
  -- On `[-1,1]` the tent function is `1 - |x|`.
  have hcongr : ∫ x in (-1 : ℝ)..1,
        ((max 0 (1 - |x|) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (x * ξ))
      = ∫ x in (-1 : ℝ)..1, ((1 - |x| : ℝ) : ℂ) * eC (x * ξ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    have hmax : max 0 (1 - |x|) = (1 - |x| : ℝ) :=
      max_eq_right (by linarith [abs_le.mpr hx])
    show ((max 0 (1 - |x|) : ℝ) : ℂ) * Complex.exp (2 * Real.pi * Complex.I * (x * ξ))
        = ((1 - |x| : ℝ) : ℂ) * eC (x * ξ)
    rw [hmax]
    simp only [eC, Complex.ofReal_mul]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc (-1 : ℝ) 1) hvan]
  rw [← intervalIntegral.integral_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
  rw [hcongr, htri, Complex.ofReal_pow]

end Work.BMF
