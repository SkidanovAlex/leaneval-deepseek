import Mathlib

namespace Work.ZeroFreeTables.P3

/-- Key algebraic kernel identity behind the Linnik zero-free region argument
(Heath-Brown 1992).  For `K : ℝ` and unit-modulus complex numbers `z₀`, `z₁`:
the quadratic kernel built out of `z₀, z₁` collapses to a perfect square times
`1 + z₀.re`. -/
theorem HbKernelIdentity (K : ℝ) (z₀ z₁ : ℂ) (h₀ : ‖z₀‖ = 1) (h₁ : ‖z₁‖ = 1) :
    (K ^ 2 + 1/2) * (1 + z₀.re) + K * ((z₁ / z₀).re + 2 * z₁.re + (z₁ * z₀).re)
        + (1/4) * ((z₁ ^ 2 / z₀).re + 2 * (z₁ ^ 2).re + (z₁ ^ 2 * z₀).re)
      = (1 + z₀.re) * (K + z₁.re) ^ 2 := by
  -- From ‖z₁‖ = 1 we get z₁.re ^ 2 + z₁.im ^ 2 = 1.
  have hns₁ : z₁.re ^ 2 + z₁.im ^ 2 = 1 := by
    have h := Complex.normSq_eq_norm_sq z₁
    rw [Complex.normSq_apply, h₁] at h
    norm_num at h
    nlinarith [h]
  -- Since ‖z₀‖ = 1, z₀⁻¹ = conj z₀; replace both divisions by this, then
  -- expand every real part into coordinates.
  simp only [div_eq_mul_inv, Complex.inv_eq_conj h₀]
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, pow_two]
  -- What remains is a polynomial identity over ℝ, closing with `hns₁`.
  linear_combination (-(1/2) * (1 + z₀.re)) * hns₁

end Work.ZeroFreeTables.P3
