import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The Fourier (power-series) expansion of the logarithm of the distance from `1` to the point
`r·e^{iθ}` of modulus `r < 1`:
`log ‖r·e^{iθ} - 1‖ = -∑_{k≥1} (r^k / k) · cos(kθ)`. -/
theorem log_norm_exp_sub_one (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    Real.log ‖(r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) - 1‖
      = -∑' k : ℕ, (r ^ (k + 1) / (k + 1)) * Real.cos ((k + 1) * θ) := by
  set z : ℂ := (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ)) with hzdef
  have hw : Complex.exp (Complex.I * (θ : ℂ)) = Complex.exp ((θ : ℂ) * Complex.I) := by
    congr 1; ring
  have hznorm : ‖z‖ = r := by
    rw [hzdef, norm_mul, Complex.norm_of_nonneg hr0, hw, Complex.norm_exp_ofReal_mul_I, mul_one]
  have hzlt : ‖z‖ < 1 := by rw [hznorm]; exact hr1
  have hsum : HasSum (fun n : ℕ => z ^ (n + 1) / (n + 1)) (-Complex.log (1 - z)) :=
    Complex.hasSum_taylorSeries_neg_log' hzlt
  have htsum := (Complex.hasSum_re hsum).tsum_eq
  have hnegr : (-Complex.log (1 - z)).re = -Real.log ‖z - 1‖ := by
    rw [Complex.neg_re, Complex.log_re, norm_sub_rev]
  have hpoint : ∀ n : ℕ, (z ^ (n + 1) / (n + 1)).re
      = (r ^ (n + 1) / (n + 1)) * Real.cos ((n + 1) * θ) := by
    intro n
    have hzpow : z ^ (n + 1) = ((r ^ (n + 1) : ℝ) : ℂ) *
        Complex.exp (((n + 1 : ℕ) : ℂ) * (Complex.I * (θ : ℂ))) := by
      rw [hzdef, mul_pow, ← Complex.ofReal_pow r (n + 1), ← Complex.exp_nat_mul]
    rw [hzpow, show (↑n + 1 : ℂ) = ((n + 1 : ℕ) : ℂ) from (Nat.cast_add_one n).symm,
      Complex.div_natCast_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [Complex.exp_re]
    have h1 : ((((n + 1 : ℕ) : ℂ) * (Complex.I * (θ : ℂ)))).re = 0 := by
      rw [Complex.mul_re]; simp
    have h2 : ((((n + 1 : ℕ) : ℂ) * (Complex.I * (θ : ℂ)))).im = (n + 1) * θ := by
      rw [Complex.mul_im]; simp
    rw [h1, h2, Real.exp_zero]
    push_cast
    ring
  have step1 : Real.log ‖z - 1‖ = -((-Complex.log (1 - z)).re) := by
    rw [hnegr, neg_neg]
  rw [step1, ← htsum]
  congr 1
  exact tsum_congr hpoint

end Work.BW
