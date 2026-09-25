import Mathlib.Analysis.Complex.Norm

namespace Commons.Analysis.Complex

/-- For a complex number `u` on the critical line `Re u = 1/2`, the two
reciprocals `1/(1-u)` and `1/u` sum to `(‖u‖²)⁻¹`. Indeed `1 - u = conj u`,
so `u·(1-u) = ‖u‖²`, and the sum collapses to `1/(u(1-u))`. -/
theorem inv_one_sub_add_inv_eq_inv_normSq {u : ℂ} (hu : u.re = 1 / 2) :
    1 / (1 - u) + 1 / u = ((‖u‖ ^ 2)⁻¹ : ℂ) := by
  -- `u ≠ 0` and `1 - u ≠ 0`, both read off from the real part.
  have hu0 : u ≠ 0 := by
    intro h
    have h0 : u.re = 0 := by rw [h]; simp
    rw [hu] at h0
    norm_num at h0
  have h1u0 : (1 : ℂ) - u ≠ 0 := by
    intro h
    have h0 : ((1 : ℂ) - u).re = 0 := by rw [h]; simp
    rw [Complex.sub_re, Complex.one_re] at h0
    rw [hu] at h0
    norm_num at h0
  -- On the critical line, `1 - u` is the complex conjugate of `u`.
  have hconj : (1 : ℂ) - u = (starRingEnd ℂ) u := by
    apply Complex.ext
    · rw [Complex.sub_re, Complex.one_re, Complex.conj_re, hu]; norm_num
    · rw [Complex.sub_im, Complex.conj_im, Complex.one_im]
      ring
  -- Hence `u * (1 - u) = u * conj u = ‖u‖²`.
  have hkey : u * (1 - u) = ((‖u‖ ^ 2 : ℝ) : ℂ) := by
    rw [hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  -- Combine the two fractions over the common denominator `u * (1 - u)`.
  have hsum : 1 / (1 - u) + 1 / u = 1 / (u * (1 - u)) := by
    field_simp
    ring
  rw [hsum, hkey, one_div]
  push_cast
  rfl

end Commons.Analysis.Complex