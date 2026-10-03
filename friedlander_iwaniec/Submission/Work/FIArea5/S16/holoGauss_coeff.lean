import Mathlib

namespace Work.FIArea5.S16

/-- Coefficient identity for the holomorphic Gaussian built from the
Friedlander–Iwaniec theta-type series: the `m`-th coefficient of
`(I/(2π)) · (1/u) · exp(-(2π/u) z · ...)` rewrites as `(-I)^m u^{-(m+1)} z^m`. -/
theorem holoGauss_coeff {u : ℝ} (hu : 0 < u) (m : ℕ) (z : ℂ) :
    (Complex.I / (2 * Real.pi)) ^ m * (1 / (u : ℂ)) * (-(2 * (Real.pi : ℂ) / (u : ℂ) * z)) ^ m
      = (-Complex.I) ^ m * ((u : ℂ) ^ (m + 1))⁻¹ * z ^ m := by
  have huC : (u : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hu)
  -- The two power bases multiply to `-I * (z/u)`.
  have key : (Complex.I / (2 * Real.pi)) * (-(2 * (Real.pi : ℂ) / (u : ℂ) * z))
      = -Complex.I * (z / (u : ℂ)) := by
    field_simp
  -- Collect the two `m`-th powers into a single one.
  rw [show (Complex.I / (2 * Real.pi)) ^ m * (1 / (u : ℂ))
        * (-(2 * (Real.pi : ℂ) / (u : ℂ) * z)) ^ m
      = (1 / (u : ℂ))
        * ((Complex.I / (2 * Real.pi)) * (-(2 * (Real.pi : ℂ) / (u : ℂ) * z))) ^ m by
        rw [mul_pow]; ring,
    key, mul_pow, div_pow]
  -- Rewrite `(u^(m+1))⁻¹ = (u^m)⁻¹ * u⁻¹` and clear denominators.
  rw [show ((u : ℂ) ^ (m + 1))⁻¹ = ((u : ℂ) ^ m)⁻¹ * ((u : ℂ))⁻¹ by
        rw [pow_succ, mul_inv_rev]; ring]
  field_simp

end Work.FIArea5.S16
