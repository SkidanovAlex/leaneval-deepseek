import Mathlib

namespace Work.FIArea5.S16Hecke

/-- Rewrites the product of the two powers of `1/(B*v)` (one with a complex exponent
`t - 1`, one with the *integer* exponent `-(m:ℤ) - 1`) together, using that the base is a
positive real number so that `Complex.cpow_add` applies after converting the integer
power `zpow` to a complex power via `Complex.cpow_intCast`; hence it is a "scaling
identity" for the change of variables `v ↦ 1/(B*v)`. -/
theorem cpow_inv_scale (B : ℝ) (hB : 0 < B) (m : ℕ) (t : ℂ) (v : ℝ) (hv : 0 < v) :
    (((1 / (B * v) : ℝ)) : ℂ) ^ (t - 1) * (((1 / (B * v) : ℝ)) : ℂ) ^ (-(m : ℤ) - 1)
        * (((B * v ^ 2)⁻¹ : ℝ) : ℂ)
      = (B : ℂ) ^ ((m : ℂ) + 1 - t) * ((v : ℂ) ^ ((m : ℂ) - t)) := by
  have hBv : (0:ℝ) < B * v := mul_pos hB hv
  have hA : ((1/(B*v) : ℝ) : ℂ) = ((B*v : ℝ) : ℂ)⁻¹ := by rw [one_div, Complex.ofReal_inv]
  have hA_ne : ((1/(B*v) : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact ne_of_gt (one_div_pos.mpr hBv)
  have hB_ne : (B:ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; exact ne_of_gt hB
  have hv_ne : (v:ℂ) ≠ 0 := by rw [Complex.ofReal_ne_zero]; exact ne_of_gt hv
  -- Combine the two powers of `1/(B*v)`: the second exponent is an integer, so first
  -- convert the `zpow` into a `cpow`.
  have step1 : (((1/(B*v) : ℝ)) : ℂ) ^ (t - 1) * (((1/(B*v) : ℝ)) : ℂ) ^ (-(m:ℤ)-1)
      = (((1/(B*v) : ℝ)) : ℂ) ^ (t - (m:ℂ) - 2) := by
    rw [← Complex.cpow_intCast]
    rw [← Complex.cpow_add]
    · congr 1; push_cast; ring
    · exact hA_ne
  -- Replace the base `1/(B*v)` by the inverse of `B*v`.
  have step2 : (((1/(B*v) : ℝ)) : ℂ) ^ (t - (m:ℂ) - 2) = ((B*v : ℝ) : ℂ) ^ ((m:ℂ) + 2 - t) := by
    rw [hA, Complex.inv_cpow_ofReal_nonneg hBv.le, ← Complex.cpow_neg]
    congr 1
    ring
  -- Split the power of the (positive) product `B*v`.
  have step3 : ((B*v : ℝ) : ℂ) ^ ((m:ℂ) + 2 - t) = (B:ℂ) ^ ((m:ℂ) + 2 - t) * (v:ℂ) ^ ((m:ℂ) + 2 - t) := by
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hB.le hv.le]
  -- Expand the third factor.
  have step4 : (((B * v^2)⁻¹ : ℝ) : ℂ) = (B:ℂ)⁻¹ * ((v:ℂ)^2)⁻¹ := by
    rw [Complex.ofReal_inv, Complex.ofReal_mul, Complex.ofReal_pow, mul_inv]
  rw [step1, step2, step3, step4, mul_mul_mul_comm,
      ← Complex.cpow_neg_one, ← Complex.cpow_natCast, ← Complex.cpow_neg]
  rw [← Complex.cpow_add _ _ hB_ne, ← Complex.cpow_add _ _ hv_ne]
  congr 1
  · congr 1; ring
  · congr 1; ring

end Work.FIArea5.S16Hecke
