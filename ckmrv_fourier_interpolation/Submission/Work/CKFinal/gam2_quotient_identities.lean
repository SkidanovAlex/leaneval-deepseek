import Mathlib

namespace Work.CKFinal

theorem gam2_quotient_identities (z : ℂ) (hz : (1 : ℂ) + z ≠ 0) :
    (z / (1 + z)).re = (z.re + (z.re ^ 2 + z.im ^ 2)) / ((1 + z.re) ^ 2 + z.im ^ 2) ∧
    ‖z / (1 + z) - 1 / 2‖ = ‖z - 1‖ / (2 * ‖1 + z‖) ∧
    ‖z / (1 + z) + 1 / 2‖ = ‖(3 : ℂ) * z + 1‖ / (2 * ‖1 + z‖) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Complex.div_re, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    ring
  · have h : z / (1 + z) - 1 / 2 = (z - 1) / (2 * (1 + z)) := by
      field_simp
      ring
    rw [h, Complex.norm_div, Complex.norm_mul, Complex.norm_ofNat]
  · have h : z / (1 + z) + 1 / 2 = ((3 : ℂ) * z + 1) / (2 * (1 + z)) := by
      field_simp
      ring
    rw [h, Complex.norm_div, Complex.norm_mul, Complex.norm_ofNat]

end Work.CKFinal
