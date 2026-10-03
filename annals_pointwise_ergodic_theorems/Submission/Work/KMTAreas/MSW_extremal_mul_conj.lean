import Mathlib

namespace Work.KMTAreas

theorem MSW_extremal_mul_conj {q : ℝ} (hq : 1 < q) (z : ℂ) :
    z * starRingEnd ℂ (z * Complex.ofReal ((‖z‖ : ℝ) ^ (q - 2))) = Complex.ofReal ((‖z‖ : ℝ) ^ q) := by
  have hr : 0 ≤ (‖z‖ : ℝ) := norm_nonneg z
  have hqne : q ≠ 0 := by linarith
  by_cases h0 : (‖z‖ : ℝ) = 0
  · have hz : z = 0 := norm_eq_zero.mp h0
    rw [hz]
    simp [Real.zero_rpow hqne]
  · have hpos : 0 < (‖z‖ : ℝ) := lt_of_le_of_ne hr (Ne.symm h0)
    rw [map_mul, Complex.conj_ofReal, ← mul_assoc, Complex.mul_conj,
      Complex.normSq_eq_norm_sq, ← Complex.ofReal_mul]
    congr 1
    rw [← Real.rpow_natCast (‖z‖) 2, ← Real.rpow_add hpos]
    congr 1
    ring

end Work.KMTAreas
