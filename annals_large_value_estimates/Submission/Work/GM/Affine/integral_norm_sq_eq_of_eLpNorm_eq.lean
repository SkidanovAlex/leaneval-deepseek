import Mathlib

namespace Work.GM.Affine

theorem integral_norm_sq_eq_of_eLpNorm_eq (g F : ℝ → ℂ)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.volume) (hF : MeasureTheory.MemLp F 2 MeasureTheory.volume)
    (h : MeasureTheory.eLpNorm g 2 MeasureTheory.volume = MeasureTheory.eLpNorm F 2 MeasureTheory.volume) :
    ∫ x, ‖g x‖ ^ 2 = ∫ x, ‖F x‖ ^ 2 := by
  have hA : 0 ≤ ∫ x, ‖g x‖ ^ 2 := MeasureTheory.integral_nonneg fun x => by positivity
  have hB : 0 ≤ ∫ x, ‖F x‖ ^ 2 := MeasureTheory.integral_nonneg fun x => by positivity
  rw [hg.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num),
      hF.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at h
  simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at h
  have h' : (∫ x, ‖g x‖ ^ 2) ^ (2 : ℝ)⁻¹ = (∫ x, ‖F x‖ ^ 2) ^ (2 : ℝ)⁻¹ :=
    (ENNReal.ofReal_eq_ofReal_iff (Real.rpow_nonneg hA _) (Real.rpow_nonneg hB _)).mp h
  rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h'
  exact (Real.sqrt_inj hA hB).mp h'

end Work.GM.Affine
