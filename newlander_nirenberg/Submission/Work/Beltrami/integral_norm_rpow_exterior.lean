import Mathlib

namespace Work.Beltrami

open MeasureTheory
open scoped NNReal ENNReal

/-! ## The tail integral of a radial power -/

/-- The `s < -2` tail integral of a radial power over the exterior of a disc in `ℂ ≅ ℝ²`:
`∫_{a < ‖w‖} ‖w‖^s dA(w) = 2π a^{s+2} / (-(s+2))`. -/
theorem integral_norm_rpow_exterior {s a : ℝ} (hs : s < -2) (ha : 0 < a) :
    ∫ w in {w : ℂ | a < ‖w‖}, ‖w‖ ^ s
      = 2 * Real.pi * a ^ (s + 2) / (-(s + 2)) := by
  have hmeas : MeasurableSet {w : ℂ | a < ‖w‖} :=
    measurableSet_lt measurable_const continuous_norm.measurable
  set g : ℝ → ℝ := fun y => if a < y then y ^ s else 0 with hg
  have step1 : ∫ w in {w : ℂ | a < ‖w‖}, ‖w‖ ^ s = ∫ w : ℂ, g ‖w‖ := by
    rw [← integral_indicator hmeas]
    apply integral_congr_ae
    filter_upwards with w
    by_cases hw : w ∈ {w : ℂ | a < ‖w‖}
    · rw [Set.indicator_of_mem hw]; simp only [hg]
      rw [if_pos (by simpa only [Set.mem_ofPred_eq] using hw)]
    · rw [Set.indicator_of_notMem hw]; simp only [hg]
      rw [if_neg (by simpa only [Set.mem_ofPred_eq] using hw)]
  rw [step1, MeasureTheory.integral_fun_norm_addHaar]
  rw [Complex.finrank_real_complex]
  have hreal : (volume : Measure ℂ).real (Metric.ball (0 : ℂ) 1) = Real.pi := by
    simp [MeasureTheory.Measure.real, Complex.volume_ball]
  rw [hreal]
  have h1 : ∫ y in Set.Ioi (0:ℝ), y * g y = -(a ^ (s + 2) / (s + 2)) := by
    have hne : ∀ᵐ y ∂(volume : Measure ℝ), y ∈ Set.Ioi (0:ℝ) →
        y * g y = y * ((Set.Ioi a).indicator (fun y => y ^ s) y) := by
      filter_upwards with y _
      simp only [hg]
      by_cases h : a < y
      · rw [ite_eq_left h, Set.indicator_of_mem (Set.mem_Ioi.mpr h)]
      · rw [ite_eq_right h, Set.indicator_of_notMem (fun hc => h (Set.mem_Ioi.mp hc)), mul_zero]
    rw [setIntegral_congr_ae measurableSet_Ioi hne]
    rw [show (fun y : ℝ => y * (Set.Ioi a).indicator (fun y => y ^ s) y)
        = (Set.Ioi a).indicator (fun y => y * y ^ s) from by
      funext y
      rw [Set.indicator_apply, Set.indicator_apply]
      by_cases h : y ∈ Set.Ioi a <;> simp [h]]
    rw [setIntegral_indicator measurableSet_Ioi]
    rw [show Set.Ioi (0:ℝ) ∩ Set.Ioi a = Set.Ioi a from by
      ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi]
      exact ⟨fun h => h.2, fun h => ⟨ha.trans h, h⟩⟩]
    have hcongr : ∫ y in Set.Ioi a, y * y ^ s = ∫ y in Set.Ioi a, y ^ (s + 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      change y * y ^ s = y ^ (s + 1)
      have hy0 : 0 < y := ha.trans hy
      rw [Real.rpow_add hy0 s 1, Real.rpow_one, mul_comm]
    rw [hcongr]
    rw [integral_Ioi_rpow_of_lt (by linarith : s + 1 < -1) ha]
    rw [show s + 1 + 1 = s + 2 from by ring]
    ring_nf
  have h2 : ∀ y : ℝ, y ^ (2 - 1 : ℕ) • g y = y * g y := by
    intro y
    norm_num
  simp only [h2]
  rw [h1]
  simp only [smul_eq_mul, nsmul_eq_mul]
  rw [← div_neg]
  ring


end Work.Beltrami
