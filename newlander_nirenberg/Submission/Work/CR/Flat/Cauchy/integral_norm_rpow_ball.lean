import Mathlib
import Submission.Work.CR.Flat.Cauchy

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal
open MeasureTheory Set

/-- The integral of `‖w‖ ^ s` over the disc of radius `ρ > 0` in `ℂ` (with `ℂ`
identified with `ℝ²`, so `volume` is Lebesgue measure): since
`∫_{‖w‖<ρ} ‖w‖^s = ∫_0^ρ ∫_0^{2π} r^{s+1} dθ dr`, the value is
`2 * π * ρ ^ (s+2) / (s+2)`.  For `s > -2` this is finite, which is the range
needed for the Cauchy kernel and its square. -/
theorem integral_norm_rpow_ball {ρ s : ℝ} (hρ : 0 < ρ) (hs : -2 < s) :
    ∫ w in Metric.ball (0 : ℂ) ρ, ‖w‖ ^ s = 2 * Real.pi * ρ ^ (s + 2) / (s + 2) := by
  -- Write the disc integral as the full-space integral of a radial function.
  set g : ℝ → ℝ := fun y => if y < ρ then y ^ s else 0 with hg
  have step1 : ∫ w in Metric.ball (0 : ℂ) ρ, ‖w‖ ^ s = ∫ w : ℂ, g ‖w‖ := by
    have A : ∫ w in Metric.ball (0 : ℂ) ρ, ‖w‖ ^ s
        = ∫ w in Metric.ball (0 : ℂ) ρ, g ‖w‖ := by
      apply setIntegral_congr_fun measurableSet_ball
      intro w hw
      show ‖w‖ ^ s = g ‖w‖
      rw [hg]
      show ‖w‖ ^ s = (if ‖w‖ < ρ then ‖w‖ ^ s else 0)
      rw [ite_eq_left (mem_ball_zero_iff.mp hw)]
    rw [A]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    show g ‖w‖ = 0
    rw [hg]
    show (if ‖w‖ < ρ then ‖w‖ ^ s else 0) = 0
    rw [ite_eq_right]
    exact fun h => hw (mem_ball_zero_iff.mpr h)
  -- Compute the one dimensional integral produced by polar coordinates.
  have hI : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) • g y
      = ρ ^ (s + 2) / (s + 2) := by
    have P : ∀ y ∈ Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) • g y
        = (Ioo (0 : ℝ) ρ).indicator (fun y => y ^ (s + 1)) y := by
      intro y hy
      have hfin : Module.finrank ℝ ℂ - 1 = 1 := by
        rw [Complex.finrank_real_complex]
      rw [hfin, pow_one, smul_eq_mul]
      show y * (if y < ρ then y ^ s else 0)
        = (Ioo (0 : ℝ) ρ).indicator (fun y => y ^ (s + 1)) y
      by_cases h : y < ρ
      · rw [ite_eq_left h, Set.indicator_of_mem (show y ∈ Ioo (0 : ℝ) ρ from ⟨hy, h⟩)]
        have h2 : y * y ^ s = y ^ (s + 1) := by
          nth_rewrite 1 [← Real.rpow_one y]
          rw [← Real.rpow_add hy (1 : ℝ) s]
          congr 1
          ring
        rw [h2]
      · rw [ite_eq_right h, mul_zero, Set.indicator_of_notMem (fun hc => h hc.2)]
    have e1 : ∫ y in Ioi (0 : ℝ), y ^ (Module.finrank ℝ ℂ - 1) • g y
        = ∫ y in Ioo (0 : ℝ) ρ, y ^ (s + 1) := by
      rw [setIntegral_congr_fun measurableSet_Ioi P]
      rw [setIntegral_indicator measurableSet_Ioo]
      rw [show Ioi (0 : ℝ) ∩ Ioo (0 : ℝ) ρ = Ioo (0 : ℝ) ρ from by
        ext y; simp [Set.mem_Ioi, Set.mem_Ioo]]
    have e2 : ∫ y in Ioo (0 : ℝ) ρ, y ^ (s + 1) = ρ ^ (s + 2) / (s + 2) := by
      rw [← integral_Ioc_eq_integral_Ioo]
      rw [← intervalIntegral.integral_of_le hρ.le]
      rw [integral_rpow (Or.inl (by linarith))]
      rw [Real.zero_rpow (by linarith : s + 1 + 1 ≠ 0), sub_zero]
      ring_nf
    rw [e1, e2]
  rw [step1, MeasureTheory.integral_fun_norm_addHaar]
  rw [hI, Complex.finrank_real_complex]
  have hreal : (volume : Measure ℂ).real (Metric.ball (0 : ℂ) 1) = Real.pi := by
    simp [MeasureTheory.Measure.real, Complex.volume_ball]
  rw [hreal]
  simp only [nsmul_eq_mul, smul_eq_mul]
  ring

end Work.CR.Flat.Cauchy
