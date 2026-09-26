import Mathlib
import Submission.Work.BoxShrink.Bubble.standard_counterexample

open LeanEval.KnotTheory.PardonDistortion

namespace Work.BoxShrink.Bubble

/-! ## Coordinates of the longitude curve at meridian parameter `π` -/

private lemma lon_pi_zero (t : ℝ) :
    (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi) t 0 = Real.cos t := by
  rw [Work.CoreTopology.longitudeCurve_apply, Work.CoreTopology.standard_psi,
    Work.CoreTopology.torusMap_apply_zero, Real.cos_pi]
  ring

private lemma lon_pi_one (t : ℝ) :
    (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi) t 1 = Real.sin t := by
  rw [Work.CoreTopology.longitudeCurve_apply, Work.CoreTopology.standard_psi,
    Work.CoreTopology.torusMap_apply_one, Real.cos_pi]
  ring

private lemma lon_pi_two (t : ℝ) :
    (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi) t 2 = 0 := by
  rw [Work.CoreTopology.longitudeCurve_apply, Work.CoreTopology.standard_psi,
    Work.CoreTopology.torusMap_apply_two, Real.sin_pi]

/-- The longitude curve at meridian parameter `π` (the unit circle `{(cos t, sin t, 0)}`) lies in
the lower half-region of the box `PBox s 0 (swap 1 2)` for every `s ≥ 5/2` and every `u > 1`. -/
theorem longitude_mem_lowerRegion_swap (s : ℝ) (hs : 5 / 2 ≤ s) (u : ℝ) (hu : 1 < u) :
    ∀ t : ℝ, (Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi) t ∈
      Work.BoxShrink.Core.lowerRegion Work.CoreTopology.standard s 0
        (Equiv.swap (1 : Fin 3) 2) u := by
  intro t
  rw [Work.BoxShrink.Core.mem_lowerRegion]
  refine ⟨(Work.CoreTopology.longitudeCurve Work.CoreTopology.standard Real.pi).mem t, ?_, ?_⟩
  · rw [cex_mem_PBox]
    refine ⟨?_, ?_, ?_⟩
    · rw [lon_pi_zero]
      have h1 : |Real.cos t| ≤ 1 := Real.abs_cos_le_one t
      linarith
    · rw [lon_pi_two, abs_zero]
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (1 / 3 : ℝ) := by positivity
      nlinarith
    · rw [lon_pi_one]
      have h1 : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
      have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 / 3 : ℝ) := Submission.one_le_rpow_two_thirds
      nlinarith
  · have hzero : (0 : R3) 1 = 0 := by simp
    rw [cex_swap_two, hzero, lon_pi_one]
    have h1 : Real.sin t ≤ 1 := Real.sin_le_one t
    linarith

end Work.BoxShrink.Bubble
