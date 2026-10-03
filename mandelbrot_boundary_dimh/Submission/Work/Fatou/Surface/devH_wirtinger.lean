import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Surface.Core
import Submission.Work.Fatou.DevH.devH_deriv

namespace Work.Fatou.Surface

/-- The Wirtinger bounds for the unfolding `D.devH`: `|∂ devH| ≥ 15/16`, `∂ devH ≠ 0`, and
`|∂̄ devH| ≤ (1/15)·|∂ devH|` (the last one from `|∂̄| ≤ 1/32` and `(1/15)(15/16) = 1/16 ≥ 1/32`). -/
theorem devH_wirtinger (D : Work.Fatou.FatouData) :
    (∀ ζ : ℂ, (15 / 16 : ℝ) ≤ ‖MandelDim.dz D.devH ζ‖) ∧
      (∀ ζ : ℂ, MandelDim.dz D.devH ζ ≠ 0) ∧
      (∀ ζ : ℂ, ‖MandelDim.dzbar D.devH ζ‖ ≤ (1 / 15) * ‖MandelDim.dz D.devH ζ‖) := by
  obtain ⟨-, -, hdz, hdzbar⟩ := Work.Fatou.DevH.devH_deriv D.adm D.nt
  have hdz' : ∀ ζ : ℂ, ‖MandelDim.dz D.devH ζ - 1‖ ≤ (1 / 16 : ℝ) := fun ζ => hdz ζ
  have hdzbar' : ∀ ζ : ℂ, ‖MandelDim.dzbar D.devH ζ‖ ≤ (1 / 32 : ℝ) := fun ζ => hdzbar ζ
  -- `|∂ devH| ≥ 1 - 1/16 = 15/16` by the reverse triangle inequality.
  have key : ∀ ζ : ℂ, (15 / 16 : ℝ) ≤ ‖MandelDim.dz D.devH ζ‖ := by
    intro ζ
    have h := abs_norm_sub_norm_le (MandelDim.dz D.devH ζ) (1 : ℂ)
    rw [norm_one] at h
    have h1 : -((1 : ℝ) / 16) ≤ ‖MandelDim.dz D.devH ζ‖ - 1 :=
      (abs_le.mp (h.trans (hdz' ζ))).1
    linarith
  refine ⟨key, fun ζ hz => ?_, fun ζ => ?_⟩
  · have h := key ζ
    rw [hz, norm_zero] at h
    norm_num at h
  · have h1 : ‖MandelDim.dzbar D.devH ζ‖ ≤ (1 / 32 : ℝ) := hdzbar' ζ
    have h2 : (1 / 32 : ℝ) ≤ (1 / 15) * ‖MandelDim.dz D.devH ζ‖ := by
      have h3 : (15 / 16 : ℝ) ≤ ‖MandelDim.dz D.devH ζ‖ := key ζ
      have hmul := mul_le_mul_of_nonneg_left h3 (by norm_num : (0 : ℝ) ≤ 1 / 15)
      have he : (1 / 15) * (15 / 16) = (1 / 16 : ℝ) := by norm_num
      rw [he] at hmul
      linarith
    linarith

end Work.Fatou.Surface
