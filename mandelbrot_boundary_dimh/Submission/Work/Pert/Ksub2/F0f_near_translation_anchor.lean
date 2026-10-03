import Mathlib
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.Ksub2.anchor_scale_close
import Submission.Work.Pert.Ksub2.F0f_eq_model
import Submission.Work.Pert.Ksub2.hF_ratio_close_of_small
import Submission.Work.Pert.Ksub2.anchor_ball_tau0_norm_le
import Submission.Work.Pert.Ksub2.differentiableAt_F0f_of_local
import Submission.Work.Interfaces.Parabolic

namespace Work.Pert.Ksub2

open Complex Metric MandelDim

theorem F0f_near_translation_anchor {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {hF : ℂ → ℂ} {ρ D : ℝ} (hρ : 0 < ρ) (hρ8 : ρ ≤ 1 / 8)
    (hroom : Metric.closedBall (0 : ℂ) ρ ⊆ D₀)
    (hfe : ∀ z ∈ Metric.ball (0 : ℂ) ρ, f₀ z = z + z ^ 2 * hF z)
    (hhF0 : hF 0 = 1)
    (hhFd : DifferentiableOn ℂ hF (Metric.ball (0 : ℂ) ρ)) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ, M₀ ≤ M →
      DifferentiableOn ℂ (Work.Pert.F0f f₀)
        (Metric.ball (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) (M / 40)) ∧
      ∀ w ∈ Metric.ball (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) (M / 40),
        ‖Work.Pert.F0f f₀ w - (w + 1)‖ < 1 / 4 := by
  obtain ⟨η, hηpos, hηρ, hη⟩ := hF_ratio_close_of_small hρ hhF0 hhFd
  obtain ⟨R, hRpos, hR⟩ := anchor_ball_tau0_norm_le d
  refine ⟨max R (max 1 (20 / (19 * η))), ?_, ?_⟩
  · positivity
  · intro M hM
    have hMR : R ≤ M := le_trans (le_max_left _ _) hM
    have hM1 : (1:ℝ) ≤ M :=
      le_trans (le_trans (le_max_left (1:ℝ) (20 / (19 * η))) (le_max_right R _)) hM
    have hMη : 20 / (19 * η) ≤ M :=
      le_trans (le_trans (le_max_right (1:ℝ) (20 / (19 * η))) (le_max_right R _)) hM
    have hMpos : 0 < M := lt_of_lt_of_le one_pos hM1
    have hηM : 20 / (19 * M) ≤ η := by
      have h1 : 20 ≤ M * (19 * η) := by
        have h19η : (0:ℝ) < 19 * η := by linarith
        exact (div_le_iff₀ h19η).mp hMη
      have h2 : 20 ≤ η * (19 * M) := by nlinarith [h1]
      have h19M : (0:ℝ) < 19 * M := by linarith
      exact (div_le_iff₀ h19M).mpr h2
    have hkey : ∀ w ∈ Metric.ball (Work.Pert.Xc d (((-M : ℝ)) : ℂ)) (M / 40),
        w ≠ 0 ∧ MandelDim.tau0 w ∈ Metric.ball (0:ℂ) ρ ∧
        1 + MandelDim.tau0 w * hF (MandelDim.tau0 w) ≠ 0 := by
      intro w hw
      obtain ⟨hw0, hwt⟩ := hR M hMR w hw
      have htη : ‖MandelDim.tau0 w‖ ≤ η := le_trans hwt hηM
      have htρ : MandelDim.tau0 w ∈ Metric.ball (0:ℂ) ρ := by
        rw [Metric.mem_ball, dist_zero_right]
        linarith
      exact ⟨hw0, htρ, (hη _ htη).1⟩
    constructor
    · intro w hw
      obtain ⟨hw0, htρ, hden⟩ := hkey w hw
      exact (differentiableAt_F0f_of_local hfe hhFd hw0 htρ hden).differentiableWithinAt
    · intro w hw
      obtain ⟨hw0, htρ, hden⟩ := hkey w hw
      obtain ⟨hw0', hwt⟩ := hR M hMR w hw
      have htη : ‖MandelDim.tau0 w‖ ≤ η := le_trans hwt hηM
      have hclose := (hη _ htη).2
      have hmodel := F0f_eq_model hw0 (hfe _ htρ) hden
      rw [hmodel]
      have hrewrite : w + hF (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) -
          (w + 1)
          = hF (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hF (MandelDim.tau0 w)) - 1 := by
        ring
      rw [hrewrite]
      exact hclose

end Work.Pert.Ksub2
