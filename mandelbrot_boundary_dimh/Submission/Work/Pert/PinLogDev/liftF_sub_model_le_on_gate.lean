import Mathlib
import Submission.Work.Pert.PinLogDev.liftF_sub_model_le_pointwise_wide
import Submission.Work.Pert.Ksub2.F0f_eq_model
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Interfaces.Fatou

namespace Work.Pert.PinLogDev

theorem liftF_sub_model_le_on_gate {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {u hFm : ℂ → ℂ} {σ α : ℂ} {Dm ρm δ₂ : ℝ}
    (hρm : 0 < ρm) (hρm4 : ρm ≤ 1 / 4) (hDm : 0 ≤ Dm)
    (hhFm0 : hFm 0 = 1)
    (hhFmd : DifferentiableOn ℂ hFm (Metric.ball (0 : ℂ) ρm))
    (hhFml : ∀ z ∈ Metric.ball (0 : ℂ) ρm, ‖deriv hFm z‖ ≤ Dm)
    (hhFmb : ∀ z ∈ Metric.ball (0 : ℂ) ρm, ‖hFm z‖ ≤ 3 / 2)
    (hfe : ∀ z ∈ Metric.ball (0 : ℂ) ρm, f₀ z = z + z ^ 2 * hFm z)
    (hα : α ≠ 0) (hαsmall : ‖α‖ ≤ 1 / 1000)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    {w : ℂ} (hw : w ≠ 0) (hwu : ‖α‖ * ‖w‖ ≤ 2)
    (hτ0 : ‖MandelDim.tau0 w‖ ≤ 1 / 64)
    (hτδ : ‖Work.Pert.tauC σ α w - MandelDim.tau0 w‖ ≤ δ₂)
    (hτδ' : 0 ≤ δ₂) (hτsum : 1 / 64 + δ₂ ≤ ρm / 4)
    (η : ℝ) (hη0 : 0 < η) (hη1 : η ≤ 1 / 1000)
    (hut : ‖u (Work.Pert.tauC σ α w) - hFm (Work.Pert.tauC σ α w)‖ ≤ η)
    (hu0 : ‖u 0 - 1‖ ≤ η) (hαη : ‖α‖ ≤ η) :
    ‖Work.Pert.liftF u σ α w - Work.Pert.F0f f₀ w‖
      ≤ 1000 * (Dm + 1) * (η + δ₂) := by
  -- `‖α‖ ≤ 1/(2π)`, from the gate smallness `‖α‖ ≤ 1/1000`
  have hαπ : ‖α‖ ≤ 1 / (2 * Real.pi) := by
    have h1 : (1 : ℝ) / 1000 ≤ 1 / (2 * Real.pi) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith [Real.pi_le_four])
    linarith
  -- `τ₀ w` lies in the ball on which `hFm` is controlled
  have hτ0mem : MandelDim.tau0 w ∈ Metric.ball (0 : ℂ) ρm := by
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    have h1 : (1 : ℝ) / 64 ≤ ρm / 4 := by linarith
    have h2 : (1 : ℝ) / 16 ≤ ρm := by linarith
    linarith
  -- the pointwise model comparison
  have hcore := liftF_sub_model_le_pointwise_wide (u := u) (hF := hFm) (σ := σ) (α := α)
      (w := w) (ρ := ρm) (D := Dm) (η := η) (δ₁ := 1 / 64) (δ₂ := δ₂)
      hρm hρm4 hDm hη0 hη1 hτ0 le_rfl hτδ hτδ' hτsum
      hhFmd hhFml hhFmb hut hu0 hα hαη hαπ hnorm hw hwu
  -- the exact model identity `F0f f₀ w = w + hFm(τ₀w)/(1 + τ₀w hFm(τ₀w))`
  have hmodel : Work.Pert.F0f f₀ w
      = w + hFm (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hFm (MandelDim.tau0 w)) := by
    refine Work.Pert.Ksub2.F0f_eq_model hw (hfe _ hτ0mem) ?_
    intro h
    have h1 : ‖MandelDim.tau0 w * hFm (MandelDim.tau0 w)‖ = 1 := by
      have h2 : MandelDim.tau0 w * hFm (MandelDim.tau0 w) = -1 := by linear_combination h
      rw [h2, norm_neg, norm_one]
    have h3 : ‖MandelDim.tau0 w * hFm (MandelDim.tau0 w)‖ ≤ (1 / 64) * (3 / 2) := by
      rw [norm_mul]
      exact mul_le_mul hτ0 (hhFmb _ hτ0mem) (norm_nonneg _) (by norm_num)
    have h4 : ((1 : ℝ) / 64) * (3 / 2) < 1 := by norm_num
    linarith [h1, h3, h4]
  calc ‖Work.Pert.liftF u σ α w - Work.Pert.F0f f₀ w‖
      = ‖Work.Pert.liftF u σ α w
          - (w + hFm (MandelDim.tau0 w) / (1 + MandelDim.tau0 w * hFm (MandelDim.tau0 w)))‖ := by
        rw [hmodel]
    _ ≤ 1000 * (Dm + 1) * (η + δ₂) := hcore

end Work.Pert.PinLogDev
