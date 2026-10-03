import Mathlib
import Submission.Work.Pert.liftF_lower_ends
import Submission.Work.Pert.sfun_lower_exp_bound
import Submission.Work.Pert.liftF_defect_decay_exp
import Submission.Work.Pert.norm_sigma_mul_u_sigma_le

namespace Work.Pert

theorem liftF_lower_decay_gate {u : ℂ → ℂ} {σ α : ℂ} {Ξ rr : ℝ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hσ : σ ≠ 0) (hα0 : α ≠ 0) (hα64 : ‖α‖ ≤ 1 / 64)
    (hα : MandelDim.InF1 α)
    (hdiff : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hσr : ‖σ‖ < rr)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hval : ∀ z ∈ Work.Pert.Qm Ξ α, ‖Work.Pert.liftF u σ α z - (z + 1)‖ ≤ 1 / 32)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ)))) :
    ∃ ρ : ℂ, ‖ρ - 1‖ ≤ 1 / 32 ∧ ∃ M κ Y : ℝ, 0 < M ∧ 0 < κ ∧
      ∀ z ∈ Work.Pert.Qm Ξ α, z.im < -Y →
        ‖Work.Pert.liftF u σ α z - (z + ρ)‖ ≤ M * Real.exp (κ * z.im) := by
  -- `σ ∈ ball 0 rr`, so `u` is holomorphic at `σ`
  have hσmem : σ ∈ Metric.ball (0 : ℂ) rr := by
    rw [Metric.mem_ball, dist_zero_right]; exact hσr
  have hdσ : DifferentiableAt ℂ u σ :=
    hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds hσmem)
  -- hence `u` is linearly bounded at `σ`
  obtain ⟨C, δ, hC, hδ, huL⟩ := Work.Pert.diffAt_linear_bound hdσ
  -- exponential convergence `1 - sfun u σ α z → 1/(1 + σuσ)` at the lower end
  obtain ⟨M, κ, Y, hM, hκ, hsfun⟩ :=
    sfun_lower_exp_bound (u := u) (σ := σ) (α := α) (Ξ := Ξ) (rr := rr)
      hΞ hα hα64 hσ hnorm hrr hσr hu hC hδ huL hτQ hval
  -- and therefore `liftF u σ α z → z + ρ` exponentially, with `‖ρ - 1‖ ≤ 1/32`
  exact liftF_lower_ends (u := u) (σ := σ) (α := α) (Ξ := Ξ) (rr := rr)
      hΞ hα hα64 hQAdm hσ hnorm hrr hσr hu hM hκ hsfun hval

end Work.Pert
