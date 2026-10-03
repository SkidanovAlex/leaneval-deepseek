import Mathlib
import Submission.Work.Pert.PinLogDev.axis_decay_budget

namespace Work.Pert.PinLogDev

/-- `NearOn` is monotone in the closeness parameter `δ`. -/
theorem nearOn_mono {f₀ f : ℂ → ℂ} {Df L : Set ℂ} {δ δ' : ℝ}
    (h : MandelDim.NearOn f₀ f Df L δ) (hle : δ ≤ δ') :
    MandelDim.NearOn f₀ f Df L δ' :=
  ⟨h.1, h.2.1, h.2.2.1, fun z hz => lt_of_lt_of_le (h.2.2.2 z hz) hle⟩

/-- **Axis decay budget, `δ`-uniform form.**  Same content as `axis_decay_budget`, but the
nearness parameter is allowed to be any `δ ≤ 1/(1000 (M+1))` (the smaller the stronger, so this is
an immediate strengthening by monotonicity of `NearOn`). -/
theorem axis_decay_budget2 {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀) (Ξ Yt : ℝ) (hΞ : 1 + 64 * Real.pi ≤ Ξ)
    (hYt : Ξ < Yt) {rr : ℝ} (hrr : 0 < rr) (hrrD : Metric.closedBall (0 : ℂ) rr ⊆ D₀) :
    ∃ (Kd Ms : ℝ), 0 ≤ Kd ∧ 0 < Ms ∧
      ∀ M : ℝ, Ms ≤ M → ∃ ε : ℝ, 0 ≤ ε ∧ ε ≤ 1 / 128 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / (1000 * (M + 1)) →
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ),
        MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) rr) δ →
        f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) → α = MandelDim.rotOf f →
        DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball (0 : ℂ) rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) →
        (∀ s : ℝ, Yt ≤ s →
          ‖Work.Pert.liftF u σ α ((s : ℂ) * Complex.I) - ((s : ℂ) * Complex.I + 1)‖ ≤ Kd / s) ∧
        (∀ s : ℝ, Yt ≤ s →
          ‖Work.Pert.liftF u σ α (-((s : ℂ) * Complex.I)) - (-((s : ℂ) * Complex.I) + 1)‖
            ≤ Kd / s + ε) := by
  obtain ⟨Kd, Ms, hKd, hMs, hmain⟩ := axis_decay_budget d hd Ξ Yt hΞ hYt hrr hrrD
  refine ⟨Kd, Ms, hKd, hMs, ?_⟩
  intro M hM
  obtain ⟨ε, hε0, hεle, hrest⟩ := hmain M hM
  refine ⟨ε, hε0, hεle, ?_⟩
  intro δ hδ0 hδle f Df u σ α hnear hf0 hInF1 hαeq huD huB hform hnorm hτQ
  exact hrest f Df u σ α (nearOn_mono hnear hδle) hf0 hInF1 hαeq huD huB hform hnorm hτQ

end Work.Pert.PinLogDev
