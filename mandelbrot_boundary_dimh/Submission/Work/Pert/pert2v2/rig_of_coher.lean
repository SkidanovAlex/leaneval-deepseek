import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Pert.Ksub2.Setup
import Submission.Work.Pert.pert2v2.gate_coord_close_minus_gen_r

namespace Work.Pert.pert2v2

theorem rig_of_coher {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ ξ : ℝ, 0 < ξ ∧ ∃ r : ℝ, 0 < r ∧ ∀ Ξ' : ℝ, ξ ≤ Ξ' →
      ∀ Ψ : ℂ → ℂ,
      MandelDim.IsFatouCoordOn
        (fun w : ℂ => MandelDim.tau0 (f₀ (MandelDim.tau0 w)))
        Ψ (MandelDim.Qreg none (some (-(Ξ' : ℂ)))) →
      ∀ M x y₀ : ℝ,
      Work.Pert.Xc d (-M) ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) →
      Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I)
        ∈ MandelDim.Qreg none (some (-(Ξ' : ℂ))) →
      ∀ c : ℂ,
      Ψ (Work.Pert.Xc d (-M)) - (-M) = c →
      Ψ (Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I))
        - ((x : ℂ) + (y₀ : ℂ) * Complex.I) = c →
      ∀ εp : ℝ, 0 < εp →
        ∀ L : Set ℂ, IsCompact L → L ⊆ D₀ →
        ∀ ρ : ℝ, r ≤ ρ → Metric.closedBall (0 : ℂ) ρ ⊆ L →
        ∃ δ₀ : ℝ, 0 < δ₀ ∧
        ∀ (f : ℂ → ℂ) (Df : Set ℂ) (u : ℂ → ℂ) (σ α : ℂ) (Φm : ℂ → ℂ),
          MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
          α = MandelDim.rotOf f →
          DifferentiableOn ℂ u (Metric.ball 0 ρ) →
          (∀ z ∈ Metric.ball 0 ρ, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
          (∀ z ∈ Metric.ball 0 ρ, f z = z + z * (z - σ) * u z) →
          1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
          (∀ z ∈ Work.Pert.Qm Ξ' α, Work.Pert.tauC σ α z ∈ Metric.ball 0 ρ) →
          MandelDim.QAdm (some ((Ξ' : ℂ) - 1 / α)) (some (-(Ξ' : ℂ))) →
          MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ' α) →
          MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ' α) →
          Φm (Work.Pert.Xc d (-M)) = (-M : ℂ) →
          ‖Φm (Work.Pert.Xc d ((x : ℂ) + (y₀ : ℂ) * Complex.I))
            - ((x : ℂ) + (y₀ : ℂ) * Complex.I)‖ < εp := by
  -- The analytic content is `gate_coord_close_minus_gen_r`: the perturbed gate coordinate
  -- converges to the model coordinate `Ψ` (relative to their common value at any base point).
  obtain ⟨ξ, hξ, r, hr, H⟩ := gate_coord_close_minus_gen_r d hF hd
  refine ⟨ξ, hξ, r, hr, fun Ξ' hΞ' => ?_⟩
  intro Ψ hΨ M x y₀ hz0Q hwQ c hc0 hcw εp hεp L hLc hLD0 ρ hρ hρball
  -- the high point of the datum's curve
  set W : ℂ := (x : ℂ) + (y₀ : ℂ) * Complex.I with hW
  -- instantiate the limit theorem at the base point `z₀ := Xc d (-M)` and the compact `K = {Xc d W}`
  obtain ⟨δ₀, hδ₀, hδ⟩ := H Ξ' hΞ' Ψ hΨ (Work.Pert.Xc d (-M)) hz0Q
      ({Work.Pert.Xc d W} : Set ℂ) isCompact_singleton (by
        rw [Set.singleton_subset_iff]; exact hwQ)
      εp hεp L hLc hLD0 ρ hρ hρball
  refine ⟨δ₀, hδ₀, ?_⟩
  intro f Df u σ α Φm hNear hf0 hInF1 hα hu hu2 hf hσ htauC hQAdm hNT hΦm hpin
  have hkey := hδ f Df u σ α Φm hNear hf0 hInF1 hα hu hu2 hf hσ htauC hQAdm hNT hΦm
      (Work.Pert.Xc d W) (Set.mem_singleton _)
  -- coherence of the model coordinate with the identity at both points, with the same constant `c`
  have hΨW : Ψ (Work.Pert.Xc d W) = W + c := by
    rw [← hcw]; ring
  have hΨ0 : Ψ (Work.Pert.Xc d (-M)) = (-M : ℂ) + c := by
    rw [← hc0]; ring
  -- the relative coordinate difference is the absolute error `Φm (Xc d W) - W`
  have hEq : Φm (Work.Pert.Xc d W) - Φm (Work.Pert.Xc d (-M))
      - (Ψ (Work.Pert.Xc d W) - Ψ (Work.Pert.Xc d (-M)))
      = Φm (Work.Pert.Xc d W) - W := by
    rw [hpin, hΨW, hΨ0]; ring
  rw [hEq] at hkey
  exact hkey

end Work.Pert.pert2v2
