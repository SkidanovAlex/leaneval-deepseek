import Mathlib
import Submission.Work.Pert.CoordDefs
import Submission.Work.Interfaces.FatouNarrow

namespace Work.Pert

/-!
# `Work.Pert.dev_deriv_on_Qc`

The pointwise derivative estimate on the safe core `Qc η ξ₁ α` of the gate `Qm ξ₁ α`, in the form
the `PertCoordClose` assembly consumes it: if `Ψ` is a Fatou coordinate of the near-translation
`F = liftF u σ α` on `Qm ξ₁ α` (`hΨ`) and `F` is a near-translation there (`hL1`, which supplies
`‖F ζ - (ζ+1)‖ ≤ 1/32`), then on the `η/100`-safe core

  `‖Ψ' ζ - 1/(F ζ - ζ)‖ ≤ 1/10000`.

Proof: `ζ ∈ Qc` gives `ball ζ (η/100) ⊆ Qm`, so on that ball `F` is differentiable (from `hL1`),
`v = F - id` satisfies `‖v - 1‖ ≤ 1/32 < 1/4`, and the Abel equation `Ψ (z + v z) = Ψ z + 1`
holds (it is `hΨ`'s third clause, `z + v z = F z`).  Lemma A.2.4(i) as packaged in the hypothesis
`hFDE` then gives `‖Ψ' ζ - 1/v ζ‖ ≤ C₂/(η/100)`, and `10^6 C₂ ≤ η` turns the right side into
`1/10000`.  All other hypotheses (`hu`, `hbdd`, `heq`, `hτ`, `hQAdm`, …) are carried for
compatibility with the assembly and are not used here.
-/

theorem dev_deriv_on_Qc {ξ₁ η rr : ℝ} {u : ℂ → ℂ} {σ α : ℂ} {Ψ : ℂ → ℂ} {R₁ C₂ : ℝ}
    (hη : 0 < η) (hR₁ : 0 < R₁) (hC₂ : 0 < C₂) (hηbig : 10 ^ 6 * C₂ ≤ η) (hR₁η : R₁ ≤ η / 100)
    (hFDE : ∀ (Φ v : ℂ → ℂ) (z₀ : ℂ) (R : ℝ), R₁ ≤ R →
      DifferentiableOn ℂ Φ (Metric.ball z₀ R) → Set.InjOn Φ (Metric.ball z₀ R) →
      DifferentiableOn ℂ v (Metric.ball z₀ R) → (∀ z ∈ Metric.ball z₀ R, ‖v z - 1‖ < 1 / 4) →
      (∀ z ∈ Metric.ball z₀ R, z + v z ∈ Metric.ball z₀ R → Φ (z + v z) = Φ z + 1) →
      ‖deriv Φ z₀ - 1 / v z₀‖ ≤ C₂ / R)
    (hξ₁ : 0 < ξ₁) (h2ξ : 2 * ξ₁ < η) (hRe : η / 2 + 2 * ξ₁ < (1 / α).re)
    (hαη : 2 * Real.pi * ‖α‖ * η ≤ 1 / 64) (hα : α ≠ 0) (hσ : σ ≠ 0)
    (hrr : 1 / (4 * η) ≤ rr) (hrrpos : 0 < rr)
    (hu : DifferentiableOn ℂ u (Metric.ball 0 rr))
    (hbdd : ∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (heq : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hτ : ∀ z ∈ Work.Pert.Qm ξ₁ α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr)
    (hQAdm : MandelDim.QAdm (some ((ξ₁ : ℂ) - 1 / α)) (some (-(ξ₁ : ℂ))))
    (hL1 : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm ξ₁ α))
    (hΨ : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Ψ (Work.Pert.Qm ξ₁ α)) :
    ∀ ζ ∈ Work.Pert.Qc η ξ₁ α,
      ‖deriv Ψ ζ - 1 / (Work.Pert.liftF u σ α ζ - ζ)‖ ≤ 1 / 10000 := by
  intro ζ hζ
  obtain ⟨hζQm, hζball⟩ := hζ
  set F : ℂ → ℂ := Work.Pert.liftF u σ α with hF
  have hsub : Metric.ball ζ (η / 100) ⊆ Work.Pert.Qm ξ₁ α := fun z hz =>
    hζball (Metric.ball_subset_closedBall hz)
  have hNT : MandelDim.NearTranslationOn F (Work.Pert.Qm ξ₁ α) := hL1.1
  have hFclose : ∀ z ∈ Work.Pert.Qm ξ₁ α, ‖F z - (z + 1)‖ ≤ 1 / 32 :=
    fun z hz => (hNT.2 z hz).1
  have hdiffv : DifferentiableOn ℂ (fun z => F z - z) (Metric.ball ζ (η / 100)) :=
    (hNT.1.mono hsub).sub differentiableOn_id
  have hvclose : ∀ z ∈ Metric.ball ζ (η / 100), ‖(fun w => F w - w) z - 1‖ < 1 / 4 := by
    intro z hz
    have h := hFclose z (hsub hz)
    have he : (F z - z) - 1 = F z - (z + 1) := by ring
    rw [he]
    linarith
  have habel : ∀ z ∈ Metric.ball ζ (η / 100), z + (F z - z) ∈ Metric.ball ζ (η / 100) →
      Ψ (z + (F z - z)) = Ψ z + 1 := by
    intro z hz hz'
    have he : z + (F z - z) = F z := by ring
    rw [he] at hz' ⊢
    exact hΨ.2.2 z (hsub hz) (hsub hz')
  have hkey := hFDE Ψ (fun z => F z - z) ζ (η / 100) hR₁η (hΨ.1.mono hsub)
      (Set.InjOn.mono hsub hΨ.2.1) hdiffv hvclose habel
  have hbound : C₂ / (η / 100) ≤ 1 / 10000 := by
    have hη' : (0 : ℝ) < η / 100 := by linarith
    rw [div_le_iff₀ hη']
    have h2 : (10 : ℝ) ^ 6 * C₂ ≤ η := hηbig
    nlinarith
  calc ‖deriv Ψ ζ - 1 / (F ζ - ζ)‖ ≤ C₂ / (η / 100) := hkey
    _ ≤ 1 / 10000 := hbound


end Work.Pert
