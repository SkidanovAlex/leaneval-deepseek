import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.Parab.inversion.deriv_ne_zero_of_injOn
import Submission.Work.L62.lift_section
import Submission.Work.HornPhi.simplyConnectedSpace_section

namespace Work.HornPhi

open Set Metric Filter
open scoped Topology

/-- Inverse branch of an injective holomorphic function, localised to a ball inside its image;
and the piece of `U` lying over that ball is simply connected.

Route. For `u ∈ ball b ρ` pick `z_u ∈ U` with `Φ z_u = u` (`hb`); `Φ` is injective on `U` and
holomorphic on the open `U`, so `deriv Φ z_u ≠ 0` (`Work.Parab.inversion.deriv_ne_zero_of_injOn`).
The inverse function theorem (`HasStrictFDerivAt.toOpenPartialHomeomorph`, or
`Work.L62.lift_section.analyticAt_of_comp_eventuallyEq_id`) gives a holomorphic local inverse at
`u`, and injectivity of `Φ` on `U` identifies it with `Ψ` near `u`; hence `Ψ` is differentiable.
For the simple connectivity: `Ψ` maps `ball b ρ` bijectively onto
`S := {w | w ∈ U ∧ Φ w ∈ ball b ρ}` (use `hinj`), `Ψ` is continuous (`DifferentiableOn`) and so is
`Φ` on `U`, so `ball b ρ ≃ₜ S`; transfer `SimplyConnectedSpace` from the convex ball with
`ContinuousMap.HomotopyEquiv.simplyConnectedSpace` (`Convex.contractibleSpace`). -/
theorem inverse_Phi_omega {Φ : ℂ → ℂ} {U : Set ℂ}
    (hUo : IsOpen U) (hΦ : DifferentiableOn ℂ Φ U) (hinj : Set.InjOn Φ U)
    {b : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (hb : Metric.ball b ρ ⊆ Φ '' U) :
    ∃ Ψ : ℂ → ℂ, DifferentiableOn ℂ Ψ (Metric.ball b ρ) ∧
      (∀ u ∈ Metric.ball b ρ, Ψ u ∈ U ∧ Φ (Ψ u) = u) ∧
      (∀ z ∈ U, Φ z ∈ Metric.ball b ρ → Ψ (Φ z) = z) ∧
      SimplyConnectedSpace ↥{w : ℂ | w ∈ U ∧ Φ w ∈ Metric.ball b ρ} := by
  classical
  -- ## The inverse branch
  -- Every point of the ball has a preimage in `U`; choose one.
  have hchoice : ∀ u : ℂ, u ∈ Metric.ball b ρ → ∃ z : ℂ, z ∈ U ∧ Φ z = u := by
    intro u hu
    obtain ⟨z, hzU, hzu⟩ := hb hu
    exact ⟨z, hzU, hzu⟩
  let Ψ : ℂ → ℂ := fun u => if hu : u ∈ Metric.ball b ρ then (hchoice u hu).choose else 0
  have hΨspec : ∀ u (hu : u ∈ Metric.ball b ρ), Ψ u ∈ U ∧ Φ (Ψ u) = u := by
    intro u hu
    have h1 : Ψ u = (hchoice u hu).choose := by simp only [Ψ, dite_eq_left hu]
    rw [h1]
    exact (hchoice u hu).choose_spec
  -- Injectivity of `Φ` pins down the choice.
  have hΨinv : ∀ z ∈ U, Φ z ∈ Metric.ball b ρ → Ψ (Φ z) = z := by
    intro z hz hzball
    obtain ⟨h1, h2⟩ := hΨspec (Φ z) hzball
    exact hinj h1 hz h2
  -- `Ψ` is holomorphic: near each `u` it is the inverse of a holomorphic local inverse of `Φ`,
  -- which exists because `deriv Φ` does not vanish at the corresponding preimage.
  have hΨdiff : DifferentiableOn ℂ Ψ (Metric.ball b ρ) := by
    intro u hu
    obtain ⟨hzU, hzΦ⟩ := hΨspec u hu
    have hana : AnalyticAt ℂ Φ (Ψ u) := hΦ.analyticAt (hUo.mem_nhds hzU)
    have hd : deriv Φ (Ψ u) ≠ 0 :=
      Work.Parab.inversion.deriv_ne_zero_of_injOn hUo hΦ hinj (Ψ u) hzU
    have hev : ∀ᶠ w in 𝓝 (Ψ u), Ψ (Φ w) = w := by
      have hc : ContinuousAt Φ (Ψ u) := hΦ.continuousOn.continuousAt (hUo.mem_nhds hzU)
      have h2 : ∀ᶠ w in 𝓝 (Ψ u), Φ w ∈ Metric.ball b ρ := by
        refine hc.preimage_mem_nhds ?_
        rw [hzΦ]
        exact Metric.isOpen_ball.mem_nhds hu
      filter_upwards [hUo.mem_nhds hzU, h2] with w hwU hwball
      exact hΨinv w hwU hwball
    have hΨan : AnalyticAt ℂ Ψ u := by
      have h := Work.L62.analyticAt_of_comp_eventuallyEq_id hana hd hev
      rwa [hzΦ] at h
    exact hΨan.differentiableAt.differentiableWithinAt
  -- ## The piece of `U` over the ball is a disc
  -- `Ψ` and `Φ` are mutually inverse continuous bijections between the ball and
  -- `S = {w | w ∈ U ∧ Φ w ∈ ball b ρ}`; the ball is convex, hence simply connected,
  -- and simple connectivity transfers along the induced homeomorphism.
  have hSC : SimplyConnectedSpace ↥{w : ℂ | w ∈ U ∧ Φ w ∈ Metric.ball b ρ} :=
    simplyConnectedSpace_section hρ hΦ.continuousOn Ψ hΨdiff.continuousOn hΨspec hΨinv
  exact ⟨Ψ, hΨdiff, hΨspec, hΨinv, hSC⟩

end Work.HornPhi
