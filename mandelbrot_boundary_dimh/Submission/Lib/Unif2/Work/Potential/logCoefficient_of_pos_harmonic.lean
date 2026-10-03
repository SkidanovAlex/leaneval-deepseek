import Mathlib
import Submission.Lib.Unif2.Work.Potential.Defs
import Submission.Lib.Unif2.Work.Potential.punctured_log_estimate
import Submission.Lib.Unif2.Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic

/-!
# Bôcher's theorem for positive harmonic functions: the logarithmic pole

`Work.Potential.logCoefficient_of_pos_harmonic`: a positive harmonic function on the punctured
complex one-manifold `X \ {z₀}` differs near `z₀`, in the preferred chart at `z₀`, from
`-c · log ‖· - z₀‖` by a bounded quantity, with `c ≥ 0`.

This is exactly the hypothesis `Submission.LogCoefficientInput` consumed by the hyperbolic
endgame of the uniformization theorem (`Submission.exists_hasGreenFunctionE_of_hasGreenFunctionWeak`).

The mathematical content is classical (Bôcher's theorem): a positive harmonic function on a
punctured disc equals `-c log‖·‖` plus a harmonic function on the full disc, and positivity forces
`c ≥ 0`.

## Structure of the proof

* `Work.Potential.punctured_log_estimate` — the planar (ℂ-level) Bôcher statement: a positive
  harmonic function on a punctured disc is `-c log‖·‖` plus a bounded harmonic remainder, with
  `c ≥ 0`.  (Its own proof lifts `u` to the half-plane by `z ↦ exp z`, uses the classification
  `Work.Potential.harmonic_halfplane_periodic_conjugate` of periodic positive harmonic functions
  there, descends through the universal cover, and removes the resulting singularity with
  `Work.Potential.analyticAt_zero_of_re_ge_log`.  The Fourier-coefficient route —
  `Work.Potential.harmonic_punctured_disc_fourier_structure` together with
  `Work.Potential.eq_zero_of_forall_moments_eq_zero` — is an independent alternative.)
* the present file transports the planar statement through the preferred chart at `z₀`.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology
open Filter Set

set_option linter.unusedSectionVars false

noncomputable section

namespace Work.Potential

/-- **Bôcher's theorem (logarithmic pole of a positive harmonic function).**

A positive harmonic function on `X \ {z₀}` behaves near `z₀` like `-c log ‖z - z₀‖` up to a
bounded error, with `c ≥ 0`. -/
theorem logCoefficient_of_pos_harmonic
    {X : Type*} [TopologicalSpace X] [T2Space X] [ChartedSpace ℂ X]
    [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {z₀ : X} {u : X → ℝ}
    (hu : Submission.HarmonicOnX u (Set.univ \ {z₀})) (hpos : ∀ x, x ≠ z₀ → 0 < u x) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ C : ℝ, ∃ V : Set X, V ∈ nhds z₀ ∧ ∀ x ∈ V, x ≠ z₀ →
      |u x + c * Real.log ‖(chartAt ℂ z₀) x - (chartAt ℂ z₀) z₀‖| ≤ C := by
  classical
  let γ : OpenPartialHomeomorph X ℂ := chartAt ℂ z₀
  have hz₀src : z₀ ∈ γ.source := mem_chart_source ℂ z₀
  obtain ⟨ρ, hρ, hρsub⟩ :=
    Metric.mem_nhds_iff.mp (γ.open_target.mem_nhds (γ.map_source hz₀src))
  have hball : ∀ ζ : ℂ, ‖ζ - γ z₀‖ < ρ → ζ ∈ Metric.ball (γ z₀) ρ := by
    intro ζ h
    rwa [Metric.mem_ball, dist_eq_norm]
  have htgt : ∀ ζ : ℂ, ‖ζ - γ z₀‖ < ρ → ζ ∈ γ.target := fun ζ h => hρsub (hball ζ h)
  have hsrc : ∀ ζ : ℂ, ‖ζ - γ z₀‖ < ρ → γ.symm ζ ∈ γ.source :=
    fun ζ h => γ.map_target (htgt ζ h)
  have hrev : ∀ ζ : ℂ, ‖ζ - γ z₀‖ < ρ → ζ = γ (γ.symm ζ) :=
    fun ζ h => (γ.right_inv (htgt ζ h)).symm
  have hne' : ∀ ζ : ℂ, 0 < ‖ζ - γ z₀‖ → ‖ζ - γ z₀‖ < ρ → γ.symm ζ ≠ z₀ := by
    intro ζ h1 h2 h
    have h3 : ‖ζ - γ z₀‖ = 0 := by rw [hrev ζ h2, h]; simp
    exact absurd h3 h1.ne'
  -- the pulled-back function
  let w : ℂ → ℝ := fun ζ => u (γ.symm ζ)
  have hw_harm : ∀ ζ : ℂ, 0 < ‖ζ - γ z₀‖ → ‖ζ - γ z₀‖ < ρ →
      InnerProductSpace.HarmonicAt w ζ := by
    intro ζ h1 h2
    have h1' : Submission.HarmonicOnXAt u (γ.symm ζ) :=
      hu (γ.symm ζ) ⟨mem_univ _, hne' ζ h1 h2⟩
    have h2' := (Submission.HarmonicOnXAt_iff_chart (u := u) (x := γ.symm ζ) (y := z₀)
      (hsrc ζ h2)).mp h1'
    rw [show ζ = (chartAt ℂ z₀) (γ.symm ζ) from hrev ζ h2]
    exact h2'
  have hw_pos : ∀ ζ : ℂ, 0 < ‖ζ - γ z₀‖ → ‖ζ - γ z₀‖ < ρ → 0 < w ζ :=
    fun ζ h1 h2 => hpos _ (hne' ζ h1 h2)
  -- translate so that the pole sits at the origin
  let w' : ℂ → ℝ := fun ξ => w (ξ + γ z₀)
  have hw'_harm : ∀ ξ : ℂ, 0 < ‖ξ‖ → ‖ξ‖ < ρ → InnerProductSpace.HarmonicAt w' ξ := by
    intro ξ h1 h2
    exact Commons.Analysis.InnerProductSpace.harmonicAt_comp_analytic
      (u := w) (f := fun ζ : ℂ => ζ + γ z₀) (x := ξ)
      (analyticAt_id.add analyticAt_const)
      (hw_harm (ξ + γ z₀) (by simpa using h1) (by simpa using h2))
  have hw'_pos : ∀ ξ : ℂ, 0 < ‖ξ‖ → ‖ξ‖ < ρ → 0 < w' ξ :=
    fun ξ h1 h2 => hw_pos (ξ + γ z₀) (by simpa using h1) (by simpa using h2)
  obtain ⟨c, hc, C, ε, hε0, hερ, hbound⟩ := punctured_log_estimate hρ hw'_harm hw'_pos
  refine ⟨c, hc, C, γ.source ∩ γ ⁻¹' Metric.ball (γ z₀) ε, ?_, ?_⟩
  · exact Filter.inter_mem (γ.open_source.mem_nhds hz₀src)
      ((γ.continuousAt hz₀src).preimage_mem_nhds (Metric.ball_mem_nhds (γ z₀) hε0))
  · intro x hx hxne
    obtain ⟨hxsrc, hxball⟩ := hx
    have hxne' : γ x ≠ γ z₀ := fun h => hxne (γ.injOn hxsrc hz₀src h)
    have h1 : 0 < ‖γ x - γ z₀‖ := by
      rw [norm_pos_iff]; exact sub_ne_zero.mpr hxne'
    have h2 : ‖γ x - γ z₀‖ < ε := by
      have := Metric.mem_ball.mp hxball
      rwa [dist_eq_norm] at this
    have hbd := hbound (γ x - γ z₀) h1 h2
    have hval : w' (γ x - γ z₀) = u x := by
      show w (γ x - γ z₀ + γ z₀) = u x
      rw [sub_add_cancel]
      show u (γ.symm (γ x)) = u x
      rw [γ.left_inv hxsrc]
    rw [hval] at hbd
    exact hbd

end Work.Potential
