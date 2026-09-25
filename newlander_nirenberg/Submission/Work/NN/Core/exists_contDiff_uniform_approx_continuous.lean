/-
# Uniform approximation of a continuous compactly supported function by a smooth one

Given a continuous function `g : (Fin n → ℂ) → ℂ` with compact support and a tolerance `ε > 0`,
there is an infinitely smooth function `w` with compact support such that `‖w z - g z‖ ≤ ε`
for every `z`.

The construction is mollification: `w = ρ ⋆ g` where `ρ` is a smooth bump (normalized probability
density) whose support is so small that `g` varies by at most `ε` on a ball of radius `ρ.rOut`.
Smoothness comes from `HasCompactSupport.contDiff_convolution_left`, compact support from
`HasCompactSupport.convolution`, and the uniform estimate from
`ContDiffBump.dist_normed_convolution_le`.
-/
import Mathlib

set_option linter.style.haveILetI false

namespace Work.NN.Core

open MeasureTheory Metric Filter Function
open scoped Convolution ContDiff Topology

theorem exists_contDiff_uniform_approx_continuous {n : ℕ} {g : (Fin n → ℂ) → ℂ}
    (hg : Continuous g) (hgc : HasCompactSupport g) {ε : ℝ} (hε : 0 < ε) :
    ∃ w : (Fin n → ℂ) → ℂ, ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) w ∧
      HasCompactSupport w ∧ ∀ z, ‖w z - g z‖ ≤ ε := by
  let μ : Measure (Fin n → ℂ) := Measure.addHaar
  haveI : μ.IsAddHaarMeasure := inferInstance
  haveI : IsLocallyFiniteMeasure μ := inferInstance
  haveI : μ.IsOpenPosMeasure := inferInstance
  haveI : μ.IsAddLeftInvariant := inferInstance
  haveI : μ.IsNegInvariant := inferInstance
  have huc : UniformContinuous g := hgc.uniformContinuous_of_continuous hg
  rcases Metric.uniformContinuous_iff.mp huc ε hε with ⟨δ, hδ, hucδ⟩
  let ρ : ContDiffBump (0 : Fin n → ℂ) := ⟨δ / 2, δ, half_pos hδ, by linarith⟩
  refine ⟨ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g, ?_, ?_, ?_⟩
  · exact ρ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (ρ.contDiff_normed (n := ⊤)) hg.locallyIntegrable
  · exact ρ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hgc
  · intro z
    have h := ρ.dist_normed_convolution_le (μ := μ) (x₀ := z) (ε := ε)
      hg.aestronglyMeasurable (fun x hx => ?_)
    · simpa [dist_eq_norm] using h
    · have hx' : dist x z < ρ.rOut := by rwa [Metric.mem_ball] at hx
      have hr : ρ.rOut = δ := rfl
      rw [hr] at hx'
      exact (hucδ hx').le

end Work.NN.Core
