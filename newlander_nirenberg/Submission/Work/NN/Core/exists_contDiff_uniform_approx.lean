/-
# Uniform `C^∞` approximation of a compactly supported `C^1` function

This file proves `Work.NN.Core.exists_contDiff_uniform_approx`: a `C^1` function `φ : E → ℂ`, on a
finite-dimensional real normed space, which vanishes outside the ball of radius `R`, can be
approximated, uniformly in the value *and* in the first derivative, by an infinitely smooth
function `ψ` which still vanishes outside the ball of radius `R + 1`.

The construction is mollification: `ψ = ρ ⋆ φ` where `ρ` is a smooth bump (normalized probability
density) whose support is so small that on its support both `φ` and `fderiv ℝ φ` vary by at most
`ε`.  The value estimate is `ContDiffBump.dist_normed_convolution_le`; the derivative estimate is
the same lemma applied to the continuous (compactly supported, hence uniformly continuous) map
`fderiv ℝ φ`, together with the computation `fderiv_normed_convolution` that the derivative of the
mollification is the mollification of the derivative.
-/
import Mathlib

namespace Work.NN.Core

open MeasureTheory Metric Filter Function
open scoped Convolution ContDiff Topology

/-- The derivative of the mollification of a compactly supported `C^1` function is the
mollification of its derivative.  Stated for the canonical Haar measure on `E`. -/
theorem fderiv_normed_convolution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {φ : E → ℂ} (hφ : ContDiff ℝ 1 φ) (hφcpt : HasCompactSupport φ)
    (ρ : ContDiffBump (0:E)) (z : E) :
    fderiv ℝ (ρ.normed (Measure.addHaar : Measure E)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (Measure.addHaar : Measure E)] φ) z
      = (ρ.normed (Measure.addHaar : Measure E)
        ⋆[ContinuousLinearMap.lsmul ℝ ℝ, (Measure.addHaar : Measure E)] (fderiv ℝ φ)) z := by
  let μ : Measure E := Measure.addHaar
  haveI : μ.IsAddHaarMeasure := inferInstance
  haveI : IsLocallyFiniteMeasure μ := inferInstance
  haveI : μ.IsOpenPosMeasure := inferInstance
  haveI : μ.IsAddLeftInvariant := inferInstance
  haveI : μ.IsNegInvariant := inferInstance
  have hρli : LocallyIntegrable (ρ.normed μ) μ :=
    (ρ.contDiff_normed (n := ⊤)).continuous.locallyIntegrable
  have hkey := hφcpt.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hρli hφ z
  rw [hkey.fderiv]
  have hL : (ContinuousLinearMap.precompR E (ContinuousLinearMap.lsmul ℝ ℝ) :
      ℝ →L[ℝ] (E →L[ℝ] ℂ) →L[ℝ] (E →L[ℝ] ℂ)) = ContinuousLinearMap.lsmul ℝ ℝ := by
    ext r A; simp [ContinuousLinearMap.precompR_apply]
  rw [hL]

theorem exists_contDiff_uniform_approx {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {φ : E → ℂ} {R : ℝ}
    (hφ : ContDiff ℝ 1 φ) (hR : 0 ≤ R) (hφ0 : ∀ z, R ≤ ‖z‖ → φ z = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ ψ : E → ℂ, ContDiff ℝ (((⊤ : ℕ∞) : WithTop ℕ∞)) ψ ∧ HasCompactSupport ψ ∧
      (∀ z, R + 1 ≤ ‖z‖ → ψ z = 0) ∧
      (∀ z, ‖ψ z - φ z‖ ≤ ε) ∧ (∀ z, ‖fderiv ℝ ψ z - fderiv ℝ φ z‖ ≤ ε) := by
  let μ : Measure E := Measure.addHaar
  haveI : μ.IsAddHaarMeasure := inferInstance
  haveI : IsLocallyFiniteMeasure μ := inferInstance
  haveI : μ.IsOpenPosMeasure := inferInstance
  haveI : μ.IsAddLeftInvariant := inferInstance
  haveI : μ.IsNegInvariant := inferInstance
  have hφcont : Continuous φ := hφ.continuous
  have hφcpt : HasCompactSupport φ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0:E) R) ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    exact hφ0 x hx.le
  have hdφcont : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by norm_num)
  have hdφcpt : HasCompactSupport (fderiv ℝ φ) := hφcpt.fderiv ℝ
  have hφuc : UniformContinuous φ := hφcpt.uniformContinuous_of_continuous hφcont
  have hdφuc : UniformContinuous (fderiv ℝ φ) := hdφcpt.uniformContinuous_of_continuous hdφcont
  rcases Metric.uniformContinuous_iff.mp hφuc ε hε with ⟨δ₁, hδ₁, huc₁⟩
  rcases Metric.uniformContinuous_iff.mp hdφuc ε hε with ⟨δ₂, hδ₂, huc₂⟩
  have hrpos : 0 < min 1 (min δ₁ δ₂) := lt_min one_pos (lt_min hδ₁ hδ₂)
  let ρ : ContDiffBump (0:E) :=
    ⟨min 1 (min δ₁ δ₂) / 2, min 1 (min δ₁ δ₂), half_pos hrpos, by linarith⟩
  refine ⟨ρ.normed μ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] φ, ?_, ?_, ?_, ?_, ?_⟩
  · exact ρ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
      (ρ.contDiff_normed (n := ⊤)) hφcont.locallyIntegrable
  · exact ρ.hasCompactSupport_normed.convolution (ContinuousLinearMap.lsmul ℝ ℝ) hφcpt
  · intro z hz
    rw [convolution_lsmul]
    have hzero : (fun t : E => ρ.normed μ t • φ (z - t)) = 0 := by
      funext t
      simp only [Pi.zero_apply]
      by_cases ht : ρ.normed μ t = 0
      · rw [ht, zero_smul]
      · have htmem : t ∈ Function.support (ρ.normed μ) := ht
        rw [ρ.support_normed_eq, Metric.mem_ball, dist_zero_right] at htmem
        have hle : R ≤ ‖z - t‖ := by
          have h1 : ‖z‖ - ‖t‖ ≤ ‖z - t‖ := (le_abs_self _).trans (abs_norm_sub_norm_le z t)
          have h4 : ρ.rOut ≤ 1 := min_le_left _ _
          linarith [htmem]
        rw [hφ0 (z - t) hle, smul_zero]
    rw [hzero]; simp
  · intro z
    have h := ρ.dist_normed_convolution_le (μ := μ) (x₀ := z) (ε := ε)
      hφcont.aestronglyMeasurable (fun x hx => ?_)
    · simpa [dist_eq_norm] using h
    · have hxz : dist x z < δ₁ := by
        have hx' : dist x z < ρ.rOut := by rwa [Metric.mem_ball] at hx
        have h4 : ρ.rOut ≤ δ₁ := (min_le_right _ _).trans (min_le_left _ _)
        linarith
      exact (huc₁ hxz).le
  · intro z
    rw [fderiv_normed_convolution hφ hφcpt ρ z]
    have h := ρ.dist_normed_convolution_le (μ := μ) (x₀ := z) (ε := ε)
      hdφcont.aestronglyMeasurable (fun x hx => ?_)
    · simpa [dist_eq_norm] using h
    · have hxz : dist x z < δ₂ := by
        have hx' : dist x z < ρ.rOut := by rwa [Metric.mem_ball] at hx
        have h4 : ρ.rOut ≤ δ₂ := (min_le_right _ _).trans (min_le_right _ _)
        linarith
      exact (huc₂ hxz).le

end Work.NN.Core
