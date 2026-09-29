import Mathlib
import Submission.Work.TMComp.RealCartanDefs

/-!
# Existence of a Lebesgue density point

This file proves `Work.TMComp.RealCartan.rcExistsDensityPoint`: a measurable set `S ⊆ ℝ`
of positive Lebesgue measure has a point `x₀ ∈ S` at which `S` has density `1`.  Concretely,
for every `τ > 0` and all sufficiently small `ℓ > 0`,

`(1 - τ) * (2 * ℓ) ≤ volume (S ∩ Icc (x₀ - ℓ) (x₀ + ℓ))`.

The point is obtained from Lebesgue's density theorem
(`Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet`): almost every point of `S` is a
density point, and since `volume S > 0` at least one such point lies in `S`.  The estimate is
then read off from the convergence of the density ratios, using
`Real.volume_closedBall` and `Real.closedBall_eq_Icc`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal

namespace Work.TMComp.RealCartan

theorem rcExistsDensityPoint {S : Set ℝ} (hS : MeasurableSet S) (hpos : 0 < MeasureTheory.volume S) :
    ∃ x₀ ∈ S, ∀ τ : ℝ, 0 < τ → ∃ ρ > 0, ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ ρ →
      (1 - τ) * (2 * ℓ)
        ≤ (MeasureTheory.volume (S ∩ Set.Icc (x₀ - ℓ) (x₀ + ℓ))).toReal := by
  -- The property of being a density point of `S`.
  let Q : ℝ → Prop := fun x => Tendsto (fun r =>
      MeasureTheory.volume (S ∩ Metric.closedBall x r) /
        MeasureTheory.volume (Metric.closedBall x r)) (𝓝[>] (0:ℝ)) (𝓝 1)
  -- Lebesgue's density theorem: almost every point `x` satisfies
  -- `volume (S ∩ closedBall x r) / volume (closedBall x r) → 1_{x ∈ S}`.
  have hae := Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet
    (MeasureTheory.volume : Measure ℝ) hS
  -- Restricting to `S`, almost every `x ∈ S` is a density point of `S`.
  have haeS : ∀ᵐ x ∂(MeasureTheory.volume.restrict S), Q x := by
    rw [MeasureTheory.ae_restrict_iff' hS]
    filter_upwards [hae] with x hx hxS
    rw [Set.indicator_of_mem hxS] at hx
    simpa [Q] using hx
  -- A density point lying in `S` exists, because `volume S > 0`.
  have hQ : ∃ x₀ ∈ S, Q x₀ := by
    by_contra hc
    push Not at hc
    have hsub : S ⊆ {x | ¬ Q x} := fun x hx => hc x hx
    have hle := measure_mono (μ := MeasureTheory.volume.restrict S) hsub
    have hB : (MeasureTheory.volume.restrict S) {x | ¬ Q x} = 0 :=
      (MeasureTheory.ae_iff (μ := (MeasureTheory.volume.restrict S)) (p := Q)).mp haeS
    rw [hB, Measure.restrict_apply_self] at hle
    exact absurd hpos (not_lt.mpr hle)
  obtain ⟨x₀, hx₀S, hx₀⟩ := hQ
  refine ⟨x₀, hx₀S, fun τ hτ => ?_⟩
  -- Pass the convergence statement through `ENNReal.toReal`.
  have h1 : Tendsto (fun r => (MeasureTheory.volume (S ∩ Metric.closedBall x₀ r) /
      MeasureTheory.volume (Metric.closedBall x₀ r)).toReal) (𝓝[>] (0:ℝ)) (𝓝 (1:ℝ)) := by
    have hne : (1:ℝ≥0∞) ≠ ⊤ := by simp
    have h2 := (ENNReal.tendsto_toReal hne).comp hx₀
    rw [ENNReal.toReal_one] at h2
    exact h2
  -- For `r > 0`, the density ratio as a real number is `volume (S ∩ closedBall x₀ r) / (2r)`.
  have hval : ∀ r : ℝ, 0 < r →
      (MeasureTheory.volume (S ∩ Metric.closedBall x₀ r) /
        MeasureTheory.volume (Metric.closedBall x₀ r)).toReal
        = (MeasureTheory.volume (S ∩ Metric.closedBall x₀ r)).toReal / (2 * r) := by
    intro r hr
    rw [ENNReal.toReal_div, Real.volume_closedBall, ENNReal.toReal_ofReal (by linarith)]
  -- `1 - τ < 1`, so the density ratio is eventually `> 1 - τ`.
  have hmem : Set.Ioi (1 - τ) ∈ 𝓝 (1:ℝ) :=
    isOpen_Ioi.mem_nhds (by rw [Set.mem_Ioi]; linarith)
  obtain ⟨ρ, hρpos, hρ⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (h1.eventually hmem)
  refine ⟨ρ, hρpos, fun ℓ hℓ hℓρ => ?_⟩
  have hℓI : ℓ ∈ Set.Ioc (0:ℝ) ρ := ⟨hℓ, hℓρ⟩
  have hlt : 1 - τ < (MeasureTheory.volume (S ∩ Metric.closedBall x₀ ℓ) /
      MeasureTheory.volume (Metric.closedBall x₀ ℓ)).toReal := hρ hℓI
  rw [hval ℓ hℓ] at hlt
  have h2ℓ : 0 < 2 * ℓ := by linarith
  rw [lt_div_iff₀ h2ℓ] at hlt
  rw [Real.closedBall_eq_Icc] at hlt
  exact le_of_lt hlt

end Work.TMComp.RealCartan
