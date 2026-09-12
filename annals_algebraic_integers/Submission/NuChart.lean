import Submission.Serre
import Submission.EquilibriumMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Map

/-!
# ν as a single pushforward of the uniform chart

Serre's measure `ν` on `[a,b]` is defined (`Submission.Serre.nu`) as the image
of the equilibrium measure of the reciprocal interval `[1/b,1/a]` under
inversion `t ↦ t⁻¹`.  Since the equilibrium measure of `[c,d]` is itself the
image of `uniform01` under the chart `u ↦ (c+d)/2 + (d−c)/2·cos(πu)`, we obtain
`ν` as a *single* pushforward:

    nu a b = Measure.map (fun u => (chart (b⁻¹) (a⁻¹) u)⁻¹) uniform01.

This module records that change of variables (and the corresponding integral
change-of-variables rules), the first piece of the A2′ balayage wiring.
-/

noncomputable section

open MeasureTheory
open scoped Real ENNReal

namespace Submission.NuChart

open Submission.Equilibrium
open Submission.Serre

/-- `ν` on `[a,b]` is the pushforward of `uniform01` under
`u ↦ (chart (1/b) (1/a) u)⁻¹` (inversion composed with the reciprocal chart). -/
lemma nu_eq_map_inv_chart (a b : ℝ) :
    nu a b = Measure.map (fun u : ℝ => (chart (b⁻¹) (a⁻¹) u)⁻¹) uniform01 := by
  unfold nu
  rw [equilibrium]
  -- map invMap (map (chart c d) uniform01) = map (invMap ∘ chart c d) uniform01
  rw [Measure.map_map]
  · rfl
  · exact invMap_measurable
  · exact chart_measurable (b⁻¹) (a⁻¹)

/-- The composed map is measurable. -/
lemma invChart_measurable (a b : ℝ) : Measurable (fun u : ℝ => (chart (b⁻¹) (a⁻¹) u)⁻¹) := by
  exact invMap_measurable.comp (chart_measurable (b⁻¹) (a⁻¹))

/-- The pushforward expression of `ν` is a probability measure. -/
lemma map_inv_chart_univ (a b : ℝ) :
    Measure.map (fun u : ℝ => (chart (b⁻¹) (a⁻¹) u)⁻¹) uniform01 Set.univ = 1 := by
  rw [← nu_eq_map_inv_chart a b]
  exact nu_univ a b

/-- Change of variables for integrals against `ν`: pull back to the reciprocal
equilibrium measure. -/
lemma nu_integral_eq_recip {a b : ℝ} (f : ℝ → ℝ)
    (hfm : AEStronglyMeasurable f (Measure.map invMap (equilibrium (b⁻¹) (a⁻¹)))) :
    (∫ x : ℝ, f x ∂nu a b) = (∫ t : ℝ, f (t⁻¹) ∂equilibrium (b⁻¹) (a⁻¹)) := by
  unfold nu
  exact MeasureTheory.integral_map (φ := invMap) (μ := equilibrium (b⁻¹) (a⁻¹))
    (f := f) invMap_measurable.aemeasurable hfm

/-- Change of variables for integrals against `ν`: pull back to the uniform
measure on the chart parameter. -/
lemma nu_integral_eq_chart {a b : ℝ} (f : ℝ → ℝ)
    (hfm : AEStronglyMeasurable f (Measure.map (fun u : ℝ => (chart (b⁻¹) (a⁻¹) u)⁻¹) uniform01)) :
    (∫ x : ℝ, f x ∂nu a b) = (∫ u : ℝ, f ((chart (b⁻¹) (a⁻¹) u)⁻¹) ∂uniform01) := by
  rw [nu_eq_map_inv_chart a b]
  exact MeasureTheory.integral_map (φ := fun u : ℝ => (chart (b⁻¹) (a⁻¹) u)⁻¹)
    (μ := uniform01) (f := f) (invChart_measurable a b).aemeasurable hfm

end Submission.NuChart
