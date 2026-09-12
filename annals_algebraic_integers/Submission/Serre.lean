import Submission.EquilibriumMeasure
import Submission.ReciprocalIntegral

/-!
# Serre's measure on an interval

Second layer of the machinery: Serre's probability measure

    μ = γ·ν + (1−γ)·μ_eq

on `[a,b]`, where `μ_eq = equilibrium a b` is the unweighted equilibrium
measure and `ν` is the image of the equilibrium measure of the reciprocal
interval `[1/b, 1/a]` under the inversion `t ↦ 1/t`.  In Smith's example
`a = 0.087353`, `b = 4.411076`, `γ = 0.215485`, and `μ` is arithmetic with
first moment just below `1.89831`.

This module records the definition and the elementary mass facts.  (The
moment computations are developed separately once the classical reciprocal
integral identity is available.)
-/

noncomputable section

open MeasureTheory
open scoped Real ENNReal

namespace Submission.Serre

open Submission.Equilibrium

/-- The inversion `t ↦ t⁻¹` (with `0⁻¹ = 0`). -/
def invMap : ℝ → ℝ := fun t => t⁻¹

/-- Serre's measure `ν` on `[a,b]`: image of the equilibrium measure of the
reciprocal interval `[1/b, 1/a]` under inversion. -/
def nu (a b : ℝ) : Measure ℝ := Measure.map invMap (equilibrium (b⁻¹) (a⁻¹))

lemma invMap_measurable : Measurable invMap := by
  exact measurable_inv

/-- `ν` is a probability measure. -/
lemma nu_univ (a b : ℝ) : nu a b Set.univ = 1 := by
  unfold nu
  rw [Measure.map_apply invMap_measurable MeasurableSet.univ]
  exact equilibrium_univ (b⁻¹) (a⁻¹)

instance nu_isProbability (a b : ℝ) : IsProbabilityMeasure (nu a b) :=
  ⟨nu_univ a b⟩

/-- Serre's measure `μ = γ·ν + (1−γ)·μ_eq` on `[a,b]` (convex combination). -/
def serreMeasure (γ : ℝ) (a b : ℝ) : Measure ℝ :=
  ENNReal.ofReal γ • nu a b + ENNReal.ofReal (1 - γ) • equilibrium a b

/-- Mass of the convex combination: `μ` is a probability measure for `γ ∈ [0,1]`. -/
lemma serre_univ {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (a b : ℝ) :
    serreMeasure γ a b Set.univ = 1 := by
  unfold serreMeasure
  rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply, nu_univ, equilibrium_univ]
  -- mass of smul: (ofReal γ • nu) univ = ofReal γ • 1 = ofReal γ
  simp
  -- ofReal γ + ofReal (1-γ) = ofReal 1 = 1
  rw [← ENNReal.ofReal_add hγ0 (sub_nonneg.mpr hγ1)]
  have : γ + (1 - γ) = 1 := by ring
  rw [this]
  simp


/-- The mean of Serre's measure `ν` on `[a,b]` equals `√(a·b)` (for `0 < a < b`). -/
lemma nu_mean {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    (∫ x : ℝ, x ∂nu a b) = Real.sqrt (a * b) := by
  have hb : 0 < b := lt_trans ha hab
  have hab_pos : 0 < a * b := mul_pos ha hb
  -- change of variables: first undo the inversion, then the chart
  have hmap1 : (∫ x : ℝ, x ∂nu a b) = (∫ t : ℝ, t⁻¹ ∂equilibrium (b⁻¹) (a⁻¹)) := by
    unfold nu
    exact MeasureTheory.integral_map (φ := invMap) (μ := equilibrium (b⁻¹) (a⁻¹))
      (f := fun y : ℝ => y) invMap_measurable.aemeasurable
      (continuous_id.aestronglyMeasurable (μ := Measure.map invMap (equilibrium (b⁻¹) (a⁻¹))))
  rw [hmap1]
  have hmap2 : (∫ t : ℝ, t⁻¹ ∂equilibrium (b⁻¹) (a⁻¹)) =
      (∫ u : ℝ, (chart (b⁻¹) (a⁻¹) u)⁻¹ ∂uniform01) := by
    rw [equilibrium]
    exact MeasureTheory.integral_map (φ := chart (b⁻¹) (a⁻¹)) (μ := uniform01)
      (f := fun y : ℝ => y⁻¹) (chart_measurable (b⁻¹) (a⁻¹)).aemeasurable
      (measurable_inv.aestronglyMeasurable
        (μ := Measure.map (chart (b⁻¹) (a⁻¹)) uniform01))
  rw [hmap2]
  rw [uniform01_integral]
  -- now: ∫ u in 0..1, (chart (b⁻¹) (a⁻¹) u)⁻¹
  -- identify A = (a+b)/(2·a·b), B = (b-a)/(2·a·b), so chart u = A + B·cos(πu)
  let A : ℝ := (a + b) / (2 * (a * b))
  let B : ℝ := (b - a) / (2 * (a * b))
  have hchart : ∀ u : ℝ, chart (b⁻¹) (a⁻¹) u = A + B * Real.cos (Real.pi * u) := by
    intro u
    unfold chart
    dsimp [A, B]
    have hb0 : b ≠ 0 := ne_of_gt hb
    have ha0 : a ≠ 0 := ne_of_gt ha
    field_simp [ha0, hb0]
  have hBpos : 0 < B := by
    dsimp [B]
    positivity
  have hBA : B < A := by
    dsimp [A, B]
    have hb0 : b ≠ 0 := ne_of_gt hb
    field_simp [ha.ne', hb0]
    nlinarith
  have hA2 : A ^ 2 - B ^ 2 = (a * b)⁻¹ := by
    dsimp [A, B]
    have hb0 : b ≠ 0 := ne_of_gt hb
    have ha0 : a ≠ 0 := ne_of_gt ha
    field_simp [ha0, hb0]
    ring
  have hsqrtAB : Real.sqrt (A ^ 2 - B ^ 2) = (Real.sqrt (a * b))⁻¹ := by
    rw [hA2, Real.sqrt_inv]
  calc
    (∫ u in (0 : ℝ)..1, (chart (b⁻¹) (a⁻¹) u)⁻¹)
        = (∫ u in (0 : ℝ)..1, (A + B * Real.cos (Real.pi * u))⁻¹) := by
          simp_rw [hchart]
    _ = (Real.sqrt (A ^ 2 - B ^ 2))⁻¹ := Submission.ReciprocalIntegral.integral_inv_affine_cos_pi_mul hBpos hBA
    _ = Real.sqrt (a * b) := by
          rw [hsqrtAB]
          rw [inv_inv]

end Submission.Serre
