import Mathlib
import Submission.ModelStarMap
import Submission.ModelStarExterior
import Submission.ModelStarPotential

/-!
# ModelStarHarmMeasure -- the harmonic measure `μ₀ = F_*(dθ/2π)` of the model star

STATUS: research isolate (NOT imported by `Submission.lean`); 0 sorries.

The harmonic measure of the model star `M = F '' unitCircle` (from `∞`) is the
pushforward of the normalised arclength on the circle under the model boundary
map `θ ↦ F(e^{iθ})`.  This module constructs it as an honest `Measure ℂ` and
records the identities needed by the `(N1)` chain of STATUS §124.
-/

noncomputable section

open scoped Real BigOperators Topology ENNReal
open Filter Set Complex MeasureTheory

namespace Submission.ModelStarHarmMeasure

open Submission.ModelStarMap
open Submission.ModelStarExterior (modelStarImage unitCircle isCompact_modelStarImage)

variable {s : ℕ} {z₀ : Fin s → ℂ} {r φ : Fin s → ℝ}

/-- The normalised arclength measure on `[0, 2π)` (total mass `1`). -/
noncomputable def circleMeasure : MeasureTheory.Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • MeasureTheory.volume.restrict (Set.Ioc 0 (2 * Real.pi))

/-- The harmonic measure of the model star: the pushforward of the normalised
arclength on the circle under `θ ↦ F(e^{iθ})`. -/
noncomputable def harmMeasure (z₀ : Fin s → ℂ) (r : Fin s → ℝ) : MeasureTheory.Measure ℂ :=
  MeasureTheory.Measure.map (fun θ : ℝ => modelF z₀ r (Complex.exp ((θ : ℂ) * Complex.I)))
    (circleMeasure : MeasureTheory.Measure ℝ)

/-- `(ofReal c)⁻¹ * ofReal c = 1` for `c > 0`. -/
lemma ofReal_inv_mul_self {c : ℝ} (h : 0 < c) :
    (ENNReal.ofReal c)⁻¹ * ENNReal.ofReal c = 1 := by
  rw [← ENNReal.ofReal_inv_of_pos h,
    ← ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr h)), inv_mul_cancel₀ h.ne',
    ENNReal.ofReal_one]

lemma circleMeasure_apply_Ioc :
    circleMeasure (Set.Ioc 0 (2 * Real.pi)) = 1 := by
  rw [circleMeasure, MeasureTheory.Measure.smul_apply,
    MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
  rw [Set.inter_self, Real.volume_Ioc, sub_zero]
  have h1 : (0:ℝ) < 2 * Real.pi := by positivity
  show (ENNReal.ofReal (2 * Real.pi))⁻¹ * ENNReal.ofReal (2 * Real.pi) = 1
  exact ofReal_inv_mul_self h1

/-- `modelF` is a measurable function. -/
lemma measurable_modelF (z₀ : Fin s → ℂ) (r : Fin s → ℝ) :
    Measurable (modelF z₀ r) := by
  have h : modelF z₀ r = fun z : ℂ =>
      z * ∏ k : Fin s, (1 - z₀ k * z⁻¹) ^ (((2 * r k : ℝ)) : ℂ) := by
    funext z
    simp only [modelF, modelProduct, modelFactor]
  rw [h]
  refine Measurable.mul measurable_id ?_
  refine Finset.measurable_prod _ (fun k _ => ?_)
  fun_prop

lemma meas_circleMap_modelF (z₀ : Fin s → ℂ) (r : Fin s → ℝ) :
    Measurable (fun θ : ℝ => modelF z₀ r (Complex.exp ((θ : ℂ) * Complex.I))) :=
  (measurable_modelF z₀ r).comp
    (Complex.measurable_exp.comp (by fun_prop : Measurable (fun θ : ℝ => (θ : ℂ) * Complex.I)))

lemma harmMeasure_apply {A : Set ℂ} (hA : MeasurableSet A) :
    harmMeasure z₀ r A
      = circleMeasure {θ : ℝ | modelF z₀ r (Complex.exp ((θ : ℂ) * Complex.I)) ∈ A} := by
  rw [harmMeasure, MeasureTheory.Measure.map_apply (meas_circleMap_modelF z₀ r) hA]
  rfl

instance (z₀ : Fin s → ℂ) (r : Fin s → ℝ) :
    MeasureTheory.IsProbabilityMeasure (harmMeasure z₀ r) := by
  constructor
  rw [harmMeasure,
    MeasureTheory.Measure.map_apply (meas_circleMap_modelF z₀ r) MeasurableSet.univ,
    Set.preimage_univ, circleMeasure, MeasureTheory.Measure.smul_apply,
    MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc,
    sub_zero]
  have h1 : (0:ℝ) < 2 * Real.pi := by positivity
  show (ENNReal.ofReal (2 * Real.pi))⁻¹ * ENNReal.ofReal (2 * Real.pi) = 1
  exact ofReal_inv_mul_self h1

/-- The harmonic measure is carried by the model star. -/
theorem harmMeasure_compl_eq_zero (hunit : ∀ k, ‖z₀ k‖ = 1) (hr : ∀ k, 0 < r k) :
    harmMeasure z₀ r (modelStarImage z₀ r)ᶜ = 0 := by
  rw [harmMeasure_apply (A := (modelStarImage z₀ r)ᶜ)
    (isCompact_modelStarImage z₀ r hunit hr).isClosed.measurableSet.compl]
  have hsub : {θ : ℝ | modelF z₀ r (Complex.exp ((θ : ℂ) * Complex.I)) ∈ (modelStarImage z₀ r)ᶜ}
      ⊆ (Set.Ioc 0 (2 * Real.pi))ᶜ := by
    intro θ hθ
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hθ ⊢
    intro hmem
    exact hθ ⟨Complex.exp ((θ : ℂ) * Complex.I),
      Submission.ModelStarExterior.mem_circle.mpr (Complex.norm_exp_ofReal_mul_I θ), rfl⟩
  refine MeasureTheory.measure_mono_null hsub ?_
  have h0 : (MeasureTheory.Measure.restrict MeasureTheory.volume
      (Set.Ioc 0 (2 * Real.pi))) ((Set.Ioc 0 (2 * Real.pi))ᶜ) = 0 := by
    rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc.compl, Set.compl_inter_self,
      measure_empty]
  rw [circleMeasure, MeasureTheory.Measure.smul_apply, h0, smul_zero]

/-- Change of variables: integration against the harmonic measure is the
normalised integral over the circle. -/
lemma lintegral_harmMeasure {g : ℂ → ENNReal} (hg : Measurable g) :
    ∫⁻ y, g y ∂(harmMeasure z₀ r)
      = (ENNReal.ofReal (2 * Real.pi))⁻¹ *
          ∫⁻ θ in Set.Ioc 0 (2 * Real.pi),
            g (modelF z₀ r (Complex.exp ((θ : ℂ) * Complex.I))) := by
  rw [harmMeasure, MeasureTheory.lintegral_map hg (meas_circleMap_modelF z₀ r), circleMeasure,
    MeasureTheory.lintegral_smul_measure]
  rfl

end Submission.ModelStarHarmMeasure
