import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open MeasureTheory Set

lemma integrableStepPeak {φ U : ℝ → ℝ} (hφ : Measurable φ) (hU : Measurable U)
    (hU_nn : ∀ x, 0 ≤ U x) (hint : MeasureTheory.Integrable (fun x => φ x * U x)) :
    MeasureTheory.Integrable
      (Function.uncurry (fun x t : ℝ => if 0 < t ∧ t ≤ U x then φ x else (0:ℝ)))
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
  classical
  set f : ℝ × ℝ → ℝ :=
    Function.uncurry (fun x t : ℝ => if 0 < t ∧ t ≤ U x then φ x else (0:ℝ)) with hf_def
  set A : Set (ℝ × ℝ) := {p | p.2 ∈ Set.Ioc (0:ℝ) (U p.1)} with hA_def
  have hA : MeasurableSet A := by
    rw [hA_def]
    simpa using (measurableSet_region_between_oc (f := fun _ : ℝ => (0:ℝ)) (g := U)
      measurable_const hU MeasurableSet.univ)
  have hmem : ∀ x t : ℝ, ((x, t) ∈ A) ↔ (0 < t ∧ t ≤ U x) := by
    intro x t
    rw [hA_def]
    simp
  have hf_eq : f = A.indicator (fun p : ℝ × ℝ => φ p.1) := by
    funext p
    obtain ⟨x, t⟩ := p
    rw [hf_def, Function.uncurry_apply_pair]
    simp only [Set.indicator_apply, hmem x t]
  have hf_meas : Measurable f := by
    rw [hf_eq]
    exact (hφ.comp measurable_fst).indicator hA
  refine ⟨hf_meas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  set c : ℝ × ℝ → ENNReal := fun p => ENNReal.ofReal ‖φ p.1‖ with hc_def
  have hc_meas : Measurable c := by
    rw [hc_def]
    exact ENNReal.measurable_ofReal.comp (hφ.norm.comp measurable_fst)
  have hF_eq : (fun p : ℝ × ℝ => ENNReal.ofReal ‖f p‖) = A.indicator c := by
    funext p
    obtain ⟨x, t⟩ := p
    rw [hf_eq, Set.indicator_apply]
    by_cases h : (x, t) ∈ A <;> simp [h, hc_def]
  have hAEM : AEMeasurable (A.indicator c)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :=
    (hc_meas.indicator hA).aemeasurable
  have hinner : ∀ x : ℝ, ∫⁻ t, (A.indicator c) (x, t) ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ)
      = ENNReal.ofReal ‖φ x‖ * ENNReal.ofReal (U x) := by
    intro x
    have hpt : (fun t : ℝ => (A.indicator c) (x, t))
        = (Set.Ioc (0:ℝ) (U x)).indicator (fun _ => ENNReal.ofReal ‖φ x‖) := by
      funext t
      simp only [Set.indicator_apply, hmem x t, Set.mem_Ioc]
      by_cases h : 0 < t ∧ t ≤ U x <;> simp [h, hc_def]
    rw [hpt, lintegral_indicator_const measurableSet_Ioc, Real.volume_Ioc]
    simp
  have hint' : ∫⁻ x, ENNReal.ofReal ‖φ x * U x‖ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) < ⊤ :=
    (hasFiniteIntegral_iff_norm (fun x : ℝ => φ x * U x)).mp hint.hasFiniteIntegral
  calc
    ∫⁻ p, ENNReal.ofReal ‖f p‖
        ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod (MeasureTheory.volume : MeasureTheory.Measure ℝ))
        = ∫⁻ p, (A.indicator c) p
            ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod (MeasureTheory.volume : MeasureTheory.Measure ℝ)) := by
          rw [hF_eq]
    _ = ∫⁻ x, ∫⁻ t, (A.indicator c) (x, t)
            ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
          lintegral_prod _ hAEM
    _ = ∫⁻ x, ENNReal.ofReal ‖φ x‖ * ENNReal.ofReal (U x)
            ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
          lintegral_congr hinner
    _ = ∫⁻ x, ENNReal.ofReal (‖φ x‖ * U x) ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
          lintegral_congr (fun x => (ENNReal.ofReal_mul (norm_nonneg (φ x))).symm)
    _ = ∫⁻ x, ENNReal.ofReal ‖φ x * U x‖ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ) :=
          lintegral_congr (fun x => by rw [norm_mul, Real.norm_of_nonneg (hU_nn x)])
    _ < ⊤ := hint'

end Work.BW
