import Mathlib
import Submission.Commons.Analysis.Fourier.nested_scales_maximal_l2_real

namespace Commons.Analysis.Fourier

open MeasureTheory

theorem bandOp_sq_integral_le (C : Set ℝ) (hC : MeasurableSet C) (hCb : Bornology.IsBounded C)
    (f : ℝ → ℂ) (hf1 : MeasureTheory.Integrable f)
    (hf2 : MeasureTheory.MemLp f 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ)) :
    ∫ x : ℝ, ‖bandOp C f x‖ ^ 2 ≤ ∫ x : ℝ, ‖f x‖ ^ 2 := by
  have hmem : MemLp (bandOp C f) 2 (volume : Measure ℝ) :=
    bandOp_memLp C hC hCb f hf1 hf2
  have hb := bandOp_lintegral C hC hCb f hf1 hf2
  rw [NestedIndicator.lintegral_enorm_rpow_two volume hmem,
    NestedIndicator.lintegral_enorm_rpow_two volume hf2] at hb
  have h1 : (∫ x : ℝ, ‖bandOp C f x‖ ^ (2:ℝ)) = ∫ x : ℝ, ‖bandOp C f x‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact Real.rpow_two _
  have h2 : (∫ x : ℝ, ‖f x‖ ^ (2:ℝ)) = ∫ x : ℝ, ‖f x‖ ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    exact Real.rpow_two _
  rw [h1, h2] at hb
  exact (ENNReal.ofReal_le_ofReal_iff
    (MeasureTheory.integral_nonneg (fun x => by positivity))).mp hb

end Commons.Analysis.Fourier
