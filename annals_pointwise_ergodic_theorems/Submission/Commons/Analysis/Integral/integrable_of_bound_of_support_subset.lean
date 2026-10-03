import Mathlib.MeasureTheory.Function.L1Space.Integrable

namespace Commons.Analysis.Integral

theorem integrable_of_bound_of_support_subset {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α} {E : Type*} [NormedAddCommGroup E] {f : α → E} {S : Set α} {C : ℝ} (hS : MeasurableSet S) (hSfin : μ S ≠ ⊤) (hsm : MeasureTheory.AEStronglyMeasurable f μ) (hb : ∀ x, ‖f x‖ ≤ C) (hsupp : ∀ x, x ∉ S → f x = 0) : MeasureTheory.Integrable f μ := by
  refine ⟨hsm, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  have hbound : ∫⁻ a, ‖f a‖ₑ ∂μ ≤ ENNReal.ofReal C * μ S := by
    calc ∫⁻ a, ‖f a‖ₑ ∂μ
        ≤ ∫⁻ a, S.indicator (fun _ => ENNReal.ofReal C) a ∂μ :=
          MeasureTheory.lintegral_mono (fun a => by
            by_cases ha : a ∈ S
            · rw [Set.indicator_of_mem ha]
              simpa using ENNReal.ofReal_le_ofReal (hb a)
            · rw [Set.indicator_of_notMem ha, hsupp a ha]
              simp)
      _ = ENNReal.ofReal C * μ S := MeasureTheory.lintegral_indicator_const hS _
  exact lt_of_le_of_lt hbound (ENNReal.mul_lt_top
    (lt_top_iff_ne_top.mpr ENNReal.ofReal_ne_top) (lt_top_iff_ne_top.mpr hSfin))

end Commons.Analysis.Integral