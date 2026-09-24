import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiSharpCrude

namespace Work.NumberTheory.Chen.APSwitchUpper

/-! Conjuncts 1 and 2 of the six in
`Work.NumberTheory.Chen.APSwitchUpper.crudePairHypotheses`: local integrability of the
crude exponential majorants
`crudeU s = if s < 1 then 8 else if s ≤ 3 then (9-s)/s else 2 exp(3-s)`,
`crudeV s = 6 exp(2-s)` of `Submission...APSwitchUpper.riPhiSharpCrude`.

`crudeV` is continuous (`Continuous.intervalIntegrable`); `crudeU` is measurable (a nested
`if` of measurable pieces) and globally bounded by `8` (`2 ≤ (9-s)/s ≤ 8` on `[1,3]` and
`2 exp (3-s) ≤ 2` for `s ≥ 3`), so each of the two `IntegrableOn` components of
`IntervalIntegrable` follows from `IntegrableOn.of_bound` (`AEStronglyMeasurable` + an a.e.
bound, the restricted measure being finite). -/

open MeasureTheory

theorem crudeU_measurable : Measurable crudeU := by
  unfold crudeU
  exact Measurable.ite measurableSet_Iio measurable_const
    (Measurable.ite measurableSet_Iic (by measurability) (by measurability))

theorem crudeU_norm_le (s : ℝ) : ‖crudeU s‖ ≤ 8 := by
  unfold crudeU
  by_cases h1 : s < 1
  · rw [if_pos h1]; norm_num
  · rw [if_neg h1]
    by_cases h3 : s ≤ 3
    · rw [if_pos h3]
      have hs : 0 < s := by linarith
      have h9 : 0 ≤ 9 - s := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg h9 (le_of_lt hs))]
      rw [div_le_iff₀ hs]
      linarith
    · rw [if_neg h3]
      have hexp : 0 ≤ Real.exp (3 - s) := le_of_lt (Real.exp_pos _)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have he : Real.exp (3 - s) ≤ 1 := by
        rw [Real.exp_le_one_iff]; linarith
      linarith

theorem crudeV_continuous : Continuous crudeV := by
  unfold crudeV; fun_prop

theorem crudeUV_intervalIntegrable :
    (∀ a b : ℝ, IntervalIntegrable Work.NumberTheory.Chen.APSwitchUpper.crudeU MeasureTheory.volume a b)
  ∧ (∀ a b : ℝ, IntervalIntegrable Work.NumberTheory.Chen.APSwitchUpper.crudeV MeasureTheory.volume a b) := by
  refine ⟨?_, ?_⟩
  · intro a b
    rw [intervalIntegrable_iff]
    refine IntegrableOn.of_bound ?hfin ?hsm 8 ?hb
    · rw [Real.volume_uIoc]; exact ENNReal.ofReal_lt_top
    · exact crudeU_measurable.aestronglyMeasurable.restrict
    · exact Filter.Eventually.of_forall crudeU_norm_le
  · intro a b
    exact crudeV_continuous.intervalIntegrable a b

end Work.NumberTheory.Chen.APSwitchUpper
