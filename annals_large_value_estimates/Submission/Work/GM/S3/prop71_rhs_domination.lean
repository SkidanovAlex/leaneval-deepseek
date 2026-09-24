import Mathlib
import Submission.Work.GM.S3.prop71_defs
import Submission.Work.GM.S3.prop71_pbox_measure

namespace Work.GM.S3

open MeasureTheory

/-- In the statement of `Work.GM.S3.prop71_main` the term `+ C · N^{-20}` is *inside* the body of
the integral `∫_{v ∈ pbox}` (the body of `∫ v in s, …` extends as far right as possible).  This
states that the resulting right-hand side still dominates `C N³ ∫_{pbox} g + C N^{-20}`, where
`g = 1_{|phas| ≤ τ}·‖Rprod‖ ≥ 0`:

`C N³ ∫_{pbox} g + C N^{-20} ≤ C N³ ∫_{pbox} (g + C N^{-20})`.

Indeed `∫_{pbox}(g + c) = ∫_{pbox} g + c · vol(pbox) = ∫_{pbox} g + (9/4)c` for `c = C N^{-20}`
(additivity of the set integral, `MeasureTheory.integral_indicator`,
`MeasureTheory.setIntegral_const`, `Work.GM.S3.prop71_pbox_measure`), so the difference of the two
sides is `(9/4) C² N^{-17} - C N^{-20} = C N^{-20} ((9/4) C N³ - 1) ≥ 0` because `C ≥ 1` and
`N ≥ 1`. -/
theorem prop71_rhs_domination (N : ℕ) (hN : 1 ≤ N) (η : ℝ) (hη : 0 < η) (C : ℝ) (hC : 1 ≤ C)
    (W : Finset ℝ) (m : ℤ × ℤ × ℤ) :
    C * (N : ℝ) ^ 3 * (∫ v in pbox, (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
        then ‖Rprod W v‖ else 0)) + C * (N : ℝ) ^ (-20 : ℤ)
    ≤ C * (N : ℝ) ^ 3 * (∫ v in pbox,
        ((if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
          then ‖Rprod W v‖ else 0) + C * (N : ℝ) ^ (-20 : ℤ))) := by
  have _ := hη
  -- Measurability of the `v`-integrand `g`.
  have hphas_meas : Measurable (fun v : ℝ × ℝ => phas m v) := by
    unfold phas; fun_prop
  have hmeas : Measurable (fun v : ℝ × ℝ =>
      (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ) then ‖Rprod W v‖ else 0)) := by
    refine Measurable.ite ?_ ?_ measurable_const
    · exact measurableSet_le (continuous_abs.measurable.comp hphas_meas) measurable_const
    · exact (Rprod_measurable W).norm
  -- `pbox` has finite volume, so constants are integrable on it.
  have hne : (MeasureTheory.volume : Measure (ℝ × ℝ)) pbox ≠ ⊤ := by
    intro h
    have h2 := prop71_pbox_measure
    rw [h] at h2
    norm_num at h2
  -- `g` is bounded by `|W|³`, hence integrable on `pbox`.
  have hconst_int :
      Integrable (fun _ : ℝ × ℝ => (W.card : ℝ) ^ 3) (MeasureTheory.volume.restrict pbox) :=
    MeasureTheory.integrableOn_const hne
  have hbound : ∀ v : ℝ × ℝ, ‖(if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
      then ‖Rprod W v‖ else 0)‖ ≤ (W.card : ℝ) ^ 3 := by
    intro v
    split_ifs with h
    · simpa using norm_Rprod_le W v
    · simp
  have hint_g : Integrable (fun v : ℝ × ℝ =>
      (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
        then ‖Rprod W v‖ else 0)) (MeasureTheory.volume.restrict pbox) :=
    hconst_int.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  have hint_c : Integrable (fun _ : ℝ × ℝ => C * (N : ℝ) ^ (-20 : ℤ))
      (MeasureTheory.volume.restrict pbox) :=
    MeasureTheory.integrableOn_const hne
  -- Additivity of the set integral and `vol(pbox) = 9/4`.
  have hsplit : ∫ v in pbox, ((if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
        then ‖Rprod W v‖ else 0) + C * (N : ℝ) ^ (-20 : ℤ))
      = (∫ v in pbox, (if |phas m v| ≤ (Submission.LargeValues.M N) ^ η / (N : ℝ)
        then ‖Rprod W v‖ else 0)) + C * (N : ℝ) ^ (-20 : ℤ) * (9 / 4) := by
    rw [MeasureTheory.integral_add hint_g hint_c]
    congr 1
    rw [MeasureTheory.setIntegral_const, MeasureTheory.Measure.real_def, prop71_pbox_measure]
    ring
  have hX : 1 ≤ C * (N : ℝ) ^ 3 := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hN3 : (1 : ℝ) ≤ (N : ℝ) ^ 3 := one_le_pow₀ hN1
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ C * (N : ℝ) ^ 3 := mul_le_mul hC hN3 zero_le_one (by linarith)
  have hz : 0 ≤ C * (N : ℝ) ^ (-20 : ℤ) :=
    mul_nonneg (by linarith) (zpow_nonneg (by positivity) _)
  rw [hsplit]
  nlinarith [hX, hz]

end Work.GM.S3
