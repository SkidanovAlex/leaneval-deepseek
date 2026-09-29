import Mathlib
import Submission.Work.TMComp.IDSEqui.defs

namespace Work.TMComp.IDSEqui

/-- The trapezium `minor δ δ'` is `1` on the two end intervals `[0, δ']` and `[1 - δ', 1]` and
nonnegative in between, so its integral over `[0, 1]` is at least `2 δ'` whenever `δ' ≤ 1 / 2`. -/
theorem integralRamp (δ δ' : ℝ) (h0 : 0 < δ') (h1 : δ' < δ) (h2 : δ ≤ 1 / 2) :
    2 * δ' ≤ ∫ x in (0 : ℝ)..1, Work.TMComp.IDSEqui.minor δ δ' x := by
  have hδ' : δ' < 1 / 2 := lt_of_lt_of_le h1 h2
  have hle : δ' ≤ 1 - δ' := by linarith
  have hcont : Continuous (minor δ δ') := continuous_minor δ δ'
  have hint : ∀ a b : ℝ, IntervalIntegrable (minor δ δ') MeasureTheory.volume a b :=
    fun a b => hcont.intervalIntegrable a b
  -- `minor` is `1` on `[0, δ']`
  have hI1 : (∫ x in (0 : ℝ)..δ', minor δ δ' x) = δ' := by
    have hcongr : (∫ x in (0 : ℝ)..δ', minor δ δ' x)
        = ∫ x in (0 : ℝ)..δ', (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le h0.le] at hx
      have hxlt : x < 1 / 2 := lt_of_le_of_lt hx.2 hδ'
      have hfd : Work.TMContract.fracDist x = x := fracDist_eq_self hx.1 hxlt
      exact minor_eq_one h1 (by rw [hfd]; exact hx.2)
    rw [hcongr, intervalIntegral.integral_const]
    simp
  -- `minor` is `1` on `[1 - δ', 1]`
  have hI3 : (∫ x in (1 - δ')..(1 : ℝ), minor δ δ' x) = δ' := by
    have hcongr : (∫ x in (1 - δ')..(1 : ℝ), minor δ δ' x)
        = ∫ x in (1 - δ')..(1 : ℝ), (1 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by linarith : (1 - δ') ≤ 1)] at hx
      have h1x : 1 / 2 ≤ x := by linarith [hx.1]
      have hfd : Work.TMContract.fracDist x = 1 - x := fracDist_eq_one_sub h1x hx.2
      exact minor_eq_one h1 (by rw [hfd]; linarith [hx.1])
    rw [hcongr, intervalIntegral.integral_const]
    simp
  -- `minor` is nonnegative on the middle interval
  have hI2 : (0 : ℝ) ≤ ∫ x in δ'..(1 - δ'), minor δ δ' x :=
    intervalIntegral.integral_nonneg hle (fun u _ => minor_nonneg δ δ' u)
  -- split `[0, 1]`
  have hA : (∫ x in (0 : ℝ)..1, minor δ δ' x)
      = (∫ x in (0 : ℝ)..δ', minor δ δ' x)
        + (∫ x in δ'..1, minor δ δ' x) :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 δ') (hint δ' 1)).symm
  have hB : (∫ x in δ'..(1 : ℝ), minor δ δ' x)
      = (∫ x in δ'..(1 - δ'), minor δ δ' x)
        + (∫ x in (1 - δ')..1, minor δ δ' x) :=
    (intervalIntegral.integral_add_adjacent_intervals (hint δ' (1 - δ'))
      (hint (1 - δ') 1)).symm
  have hmain : (∫ x in (0 : ℝ)..1, minor δ δ' x)
      = (∫ x in (0 : ℝ)..δ', minor δ δ' x)
        + (∫ x in δ'..(1 - δ'), minor δ δ' x)
        + (∫ x in (1 - δ')..1, minor δ δ' x) := by
    rw [hA, hB]; ring
  rw [hmain]
  linarith [hI1, hI2, hI3]

end Work.TMComp.IDSEqui
