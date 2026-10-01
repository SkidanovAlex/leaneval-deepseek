import Mathlib
import Submission.Work.LinnikAreas.Density4.selberg_U_aux
import Submission.Commons.NumberTheory.Moebius.sum_moebius_div_abs_le

namespace Work.LinnikAreas.Density4.Udecay

open MeasureTheory

/-- `t ↦ A(t)/t` with `A(t) = Σ_{m ≤ ⌊t⌋} μ(m)/m` is interval integrable on `[a,b]` whenever
`1 ≤ a ≤ b`.

`A` is the step function `t ↦ muRecipSum ⌊t⌋₊`, hence measurable; on `[a,b]` the partial sums
`muRecipSum ⌊t⌋₊` are uniformly bounded (by `sum_moebius_div_abs_le`) and `1/t ≤ 1` because
`t > a ≥ 1`, so `|A(t)/t|` is bounded on the (finite measure) interval. -/
theorem intervalIntegrable_muRecip_div (a b : ℝ) (ha : 1 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => Work.LinnikAreas.Density4.muRecip t / t) MeasureTheory.volume a b := by
  obtain ⟨C, hCpos, hCbound⟩ := Commons.NumberTheory.Moebius.sum_moebius_div_abs_le
  have hmeasM : Measurable (fun t : ℝ => Work.LinnikAreas.Density4.muRecip t) :=
    (measurable_of_countable Commons.NumberTheory.Moebius.muRecipSum).comp Nat.measurable_floor
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine IntegrableOn.of_bound ?_ (hmeasM.div measurable_id).aestronglyMeasurable C ?_
  · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht1 : (1 : ℝ) < t := lt_of_le_of_lt ha ht.1
    have htpos : (0 : ℝ) < t := lt_trans zero_lt_one ht1
    have hfl : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by exact_mod_cast ht1.le : ((1 : ℕ) : ℝ) ≤ t)
    have hmu : |Work.LinnikAreas.Density4.muRecip t| ≤ C := by
      have h := hCbound ⌊t⌋₊ hfl
      simpa [Work.LinnikAreas.Density4.muRecip, Commons.NumberTheory.Moebius.muRecipSum] using h
    rw [Real.norm_eq_abs, abs_div, abs_of_pos htpos]
    calc |Work.LinnikAreas.Density4.muRecip t| / t
          ≤ |Work.LinnikAreas.Density4.muRecip t| := div_le_self (abs_nonneg _) ht1.le
      _ ≤ C := hmu

end Work.LinnikAreas.Density4.Udecay
