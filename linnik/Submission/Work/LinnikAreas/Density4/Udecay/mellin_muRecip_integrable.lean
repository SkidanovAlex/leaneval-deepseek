import Mathlib
import Submission.Work.LinnikAreas.Density4.Udecay.recip_bound
import Submission.Work.LinnikAreas.Density4.Udecay.exp_sqrtlog_integrable

namespace Work.LinnikAreas.Density4.Udecay

open MeasureTheory

/-- `A(t)/t^{1+s}` is integrable on `[1, ∞)` for every `s > 0`.

The decay `|A(t)| ≤ C exp(-c √(log t))` of `recip_bound` dominates `A(t)/t^{1+s}` by
`C · exp(-c √(log t))/t` (using `t^{1+s} ≥ t` for `t ≥ 1`), and the latter is integrable on
`(1, ∞)` by `exp_sqrtlog_integrable`.  Passing from `(1, ∞)` to `[1, ∞)` removes a single
point. -/
theorem mellin_muRecip_integrable {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn
      (fun t : ℝ => Work.LinnikAreas.Density4.muRecip t / t ^ (1 + s : ℝ)) (Set.Ici 1) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  obtain ⟨c, C, hc, _hC, hbound⟩ := recip_bound
  obtain ⟨hint1, _⟩ := exp_sqrtlog_integrable hc
  have hmeasM : Measurable (fun t : ℝ => Work.LinnikAreas.Density4.muRecip t) :=
    (measurable_of_countable Commons.NumberTheory.Moebius.muRecipSum).comp Nat.measurable_floor
  have hg_meas : AEStronglyMeasurable
      (fun t : ℝ => Work.LinnikAreas.Density4.muRecip t / t ^ (1 + s : ℝ))
      (volume.restrict (Set.Ioi 1)) :=
    (hmeasM.div
      ((Real.continuous_rpow_const (by linarith : (0:ℝ) ≤ 1 + s)).measurable)).aestronglyMeasurable
  refine (hint1.const_mul C).mono' hg_meas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : (1:ℝ) ≤ t := le_of_lt ht
  have ht0 : (0:ℝ) < t := lt_trans zero_lt_one ht
  have hpowpos : (0:ℝ) < t ^ (1 + s : ℝ) := Real.rpow_pos_of_pos ht0 _
  have hpowge : t ≤ t ^ (1 + s : ℝ) := by
    calc t = t ^ (1 : ℝ) := (Real.rpow_one t).symm
      _ ≤ t ^ (1 + s : ℝ) := Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hpowpos]
  have hnn : (0:ℝ) ≤ C * Real.exp (-(c * Real.sqrt (Real.log t))) := by positivity
  calc |Work.LinnikAreas.Density4.muRecip t| / t ^ (1 + s : ℝ)
      ≤ C * Real.exp (-(c * Real.sqrt (Real.log t))) / t ^ (1 + s : ℝ) :=
        div_le_div_of_nonneg_right (hbound t ht1) (le_of_lt hpowpos)
    _ ≤ C * Real.exp (-(c * Real.sqrt (Real.log t))) / t :=
        div_le_div_of_nonneg_left hnn ht0 hpowge
    _ = C * (Real.exp (-(c * Real.sqrt (Real.log t))) / t) := by ring

end Work.LinnikAreas.Density4.Udecay
