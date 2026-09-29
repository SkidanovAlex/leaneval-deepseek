import Mathlib

namespace Work.ANum3

open MeasureTheory intervalIntegral

/-- If `g 0 = 0` and `‖g' t‖ ≤ K * t` on `[0,1]`, then `‖g 1‖ ≤ K / 2`. -/
theorem norm_one_le_of_hasDerivAt_norm_le {g g' : ℝ → ℂ} {K : ℝ}
    (hd : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt g (g' t) t)
    (hc : ContinuousOn g' (Set.uIcc (0:ℝ) 1))
    (h0 : g 0 = 0)
    (hb : ∀ t ∈ Set.uIcc (0:ℝ) 1, ‖g' t‖ ≤ K * t) :
    ‖g 1‖ ≤ K / 2 := by
  have hI : IntervalIntegrable g' volume (0:ℝ) 1 := hc.intervalIntegrable
  have hftc : ∫ t in (0:ℝ)..1, g' t = g 1 - g 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hd hI
  have hbnd : IntervalIntegrable (fun t : ℝ => K * t) volume (0:ℝ) 1 :=
    (continuous_const.mul continuous_id).continuousOn.intervalIntegrable
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Ioc (0:ℝ) 1 → ‖g' t‖ ≤ K * t := by
    filter_upwards with t ht
    exact hb t (by rw [Set.uIcc_of_le zero_le_one]; exact Set.Ioc_subset_Icc_self ht)
  have hineq : ‖∫ t in (0:ℝ)..1, g' t‖ ≤ ∫ t in (0:ℝ)..1, K * t :=
    intervalIntegral.norm_integral_le_of_norm_le zero_le_one hae hbnd
  have hint : ∫ t in (0:ℝ)..1, K * t = K / 2 := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  have hnorm : ‖g 1‖ = ‖∫ t in (0:ℝ)..1, g' t‖ := by rw [hftc, h0, sub_zero]
  rw [hnorm]
  exact hineq.trans_eq hint

end Work.ANum3
