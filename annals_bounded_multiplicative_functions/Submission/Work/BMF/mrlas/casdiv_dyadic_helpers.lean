import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Technical helpers for the dyadic summation of the per-scale bound

(Bounded multiplicative functions, Ramaré's `casdiv`, step 8.)

This module collects the elementary analytic facts used by
`Work.BMF.mrlas.casdiv_dyadic_sum_meas` and its auxiliary lemmas
`Work.BMF.mrlas.casdiv_wsum_dyadic` (the `W`-sum bound) and
`Work.BMF.mrlas.casdiv_zsum_dyadic` (the `Z`-sum bound):

* `intervalIntegrable_M_div_sq` : `t ↦ M t / t²` is interval-integrable on any interval with
  positive endpoints, when `M` is measurable, nonnegative on `[0,∞)` and `M t ≤ t`;
* `intervalIntegrable_W_div` : `α ↦ W α / α` is interval-integrable on `[a,b] ⊆ (0,1]` when `W`
  is measurable, nonnegative on `(0,1]` and bounded by `c ≥ 0` there;
* `sqrt_exp_two_pow` : `√(e^{2^{k+1}}) = e^{2^k}`, the "`y_k = √(y_{k+1})`" identity of the dyadic
  cover of `[e, x]` by the intervals `[e^{2^k}, e^{2^{k+1}}]`.
-/

namespace Work.BMF.mrlas

open MeasureTheory Set intervalIntegral

set_option autoImplicit false

/-- For `M` measurable, nonnegative on `[0,∞)` and dominated by the identity, the function
`t ↦ M t / t²` is integrable on the half-open interval `(a, b]` with `0 < a ≤ b`
(bounded by `1 / a` there, and `M t ≤ t` gives `M t / t² ≤ 1 / t`). -/
lemma intervalIntegrable_M_div_sq_of_le {M : ℝ → ℝ} (hMmeas : Measurable M)
    (hMnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ M t) (hMle : ∀ t : ℝ, 0 ≤ t → M t ≤ t)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => M t / t ^ 2) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top ?_ (1 / a) ?_
  · exact ((hMmeas.div (measurable_id.pow_const 2)).aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := lt_trans ha ht.1
    have h2 : (0 : ℝ) < t ^ 2 := by positivity
    have hnn : 0 ≤ M t / t ^ 2 := div_nonneg (hMnn t ht0.le) h2.le
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    calc M t / t ^ 2 ≤ t / t ^ 2 := div_le_div_of_nonneg_right (hMle t ht0.le) h2.le
      _ = 1 / t := by
            rw [div_eq_div_iff (ne_of_gt h2) (ne_of_gt ht0)]
            ring
      _ ≤ 1 / a := one_div_le_one_div_of_le ha ht.1.le

/-- Two-sided version of `intervalIntegrable_M_div_sq_of_le`. -/
lemma intervalIntegrable_M_div_sq {M : ℝ → ℝ} (hMmeas : Measurable M)
    (hMnn : ∀ t : ℝ, 0 ≤ t → 0 ≤ M t) (hMle : ∀ t : ℝ, 0 ≤ t → M t ≤ t)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IntervalIntegrable (fun t : ℝ => M t / t ^ 2) volume a b := by
  rcases le_total a b with h | h
  · exact intervalIntegrable_M_div_sq_of_le hMmeas hMnn hMle ha h
  · exact (intervalIntegrable_M_div_sq_of_le hMmeas hMnn hMle hb h).symm

/-- For `W` measurable, nonnegative on `(0,1]` and bounded by `c ≥ 0` there, the function
`α ↦ W α / α` is integrable on `[a,b] ⊆ (0,1]` (bounded by `c / a`). -/
lemma intervalIntegrable_W_div {W : ℝ → ℝ} (hWmeas : Measurable W) {c : ℝ} (hc : 0 ≤ c)
    (hWbd : ∀ α : ℝ, 0 < α → α ≤ 1 → W α ≤ c)
    (hWnn : ∀ α : ℝ, 0 < α → α ≤ 1 → 0 ≤ W α)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    IntervalIntegrable (fun α : ℝ => W α / α) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  refine MeasureTheory.IntegrableOn.of_bound measure_Ioc_lt_top ?_ (c / a) ?_
  · exact ((hWmeas.div measurable_id).aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht0 : 0 < t := lt_trans ha ht.1
    have ht1 : t ≤ 1 := le_trans ht.2 hb1
    have hbnd : W t ≤ c := hWbd t ht0 ht1
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hWnn t ht0 ht1) ht0.le)]
    calc W t / t ≤ c / t := div_le_div_of_nonneg_right hbnd ht0.le
      _ ≤ c / a := div_le_div_of_nonneg_left hc ha ht.1.le

/-- The dyadic scales `y_k = e^{2^k}` satisfy `√(y_{k+1}) = y_k`; equivalently
`(e^{2^k})² = e^{2^{k+1}}`. -/
lemma sqrt_exp_two_pow (k : ℕ) :
    Real.sqrt (Real.exp ((2 : ℝ) ^ (k + 1))) = Real.exp ((2 : ℝ) ^ k) := by
  have hpos : 0 ≤ Real.exp ((2 : ℝ) ^ k) := (Real.exp_pos _).le
  have h : ((2 : ℝ) ^ k) + ((2 : ℝ) ^ k) = (2 : ℝ) ^ (k + 1) := by
    rw [pow_succ']; ring
  calc Real.sqrt (Real.exp ((2 : ℝ) ^ (k + 1)))
      = Real.sqrt ((Real.exp ((2 : ℝ) ^ k)) ^ 2) := by rw [sq, ← Real.exp_add, h]
    _ = Real.exp ((2 : ℝ) ^ k) := Real.sqrt_sq hpos

end Work.BMF.mrlas
