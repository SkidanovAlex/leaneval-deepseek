/-
# `Submission.Work.FIChain.RhoTailDoubleIntegralBound`

The `log C · log (b/a)` double-integral bound underlying the `ρ`-tail of the
`X² + Y⁴` sieve.  For a pointwise bounded, nonnegative kernel `F s t` one has

  `∫_a^b (∫_1^C F s t / s) dt / t ≤ B · log C · log (b/a)`.

The argument is the obvious one: for each `t` the inner integrand `F s t / s` is squeezed
between `0` and `B / s` on `s ∈ [1, C]`, so the inner integral is at most
`∫_1^C B/s = B log C`; dividing by the positive `t` and integrating against `dt/t` over
`[a, b]` gives `B log C · (log b - log a)`.  No measurability of `F` is assumed: the bounds
are established with `integral_mono_of_nonneg`, which only needs the *upper* function to be
integrable, and only the explicit `1/t` (a measurable function) has to be integrated exactly.

-/
import Mathlib

set_option autoImplicit false

namespace Work.FIChain

open MeasureTheory

/-- Double-integral bound for the `ρ`-tail: `∫_a^b (∫_1^C F s t / s) / t ≤ B log C log(b/a)`
for a nonnegative kernel `F` bounded above by `B` and `1 ≤ C`, `0 < a ≤ b`. -/
theorem RhoTailDoubleIntegralBound {F : ℝ → ℝ → ℝ} {a b C B : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hC : 1 ≤ C)
    (hFnn : ∀ s t, 0 ≤ F s t) (hFbd : ∀ s t, F s t ≤ B) (hB : 0 ≤ B) :
    (∫ t in a..b, (∫ s in (1 : ℝ)..C, F s t / s) / t) ≤ B * Real.log C * Real.log (b / a) := by
  have hC1 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hb : 0 < b := lt_of_lt_of_le ha hab
  -- Step 1: a uniform bound for the inner integral, at every fixed `t`.
  have hinner : ∀ t, (∫ s in (1 : ℝ)..C, F s t / s) ≤ B * Real.log C := by
    intro t
    rw [intervalIntegral.integral_of_le hC]
    -- `s ↦ B/s` is integrable on `(1, C]` because it is measurable and bounded by `B` there.
    have hg : Integrable (fun s : ℝ => B / s) (volume.restrict (Set.Ioc (1 : ℝ) C)) := by
      refine IntegrableOn.of_bound (measure_Ioc_lt_top (a := (1 : ℝ)) (b := C)) ?_ B ?_
      · exact (measurable_const.div measurable_id).aestronglyMeasurable
      · rw [ae_restrict_iff' measurableSet_Ioc]
        refine Filter.Eventually.of_forall (fun s hs => ?_)
        have hspos : 0 < s := lt_trans zero_lt_one hs.1
        have hs1 : (1 : ℝ) ≤ s := le_of_lt hs.1
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hB (le_of_lt hspos))]
        rw [div_le_iff₀ hspos]
        exact le_mul_of_one_le_right hB hs1
    have h1 : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Set.Ioc (1 : ℝ) C)]
        (fun s : ℝ => F s t / s) := by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall
        (fun s hs => div_nonneg (hFnn s t) (le_of_lt (lt_trans zero_lt_one hs.1)))
    have h2 : (fun s : ℝ => F s t / s) ≤ᵐ[volume.restrict (Set.Ioc (1 : ℝ) C)]
        (fun s : ℝ => B / s) := by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall
        (fun s hs => div_le_div_of_nonneg_right (hFbd s t) (le_of_lt (lt_trans zero_lt_one hs.1)))
    calc ∫ s in Set.Ioc (1 : ℝ) C, F s t / s ≤ ∫ s in Set.Ioc (1 : ℝ) C, B / s :=
          integral_mono_of_nonneg h1 hg h2
      _ = ∫ s in (1 : ℝ)..C, B / s := by rw [intervalIntegral.integral_of_le hC]
      _ = B * Real.log C := by
          have hfun : (fun s : ℝ => B / s) = fun s => B * s⁻¹ := by
            funext s; rw [div_eq_mul_inv]
          rw [hfun, intervalIntegral.integral_const_mul, integral_inv_of_pos zero_lt_one hC1,
            div_one]
  -- Step 2: the inner integral is nonnegative (needed only to divide by the positive `t`).
  have hinnernn : ∀ t, 0 ≤ ∫ s in (1 : ℝ)..C, F s t / s := by
    intro t
    refine intervalIntegral.integral_nonneg hC (fun s hs => ?_)
    exact div_nonneg (hFnn s t) (le_of_lt (lt_of_lt_of_le zero_lt_one hs.1))
  have hBlC : 0 ≤ B * Real.log C := mul_nonneg hB hlogC
  -- Step 3: replace the inner integral by its bound, and integrate `dt/t`.
  have hmain : (∫ t in a..b, (∫ s in (1 : ℝ)..C, F s t / s) / t)
      ≤ ∫ t in a..b, (B * Real.log C) / t := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    refine integral_mono_of_nonneg ?_ ?_ ?_
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall
        (fun t ht => div_nonneg (hinnernn t) (le_of_lt (lt_trans ha ht.1)))
    · refine IntegrableOn.of_bound (measure_Ioc_lt_top (a := a) (b := b)) ?_
        (B * Real.log C / a) ?_
      · exact (measurable_const.div measurable_id).aestronglyMeasurable
      · rw [ae_restrict_iff' measurableSet_Ioc]
        refine Filter.Eventually.of_forall (fun t ht => ?_)
        have htpos : 0 < t := lt_trans ha ht.1
        rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hBlC htpos.le)]
        exact div_le_div_of_nonneg_left hBlC ha ht.1.le
    · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Filter.Eventually.of_forall
        (fun t ht => div_le_div_of_nonneg_right (hinner t) (le_of_lt (lt_trans ha ht.1)))
  -- Step 4: exact evaluation of the comparison integral.
  have hval : (∫ t in a..b, (B * Real.log C) / t) = B * Real.log C * Real.log (b / a) := by
    have hfun : (fun t : ℝ => (B * Real.log C) / t) = fun t => (B * Real.log C) * t⁻¹ := by
      funext t; rw [div_eq_mul_inv]
    rw [hfun, intervalIntegral.integral_const_mul, integral_inv_of_pos ha hb]
  exact hmain.trans (le_of_eq hval)

end Work.FIChain
