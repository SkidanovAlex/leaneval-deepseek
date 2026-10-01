import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.OffAxis.Tf72One.abs_interp_error_le
import Submission.Work.OffAxis.Tf72One.Mtt_bound
import Submission.Work.OffAxis.Tf72One.integrand_interp_le

open scoped Interval
open MeasureTheory

namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables

/-- **Auxiliary: `σ`-interpolation for `Isub` with a general pair of endpoints.**
If `M` bounds `∫₀² y²|e^{sy}-2|g72 y dy` (the uniform bound on the second `t`-derivative of
`Isub s ·`), then for `a < b` and `t ∈ [a,b]`
`Isub s t ≤ max (Isub s a) (Isub s b) + (b-a)²/8 · M`.

Integrate the pointwise bound `integrand_interp_le` over `y ∈ [0,2]`: the interpolant part
integrates to `((b-t) Isub s a + (t-a) Isub s b)/(b-a)`, a convex combination of the endpoint
values, while the error part integrates to `(b-a)²/8 · ∫₀² y²|e^{sy}-2|g72 y`. -/
theorem isub_le_interp_aux (s t a b : ℝ) (hab : a < b) (hta : a ≤ t) (htb : t ≤ b)
    (hM : ∫ y in (0:ℝ)..2, y ^ 2 * |Real.exp (s * y) - 2| * g72 y ≤ 5/8) :
    Work.ZeroFreeTables.OffAxis.Isub s t ≤
      max (Work.ZeroFreeTables.OffAxis.Isub s a) (Work.ZeroFreeTables.OffAxis.Isub s b)
        + (b - a) ^ 2 / 8 * (5/8) := by
  have hba : (0:ℝ) < b - a := by linarith
  have hIt : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have hIa : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have hIb : IntervalIntegrable (fun y : ℝ => (Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have hIe : IntervalIntegrable (fun y : ℝ => y^2 * |Real.exp (s*y) - 2| * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]
    fun_prop
  have hpt : ∀ y ∈ Set.Icc (0:ℝ) 2,
      (Real.exp (s*y) - 2) * Real.cos (t*y) * g72 y ≤
        (b - t) / (b - a) * ((Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
        + (t - a) / (b - a) * ((Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
        + (b - a)^2 / 8 * (y^2 * |Real.exp (s*y) - 2| * g72 y) :=
    fun y hy => integrand_interp_le s t a b y hab hta htb hy
  have hsumI : IntervalIntegrable
      (fun y : ℝ => (b - t)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
        + (t - a)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
        + (b - a)^2/8 * (y^2 * |Real.exp (s*y) - 2| * g72 y)) volume (0:ℝ) 2 :=
    ((hIa.const_mul _).add (hIb.const_mul _)).add (hIe.const_mul _)
  have hmono := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 2 by norm_num) hIt hsumI hpt
  have hsplit : (∫ y in (0:ℝ)..2, ((b - t)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (a*y) * g72 y)
        + (t - a)/(b - a) * ((Real.exp (s*y) - 2) * Real.cos (b*y) * g72 y)
        + (b - a)^2/8 * (y^2 * |Real.exp (s*y) - 2| * g72 y)))
      = (b - t)/(b - a) * Work.ZeroFreeTables.OffAxis.Isub s a
        + (t - a)/(b - a) * Work.ZeroFreeTables.OffAxis.Isub s b
        + (b - a)^2/8 * (∫ y in (0:ℝ)..2, y^2 * |Real.exp (s*y) - 2| * g72 y) := by
    rw [intervalIntegral.integral_add ((hIa.const_mul _).add (hIb.const_mul _)) (hIe.const_mul _),
        intervalIntegral.integral_add (hIa.const_mul _) (hIb.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        ← Work.ZeroFreeTables.OffAxis.Isub_eq_integral s a,
        ← Work.ZeroFreeTables.OffAxis.Isub_eq_integral s b]
  rw [hsplit, ← Work.ZeroFreeTables.OffAxis.Isub_eq_integral s t] at hmono
  have h0 : 0 ≤ (b - t)/(b - a) := div_nonneg (by linarith) (le_of_lt hba)
  have h1 : 0 ≤ (t - a)/(b - a) := div_nonneg (by linarith) (le_of_lt hba)
  have hsum : (b - t)/(b - a) + (t - a)/(b - a) = 1 := by
    rw [← add_div, show b - t + (t - a) = b - a by ring, div_self (ne_of_gt hba)]
  have hmax : (b - t)/(b - a) * Work.ZeroFreeTables.OffAxis.Isub s a
      + (t - a)/(b - a) * Work.ZeroFreeTables.OffAxis.Isub s b
      ≤ max (Work.ZeroFreeTables.OffAxis.Isub s a) (Work.ZeroFreeTables.OffAxis.Isub s b) := by
    have hMx : (b - t)/(b - a) * Work.ZeroFreeTables.OffAxis.Isub s a
        + (t - a)/(b - a) * Work.ZeroFreeTables.OffAxis.Isub s b
        ≤ (b - t)/(b - a) * max (Work.ZeroFreeTables.OffAxis.Isub s a) (Work.ZeroFreeTables.OffAxis.Isub s b)
          + (t - a)/(b - a) * max (Work.ZeroFreeTables.OffAxis.Isub s a) (Work.ZeroFreeTables.OffAxis.Isub s b) :=
      add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) h0)
        (mul_le_mul_of_nonneg_left (le_max_right _ _) h1)
    calc (b - t)/(b - a) * Work.ZeroFreeTables.OffAxis.Isub s a
          + (t - a)/(b - a) * Work.ZeroFreeTables.OffAxis.Isub s b
        ≤ _ := hMx
      _ = max (Work.ZeroFreeTables.OffAxis.Isub s a) (Work.ZeroFreeTables.OffAxis.Isub s b) := by
          rw [← add_mul, hsum, one_mul]
  have herr : (b - a)^2/8 * (∫ y in (0:ℝ)..2, y^2 * |Real.exp (s*y) - 2| * g72 y)
      ≤ (b - a)^2/8 * (5/8) := mul_le_mul_of_nonneg_left hM (by positivity)
  linarith [hmono, hmax, herr]

/-- **`σ`-interpolation for `Isub`.**  `t ↦ Isub s t = ∫₀² (e^{sy}-2)cos(ty)g72 y dy` is controlled by
its values at the endpoints of `[t0,t1]`: the second `t`-derivative is
`-∫₀² y²(e^{sy}-2)cos(ty)g72 y dy`, of absolute value at most `∫₀² y²|e^{sy}-2|g72 ≤ 5/8`, so the
sharp two-point interpolation bound applied pointwise in `y` and integrated gives the claim. -/
theorem Isub_le_interp_t (s t t0 t1 : ℝ) (hs0 : 0 ≤ s) (hs17 : s ≤ 17/16)
    (ht0 : t0 ≤ t) (ht1 : t ≤ t1) :
    Work.ZeroFreeTables.OffAxis.Isub s t ≤
      max (Work.ZeroFreeTables.OffAxis.Isub s t0) (Work.ZeroFreeTables.OffAxis.Isub s t1)
        + (t1 - t0) ^ 2 / 8 * (5/8) := by
  rcases lt_or_ge t0 t1 with h | h
  · exact isub_le_interp_aux s t t0 t1 h ht0 ht1 (Mtt_bound s hs0 hs17)
  · have ht1t0 : t1 = t0 := le_antisymm h (le_trans ht0 ht1)
    have htt0 : t = t0 := le_antisymm (by rw [ht1t0] at ht1; exact ht1) ht0
    rw [htt0, ht1t0]
    simp

end Work.OffAxis.Tf72One
