import Mathlib

namespace Work.ZeroDensity.Ingham

open MeasureTheory Filter Asymptotics Set

theorem integrableOn_one_add_pow_mul_exp_neg (n : ℕ) {b : ℝ} (hb : 0 < b) :
    MeasureTheory.IntegrableOn (fun s : ℝ => (1 + s) ^ n * Real.exp (-(b * s))) (Set.Ioi 0) := by
  have hb2 : 0 < b / 2 := by positivity
  refine integrable_of_isBigO_exp_neg hb2 (by fun_prop) ?_
  have h1 : (fun s : ℝ => (1 + s) ^ n) =O[atTop] (fun s : ℝ => s ^ n) := by
    refine IsBigO.of_bound (2 ^ n : ℝ) ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with s hs
    have hs1 : (0 : ℝ) ≤ 1 + s := by linarith
    have hs0 : (0 : ℝ) ≤ s := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hs1 n),
      abs_of_nonneg (pow_nonneg hs0 n)]
    have hle : (1 + s) ^ n ≤ (2 * s) ^ n := pow_le_pow_left₀ hs1 (by linarith) n
    rwa [mul_pow] at hle
  have hs : (fun s : ℝ => s ^ n * Real.exp (-(b / 2) * s)) =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
    have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) (b / 2) hb2
    simpa only [Real.rpow_natCast] using h.isBigO_one ℝ
  have hmain : (fun s : ℝ => (1 + s) ^ n * Real.exp (-(b / 2) * s))
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) :=
    (h1.mul (isBigO_refl (fun s : ℝ => Real.exp (-(b / 2) * s)) atTop)).trans hs
  have hkey :
      (fun s : ℝ => (1 + s) ^ n * Real.exp (-(b / 2) * s) * Real.exp (-(b / 2) * s))
        =O[atTop] (fun s : ℝ => (1 : ℝ) * Real.exp (-(b / 2) * s)) :=
    hmain.mul (isBigO_refl (fun s : ℝ => Real.exp (-(b / 2) * s)) atTop)
  refine hkey.congr' ?_ ?_
  · refine Filter.EventuallyEq.of_eq ?_
    funext s
    have h : (-(b / 2)) * s + (-(b / 2)) * s = -(b * s) := by ring
    rw [mul_assoc, ← Real.exp_add, h]
  · refine Filter.EventuallyEq.of_eq ?_
    funext s
    rw [one_mul]

end Work.ZeroDensity.Ingham
