import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Algebra.EuclideanDomain.Field
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Commons.NumberTheory.Sieve

/-- Lower bound for the logarithm: for `1 ≤ t`, `log t ≥ 2 (t-1)/(t+1)`.
This is the `n = 1` truncation of the series `½ log((1+x)/(1-x)) = ∑ x^(2i+1)/(2i+1)`
with `x = (t-1)/(t+1)`. -/
private lemma two_mul_sub_div_le_log {t : ℝ} (h : 1 ≤ t) :
    2 * ((t - 1) / (t + 1)) ≤ Real.log t := by
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one h
  have ht1 : 0 < t + 1 := by linarith
  have hx0 : 0 ≤ (t - 1) / (t + 1) := div_nonneg (by linarith) ht1.le
  have hx1 : (t - 1) / (t + 1) < 1 := by
    rw [div_lt_iff₀ ht1]; linarith
  have hS := Real.sum_range_le_log_div hx0 hx1 1
  rw [Finset.sum_range_one] at hS
  simp only [Nat.mul_zero, Nat.zero_add, pow_one] at hS
  have hfrac : (1 + (t - 1) / (t + 1)) / (1 - (t - 1) / (t + 1)) = t := by
    field_simp
    ring
  rw [hfrac] at hS
  linarith

/-- Numeric fact: `log 3 ≤ 12 log(log 3)`. -/
private lemma log_three_le_twelve_loglog_three :
    Real.log 3 ≤ 12 * Real.log (Real.log 3) := by
  have hgt := Real.log_three_gt_d9
  have hlt := Real.log_three_lt_d9
  have h1 : (1 : ℝ) ≤ Real.log 3 := by linarith
  have hser := two_mul_sub_div_le_log h1
  have hsq : (Real.log 3) ^ 2 ≤ (1.0986122888 : ℝ) ^ 2 := by nlinarith [hgt, hlt]
  have hq : (Real.log 3) ^ 2 - 23 * Real.log 3 + 24 ≤ 0 := by nlinarith [hsq, hgt]
  have hpos : 0 < Real.log 3 + 1 := by linarith
  have hA : Real.log 3 * (Real.log 3 + 1) ≤ 24 * (Real.log 3 - 1) := by nlinarith [hq]
  have hB : Real.log 3 ≤ 24 * (Real.log 3 - 1) / (Real.log 3 + 1) := by
    rw [le_div_iff₀ hpos]; linarith [hA]
  calc Real.log 3
      ≤ 24 * (Real.log 3 - 1) / (Real.log 3 + 1) := hB
    _ = 12 * (2 * ((Real.log 3 - 1) / (Real.log 3 + 1))) := by ring
    _ ≤ 12 * Real.log (Real.log 3) := by linarith [hser]

/-- On `(0,1]`, `s ↦ e^s / s` is antitone. -/
private lemma exp_div_self_antitone {s u : ℝ} (h0 : 0 < u) (h1 : u ≤ s) (h2 : s ≤ 1) :
    Real.exp s / s ≤ Real.exp u / u := by
  have hs : 0 < s := lt_of_lt_of_le h0 h1
  have hδ : 0 ≤ s - u := by linarith
  have hq : 0 < 1 + (s - u) / u := by
    have : 0 ≤ (s - u) / u := div_nonneg hδ h0.le; linarith
  have hkey : s - u ≤ Real.log (1 + (s - u) / u) := by
    have h := Real.one_sub_inv_le_log_of_pos hq
    have e1 : 1 - (1 + (s - u) / u)⁻¹ = (s - u) / s := by
      field_simp
      ring
    rw [e1] at h
    have e2 : s - u ≤ (s - u) / s := by
      rw [le_div_iff₀ hs]; nlinarith [h2, hδ]
    linarith
  have hexp : Real.exp (s - u) ≤ 1 + (s - u) / u := (Real.le_log_iff_exp_le hq).mp hkey
  have e3 : 1 + (s - u) / u = s / u := by field_simp; ring
  rw [e3] at hexp
  rw [div_le_iff₀ hs, div_mul_eq_mul_div₀, le_div_iff₀ h0]
  have e4 : Real.exp (s - u) * (Real.exp u * u) = Real.exp s * u := by
    rw [← mul_assoc, ← Real.exp_add, sub_add_cancel]
  have e5 : (s / u) * (Real.exp u * u) = Real.exp u * s := by
    rw [div_mul_eq_mul_div₀, ← mul_assoc, mul_div_cancel_right₀ _ h0.ne']
    exact mul_comm _ _
  have key2 := mul_le_mul_of_nonneg_right hexp (by positivity : (0 : ℝ) ≤ Real.exp u * u)
  rw [e4, e5] at key2
  exact key2

/-- On `[1,∞)`, `s ↦ e^s / s` is monotone. -/
private lemma exp_div_self_mono {s A : ℝ} (h1 : 1 ≤ s) (h2 : s ≤ A) :
    Real.exp s / s ≤ Real.exp A / A := by
  have hs : 0 < s := by linarith
  have hA : 0 < A := by linarith
  have hd : 0 < A / s := div_pos hA hs
  have key : A / s ≤ Real.exp (A - s) := by
    refine (Real.log_le_iff_le_exp hd).mp ?_
    have hlog : Real.log (A / s) ≤ A / s - 1 := Real.log_le_sub_one_of_pos hd
    have hsub : A / s - 1 = (A - s) / s := by field_simp
    rw [hsub] at hlog
    have hle : (A - s) / s ≤ A - s := by
      rw [div_le_iff₀ hs]; nlinarith [h1, h2]
    linarith
  rw [div_le_iff₀ hs, div_mul_eq_mul_div₀, le_div_iff₀ hA]
  have e4 : (A / s) * (s * Real.exp s) = Real.exp s * A := by
    rw [← mul_assoc, div_mul_cancel₀ _ hs.ne']
    exact mul_comm _ _
  have e5 : Real.exp (A - s) * (s * Real.exp s) = Real.exp A * s := by
    rw [← mul_assoc, mul_comm (Real.exp (A - s)) s, mul_assoc, ← Real.exp_add, sub_add_cancel]
    exact mul_comm _ _
  have key2 := mul_le_mul_of_nonneg_right key (by positivity : (0 : ℝ) ≤ s * Real.exp s)
  rw [e4, e5] at key2
  exact key2

theorem inv_mul_exp_log_div_loglog_le (A : ℝ) (hA : 0 ≤ A) (p : ℕ) (hp : 3 ≤ p) :
    (p : ℝ)⁻¹ * Real.exp (A * Real.log (p : ℝ) / Real.log (Real.log (p : ℝ)))
      ≤ Real.exp (max (12 * A) (Real.exp A)) := by
  have hlog3_pos : 0 < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hs0_pos : 0 < Real.log (Real.log 3) := Real.log_pos (by linarith [Real.log_three_gt_d9])
  have hkey : Real.exp (Real.log (Real.log 3)) / Real.log (Real.log 3) ≤ 12 := by
    rw [Real.exp_log hlog3_pos, div_le_iff₀ hs0_pos]
    exact log_three_le_twelve_loglog_three
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp_pos : (0 : ℝ) < (p : ℝ) := by linarith
  set L : ℝ := Real.log (p : ℝ) with hL
  set s : ℝ := Real.log L with hs
  have hL_ge : Real.log 3 ≤ L := by
    rw [hL]; exact Real.log_le_log (by norm_num) hp3
  have hL_pos : 0 < L := lt_of_lt_of_le hlog3_pos hL_ge
  have hs_ge : Real.log (Real.log 3) ≤ s := by
    rw [hs]; exact Real.log_le_log hlog3_pos hL_ge
  have hs_pos : 0 < s := lt_of_lt_of_le hs0_pos hs_ge
  have hL_exp : Real.exp L = (p : ℝ) := by rw [hL]; exact Real.exp_log hp_pos
  have hLs : L = Real.exp s := by rw [hs]; exact (Real.exp_log hL_pos).symm
  suffices hmain : -L + A * L / s ≤ max (12 * A) (Real.exp A) by
    have h1 : (p : ℝ)⁻¹ = Real.exp (-L) := by rw [← hL_exp, Real.exp_neg]
    rw [h1, ← Real.exp_add]
    exact Real.exp_le_exp.mpr hmain
  by_cases hAs : A ≤ s
  · have hAL : A * L / s ≤ L := by
      rw [div_le_iff₀ hs_pos]; nlinarith [hAs, hL_pos]
    calc -L + A * L / s ≤ 0 := by linarith
      _ ≤ 12 * A := by linarith
      _ ≤ max (12 * A) (Real.exp A) := le_max_left _ _
  · have hAs' : s < A := not_le.mp hAs
    have hexpr : -L + A * L / s = Real.exp s * (A - s) / s := by
      rw [hLs]
      field_simp
      ring
    have hLhs_le : Real.exp s * (A - s) / s = (A - s) * (Real.exp s / s) := by ring
    rw [hexpr, hLhs_le]
    have hes_pos : 0 ≤ Real.exp s / s := div_nonneg (Real.exp_pos s).le hs_pos.le
    have hAs_le : A - s ≤ A := by linarith [hs_pos.le]
    rcases le_total s 1 with hs1 | hs1'
    · have hb : Real.exp s / s ≤ 12 := (exp_div_self_antitone hs0_pos hs_ge hs1).trans hkey
      calc (A - s) * (Real.exp s / s) ≤ A * (Real.exp s / s) :=
            mul_le_mul_of_nonneg_right hAs_le hes_pos
        _ ≤ A * 12 := mul_le_mul_of_nonneg_left hb hA
        _ = 12 * A := by ring
        _ ≤ max (12 * A) (Real.exp A) := le_max_left _ _
    · have hApos : 0 < A := by linarith [hs_pos, hs1']
      have hb : Real.exp s / s ≤ Real.exp A / A := exp_div_self_mono hs1' (le_of_lt hAs')
      calc (A - s) * (Real.exp s / s) ≤ A * (Real.exp s / s) :=
            mul_le_mul_of_nonneg_right hAs_le hes_pos
        _ ≤ A * (Real.exp A / A) := mul_le_mul_of_nonneg_left hb hA
        _ = Real.exp A := by rw [mul_comm A (Real.exp A / A), div_mul_cancel₀ _ hApos.ne']
        _ ≤ max (12 * A) (Real.exp A) := le_max_right _ _

end Commons.NumberTheory.Sieve