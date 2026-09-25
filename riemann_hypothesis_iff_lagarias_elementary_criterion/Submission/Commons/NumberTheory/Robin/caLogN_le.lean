import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Commons.NumberTheory.Robin

/-- For `x > 1`, `ε * log x ≤ x ^ ε - 1`. -/
lemma rpow_sub_one_ge_log (ε : ℝ) {x : ℝ} (hx : 1 < x) :
    ε * Real.log x ≤ x ^ ε - 1 := by
  have h := Real.add_one_le_exp (Real.log x * ε)
  rw [Real.rpow_def_of_pos (by linarith : 0 < x)]
  nlinarith

/-- For `x ≥ 2`, `1/2 ≤ Real.log x`. -/
lemma half_le_log_of_two_le {x : ℝ} (hx : 2 ≤ x) : (1 / 2 : ℝ) ≤ Real.log x := by
  have h2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  linarith [Real.log_two_gt_d9, h2]

/-- The inner logarithmic ratio is nonnegative. -/
lemma log_ratio_div_log_nonneg (ε : ℝ) (hε : 0 < ε) {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ Real.log ((x ^ (1 + ε) - 1) / (x ^ (1 + ε) - x)) / Real.log x := by
  have hxpos : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos hx1
  have hpow : x ^ (1 + ε) = x * x ^ ε := by
    rw [Real.rpow_add hxpos 1 ε, Real.rpow_one]
  have hxe1 : 0 < x ^ ε - 1 := by
    have h := rpow_sub_one_ge_log ε hx1
    nlinarith [mul_pos hε hLpos]
  have hden : x ^ (1 + ε) - x = x * (x ^ ε - 1) := by rw [hpow]; ring
  have hnum : x ^ (1 + ε) - 1 = x * (x ^ ε - 1) + (x - 1) := by rw [hpow]; ring
  have hdne : x * (x ^ ε - 1) ≠ 0 := ne_of_gt (mul_pos hxpos hxe1)
  have hratio : (x ^ (1 + ε) - 1) / (x ^ (1 + ε) - x) = 1 + (x - 1) / (x * (x ^ ε - 1)) := by
    rw [hden, hnum, add_div, div_self hdne]
  rw [hratio]
  apply div_nonneg
  · apply Real.log_nonneg
    have ht : 0 < (x - 1) / (x * (x ^ ε - 1)) := div_pos (by linarith) (mul_pos hxpos hxe1)
    linarith
  · exact hLpos.le

/-- The main analytic bound: `log ((x^(1+ε)-1)/(x^(1+ε)-x)) / log x ≤ 4/ε` for `x ≥ 2`. -/
lemma log_ratio_div_log_le (ε : ℝ) (hε : 0 < ε) {x : ℝ} (hx : 2 ≤ x) :
    Real.log ((x ^ (1 + ε) - 1) / (x ^ (1 + ε) - x)) / Real.log x ≤ 4 / ε := by
  have hxpos : 0 < x := by linarith
  have hx1 : 1 < x := by linarith
  have hLpos : 0 < Real.log x := Real.log_pos hx1
  have hpow : x ^ (1 + ε) = x * x ^ ε := by
    rw [Real.rpow_add hxpos 1 ε, Real.rpow_one]
  have hxeps : ε * Real.log x ≤ x ^ ε - 1 := rpow_sub_one_ge_log ε hx1
  have hεLpos : 0 < ε * Real.log x := mul_pos hε hLpos
  have hxe1 : 0 < x ^ ε - 1 := by linarith
  have hden : x ^ (1 + ε) - x = x * (x ^ ε - 1) := by rw [hpow]; ring
  have hnum : x ^ (1 + ε) - 1 = x * (x ^ ε - 1) + (x - 1) := by rw [hpow]; ring
  have hdne : x * (x ^ ε - 1) ≠ 0 := ne_of_gt (mul_pos hxpos hxe1)
  have hratio : (x ^ (1 + ε) - 1) / (x ^ (1 + ε) - x) = 1 + (x - 1) / (x * (x ^ ε - 1)) := by
    rw [hden, hnum, add_div, div_self hdne]
  have hlog_le : Real.log (1 + (x - 1) / (x * (x ^ ε - 1))) ≤ (x - 1) / (x * (x ^ ε - 1)) := by
    have h1 : 0 < 1 + (x - 1) / (x * (x ^ ε - 1)) := by
      have : 0 < (x - 1) / (x * (x ^ ε - 1)) := div_pos (by linarith) (mul_pos hxpos hxe1)
      linarith
    have := Real.log_le_sub_one_of_pos h1
    linarith
  have hsq : (1 / 4 : ℝ) ≤ (Real.log x) ^ 2 := by
    have hhalf : (1 / 2 : ℝ) ≤ Real.log x := half_le_log_of_two_le hx
    have h := pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 / 2 by norm_num) hhalf 2
    have h2 : ((1 : ℝ) / 2) ^ 2 = 1 / 4 := by norm_num
    rwa [h2] at h
  have key : ε * Real.log ((x ^ (1 + ε) - 1) / (x ^ (1 + ε) - x)) ≤ 4 * Real.log x := by
    rw [hratio]
    have hεt : ε * Real.log (1 + (x - 1) / (x * (x ^ ε - 1)))
        ≤ ε * ((x - 1) / (x * (x ^ ε - 1))) :=
      mul_le_mul_of_nonneg_left hlog_le hε.le
    have hb1 : ε * ((x - 1) / (x * (x ^ ε - 1)))
        ≤ ε * ((x - 1) / (x * (ε * Real.log x))) := by
      apply mul_le_mul_of_nonneg_left _ hε.le
      exact div_le_div_of_nonneg_left (by linarith) (mul_pos hxpos hεLpos)
        (mul_le_mul_of_nonneg_left hxeps hxpos.le)
    have hsimp : ε * ((x - 1) / (x * (ε * Real.log x))) = (x - 1) / (x * Real.log x) := by
      field_simp
    have hb2 : ε * ((x - 1) / (x * (ε * Real.log x))) ≤ 4 * Real.log x := by
      rw [hsimp, div_le_iff₀ (mul_pos hxpos hLpos)]
      nlinarith [hsq, hxpos]
    linarith [hεt, hb1, hb2]
  rw [div_le_div_iff₀ hLpos hε]
  linarith [key]

/-- `4/ε ≤ exp (2/ε) + 2` for `ε > 0`. -/
lemma four_div_le_exp_add_two (ε : ℝ) (hε : 0 < ε) :
    4 / ε ≤ Real.exp (2 / ε) + 2 := by
  have hs : 0 ≤ 2 / ε := by positivity
  have hq := Real.quadratic_le_exp_of_nonneg hs
  have h4 : (4 : ℝ) / ε = 2 * (2 / ε) := by ring
  nlinarith [hq, sq_nonneg (2 / ε - 1)]

theorem caLogN_le (ε : ℝ) (hε : 0 < ε) {p : ℕ} (hp : 2 ≤ p) :
    ⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ)⌋₊ ≤ Nat.ceil (Real.exp (2 / ε)) + 2 := by
  have hx2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hbound : Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ)))
      / Real.log (p : ℝ) ≤ 4 / ε := log_ratio_div_log_le ε hε hx2
  have hnonneg : 0 ≤ Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ)))
      / Real.log (p : ℝ) := log_ratio_div_log_nonneg ε hε hx2
  have hexp : 4 / ε ≤ Real.exp (2 / ε) + 2 := four_div_le_exp_add_two ε hε
  have hfloor : (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ)))
      / Real.log (p : ℝ)⌋₊ : ℝ) ≤
      Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ))) / Real.log (p : ℝ) :=
    Nat.floor_le hnonneg
  have hceil : Real.exp (2 / ε) + 2 ≤ (↑(Nat.ceil (Real.exp (2 / ε)) + 2) : ℝ) := by
    have := Nat.le_ceil (Real.exp (2 / ε))
    push_cast
    linarith
  have hfinal : (⌊Real.log ((((p : ℝ) ^ (1 + ε)) - 1) / ((((p : ℝ) ^ (1 + ε))) - (p : ℝ)))
      / Real.log (p : ℝ)⌋₊ : ℝ) ≤ (↑(Nat.ceil (Real.exp (2 / ε)) + 2) : ℝ) := by
    linarith [hfloor, hbound, hexp, hceil]
  exact_mod_cast hfinal

end Commons.NumberTheory.Robin