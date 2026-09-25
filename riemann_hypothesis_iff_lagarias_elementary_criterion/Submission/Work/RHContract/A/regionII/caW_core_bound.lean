import Mathlib

/-!
# `Work.RHContract.A.regionII.caW_core_bound`

Real-variable core of the region-II `W`-estimate: for `δ ≥ -1/50` and `L ≥ 10`,

`δ/L - log (1 + log (1+δ)/L) ≤ (13/200) * δ^2`.

Write `g = log (1+δ)` and `w = g/L`.  Then `δ/L - log (1 + w)
= (δ - g)/L + (w - log (1+w))`, and both terms are of the form `t - log (1+t)`.

* For `t ≥ 0`, `Real.le_log_one_add_of_nonneg` gives `t - log (1+t) ≤ t²/2`.
* For `t ∈ [-1/50, 0]`, the second-order Taylor remainder
  `Real.abs_log_sub_add_sum_range_le` gives `t - log (1+t) ≤ t²/2 + |t|³/(1-|t|)`,
  which on this range is at most `(51/98) t²`.

Hence `t - log (1+t) ≤ (51/98) t²` for every `t ≥ -1/50`, while `|g| ≤ (50/49)|δ|`
(because `-log (1-x) ≤ x/(1-x)` on `[0,1/50)`), so `w² ≤ (50/49)²δ²/L²`.  Combining,

`δ/L - log (1 + w) ≤ δ² * ((51/98)/L + (51/98)(50/49)²/L²) ≤ (13/200) δ²`
for `L ≥ 10`.
-/

namespace Work.RHContract.A.regionII

open scoped BigOperators

/-- For `|t| < 1`: `t - log (1+t) ≤ t²/2 + |t|³/(1-|t|)`, the second-order Taylor
remainder obtained from `Real.abs_log_sub_add_sum_range_le`. -/
private lemma caWcb_t_sub_log_le (t : ℝ) (ht : |t| < 1) :
    t - Real.log (1 + t) ≤ t^2/2 + |t|^3/(1 - |t|) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -t) (by rwa [abs_neg]) 2
  have hsum : (∑ i ∈ Finset.range 2, (-t)^(i+1)/((i:ℝ)+1)) = -t + t^2/2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]; norm_num
  rw [hsum, show (1:ℝ) - -t = 1 + t by ring, abs_neg] at h
  have h1 : -(|t|^3/(1-|t|)) ≤ -t + t^2/2 + Real.log (1+t) := (abs_le.mp h).1
  linarith

/-- For `x ≥ 0`: `x - log (1+x) ≤ x²/2`. -/
private lemma caWcb_sub_log_le_sq_half (x : ℝ) (hx : 0 ≤ x) :
    x - Real.log (1 + x) ≤ x^2/2 := by
  have h := Real.le_log_one_add_of_nonneg hx
  have h2 : x - 2*x/(x+2) = x^2/(x+2) := by field_simp; ring
  have h3 : x^2/(x+2) ≤ x^2/2 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < x+2)]
    nlinarith [sq_nonneg x, hx]
  linarith

/-- For `x ≥ -1/50`: `x - log (1+x) ≤ (51/98)·x²`. -/
private lemma caWcb_sub_log_le_rat (x : ℝ) (hx : -(1/50) ≤ x) :
    x - Real.log (1 + x) ≤ (51/98) * x^2 := by
  rcases le_or_gt 0 x with hx0 | hx0
  · have h := caWcb_sub_log_le_sq_half x hx0
    nlinarith [sq_nonneg x]
  · have hx1 : |x| < 1 := by rw [abs_of_neg hx0]; linarith
    have h := caWcb_t_sub_log_le x hx1
    have habs : |x| ≤ 1/50 := by rw [abs_of_neg hx0]; linarith
    have h3 : |x|^3/(1-|x|) ≤ x^2/49 := by
      rw [← sq_abs x, div_le_iff₀ (by linarith [abs_nonneg x] : (0:ℝ) < 1 - |x|)]
      nlinarith [abs_nonneg x, habs]
    have h4 : (51/98) * x^2 = x^2/2 + x^2/49 := by ring
    rw [h4]
    linarith

/-- For `x ≥ -1/50`: `|log (1+x)| ≤ (50/49)·|x|`. -/
private lemma caWcb_abs_log_ratio (x : ℝ) (hx : -(1/50) ≤ x) :
    |Real.log (1 + x)| ≤ (50/49) * |x| := by
  have hx1 : 0 < 1 + x := by linarith
  rcases le_or_gt 0 x with hx0 | hx0
  · have hlog : 0 ≤ Real.log (1+x) := Real.log_nonneg (by linarith)
    rw [abs_of_nonneg hlog, abs_of_nonneg hx0]
    have h : Real.log (1+x) ≤ x := by
      have := Real.log_le_sub_one_of_pos hx1; linarith
    nlinarith [h, hx0]
  · rw [abs_of_neg (Real.log_neg hx1 (by linarith)), abs_of_neg hx0]
    have h : Real.log (1/(1+x)) ≤ 1/(1+x) - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div one_ne_zero hx1.ne', Real.log_one, zero_sub] at h
    have e : 1/(1+x) - 1 = -x/(1+x) := by field_simp; ring
    rw [e] at h
    have h2 : -x/(1+x) ≤ (50/49)*(-x) := by
      rw [div_le_iff₀ hx1]
      nlinarith [hx0]
    linarith

/-- For `g ≤ 0` and `L ≥ 10`: `g/10 ≤ g/L`. -/
private lemma caWcb_div_ge_div_of_nonpos (g L : ℝ) (hg : g ≤ 0) (hL : 10 ≤ L) :
    g / 10 ≤ g / L := by
  rw [div_le_div_iff₀ (by norm_num : (0:ℝ) < 10) (by linarith : (0:ℝ) < L)]
  nlinarith [hg, hL]

/-- The numerical core: `(51/98)/L + (51/98)(50/49)²/L² ≤ 13/200` for `L ≥ 10`. -/
private lemma caWcb_numeric (L : ℝ) (hL : 10 ≤ L) :
    (51/98)/L + (51/98)*(50/49)^2/L^2 ≤ 13/200 := by
  have hL0 : 0 < L := by linarith
  have h1 : 1/L ≤ 1/10 := by rw [div_le_div_iff₀ hL0 (by norm_num : (0:ℝ) < 10)]; linarith
  have h2 : 1/L^2 ≤ 1/100 := by
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < L^2) (by norm_num : (0:ℝ) < 100)]
    nlinarith
  have h1nn : (0:ℝ) ≤ 1/L := by positivity
  have h2nn : (0:ℝ) ≤ 1/L^2 := by positivity
  calc (51/98)/L + (51/98)*(50/49)^2/L^2
      = (51/98)*(1/L) + (51/98)*(50/49)^2*(1/L^2) := by ring
    _ ≤ (51/98)*(1/10) + (51/98)*(50/49)^2*(1/100) := by
        nlinarith [h1, h2, h1nn, h2nn]
    _ ≤ 13/200 := by norm_num

theorem caW_core_bound (δ L : ℝ) (hδ : -(1/50) ≤ δ) (hL : 10 ≤ L) :
    δ / L - Real.log (1 + Real.log (1 + δ) / L) ≤ (13/200) * δ^2 := by
  have hL0 : 0 < L := by linarith
  set g : ℝ := Real.log (1 + δ) with hg
  set w : ℝ := g / L with hw
  have hglow : -(1/49) ≤ g := by
    rw [hg]
    have h1 : Real.log (49/50) ≤ Real.log (1 + δ) :=
      Real.log_le_log (by norm_num) (by linarith)
    have h2 : Real.log (49/50) = -Real.log (50/49) := by rw [← Real.log_inv]; norm_num
    have h3 : Real.log (50/49) ≤ 1/49 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ) < 50/49); linarith
    linarith
  have hw_low : -(1/50) ≤ w := by
    rw [hw]
    rcases le_or_gt 0 g with hg0 | hgneg
    · have : (0:ℝ) ≤ g/L := div_nonneg hg0 hL0.le
      linarith
    · have h10 : g/10 ≤ g/L := caWcb_div_ge_div_of_nonpos g L (le_of_lt hgneg) hL
      linarith
  have hgabs : |g| ≤ (50/49) * |δ| := by rw [hg]; exact caWcb_abs_log_ratio δ hδ
  have hg2 : g^2 ≤ (50/49)^2 * δ^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg g) hgabs 2
    rw [mul_pow, sq_abs, sq_abs] at h
    exact h
  have hw2 : w^2 ≤ (50/49)^2 * δ^2 / L^2 := by
    rw [hw, div_pow]
    exact div_le_div_of_nonneg_right hg2 (sq_nonneg L)
  have hkey : δ / L - Real.log (1 + w) = (δ - g) / L + (w - Real.log (1 + w)) := by
    rw [hw]; field_simp; ring
  have hb1 : δ - g ≤ (51/98) * δ^2 := by rw [hg]; exact caWcb_sub_log_le_rat δ hδ
  have hb2 : w - Real.log (1 + w) ≤ (51/98) * w^2 := caWcb_sub_log_le_rat w hw_low
  rw [hkey]
  calc (δ - g) / L + (w - Real.log (1 + w))
      ≤ (51/98) * δ^2 / L + (51/98) * w^2 := by
          have h1 : (δ - g)/L ≤ (51/98)*δ^2/L := div_le_div_of_nonneg_right hb1 hL0.le
          linarith [h1, hb2]
    _ ≤ (51/98) * δ^2 / L + (51/98) * ((50/49)^2 * δ^2 / L^2) := by
          have h : (51/98)*w^2 ≤ (51/98)*((50/49)^2*δ^2/L^2) :=
            mul_le_mul_of_nonneg_left hw2 (by norm_num)
          linarith [h]
    _ = δ^2 * ((51/98)/L + (51/98)*(50/49)^2/L^2) := by ring
    _ ≤ δ^2 * (13/200) := mul_le_mul_of_nonneg_left (caWcb_numeric L hL) (sq_nonneg δ)
    _ = (13/200) * δ^2 := by ring

end Work.RHContract.A.regionII
