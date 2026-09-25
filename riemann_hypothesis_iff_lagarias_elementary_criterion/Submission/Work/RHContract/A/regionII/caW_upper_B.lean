import Mathlib
import Submission.Work.RHContract.A.regionII.Defs
import Submission.Work.RHContract.A.ca_margin_lower
import Submission.Work.RHContract.Corpus

/-!
# `Work.RHContract.A.regionII.caW_upper_B`

Upper bound for the `log log` correction `W = caW ε` in the region `10^5 ≤ ξ = ξ(ε) < 10^8`,
from the Chebyshev bound `|ψ ξ − ξ| ≤ 0.45 ξ^{3/4} + 2` alone:

`caW ε ≤ (12/100) · caU ξ`,  `caU ξ = 1/(√ξ · log ξ)`.

Write `x = ξ`, `p = ψ x`, `u = (p − x)/x`, `L = log x`, `v = log(1+u)`, `w = v/L`.  Then

`caW = log log x + (p−x)/(x log x) − log log p = u/L − log(1+w) = (u−v)/L + (w − log(1+w))`.

The second-order Taylor estimate `t − log(1+t) ≤ t²/2 + |t|³/(1−|t|)` (valid for `|t| < 1`)
gives, after multiplying by `√x · L`,

`√x L caW ≤ √x(|u|²/2 + |u|³/(1−|u|)) + √x(|v|²/(2L) + |v|³/(L²(1−|w|)))`.

With `s = x^{-1/4}` one has `√x |u|² ≤ (0.45 + 2s³)²`, `√x|u|³ ≤ (0.45+2s³)²|u|`,
`|v| ≤ 1.03|u|`, `|u| ≤ 0.45 s + 2 s⁴ ≤ 0.0253326`, `|w| ≤ 1/2` and `L ≥ 11.5` for `x ≥ 10^5`,
so the right-hand side is at most

`0.202821/2 + 1.026·0.005138 + 0.215173/(2·11.5) + 2·0.005615/11.5² ≤ 0.12`.
-/

open scoped BigOperators

namespace Work.RHContract.A.regionII

noncomputable section

set_option maxHeartbeats 2000000

/-- For `|t| < 1`: `t - log(1+t) ≤ t²/2 + |t|³/(1-|t|)`.

Second-order Taylor estimate for `log(1+t)` obtained from the alternating-series remainder
`Real.abs_log_sub_add_sum_range_le`. -/
lemma t_sub_log_le_B (t : ℝ) (ht : |t| < 1) :
    t - Real.log (1 + t) ≤ t ^ 2 / 2 + |t| ^ 3 / (1 - |t|) := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -t) (by rwa [abs_neg]) 2
  have hsum : (∑ i ∈ Finset.range 2, (-t) ^ (i + 1) / ((i : ℝ) + 1)) = -t + t ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]; norm_num
  rw [hsum, show (1 : ℝ) - -t = 1 + t by ring, abs_neg] at h
  have h1 : -(|t| ^ 3 / (1 - |t|)) ≤ -t + t ^ 2 / 2 + Real.log (1 + t) := (abs_le.mp h).1
  linarith

/-- For `|t| < 1`: `|log(1+t)| ≤ |t|/(1-|t|)`. -/
lemma abs_log_one_add_le_B (t : ℝ) (ht : |t| < 1) :
    |Real.log (1 + t)| ≤ |t| / (1 - |t|) := by
  have ht2 : t < 1 := lt_of_abs_lt ht
  have hpos : 0 < 1 - |t| := by linarith [abs_nonneg t]
  rcases lt_or_ge t 0 with ht0 | ht0
  · have h1p : 0 < 1 + t := by linarith [neg_lt_of_abs_lt ht]
    have hlog : Real.log (1 + t) ≤ 0 := by
      have := Real.log_le_sub_one_of_pos h1p; linarith
    rw [abs_of_nonpos hlog, abs_of_neg ht0, show (1 : ℝ) - -t = 1 + t by ring]
    have h2 : Real.log (1 / (1 + t)) ≤ 1 / (1 + t) - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by norm_num) (ne_of_gt h1p), Real.log_one] at h2
    have e2 : 1 / (1 + t) - 1 = -t / (1 + t) := by field_simp; ring
    rw [e2] at h2
    linarith
  · have hlog : 0 ≤ Real.log (1 + t) := Real.log_nonneg (by linarith)
    rw [abs_of_nonneg hlog, abs_of_nonneg ht0]
    have h2 : Real.log (1 + t) ≤ t := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + t); linarith
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - t)]
    nlinarith [h2, hlog, ht0]

/-- `2.3016 ≤ log 10`. -/
lemma log_ten_ge_B : (2.3016 : ℝ) ≤ Real.log 10 := by
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have e : Real.log 10 = 3 * Real.log 2 + Real.log (1 + 1 / 4) := by
    rw [show (10 : ℝ) = 2 ^ 3 * (1 + 1 / 4) by norm_num]
    rw [Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    push_cast
    ring
  have h3 : 2 * (1 / 4) / (1 / 4 + 2) ≤ Real.log (1 + 1 / 4) :=
    Real.le_log_one_add_of_nonneg (by norm_num)
  linarith

/-- `11.5 ≤ log x` for `x ≥ 10^5`. -/
lemma log_ge_115_B (x : ℝ) (hx : 100000 ≤ x) : (11.5 : ℝ) ≤ Real.log x := by
  have h1 : Real.log 100000 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have h2 : Real.log 100000 = 5 * Real.log 10 := by
    rw [show (100000 : ℝ) = 10 ^ 5 by norm_num, Real.log_pow]
    push_cast
    ring
  linarith [log_ten_ge_B]

/-- Real-variable core of the region-II `W`-estimate: for `x ≥ 10^5` and
`|p − x| ≤ 0.45 x^{3/4} + 2`,

`log log x + (p − x)/(x log x) − log log p ≤ (12/100)/(√x · log x)`. -/
theorem caW_core_B (x p : ℝ) (hx : 100000 ≤ x)
    (hp : |p - x| ≤ 0.45 * x ^ (3/4:ℝ) + 2) :
    Real.log (Real.log x) + (p - x) / (x * Real.log x) - Real.log (Real.log p)
      ≤ (12/100) * (1 / (Real.sqrt x * Real.log x)) := by
  have hx0 : 0 < x := by linarith
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hx34le : x ^ (3/4:ℝ) ≤ x := by
    have h := Real.rpow_le_rpow_of_exponent_le hx1 (show (3/4:ℝ) ≤ 1 by norm_num)
    rwa [Real.rpow_one] at h
  have hp1 : 1 < p := by
    have h := (abs_le.mp hp).1
    nlinarith [hx34le, hx]
  have hp0 : 0 < p := by linarith
  set L : ℝ := Real.log x with hL
  have hL115 : (11.5:ℝ) ≤ L := by rw [hL]; exact log_ge_115_B x hx
  have hL0 : 0 < L := by linarith
  have hLne : L ≠ 0 := ne_of_gt hL0
  set u : ℝ := (p - x)/x with hu
  have hp_eq : p = x * (1 + u) := by rw [hu]; field_simp; ring
  have h1u : 0 < 1 + u := by
    have h : p / x = 1 + u := by rw [hu]; field_simp; ring
    rw [← h]; exact div_pos hp0 hx0
  set v : ℝ := Real.log (1 + u) with hv
  have hlogp : Real.log p = L + v := by
    rw [hp_eq, Real.log_mul (ne_of_gt hx0) (ne_of_gt h1u), hL, hv]
  -- `s = x^{-1/4}`
  set s : ℝ := x ^ (-(1/4):ℝ) with hs
  have hs0 : 0 < s := by rw [hs]; exact Real.rpow_pos_of_pos hx0 _
  have hs4 : s ^ 4 = 1/x := by
    rw [hs, ← Real.rpow_natCast (x ^ (-(1/4):ℝ)) 4,
        ← Real.rpow_mul (x := x) hx0.le (-(1/4:ℝ)) ((4:ℕ):ℝ)]
    rw [show (-(1/4:ℝ) * ((4:ℕ):ℝ)) = -1 by norm_num, Real.rpow_neg_one, one_div]
  have hs2 : s ^ 2 = x ^ (-(1/2):ℝ) := by
    rw [hs, ← Real.rpow_natCast (x ^ (-(1/4):ℝ)) 2,
        ← Real.rpow_mul (x := x) hx0.le (-(1/4:ℝ)) ((2:ℕ):ℝ)]
    rw [show (-(1/4:ℝ) * ((2:ℕ):ℝ)) = -(1/2) by norm_num]
  have hsqrt_s2 : Real.sqrt x * s ^ 2 = 1 := by
    rw [hs2, Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    rw [show (1/2:ℝ) + (-(1/2)) = 0 by norm_num, Real.rpow_zero]
  have hs_le : s ≤ 0.05625 := by
    have h1 : s ^ 4 ≤ (0.05625:ℝ)^4 := by
      rw [hs4]
      have h2 : (1:ℝ)/x ≤ 1/100000 := one_div_le_one_div_of_le (by norm_num) hx
      have h3 : (1:ℝ)/100000 ≤ (0.05625:ℝ)^4 := by norm_num
      linarith
    exact (pow_le_pow_iff_left₀ (le_of_lt hs0) (by norm_num) (by norm_num : (4:ℕ) ≠ 0)).1 h1
  have hs3_le : s ^ 3 ≤ (0.05625:ℝ)^3 := pow_le_pow_left₀ (le_of_lt hs0) hs_le 3
  have hs4_le : s ^ 4 ≤ (0.05625:ℝ)^4 := pow_le_pow_left₀ (le_of_lt hs0) hs_le 4
  -- bound on `u`
  have hu_45 : |u| ≤ 0.45 * s + 2 * s ^ 4 := by
    have h1 : |u| = |p - x| / x := by rw [hu, abs_div, abs_of_pos hx0]
    have h2 : |p - x| / x ≤ (0.45 * x ^ (3/4:ℝ) + 2) / x :=
      div_le_div_of_nonneg_right hp hx0.le
    have h3 : (0.45 * x ^ (3/4:ℝ) + 2) / x = 0.45 * s + 2 * s ^ 4 := by
      have hxpow : x ^ (3/4:ℝ) / x = s := by
        have h := Real.rpow_sub hx0 (3/4:ℝ) (1:ℝ)
        rw [Real.rpow_one] at h
        rw [← h, hs]
        norm_num
      rw [add_div, mul_div_assoc, hxpow, show (2:ℝ)/x = 2 * s ^ 4 by rw [hs4]; ring]
    linarith
  have hu_bound : |u| ≤ 0.0253326 := by
    have h2 : 0.45 * s + 2 * s ^ 4 ≤ 0.0253326 := by
      nlinarith [hs_le, hs4_le, hs0]
    linarith [hu_45, h2]
  have hu_lt1 : |u| < 1 := by linarith
  have hu_half : |u| ≤ 1/2 := by linarith
  have hd_u : (0:ℝ) < 1 - |u| := by linarith
  have hu_nn : (0:ℝ) ≤ |u| := abs_nonneg u
  have hv_le : |v| ≤ |u| / (1 - |u|) := by rw [hv]; exact abs_log_one_add_le_B u hu_lt1
  have hv_103 : |v| ≤ 1.03 * |u| := by
    have h106 : (1:ℝ)/(1 - |u|) ≤ 1.026 := by
      rw [div_le_iff₀ hd_u]; linarith [hu_bound]
    have h1 : |u| / (1 - |u|) ≤ 1.03 * |u| := by
      have he : |u|/(1-|u|) = |u| * (1/(1-|u|)) := by ring
      rw [he]
      nlinarith [h106, hu_nn]
    linarith [hv_le, h1]
  -- `√x · |u|²` and `√x · |u|³`
  have hbase_le : 0.45 + 2 * s ^ 3 ≤ 0.450355958 := by linarith [hs3_le]
  have hbase0 : 0 ≤ 0.45 + 2 * s ^ 3 := by positivity
  have hu_sq : |u| ^ 2 ≤ s ^ 2 * (0.45 + 2 * s ^ 3) ^ 2 := by
    have h1 : |u| ≤ s * (0.45 + 2 * s ^ 3) := by
      have he : 0.45 * s + 2 * s ^ 4 = s * (0.45 + 2 * s ^ 3) := by ring
      linarith [hu_45, he]
    calc |u| ^ 2 ≤ (s * (0.45 + 2 * s ^ 3)) ^ 2 := pow_le_pow_left₀ (abs_nonneg u) h1 2
      _ = s ^ 2 * (0.45 + 2 * s ^ 3) ^ 2 := by ring
  have hsr2 : Real.sqrt x * |u| ^ 2 ≤ 0.202821 := by
    have h1 : Real.sqrt x * |u| ^ 2 ≤ Real.sqrt x * (s ^ 2 * (0.45 + 2 * s ^ 3) ^ 2) :=
      mul_le_mul_of_nonneg_left hu_sq (Real.sqrt_nonneg x)
    have h2 : Real.sqrt x * (s ^ 2 * (0.45 + 2 * s ^ 3) ^ 2) = (0.45 + 2 * s ^ 3) ^ 2 := by
      rw [← mul_assoc, hsqrt_s2, one_mul]
    have h3 : (0.45 + 2 * s ^ 3) ^ 2 ≤ (0.450355958:ℝ) ^ 2 :=
      pow_le_pow_left₀ hbase0 hbase_le 2
    have h4 : (0.450355958:ℝ) ^ 2 ≤ 0.202821 := by norm_num
    linarith
  have hsr3 : Real.sqrt x * |u| ^ 3 ≤ 0.005138 := by
    have h1 : Real.sqrt x * |u| ^ 3 = (Real.sqrt x * |u| ^ 2) * |u| := by ring
    rw [h1]
    have h2 : (Real.sqrt x * |u| ^ 2) * |u| ≤ 0.202821 * 0.0253326 :=
      mul_le_mul hsr2 hu_bound hu_nn (by norm_num)
    have h3 : (0.202821:ℝ) * 0.0253326 ≤ 0.005138 := by norm_num
    linarith
  -- `√x · |v|²` and `√x · |v|³`
  have hvr2 : Real.sqrt x * |v| ^ 2 ≤ 0.215173 := by
    have h1 : |v| ^ 2 ≤ (1.03 * |u|) ^ 2 := pow_le_pow_left₀ (abs_nonneg v) hv_103 2
    have h1' : (1.03 * |u|) ^ 2 = 1.0609 * |u| ^ 2 := by ring
    have h2 : |v| ^ 2 ≤ 1.0609 * |u| ^ 2 := by linarith [h1, h1']
    have h3 : Real.sqrt x * |v| ^ 2 ≤ Real.sqrt x * (1.0609 * |u| ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg x)
    have h4 : Real.sqrt x * (1.0609 * |u| ^ 2) = 1.0609 * (Real.sqrt x * |u| ^ 2) := by ring
    have h5 : 1.0609 * (Real.sqrt x * |u| ^ 2) ≤ 1.0609 * 0.202821 :=
      mul_le_mul_of_nonneg_left hsr2 (by norm_num)
    have h6 : (1.0609:ℝ) * 0.202821 ≤ 0.215173 := by norm_num
    linarith
  have hvr3 : Real.sqrt x * |v| ^ 3 ≤ 0.005615 := by
    have h1 : |v| ^ 3 ≤ (1.03 * |u|) ^ 3 := pow_le_pow_left₀ (abs_nonneg v) hv_103 3
    have h1' : (1.03 * |u|) ^ 3 = 1.092727 * |u| ^ 3 := by ring
    have h2 : |v| ^ 3 ≤ 1.092727 * |u| ^ 3 := by linarith [h1, h1']
    have h3 : Real.sqrt x * |v| ^ 3 ≤ Real.sqrt x * (1.092727 * |u| ^ 3) :=
      mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg x)
    have h4 : Real.sqrt x * (1.092727 * |u| ^ 3) = 1.092727 * (Real.sqrt x * |u| ^ 3) := by ring
    have h5 : 1.092727 * (Real.sqrt x * |u| ^ 3) ≤ 1.092727 * 0.005138 :=
      mul_le_mul_of_nonneg_left hsr3 (by norm_num)
    have h6 : (1.092727:ℝ) * 0.005138 ≤ 0.005615 := by norm_num
    linarith
  -- `w = v / L`
  set w : ℝ := v / L with hw
  have hw_abs : |w| ≤ 1/2 := by
    rw [hw, abs_div, abs_of_pos hL0]
    rw [div_le_iff₀ hL0]
    nlinarith [hv_103, hu_bound, hL115, hu_nn]
  have hw_lt1 : |w| < 1 := by linarith
  have hd_w : (0:ℝ) < 1 - |w| := by linarith
  have hw3 : |w| ^ 3 / (1 - |w|) ≤ 2 * |w| ^ 3 := by
    rw [div_le_iff₀ hd_w]
    have h3 : (0:ℝ) ≤ |w| ^ 3 := by positivity
    nlinarith [hw_abs, abs_nonneg w]
  -- the `log log ψ` identity
  have hloglogp : Real.log (Real.log p) = Real.log L + Real.log (1 + w) := by
    have hLv : L + v = L * (1 + w) := by rw [hw]; field_simp
    have h1w : 0 < 1 + w := by
      have he : (L + v)/L = 1 + w := by rw [hw]; field_simp
      rw [← he, hlogp.symm]
      exact div_pos (Real.log_pos hp1) hL0
    rw [hlogp, hLv, Real.log_mul hLne (ne_of_gt h1w)]
  have hE : Real.log (Real.log x) + (p - x) / (x * Real.log x) - Real.log (Real.log p)
      = u/L - Real.log (1 + w) := by
    have hdiv : (p - x)/(x * L) = u/L := by rw [hu]; field_simp
    rw [hloglogp, ← hL, hdiv]
    ring
  -- second order Taylor estimates
  have hu_v : u - v ≤ |u| ^ 2/2 + 1.026 * |u| ^ 3 := by
    have h := t_sub_log_le_B u hu_lt1
    have h2 : |u| ^ 3 / (1 - |u|) ≤ 1.026 * |u| ^ 3 := by
      rw [div_le_iff₀ hd_u]
      have h3 : (0:ℝ) ≤ |u| ^ 3 := by positivity
      nlinarith [hu_bound, hu_nn]
    have h3 : u ^ 2/2 = |u| ^ 2/2 := by rw [sq_abs]
    rw [hv]
    linarith
  have hw_v : w - Real.log (1 + w) ≤ |w| ^ 2/2 + 2 * |w| ^ 3 := by
    have h := t_sub_log_le_B w hw_lt1
    have h3 : w ^ 2/2 = |w| ^ 2/2 := by rw [sq_abs]
    linarith [h, hw3, h3]
  -- main chain
  have hbody : Real.sqrt x * L * (u/L - Real.log (1 + w))
      ≤ Real.sqrt x * |u| ^ 2/2 + 1.026 * (Real.sqrt x * |u| ^ 3)
        + Real.sqrt x * |v| ^ 2/(2*L) + 2 * (Real.sqrt x * |v| ^ 3)/L^2 := by
    have hsplit : u/L - Real.log (1 + w) = (u - v)/L + (w - Real.log (1 + w)) := by
      rw [hw]; field_simp; ring
    have hstep : u/L - Real.log (1 + w)
        ≤ (|u| ^ 2/2 + 1.026 * |u| ^ 3)/L + (|w| ^ 2/2 + 2 * |w| ^ 3) := by
      rw [hsplit]
      have h1 : (u - v)/L ≤ (|u| ^ 2/2 + 1.026 * |u| ^ 3)/L :=
        div_le_div_of_nonneg_right hu_v hL0.le
      linarith [h1, hw_v]
    have hmul := mul_le_mul_of_nonneg_left hstep (by positivity : (0:ℝ) ≤ Real.sqrt x * L)
    have he1 : Real.sqrt x * L * ((|u| ^ 2/2 + 1.026 * |u| ^ 3)/L + (|w| ^ 2/2 + 2 * |w| ^ 3))
        = Real.sqrt x * |u| ^ 2/2 + 1.026 * (Real.sqrt x * |u| ^ 3)
          + Real.sqrt x * L * (|w| ^ 2/2) + Real.sqrt x * L * (2 * |w| ^ 3) := by
      field_simp
      ring
    have he2 : Real.sqrt x * L * (|w| ^ 2/2) = Real.sqrt x * |v| ^ 2/(2*L) := by
      rw [hw, abs_div, abs_of_pos hL0]
      field_simp
    have he3 : Real.sqrt x * L * (2 * |w| ^ 3) = 2 * (Real.sqrt x * |v| ^ 3)/L^2 := by
      rw [hw, abs_div, abs_of_pos hL0]
      field_simp
    rw [he1, he2, he3] at hmul
    exact hmul
  have hfinal : Real.sqrt x * L * (u/L - Real.log (1 + w)) ≤ 0.12 := by
    have e1 : Real.sqrt x * |u| ^ 2/2 ≤ 0.202821/2 := by linarith [hsr2]
    have e2 : 1.026 * (Real.sqrt x * |u| ^ 3) ≤ 1.026 * 0.005138 :=
      mul_le_mul_of_nonneg_left hsr3 (by norm_num)
    have e3 : Real.sqrt x * |v| ^ 2/(2*L) ≤ 0.215173/(2*11.5) := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < 2*L) (by norm_num : (0:ℝ) < 2*11.5)]
      nlinarith [hvr2, hL115, abs_nonneg v, Real.sqrt_nonneg x]
    have e4 : 2 * (Real.sqrt x * |v| ^ 3)/L^2 ≤ 2 * 0.005615/(11.5^2) := by
      rw [div_le_div_iff₀ (by positivity : (0:ℝ) < L^2) (by norm_num : (0:ℝ) < 11.5^2)]
      nlinarith [hvr3, hL115, abs_nonneg v, Real.sqrt_nonneg x]
    have hnum : (0.202821:ℝ)/2 + 1.026 * 0.005138 + 0.215173/(2*11.5)
        + 2 * 0.005615/(11.5^2) ≤ 0.12 := by norm_num
    linarith [hbody, e1, e2, e3, e4, hnum]
  have hfin : u/L - Real.log (1 + w) ≤ 0.12/(Real.sqrt x * L) := by
    rw [le_div_iff₀ (by positivity : (0:ℝ) < Real.sqrt x * L)]
    have he : (u/L - Real.log (1 + w)) * (Real.sqrt x * L)
        = Real.sqrt x * L * (u/L - Real.log (1 + w)) := by ring
    rw [he]
    exact hfinal
  have hgoal : (12/100) * (1 / (Real.sqrt x * Real.log x)) = 0.12/(Real.sqrt x * L) := by
    rw [← hL]
    have h12 : (12:ℝ)/100 = 0.12 := by norm_num
    rw [h12, one_div, div_eq_mul_inv]
  rw [hE, hgoal]
  exact hfin

set_option linter.unusedVariables false in
/-- Region II upper bound for the `log log` correction, from the Chebyshev bound
`|ψ ξ − ξ| ≤ 0.45 ξ^{3/4} + 2` (valid for `10^5 ≤ ξ < 10^8`). -/
theorem caW_upper_B (ε : ℝ) (hε : 0 < ε)
    (hlo : 100000 ≤ (Work.RHPlan.caXi ε : ℝ)) (hhi : (Work.RHPlan.caXi ε : ℝ) < (10:ℝ)^8)
    (hA2 : |Chebyshev.psi (Work.RHPlan.caXi ε : ℝ) - (Work.RHPlan.caXi ε : ℝ)|
        ≤ 0.45 * (Work.RHPlan.caXi ε : ℝ) ^ (3/4:ℝ) + 2) :
    Work.RHContract.Margin.caW ε
      ≤ (12/100) * Work.RHContract.A.RegionII.caU (Work.RHPlan.caXi ε : ℝ) := by
  have h := caW_core_B (Work.RHPlan.caXi ε : ℝ) (Chebyshev.psi (Work.RHPlan.caXi ε : ℝ)) hlo hA2
  simpa only [Work.RHContract.Margin.caW, Work.RHContract.A.RegionII.caU] using h

end

end Work.RHContract.A.regionII
