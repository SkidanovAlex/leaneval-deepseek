import Mathlib

set_option maxHeartbeats 4000000

/-!
# `Work.RHContract.A.R3.caW_core`

The real-variable core of the `W`-estimate (`Margin.caW`) of the colossally abundant
analysis.  For `x ≥ 10^8` and `p > 1` with `|p − x| ≤ 0.45 x^{3/4} + 2` we prove

`log log x + (p − x)/(x log x) − log log p ≤ (115/1000) / (√x · log x)`.

Writing `u = (p − x)/x`, `v = log (1 + u)` and `L = log x`, the left-hand side times `L` is
`γ u + L · γ (v/L)` where `γ w = w − log (1 + w)`; with `x ≥ 10^8` one has `|u| ≤ 0.45/√[4]{x}`
and the estimates `γ w ≤ w²/2 + 2|w|³` (`|w| ≤ 1/2`) and `|log (1+u)| ≤ |u| + 2u²` give the
claim after an explicit numerical bound.
-/

namespace Work.RHContract.A.R3

noncomputable section

/-- `(10^8)^{-1/4} = 1/100`. -/
lemma ten8_rpow_neg_quarter : ((10:ℝ)^8) ^ (-(1/4:ℝ)) = 1/100 := by
  rw [← Real.rpow_natCast (10:ℝ) 8]
  rw [← Real.rpow_mul (x := (10:ℝ)) (by norm_num) ((8:ℕ):ℝ) (-(1/4:ℝ))]
  norm_num

/-- `16 ≤ log x` for `x ≥ 10^8` (as `exp 16 < 3^16 < 10^8`). -/
lemma sixteen_le_log_of_ge (x : ℝ) (hx : (10:ℝ)^8 ≤ x) : 16 ≤ Real.log x := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le (by norm_num) hx
  rw [Real.le_log_iff_exp_le hx0]
  have he : Real.exp 16 = (Real.exp 1) ^ (16:ℕ) := by
    rw [show (16:ℝ) = ((16:ℕ):ℝ) * 1 by norm_num, Real.exp_nat_mul]
  rw [he]
  have h3 : (Real.exp 1)^(16:ℕ) ≤ (3:ℝ)^(16:ℕ) :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_three) 16
  have h316 : (3:ℝ)^(16:ℕ) < (10:ℝ)^8 := by norm_num
  linarith

/-- `γ (-t) = -t - log (1-t) ≤ t²/2 + 2t³` for `0 ≤ t ≤ 1/2`. -/
lemma gamma_neg (t : ℝ) (ht : 0 ≤ t) (ht2 : t ≤ 1/2) :
    -t - Real.log (1 - t) ≤ t^2/2 + 2*t^3 := by
  have ht1 : |t| < 1 := by rw [abs_of_nonneg ht]; linarith
  have h := Real.abs_log_sub_add_sum_range_le (x := t) ht1 2
  have hsum : (∑ i ∈ Finset.range 2, t ^ (i + 1) / ((i : ℝ) + 1)) = t + t^2/2 := by
    norm_num [Finset.sum_range_succ]
  rw [hsum, abs_of_nonneg ht] at h
  have h2 : t + t^2/2 + Real.log (1 - t) ≥ -(t^3/(1-t)) := (abs_le.mp h).1
  have h3 : t^3/(1-t) ≤ 2*t^3 := by
    rw [div_le_iff₀ (by linarith : (0:ℝ) < 1 - t)]
    have ht3 : (0:ℝ) ≤ t^3 := by positivity
    have : t^3 * (2*t) ≤ t^3 * 1 := mul_le_mul_of_nonneg_left (by linarith) ht3
    linarith
  linarith

/-- `γ w = w - log (1+w) ≤ w²/2 + 2|w|³` for `w > -1`, `|w| ≤ 1/2`. -/
lemma gamma_bound (w : ℝ) (hw : -1 < w) (habs : |w| ≤ 1/2) :
    w - Real.log (1 + w) ≤ w^2/2 + 2*|w|^3 := by
  rcases le_or_gt 0 w with hw0 | hwneg
  · have h1 : 2 * w / (w + 2) ≤ Real.log (1 + w) := Real.le_log_one_add_of_nonneg hw0
    have hwabs : |w| = w := abs_of_nonneg hw0
    rw [hwabs]
    have h3 : w - 2*w/(w+2) = w^2/(w+2) := by field_simp; try ring
    have h4 : w^2/(w+2) ≤ w^2/2 := by
      rw [div_le_iff₀ (by linarith : (0:ℝ) < w + 2)]
      nlinarith
    have h5 : w - Real.log (1 + w) ≤ w - 2*w/(w+2) := by linarith
    rw [h3] at h5
    nlinarith [h4, h5, hw0]
  · set t := -w with ht
    have ht0 : 0 ≤ t := by rw [ht]; linarith
    have ht12 : t ≤ 1/2 := by
      have habs' : |w| = t := by rw [ht]; exact abs_of_neg hwneg
      linarith [habs, habs']
    have hwt : w = -t := by rw [ht]; ring
    rw [hwt]
    have key : -t - Real.log (1 - t) ≤ t^2/2 + 2*t^3 := gamma_neg t ht0 ht12
    have habs_t : |(-t)| = t := by rw [abs_neg, abs_of_nonneg ht0]
    rw [habs_t]
    have h1t : (1:ℝ) + (-t) = 1 - t := by ring
    rw [h1t]
    have hsq : (-t)^2 = t^2 := by ring
    rw [hsq]
    exact key

/-- `|log (1+u)| ≤ |u| + 2u²` for `|u| ≤ 1/2`. -/
lemma abs_log_one_add_le {u : ℝ} (hu : |u| ≤ 1/2) :
    |Real.log (1 + u)| ≤ |u| + 2*u^2 := by
  have hulow : -(1/2) ≤ u := (abs_le.mp hu).1
  rcases le_or_gt 0 u with h0 | hneg
  · have h1 : Real.log (1 + u) ≤ u := by
      have := Real.log_le_sub_one_of_pos (by linarith : (0:ℝ) < 1 + u)
      linarith
    have h2 : 0 ≤ Real.log (1 + u) := Real.log_nonneg (by linarith)
    rw [abs_of_nonneg h2, abs_of_nonneg h0]
    nlinarith [h1, h0]
  · have hlog : Real.log (1 + u) < 0 := Real.log_neg (by linarith : (0:ℝ) < 1 + u) (by linarith)
    rw [abs_of_neg hlog, abs_of_neg hneg]
    have h1u : 0 < 1 + u := by linarith
    have h : Real.log ((1+u)⁻¹) ≤ (1+u)⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr h1u)
    rw [Real.log_inv] at h
    have hb : (1+u)⁻¹ ≤ 1 - u + 2*u^2 := by
      rw [inv_le_iff_one_le_mul₀ h1u]
      nlinarith
    linarith

/-- The explicit numerical core: for `0 < s ≤ 1/100`, `0 ≤ b ≤ 1/16` and `0 ≤ a ≤ 0.450002 s`,
`a²/2 + 2a³ + 1.0201 a² b/2 + 2·1.030301 a³ b² ≤ 0.115 s²`. -/
lemma num_caW (a s b : ℝ) (ha0 : 0 ≤ a) (hs0 : 0 < s) (hs : s ≤ 1/100)
    (hb0 : 0 ≤ b) (hb : b ≤ 1/16) (ha : a ≤ 0.450002 * s) :
    a^2/2 + 2*a^3 + 1.0201*a^2*b/2 + 2*1.030301*a^3*b^2 ≤ 0.115 * s^2 := by
  have hs2 : 0 ≤ s^2 := sq_nonneg s
  have hs3 : s^3 ≤ s^2 * (1/100) := by nlinarith
  have ha2 : a^2 ≤ 0.202502 * s^2 := by nlinarith
  have ha3 : a^3 ≤ 0.000911263 * s^2 := by nlinarith
  have hb2 : a^2 * b ≤ 0.202502 * s^2 * (1/16) := by nlinarith
  have hbsq : b^2 ≤ 1/256 := by nlinarith
  have hb3 : a^3 * b^2 ≤ 0.000911263 * s^2 * (1/256) := by nlinarith
  nlinarith

theorem caW_core (x p : ℝ) (hx8 : (10:ℝ)^8 ≤ x) (hp1 : 1 < p)
    (he : |p - x| ≤ 0.45 * x^(3/4:ℝ) + 2) :
    Real.log (Real.log x) + (p - x)/(x * Real.log x) - Real.log (Real.log p)
      ≤ (115/1000) * (1/(Real.sqrt x * Real.log x)) := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le (by norm_num) hx8
  have hp0 : (0:ℝ) < p := lt_trans zero_lt_one hp1
  set L : ℝ := Real.log x with hL
  have hL16 : 16 ≤ L := by rw [hL]; exact sixteen_le_log_of_ge x hx8
  have hL0 : 0 < L := by linarith
  set u : ℝ := (p - x)/x with hu
  have hp_eq : p = x * (1 + u) := by rw [hu]; field_simp; try ring
  have h1u : 0 < 1 + u := by
    have hpdiv : p / x = 1 + u := by rw [hu]; field_simp; try ring
    rw [← hpdiv]; exact div_pos hp0 hx0
  set v : ℝ := Real.log (1 + u) with hv
  have hlogp : Real.log p = L + v := by
    rw [hp_eq, Real.log_mul (ne_of_gt hx0) (ne_of_gt h1u), hL, hv]
  set s : ℝ := x ^ (-(1/4:ℝ)) with hs
  have hs0 : 0 < s := by rw [hs]; exact Real.rpow_pos_of_pos hx0 _
  have hsle : s ≤ 1/100 := by
    rw [hs]
    have h := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < (10:ℝ)^8) hx8
      (by norm_num : (-(1/4:ℝ)) ≤ 0)
    rwa [ten8_rpow_neg_quarter] at h
  have hs4 : s^4 = 1/x := by
    rw [hs, ← Real.rpow_natCast (x ^ (-(1/4:ℝ))) 4,
        ← Real.rpow_mul (x := x) hx0.le (-(1/4:ℝ)) ((4:ℕ):ℝ)]
    rw [show (-(1/4:ℝ) * ((4:ℕ):ℝ)) = -1 by norm_num, Real.rpow_neg_one, one_div]
  have hx34 : x^(3/4:ℝ) = x * s := by
    rw [hs]
    rw [show (3/4:ℝ) = 1 + (-(1/4)) by norm_num, Real.rpow_add hx0, Real.rpow_one]
  have hu_bound : |u| ≤ 0.45 * s + 2 * s^4 := by
    have h1 : |u| = |p - x| / x := by rw [hu, abs_div, abs_of_pos hx0]
    rw [h1]
    refine le_trans (div_le_div_of_nonneg_right he hx0.le) ?_
    rw [hx34]
    rw [show (0.45 * (x * s) + 2)/x = 0.45 * s + 2 * s^4 by rw [hs4]; field_simp]
  have hu_le : |u| ≤ 0.450002 * s := by
    have hs4b : 2 * s^4 ≤ 0.000002 * s := by
      have h : s^3 ≤ (1/100:ℝ)^3 := pow_le_pow_left₀ hs0.le hsle 3
      have hs4eq : s^4 = s^3 * s := by ring
      rw [hs4eq]; nlinarith [hs0, h]
    nlinarith [hu_bound, hs4b]
  have hu_abs : |u| ≤ 1/2 := by
    have h2 : 0.450002 * s ≤ 0.450002 * (1/100) := mul_le_mul_of_nonneg_left hsle (by norm_num)
    nlinarith [hu_le]
  have hu_005 : |u| ≤ 0.005 := by
    have h2 : 0.450002 * s ≤ 0.450002 * (1/100) := mul_le_mul_of_nonneg_left hsle (by norm_num)
    nlinarith [hu_le]
  have hu_gt : -1 < u := by
    have h := (abs_le.mp hu_abs).1
    linarith
  have hvu : |v| ≤ |u| + 2*u^2 := by rw [hv]; exact abs_log_one_add_le hu_abs
  have hv_le : |v| ≤ 1.01 * |u| := by
    have h2 : 2*u^2 ≤ 0.01 * |u| := by
      rw [← sq_abs]
      nlinarith [abs_nonneg u, hu_005]
    nlinarith [hvu, h2]
  have hv2 : v^2 ≤ 1.0201 * u^2 := by
    have h1 : |v|^2 ≤ (1.01 * |u|)^2 := pow_le_pow_left₀ (abs_nonneg v) hv_le 2
    rw [mul_pow] at h1
    rw [sq_abs, sq_abs] at h1
    norm_num at h1 ⊢
    exact h1
  have hv3 : |v|^3 ≤ 1.030301 * |u|^3 := by
    have h1 : |v|^3 ≤ (1.01 * |u|)^3 := pow_le_pow_left₀ (abs_nonneg v) hv_le 3
    rw [mul_pow] at h1
    norm_num at h1 ⊢
    exact h1
  have hvL_gt : -1 < v / L := by
    rw [lt_div_iff₀ hL0]
    have h : L + v = Real.log p := by rw [hlogp]
    linarith [Real.log_pos hp1]
  have hvL_abs : |v / L| ≤ 1/2 := by
    rw [abs_div, abs_of_pos hL0]
    rw [div_le_iff₀ hL0]
    nlinarith [hv_le, hu_abs, hL16]
  have hg1 : u - Real.log (1 + u) ≤ u^2/2 + 2*|u|^3 := gamma_bound u hu_gt hu_abs
  have hg2 : v/L - Real.log (1 + v/L) ≤ (v/L)^2/2 + 2*|v/L|^3 := gamma_bound (v/L) hvL_gt hvL_abs
  have hLabs : L * ((v/L)^2/2 + 2*|v/L|^3) = v^2/(2*L) + 2*|v|^3/L^2 := by
    rw [abs_div, abs_of_pos hL0]
    field_simp
  have hAbound : u - L * Real.log (1 + v/L)
      ≤ |u|^2/2 + 2*|u|^3 + 1.0201*|u|^2/(2*L) + 2*1.030301*|u|^3/L^2 := by
    have hA : u - L * Real.log (1 + v/L)
        = (u - Real.log (1 + u)) + L * (v/L - Real.log (1 + v/L)) := by
      rw [hv]; field_simp; try ring
    rw [hA]
    have h1 : u - Real.log (1 + u) ≤ |u|^2/2 + 2*|u|^3 := by
      simpa only [sq_abs] using hg1
    have h2 := mul_le_mul_of_nonneg_left hg2 hL0.le
    rw [hLabs] at h2
    have h4 : v^2/(2*L) ≤ 1.0201*|u|^2/(2*L) := by
      apply div_le_div_of_nonneg_right _ (by linarith : (0:ℝ) ≤ 2*L)
      rw [sq_abs]; exact hv2
    have h5 : 2*|v|^3/L^2 ≤ 2*1.030301*|u|^3/L^2 := by
      apply div_le_div_of_nonneg_right _ (by positivity : (0:ℝ) ≤ L^2)
      nlinarith [hv3]
    linarith
  have hb : (1:ℝ)/L ≤ 1/16 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 16) hL16
  have hb0 : (0:ℝ) ≤ 1/L := by positivity
  have hnum := num_caW |u| s (1/L) (abs_nonneg u) hs0 hsle hb0 hb hu_le
  have hnum2 : |u|^2/2 + 2*|u|^3 + 1.0201*|u|^2/(2*L) + 2*1.030301*|u|^3/L^2 ≤ 0.115 * s^2 := by
    have e1 : 1.0201*|u|^2/(2*L) = 1.0201*|u|^2*(1/L)/2 := by ring_nf
    have e2 : 2*1.030301*|u|^3/L^2 = 2*1.030301*|u|^3*(1/L)^2 := by ring_nf
    rw [e1, e2]
    exact hnum
  have hs2 : s^2 = 1/Real.sqrt x := by
    have h : s^2 = x^(-(1/2:ℝ)) := by
      rw [hs, ← Real.rpow_natCast (x ^ (-(1/4:ℝ))) 2,
          ← Real.rpow_mul (x := x) hx0.le (-(1/4:ℝ)) ((2:ℕ):ℝ)]
      rw [show (-(1/4:ℝ) * ((2:ℕ):ℝ)) = -(1/2) by norm_num]
    have hsqrt : (0:ℝ) < Real.sqrt x := Real.sqrt_pos.mpr hx0
    rw [eq_div_iff hsqrt.ne']
    rw [h, Real.sqrt_eq_rpow, ← Real.rpow_add hx0 (-(1/2:ℝ)) (1/2:ℝ)]
    rw [show (-(1/2:ℝ)) + (1/2) = 0 by norm_num, Real.rpow_zero]
  have hbound : u - L * Real.log (1 + v/L) ≤ (115/1000)/Real.sqrt x := by
    have h := le_trans hAbound hnum2
    rw [hs2] at h
    have heq : (0.115:ℝ) * (1/Real.sqrt x) = (115/1000)/Real.sqrt x := by
      rw [show (0.115:ℝ) = 115/1000 by norm_num, mul_one_div]
    linarith [h, heq]
  have hloglogp : Real.log (Real.log p) = Real.log L + Real.log (1 + v/L) := by
    rw [hlogp]
    have hLv : L + v = L * (1 + v/L) := by field_simp; try ring
    have hvp : 0 < 1 + v/L := by
      have : (L+v)/L = 1 + v/L := by field_simp; try ring
      rw [← this]
      have h2 : L + v = Real.log p := by rw [hlogp]
      rw [h2]; exact div_pos (Real.log_pos hp1) hL0
    rw [hLv, Real.log_mul (ne_of_gt hL0) (ne_of_gt hvp)]
  have hE : Real.log L + (p - x)/(x * L) - Real.log (Real.log p) = u/L - Real.log (1 + v/L) := by
    rw [hloglogp]
    have hdiv : (p - x)/(x * L) = u/L := by rw [hu]; field_simp; try ring
    rw [hdiv]; ring
  calc Real.log L + (p - x)/(x * L) - Real.log (Real.log p)
      = u/L - Real.log (1 + v/L) := hE
    _ = (1/L) * (u - L * Real.log (1 + v/L)) := by field_simp; try ring
    _ ≤ (1/L) * ((115/1000)/Real.sqrt x) := mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (115/1000) * (1/(Real.sqrt x * L)) := by field_simp; try ring

end

end Work.RHContract.A.R3
