import Mathlib
import Submission.Work.BW.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Real

/-! ### Elementary bounds on `ξ = pxi r = 1 - 0.536/r` and on `exp (-0.536)`.

These are the pure real-arithmetic inputs to the §19 integer-step numerics
(`0 ≤ j ≤ r-2`, `J ≤ 50 log(2rd)`), specialised to the constant `16.05` used by
the `extrap_int_h1` consumer. -/

private lemma pxi_pos_lo {r : ℕ} (hr : 2 ≤ r) : 0 < pxi r := by
  have hrR : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  rw [pxi, sub_pos]
  have h : 0.536 / (r:ℝ) ≤ 0.536/2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hrR
  linarith

private lemma pxi_le_one_lo (r : ℕ) : pxi r ≤ 1 := by
  rw [pxi]
  have h : (0:ℝ) ≤ 0.536 / (r:ℝ) := by positivity
  linarith

private lemma exp_neg_536_ge_lo : (0.5847 : ℝ) ≤ Real.exp (-0.536) := by
  have h := Real.exp_bound (x := (-0.536:ℝ)) (by norm_num) (n := 6) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

private lemma pxi_mono_lo {r r₀ : ℕ} (h : r₀ ≤ r) (hr₀ : 1 ≤ r₀) : pxi r₀ ≤ pxi r := by
  rw [pxi, pxi]
  have h1 : (0:ℝ) < r₀ := by exact_mod_cast (by omega : 0 < r₀)
  have h3 : (r₀:ℝ) ≤ r := by exact_mod_cast h
  have : 0.536 / (r:ℝ) ≤ 0.536 / (r₀:ℝ) := div_le_div_of_nonneg_left (by norm_num) h1 h3
  linarith

private lemma pxi_pow_pred_lower_lo {r : ℕ} (hr : 2 ≤ r) : Real.exp (-0.536) ≤ pxi r ^ (r - 1) := by
  have hrR : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hrpos : (0:ℝ) < (r:ℝ) := by linarith
  have hrne : (r:ℝ) ≠ 0 := ne_of_gt hrpos
  have hx0 : 0 < pxi r := pxi_pos_lo hr
  have h1 : (0:ℝ) < 1 - 0.536/(r:ℝ) := by
    rw [sub_pos, div_lt_one hrpos]; linarith
  have h2 : Real.log ((1 - 0.536/(r:ℝ))⁻¹) ≤ (1 - 0.536/(r:ℝ))⁻¹ - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_inv] at h2
  have h3 : (1 - 0.536/(r:ℝ))⁻¹ - 1 = 0.536/((r:ℝ) - 0.536) := by
    have hne : (1 - 0.536/(r:ℝ)) ≠ 0 := ne_of_gt h1
    have hne2 : ((r:ℝ) - 0.536) ≠ 0 := by apply ne_of_gt; linarith
    field_simp
    ring
  rw [h3] at h2
  have h4 : (1 - 0.536/(r:ℝ)) = pxi r := by simp [pxi]
  rw [h4] at h2
  have hrk : (0:ℝ) < (r:ℝ) - 0.536 := by linarith
  have hfac : (0:ℝ) ≤ ((r-1:ℕ):ℝ) := by positivity
  have hr1c : ((r-1:ℕ):ℝ) = (r:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  have hle : ((r-1:ℕ):ℝ) * (0.536/((r:ℝ) - 0.536)) ≤ 0.536 := by
    rw [hr1c, ← mul_div_assoc, div_le_iff₀ hrk]
    nlinarith
  have h5 : ((r-1:ℕ):ℝ) * (-Real.log (pxi r)) ≤ 0.536 :=
    le_trans (mul_le_mul_of_nonneg_left h2 hfac) hle
  have hp : 0 < pxi r ^ (r-1) := pow_pos hx0 _
  rw [← Real.log_le_log_iff (Real.exp_pos _) hp, Real.log_exp, Real.log_pow]
  linarith

private lemma two_pxi_pow_r_ge_one_lo {r : ℕ} (hr : 2 ≤ r) : 1 ≤ 2 * pxi r ^ r := by
  have hx0 : 0 < pxi r := pxi_pos_lo hr
  rcases lt_or_ge r 5 with h5 | h5
  · interval_cases r <;> norm_num [pxi]
  · have hlow : Real.exp (-0.536) ≤ pxi r ^ (r-1) := pxi_pow_pred_lower_lo hr
    have he : (0.5847:ℝ) ≤ pxi r ^ (r-1) := le_trans exp_neg_536_ge_lo hlow
    have hx5 : (1 - 0.536/5 : ℝ) ≤ pxi r := by
      rw [pxi]
      have hrR : (5:ℝ) ≤ (r:ℝ) := by exact_mod_cast h5
      have : 0.536/(r:ℝ) ≤ 0.536/5 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hrR
      linarith
    have hmul : pxi r ^ (r-1) * pxi r = pxi r ^ r := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ r)]
    have h1 : (0.5847:ℝ) * (1 - 0.536/5) ≤ pxi r ^ r := by
      rw [← hmul]
      exact mul_le_mul he hx5 (by norm_num) (le_of_lt (pow_pos hx0 _))
    nlinarith [h1]

/-- The key numeric inequality for `0 ≤ j ≤ 5`: `2^j (16.05 ξ^j - 9.30) ≥ 4.99`,
by a finite check at the minimal admissible `r = j + 2`. -/
private lemma pxi_mul_two_pow_lower_small {r j : ℕ} (_hr : 2 ≤ r) (hj : j ≤ 5) (hjr : j + 2 ≤ r) :
    4.99 ≤ 16.05 * (2 * pxi r) ^ j - 9.30 * (2:ℝ)^j := by
  have hx2 : (0:ℝ) ≤ pxi (j+2) := le_of_lt (pxi_pos_lo (by omega))
  have hmono : pxi (j+2) ≤ pxi r := pxi_mono_lo hjr (by omega)
  have hpj : pxi (j+2) ^ j ≤ pxi r ^ j := pow_le_pow_left₀ hx2 hmono j
  have h2j : (0:ℝ) ≤ (2:ℝ)^j := by positivity
  have hstep : (2:ℝ)^j * (16.05 * pxi (j+2)^j - 9.30) ≤ (2:ℝ)^j * (16.05 * pxi r ^ j - 9.30) :=
    mul_le_mul_of_nonneg_left (by linarith) h2j
  have hkey : 4.99 ≤ (2:ℝ)^j * (16.05 * pxi (j+2)^j - 9.30) := by
    interval_cases j <;> norm_num [pxi]
  have hfin : (2:ℝ)^j * (16.05 * pxi r ^ j - 9.30) = 16.05 * (2 * pxi r) ^ j - 9.30 * (2:ℝ)^j := by
    rw [mul_pow]; ring
  rw [hfin] at hstep
  linarith

/-- The key numeric inequality for `j ≥ 6`: `2^j (16.05 ξ^j - 9.30) ≥ 4.99`, using
`ξ^j ≥ ξ^{r-1} ≥ e^{-0.536} ≥ 0.5847` and `2^j ≥ 64`. -/
private lemma pxi_mul_two_pow_lower_big {r j : ℕ} (hr : 2 ≤ r) (hj : 6 ≤ j) (hjr : j + 2 ≤ r) :
    4.99 ≤ 16.05 * (2 * pxi r) ^ j - 9.30 * (2:ℝ)^j := by
  have hx0 : 0 < pxi r := pxi_pos_lo hr
  have hx1 : pxi r ≤ 1 := pxi_le_one_lo r
  have hjr' : j ≤ r - 2 := by omega
  have hp : pxi r ^ (r-2) ≤ pxi r ^ j := pow_le_pow_of_le_one (le_of_lt hx0) hx1 hjr'
  have hp2 : pxi r ^ (r-1) ≤ pxi r ^ (r-2) := pow_le_pow_of_le_one (le_of_lt hx0) hx1 (by omega)
  have hlow : Real.exp (-0.536) ≤ pxi r ^ (r-1) := pxi_pow_pred_lower_lo hr
  have he : (0.5847:ℝ) ≤ pxi r ^ j := by
    have h1 : (0.5847:ℝ) ≤ pxi r ^ (r-1) := le_trans exp_neg_536_ge_lo hlow
    linarith
  have h2j : (64:ℝ) ≤ (2:ℝ)^j := by
    have h := pow_le_pow_right₀ (show (1:ℝ) ≤ 2 by norm_num) hj
    norm_num at h
    linarith [h]
  have hc : (0:ℝ) ≤ 16.05 * pxi r ^ j - 9.30 := by linarith
  have hkey : 64 * 0.084 ≤ (2:ℝ)^j * (16.05 * pxi r ^ j - 9.30) := by
    calc 64 * 0.084 ≤ 64 * (16.05 * pxi r ^ j - 9.30) := by linarith
      _ ≤ (2:ℝ)^j * (16.05 * pxi r ^ j - 9.30) := mul_le_mul_of_nonneg_right h2j hc
  have hfin : (2:ℝ)^j * (16.05 * pxi r ^ j - 9.30) = 16.05 * (2 * pxi r) ^ j - 9.30 * (2:ℝ)^j := by
    rw [mul_pow]; ring
  rw [hfin] at hkey
  linarith

theorem num19_int_JP_lo {r d : ℕ} (hr : 2 ≤ r) (hd : 1 ≤ d) (J : ℕ)
    (hJ : (J : ℝ) ≤ 50 * Real.log (2 * r * d)) (j : ℕ) (hj : j + 2 ≤ r) :
    0.735 * pxi r ^ (j + 1 + r * J) + 1.055 + 0.044 * (J : ℝ) / Real.log (2 * r * d) +
      9.30 * (2 : ℝ) ^ j * ((2 * pxi r ^ r)⁻¹) ^ J - 16.05 * (2 * pxi r) ^ j ≤ -1 := by
  have hrR : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hdR : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  have hx0 : 0 < pxi r := pxi_pos_lo hr
  have hx1 : pxi r ≤ 1 := pxi_le_one_lo r
  have hLpos : 0 < Real.log (2 * r * d) := by
    apply Real.log_pos
    nlinarith [hrR, hdR]
  have hcJ : 0.044 * (J:ℝ) / Real.log (2 * r * d) ≤ 2.2 := by
    rw [div_le_iff₀ hLpos]
    nlinarith [hJ]
  have hT1 : 0.735 * pxi r ^ (j + 1 + r * J) ≤ 0.735 := by
    have h := pow_le_one₀ (le_of_lt hx0) hx1 (n := j + 1 + r*J)
    nlinarith [h]
  have hT4 : 9.30 * (2:ℝ)^j * ((2 * pxi r ^ r)⁻¹)^J ≤ 9.30 * (2:ℝ)^j := by
    have hb : 1 ≤ 2 * pxi r ^ r := two_pxi_pow_r_ge_one_lo hr
    have hbin : ((2 * pxi r ^ r)⁻¹)^J ≤ 1 := by
      rw [inv_pow]
      exact inv_le_one_of_one_le₀ (one_le_pow₀ hb)
    have h930 : (0:ℝ) ≤ 9.30 * (2:ℝ)^j := by positivity
    calc 9.30 * (2:ℝ)^j * ((2*pxi r^r)⁻¹)^J ≤ 9.30 * (2:ℝ)^j * 1 :=
          mul_le_mul_of_nonneg_left hbin h930
      _ = 9.30 * (2:ℝ)^j := by ring
  have hkey : 4.99 ≤ 16.05 * (2 * pxi r) ^ j - 9.30 * (2:ℝ)^j := by
    rcases lt_or_ge j 6 with h6 | h6
    · exact pxi_mul_two_pow_lower_small hr (by omega) hj
    · exact pxi_mul_two_pow_lower_big hr h6 hj
  linarith [hT1, hcJ, hT4, hkey]

end Work.BW
