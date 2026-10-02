import Mathlib

/-!
# `Work.ZeroDensity.LogFree.exists_const_log_bound`

Elementary arithmetic behind the pole-residue bound: for every `C₀ > 0` there is `C > 0` with

  `2·(log ⌈W⌉₊ + C₀) + 2·(log(⌈W⌉₊/W))^2·(1 + log ⌈W⌉₊)^3 ≤ C·log W`   for all `W ≥ 4`.

With `z = ⌈W⌉₊ ∈ [W, W+1)`: `log z ≤ log W + log 2`, `0 ≤ log(z/W) ≤ z/W - 1 ≤ 1/W`, so the
second term is at most `2(1+log W + log 2)^3/W^2`, and since `1 ≤ log W ≤ W` on `W ≥ 4` this is at
most `54 log W`, while the first term is at most `(2 + 2 log 2 + 2C₀)·log W`.
-/

noncomputable section

namespace Work.ZeroDensity.LogFree

theorem exists_const_log_bound (C₀ : ℝ) (hC₀ : 0 < C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ W : ℝ, 4 ≤ W →
      2 * (Real.log (⌈W⌉₊ : ℝ) + C₀)
        + 2 * (Real.log ((⌈W⌉₊ : ℝ) / W)) ^ 2 * (1 + Real.log (⌈W⌉₊ : ℝ)) ^ 3
        ≤ C * Real.log W := by
  refine ⟨56 + 2 * Real.log 2 + 2 * C₀, by positivity, ?_⟩
  intro W hW
  set z : ℕ := ⌈W⌉₊ with hzdef
  have hWpos : 0 < W := by linarith only [hW]
  have hW1 : (1 : ℝ) ≤ W := by linarith only [hW]
  have hzpos : (0 : ℝ) < (z : ℝ) := by
    rw [hzdef]; exact_mod_cast Nat.ceil_pos.mpr hWpos
  have hzge : W ≤ (z : ℝ) := by rw [hzdef]; exact Nat.le_ceil W
  have hzlt : (z : ℝ) < W + 1 := by rw [hzdef]; exact Nat.ceil_lt_add_one hWpos.le
  have hz2W : (z : ℝ) ≤ W * 2 := by linarith only [hW, hzlt]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith only [h]
  have hu1 : 1 ≤ Real.log W := by
    have h4 : (1 : ℝ) ≤ Real.log 4 := by
      have h2 : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        ring
      rw [h2]
      linarith only [Real.log_two_gt_d9, hlog2pos]
    exact h4.trans (Real.log_le_log (by norm_num) hW)
  have hu0 : 0 ≤ Real.log W := by linarith only [hu1]
  have hlogWle : Real.log W ≤ W := by
    have h := Real.log_le_sub_one_of_pos hWpos; linarith only [h]
  have hlogz_le : Real.log (z : ℝ) ≤ Real.log W + Real.log 2 := by
    have h := Real.log_le_log hzpos hz2W
    rwa [Real.log_mul (ne_of_gt hWpos) (by norm_num : (2 : ℝ) ≠ 0)] at h
  have hlogz0 : 0 ≤ Real.log (z : ℝ) := Real.log_nonneg (by linarith only [hW, hzge])
  have hratio0 : 0 ≤ Real.log ((z : ℝ) / W) :=
    Real.log_nonneg (by rw [le_div_iff₀ hWpos, one_mul]; exact hzge)
  have hratio_le : Real.log ((z : ℝ) / W) ≤ 1 / W := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < (z : ℝ) / W by positivity)
    have h2 : (z : ℝ) / W - 1 ≤ 1 / W := by
      rw [div_sub_one (ne_of_gt hWpos), div_le_div_iff_of_pos_right hWpos]
      linarith only [hzlt]
    linarith only [h1, h2]
  -- Step 1: replace `z` by `W` in the two logarithmic factors.
  have hstep1 : 2 * (Real.log (z : ℝ) + C₀)
        + 2 * (Real.log ((z : ℝ) / W)) ^ 2 * (1 + Real.log (z : ℝ)) ^ 3
      ≤ 2 * (Real.log W + Real.log 2 + C₀)
        + 2 * (1 / W) ^ 2 * (1 + Real.log W + Real.log 2) ^ 3 := by
    have hA : 2 * (Real.log (z : ℝ) + C₀) ≤ 2 * (Real.log W + Real.log 2 + C₀) := by
      linarith only [hlogz_le]
    have hB : (Real.log ((z : ℝ) / W)) ^ 2 ≤ (1 / W) ^ 2 :=
      pow_le_pow_left₀ hratio0 hratio_le 2
    have hC : (1 + Real.log (z : ℝ)) ^ 3 ≤ (1 + Real.log W + Real.log 2) ^ 3 :=
      pow_le_pow_left₀ (by linarith only [hlogz0]) (by linarith only [hlogz_le]) 3
    have hBC : 2 * (Real.log ((z : ℝ) / W)) ^ 2 * (1 + Real.log (z : ℝ)) ^ 3
        ≤ 2 * (1 / W) ^ 2 * (1 + Real.log W + Real.log 2) ^ 3 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hB (by norm_num)) hC (by positivity) (by positivity)
    linarith only [hlogz_le, hBC]
  -- Step 2: the purely `log W`-estimate.
  have hstep2 : 2 * (Real.log W + Real.log 2 + C₀)
        + 2 * (1 / W) ^ 2 * (1 + Real.log W + Real.log 2) ^ 3
      ≤ (56 + 2 * Real.log 2 + 2 * C₀) * Real.log W := by
    set u : ℝ := Real.log W with hudef
    have hu1' : 1 ≤ u := hu1
    have hu0' : 0 ≤ u := hu0
    have hbase : 1 + u + Real.log 2 ≤ 3 * u := by linarith only [hlog2le1, hu1]
    have hcube : (1 + u + Real.log 2) ^ 3 ≤ 27 * u ^ 3 := by
      have h := pow_le_pow_left₀ (by linarith only [hlog2pos, hu1] : (0:ℝ) ≤ 1 + u + Real.log 2) hbase 3
      have h3u : (3 * u) ^ 3 = 27 * u ^ 3 := by ring
      linarith only [h]
    have huw : u / W ≤ 1 := by
      rw [div_le_one hWpos]; exact hlogWle
    have huWnn : 0 ≤ u / W := by positivity
    have hsq : (u / W) ^ 2 ≤ 1 := pow_le_one₀ huWnn huw
    have hkey : (1 / W) ^ 2 * (1 + u + Real.log 2) ^ 3 ≤ 27 * u := by
      have h1 : (1 / W) ^ 2 * (1 + u + Real.log 2) ^ 3 ≤ (1 / W) ^ 2 * (27 * u ^ 3) :=
        mul_le_mul_of_nonneg_left hcube (by positivity)
      have h2 : (1 / W) ^ 2 * (27 * u ^ 3) = 27 * (u * (u / W) ^ 2) := by
        field_simp
      have h3 : u * (u / W) ^ 2 ≤ u * 1 := mul_le_mul_of_nonneg_left hsq hu0'
      linarith only [h1, h2, h3]
    have hsmall : 2 * (1 / W) ^ 2 * (1 + u + Real.log 2) ^ 3 ≤ 54 * u := by
      rw [mul_assoc]
      calc 2 * ((1 / W) ^ 2 * (1 + u + Real.log 2) ^ 3) ≤ 2 * (27 * u) :=
            mul_le_mul_of_nonneg_left hkey (by norm_num)
        _ = 54 * u := by ring
    have hbig : 2 * (u + Real.log 2 + C₀) ≤ (2 + 2 * Real.log 2 + 2 * C₀) * u := by
      have h1 : Real.log 2 + C₀ ≤ (Real.log 2 + C₀) * u := by nlinarith only [hC₀, hu1, hlog2pos]
      linarith only [h1]
    have hfin : 2 * (u + Real.log 2 + C₀) + 2 * (1 / W) ^ 2 * (1 + u + Real.log 2) ^ 3
        ≤ (2 + 2 * Real.log 2 + 2 * C₀) * u + 54 * u := by linarith only [hkey, hbig]
    have hconst : (2 + 2 * Real.log 2 + 2 * C₀) * u + 54 * u
        = (56 + 2 * Real.log 2 + 2 * C₀) * u := by ring
    linarith only [hfin, hconst.le, hconst.ge, hkey, hbig]
  have hgoal : 2 * (Real.log (z : ℝ) + C₀)
        + 2 * (Real.log ((z : ℝ) / W)) ^ 2 * (1 + Real.log (z : ℝ)) ^ 3
      ≤ (56 + 2 * Real.log 2 + 2 * C₀) * Real.log W := le_trans hstep1 hstep2
  rw [hzdef] at hgoal
  exact hgoal

end Work.ZeroDensity.LogFree
