import Mathlib
import Submission.Work.BMF.VKF.defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.VKF

/-- Bernoulli-type bound: for `k ≥ 1` and `n : ℕ`, `(1 - 1/k)^n ≤ exp(-n/k)`.
This is `1 - x ≤ exp(-x)` raised to the `n`-th power. -/
private lemma one_sub_inv_pow_le_exp (k : ℝ) (hk : 1 ≤ k) (n : ℕ) :
    (1 - 1 / k) ^ n ≤ Real.exp (-(n / k)) := by
  have hk0 : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hbase : 0 ≤ 1 - 1 / k := by
    have h : 1 / k ≤ 1 := by rw [div_le_one hk0]; linarith
    linarith
  have h1 : 1 - 1 / k ≤ Real.exp (-(1 / k)) := Real.one_sub_le_exp_neg (1 / k)
  calc (1 - 1 / k) ^ n ≤ (Real.exp (-(1 / k))) ^ n := pow_le_pow_left₀ hbase h1 n
    _ = Real.exp (-(n / k)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring

/-- `e⁻¹ ≤ 46/125`, from `e > 2.7182818283 > 125/46`. -/
private lemma exp_neg_one_le : Real.exp (-1) ≤ (46 : ℝ) / 125 := by
  have h : (125 : ℝ) / 46 ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have h2 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (125 : ℝ) / 46) h
  rw [Real.exp_neg, inv_eq_one_div]
  calc (1 : ℝ) / Real.exp 1 ≤ 1 / ((125 : ℝ) / 46) := h2
    _ = 46 / 125 := by norm_num

/-- `e^{-4/5} ≤ 1/2`, since `e^{4/5} ≥ 1 + 4/5 + (4/5)²/2 > 2`. -/
private lemma exp_neg_four_fifths_le : Real.exp (-((4 : ℝ) / 5)) ≤ 1 / 2 := by
  have h2 : (2 : ℝ) ≤ Real.exp ((4 : ℝ) / 5) := by
    have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ (4 : ℝ) / 5) 3
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero] at hs
    linarith
  rw [Real.exp_neg, inv_eq_one_div]
  calc (1 : ℝ) / Real.exp ((4 : ℝ) / 5) ≤ 1 / (2 : ℝ) :=
        one_div_le_one_div_of_le (by norm_num) h2
    _ = 1 / 2 := by norm_num

/-- `e^{-6} ≤ (46/125)^6`. -/
private lemma exp_neg_six_le : Real.exp (-(6 : ℝ)) ≤ ((46 : ℝ) / 125) ^ 6 := by
  have h := Real.exp_nat_mul (-1) 6
  norm_num at h
  rw [h]
  exact pow_le_pow_left₀ (Real.exp_pos (-1)).le exp_neg_one_le 6

/-- `e^{-34/5} = e^{-6,8} ≤ (46/125)^6/2`. -/
private lemma exp_neg_34_5_le : Real.exp (-((34 : ℝ) / 5)) ≤ ((46 : ℝ) / 125) ^ 6 * (1 / 2) := by
  have hsplit : Real.exp (-((34 : ℝ) / 5)) = Real.exp (-(6 : ℝ)) * Real.exp (-((4 : ℝ) / 5)) := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  exact mul_le_mul exp_neg_six_le exp_neg_four_fifths_le (by positivity) (by positivity)

/-- `e^{-9} ≤ 1/1000`. -/
private lemma exp_neg_nine_le : Real.exp (-(9 : ℝ)) ≤ 1 / 1000 := by
  have h9 : Real.exp (-(9 : ℝ)) = Real.exp (-1) ^ 9 := by
    have h := Real.exp_nat_mul (-1) 9
    norm_num at h
    exact h
  rw [h9]
  calc Real.exp (-1) ^ 9 ≤ ((46 : ℝ) / 125) ^ 9 :=
        pow_le_pow_left₀ (Real.exp_pos (-1)).le exp_neg_one_le 9
    _ ≤ 1 / 1000 := by norm_num

/-- The two Stechkin excesses of the Ford §5 extraction are small:
`Δ₁ = (k²/2)(1-1/k)^{r'} ≤ λ²/50` and `Δ₂ = (g²/2)(1-1/g)^{s'} ≤ λ²/50` for `λ ≥ 13/5`.
Proof: `1-x ≤ e^{-x}` gives `(1-1/k)^{r'} ≤ e^{-r'/k} ≤ e^{-300λ²/k²}` (using `r'·k ≥ 300λ²`),
and `k ≤ 5λ+2` gives `k/λ ≤ 5+2/(13/5) ≤ 5.77`, so `Δ₁/λ² ≤ (k²/2λ²)e^{-300λ²/k²} ≤ 16.7·e^{-9} ≤ 1/50`;
the second is identical with `s'·g ≥ 200λ²`, `g ≤ 5λ+1`, `g/λ ≤ 5+1/(13/5) ≤ 5.39`. -/
theorem vkf_delta (lam : ℝ) (hlam : 13 / 5 ≤ lam)
    (hk : ((Work.BMF.VKF.dK lam : ℕ) : ℝ) ≤ 5 * lam + 2)
    (hrp : 300 * lam ^ 2 ≤ ((Work.BMF.VKF.dRp lam : ℕ) : ℝ) * ((Work.BMF.VKF.dK lam : ℕ) : ℝ))
    (hg : ((Work.BMF.VKF.dG lam : ℕ) : ℝ) ≤ 5 * lam + 1)
    (hsp : 200 * lam ^ 2 ≤ ((Work.BMF.VKF.dSp lam : ℕ) : ℝ) * ((Work.BMF.VKF.dG lam : ℕ) : ℝ)) :
    (Work.BMF.VKF.dDelta1 lam ≤ lam ^ 2 / 50) ∧ (Work.BMF.VKF.dDelta2 lam ≤ lam ^ 2 / 50) := by
  have hlam0 : (0 : ℝ) < lam := by linarith
  have hK1 : (1 : ℝ) ≤ (dK lam : ℝ) := by
    have := dK_pos lam hlam; exact_mod_cast this
  have hK0 : (0 : ℝ) < (dK lam : ℝ) := lt_of_lt_of_le zero_lt_one hK1
  have hG1 : (1 : ℝ) ≤ (dG lam : ℝ) := by
    have := dG_pos lam hlam; exact_mod_cast this
  have hG0 : (0 : ℝ) < (dG lam : ℝ) := lt_of_lt_of_le zero_lt_one hG1
  constructor
  · -- First Stechkin excess: `Δ₁ ≤ (k²/2)·e^{-300λ²/k²} ≤ (k²/2)·e^{-9}`.
    simp only [dDelta1]
    have hbase := one_sub_inv_pow_le_exp (dK lam : ℝ) hK1 (dRp lam)
    have hle1 : 300 * lam ^ 2 / (dK lam : ℝ) ^ 2 ≤ (dRp lam : ℝ) / (dK lam : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hK0]
      nlinarith [hrp, hK0]
    have hexpr1 : Real.exp (-((dRp lam : ℝ) / (dK lam : ℝ)))
        ≤ Real.exp (-(300 * lam ^ 2 / (dK lam : ℝ) ^ 2)) := Real.exp_le_exp.mpr (by linarith)
    have hk75 : (dK lam : ℝ) ≤ (75 / 13) * lam := by
      have h : 5 * lam + 2 ≤ (75 / 13) * lam := by nlinarith [hlam]
      linarith
    have hk2 : (dK lam : ℝ) ^ 2 ≤ (5625 / 169) * lam ^ 2 := by
      have h := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ (dK lam : ℝ)) hk75
      calc (dK lam : ℝ) ^ 2 = (dK lam : ℝ) * (dK lam : ℝ) := by ring
        _ ≤ ((75 / 13) * lam) * ((75 / 13) * lam) := h
        _ = (5625 / 169) * lam ^ 2 := by ring
    have h9 : Real.exp (-(300 * lam ^ 2 / (dK lam : ℝ) ^ 2)) ≤ 1 / 1000 := by
      have hge : (9 : ℝ) ≤ 300 * lam ^ 2 / (dK lam : ℝ) ^ 2 := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < (dK lam : ℝ) ^ 2)]
        nlinarith [hk2]
      exact le_trans (Real.exp_le_exp.mpr (by linarith)) exp_neg_nine_le
    calc (dK lam : ℝ) ^ 2 / 2 * (1 - 1 / (dK lam : ℝ)) ^ (dRp lam)
        ≤ (dK lam : ℝ) ^ 2 / 2 * Real.exp (-(300 * lam ^ 2 / (dK lam : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (le_trans hbase hexpr1) (by positivity)
      _ ≤ (dK lam : ℝ) ^ 2 / 2 * (1 / 1000) := mul_le_mul_of_nonneg_left h9 (by positivity)
      _ = (dK lam : ℝ) ^ 2 / 2000 := by ring
      _ ≤ ((5625 / 169) * lam ^ 2) / 2000 := div_le_div_of_nonneg_right hk2 (by norm_num)
      _ = (5625 / 338000) * lam ^ 2 := by ring
      _ ≤ lam ^ 2 / 50 := by
          have h : (5625 / 338000 : ℝ) ≤ 1 / 50 := by norm_num
          calc (5625 / 338000 : ℝ) * lam ^ 2 ≤ (1 / 50) * lam ^ 2 :=
                mul_le_mul_of_nonneg_right h (sq_nonneg lam)
            _ = lam ^ 2 / 50 := by ring
  · -- Second Stechkin excess: `Δ₂ ≤ (g²/2)·e^{-200λ²/g²} ≤ (g²/2)·e^{-34/5}`.
    simp only [dDelta2]
    have hbase2 := one_sub_inv_pow_le_exp (dG lam : ℝ) hG1 (dSp lam)
    have hle2 : 200 * lam ^ 2 / (dG lam : ℝ) ^ 2 ≤ (dSp lam : ℝ) / (dG lam : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hG0]
      nlinarith [hsp, hG0]
    have hexpr2 : Real.exp (-((dSp lam : ℝ) / (dG lam : ℝ)))
        ≤ Real.exp (-(200 * lam ^ 2 / (dG lam : ℝ) ^ 2)) := Real.exp_le_exp.mpr (by linarith)
    have hg70 : (dG lam : ℝ) ≤ (70 / 13) * lam := by
      have h : 5 * lam + 1 ≤ (70 / 13) * lam := by nlinarith [hlam]
      linarith
    have hg2 : (dG lam : ℝ) ^ 2 ≤ (4900 / 169) * lam ^ 2 := by
      have h := mul_self_le_mul_self (by positivity : (0:ℝ) ≤ (dG lam : ℝ)) hg70
      calc (dG lam : ℝ) ^ 2 = (dG lam : ℝ) * (dG lam : ℝ) := by ring
        _ ≤ ((70 / 13) * lam) * ((70 / 13) * lam) := h
        _ = (4900 / 169) * lam ^ 2 := by ring
    have h68 : Real.exp (-(200 * lam ^ 2 / (dG lam : ℝ) ^ 2)) ≤ ((46 : ℝ) / 125) ^ 6 * (1 / 2) := by
      have hge : (34 : ℝ) / 5 ≤ 200 * lam ^ 2 / (dG lam : ℝ) ^ 2 := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < (dG lam : ℝ) ^ 2)]
        nlinarith [hg2]
      exact le_trans (Real.exp_le_exp.mpr (by linarith)) exp_neg_34_5_le
    calc (dG lam : ℝ) ^ 2 / 2 * (1 - 1 / (dG lam : ℝ)) ^ (dSp lam)
        ≤ (dG lam : ℝ) ^ 2 / 2 * Real.exp (-(200 * lam ^ 2 / (dG lam : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left (le_trans hbase2 hexpr2) (by positivity)
      _ ≤ (dG lam : ℝ) ^ 2 / 2 * (((46 : ℝ) / 125) ^ 6 * (1 / 2)) :=
          mul_le_mul_of_nonneg_left h68 (by positivity)
      _ = (dG lam : ℝ) ^ 2 * (((46 : ℝ) / 125) ^ 6 / 4) := by ring
      _ ≤ ((4900 / 169) * lam ^ 2) * (((46 : ℝ) / 125) ^ 6 / 4) :=
          mul_le_mul_of_nonneg_right hg2 (by positivity)
      _ = ((1225 : ℝ) / 169) * ((46 : ℝ) / 125) ^ 6 * lam ^ 2 := by ring
      _ ≤ lam ^ 2 / 50 := by
          have h : ((1225 : ℝ) / 169) * ((46 : ℝ) / 125) ^ 6 ≤ 1 / 50 := by norm_num
          calc ((1225 : ℝ) / 169) * ((46 : ℝ) / 125) ^ 6 * lam ^ 2
              ≤ (1 / 50) * lam ^ 2 := mul_le_mul_of_nonneg_right h (sq_nonneg lam)
            _ = lam ^ 2 / 50 := by ring

end Work.BMF.VKF
