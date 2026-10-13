import Mathlib

namespace Work.WilG4c

theorem subdiv_rescale_bound {n r m N : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hN : (2 * Real.exp 1 * (1 + n * Real.exp 1) * ((n : ℝ) + 1) + 1) * (r : ℝ) ≤ (N : ℝ)) :
    (2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) * ((n : ℝ) + 1) ^ m) * ((N : ℝ)⁻¹) ^ m
      ≤ 1 := by
  have he1 : (1:ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have he0 : (0:ℝ) ≤ Real.exp 1 := le_trans zero_le_one he1
  have hr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hr0 : (0:ℝ) ≤ (r:ℝ) := le_trans zero_le_one hr1
  have hn0 : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
  have hne1 : (1:ℝ) ≤ 1 + (n:ℝ) * Real.exp 1 := by
    have := mul_nonneg hn0 he0; linarith
  have hnp1 : (1:ℝ) ≤ (n:ℝ) + 1 := by linarith
  have hA0 : (0:ℝ) ≤ (r:ℝ) * (1 + n * Real.exp 1) * ((n:ℝ)+1) := by positivity
  have hA1 : (1:ℝ) ≤ (r:ℝ) * (1 + n * Real.exp 1) * ((n:ℝ)+1) := by
    have h1 : (1:ℝ) ≤ (r:ℝ) * (1 + n * Real.exp 1) := by
      have := mul_le_mul hr1 hne1 (by norm_num) hr0
      simpa using this
    have := mul_le_mul h1 hnp1 (by norm_num) (le_trans zero_le_one h1)
    simpa using this
  have h2eA : 2 * Real.exp 1 * ((r:ℝ) * (1 + n * Real.exp 1) * ((n:ℝ)+1)) ≤ (N:ℝ) := by
    have h1 : 2 * Real.exp 1 * ((r:ℝ) * (1 + n * Real.exp 1) * ((n:ℝ)+1))
        = (2 * Real.exp 1 * (1 + n * Real.exp 1) * ((n:ℝ)+1)) * (r:ℝ) := by ring
    rw [h1]
    have h2 : (2 * Real.exp 1 * (1 + n * Real.exp 1) * ((n:ℝ)+1)) * (r:ℝ)
        ≤ (2 * Real.exp 1 * (1 + n * Real.exp 1) * ((n:ℝ)+1) + 1) * (r:ℝ) := by
      apply mul_le_mul_of_nonneg_right _ hr0
      linarith
    linarith [h2, hN]
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have h2e : (2:ℝ) * Real.exp 1 ≤ (N:ℝ) := by
      have := mul_le_mul_of_nonneg_left hA1 (by positivity : (0:ℝ) ≤ 2 * Real.exp 1)
      linarith [h2eA, this]
    nlinarith [Real.exp_pos 1]
  have hp1 : 2 * Real.exp 1 * ((r:ℝ) * (1 + n * Real.exp 1) * ((n:ℝ)+1))^m
      ≤ (2 * Real.exp 1 * ((r:ℝ) * (1 + n * Real.exp 1) * ((n:ℝ)+1)))^m := by
    conv_rhs => rw [mul_pow]
    have hb : 2 * Real.exp 1 ≤ (2 * Real.exp 1)^m := by
      have h1 : (1:ℝ) ≤ 2 * Real.exp 1 := by linarith
      have := pow_le_pow_right₀ h1 hm
      simpa using this
    exact mul_le_mul_of_nonneg_right hb (pow_nonneg hA0 m)
  have hp2 : (2 * Real.exp 1 * ((r:ℝ) * (1 + n * Real.exp 1) * ((n:ℝ)+1)))^m ≤ (N:ℝ)^m :=
    pow_le_pow_left₀ (by positivity) h2eA m
  have hmain := le_trans hp1 hp2
  have hfin : 2 * Real.exp 1 * ((r:ℝ) * (1 + n * Real.exp 1) * ((n:ℝ)+1))^m * ((N:ℝ)⁻¹)^m ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hmain (pow_nonneg (inv_nonneg.mpr (le_of_lt hNpos)) m)
    have hone : (N:ℝ)^m * ((N:ℝ)⁻¹)^m = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hNpos), one_pow]
    linarith [h, hone]
  have hL : (2 * (Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) * ((n : ℝ) + 1) ^ m) * ((N : ℝ)⁻¹) ^ m
      = 2 * Real.exp 1 * ((r:ℝ) * (1 + n * Real.exp 1) * ((n:ℝ)+1))^m * ((N:ℝ)⁻¹)^m := by
    conv_rhs => rw [mul_pow]
    ring
  rw [hL]; exact hfin

end Work.WilG4c
