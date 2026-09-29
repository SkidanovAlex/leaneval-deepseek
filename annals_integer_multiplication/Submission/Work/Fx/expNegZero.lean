import Mathlib

namespace Work.Fx

/-- For `p ≥ 100` and `j ≥ k·(p+2)` with `k ≥ 1`, the quantity
`2^p · exp(-π j / k)` is strictly less than `2`. -/
theorem expNegZero (p j k : ℕ) (hp : 100 ≤ p) (hk : 1 ≤ k) (hj : k * (p + 2) ≤ j) :
    (2 : ℝ) ^ p * Real.exp (-(Real.pi * j / k)) < 2 := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hcast : (k : ℝ) * ((p : ℝ) + 2) ≤ (j : ℝ) := by exact_mod_cast hj
  have hge : (p : ℝ) + 2 ≤ (j : ℝ) / k := by
    rw [le_div_iff₀ hk0]
    nlinarith [hcast]
  have harg : -(Real.pi * (j : ℝ) / k) ≤ -(Real.pi * ((p : ℝ) + 2)) := by
    have hpi : Real.pi * ((p : ℝ) + 2) ≤ Real.pi * ((j : ℝ) / k) :=
      mul_le_mul_of_nonneg_left hge Real.pi_pos.le
    have heq : Real.pi * (j : ℝ) / k = Real.pi * ((j : ℝ) / k) := by ring
    rw [heq]; linarith
  have hexp : Real.exp (-(Real.pi * (j : ℝ) / k)) ≤ Real.exp (-(Real.pi * ((p : ℝ) + 2))) :=
    Real.exp_le_exp.mpr harg
  have h2exp : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
  have h2p : (2 : ℝ) ^ p ≤ Real.exp (2 * (p : ℝ)) := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) h2exp p
    calc (2 : ℝ) ^ p ≤ (Real.exp 2) ^ p := h
      _ = Real.exp (2 * (p : ℝ)) := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
  have hbd : 2 * (p : ℝ) + -(Real.pi * ((p : ℝ) + 2)) ≤ -4 := by
    nlinarith [Real.pi_gt_three, (Nat.cast_nonneg p : (0 : ℝ) ≤ p)]
  calc (2 : ℝ) ^ p * Real.exp (-(Real.pi * (j : ℝ) / k))
      ≤ (2 : ℝ) ^ p * Real.exp (-(Real.pi * ((p : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_left hexp (pow_nonneg (by norm_num) p)
    _ ≤ Real.exp (2 * (p : ℝ)) * Real.exp (-(Real.pi * ((p : ℝ) + 2))) :=
        mul_le_mul_of_nonneg_right h2p (Real.exp_pos _).le
    _ = Real.exp (2 * (p : ℝ) + -(Real.pi * ((p : ℝ) + 2))) := by rw [Real.exp_add]
    _ ≤ Real.exp (-4) := Real.exp_le_exp.mpr hbd
    _ < 2 := by
        have h4 : Real.exp (-4) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
        linarith

end Work.Fx
