import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling

namespace Commons.Nat.Choose

private lemma factorial_exp_lower_bound (k : ℕ) (hk : 1 ≤ k) :
    ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := by
  have hsqrt : (1 : ℝ) ≤ √(2 * Real.pi * (k : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hk1r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    have htwo : (1 : ℝ) ≤ 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    have hmul : (1 : ℝ) * 1 ≤ (2 * Real.pi) * (k : ℝ) := by
      exact mul_le_mul htwo hk1r (by norm_num) (by positivity)
    nlinarith
  have hnonneg : 0 ≤ ((k : ℝ) / Real.exp 1) ^ k := by
    exact pow_nonneg (div_nonneg (by exact_mod_cast (Nat.zero_le k)) (Real.exp_pos _).le) k
  calc
    ((k : ℝ) / Real.exp 1) ^ k
        ≤ √(2 * Real.pi * (k : ℝ)) * ((k : ℝ) / Real.exp 1) ^ k := by
          exact le_mul_of_one_le_left hnonneg hsqrt
    _ ≤ (k.factorial : ℝ) := Stirling.le_factorial_stirling k

theorem choose_le_exp_div (n k : ℕ) (hk : 0 < k) (hkn : k ≤ n) :
    (n.choose k : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
  have hk1 : 1 ≤ k := Nat.succ_le_of_lt hk
  have hfact : ((k : ℝ) / Real.exp 1) ^ k ≤ (k.factorial : ℝ) := factorial_exp_lower_bound k hk1
  refine (Nat.choose_le_pow_div (α := ℝ) k n).trans ?_
  -- remaining goal: (n : ℝ) ^ k / (k.factorial : ℝ) ≤ (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k
  have hk0r : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk1r : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hknr : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
  have hn1r : (1 : ℝ) ≤ (n : ℝ) := le_trans hk1r hknr
  have hn0r : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le zero_lt_one hn1r
  have hke0 : 0 < ((k : ℝ) / Real.exp 1) ^ k :=
    pow_pos (div_pos hk0r (Real.exp_pos _)) k
  have hrec : (1 : ℝ) / (k.factorial : ℝ) ≤ 1 / ((k : ℝ) / Real.exp 1) ^ k :=
    one_div_le_one_div_of_le hke0 hfact
  have hnk0 : 0 ≤ (n : ℝ) ^ k := pow_nonneg hn0r.le k
  calc
    (n : ℝ) ^ k / (k.factorial : ℝ)
        = (n : ℝ) ^ k * (1 / (k.factorial : ℝ)) := by ring
    _ ≤ (n : ℝ) ^ k * (1 / ((k : ℝ) / Real.exp 1) ^ k) := by
          exact mul_le_mul_of_nonneg_left hrec hnk0
    _ = (n : ℝ) ^ k / ((k : ℝ) / Real.exp 1) ^ k := by ring
    _ = (Real.exp 1 * (n : ℝ) / (k : ℝ)) ^ k := by
          rw [div_pow]
          rw [div_pow]
          have hE : Real.exp 1 ≠ 0 := (Real.exp_pos _).ne'
          have hX : (k : ℝ) ≠ 0 := hk0r.ne'
          field_simp [hE, hX]
          rw [mul_pow]
          ring

end Commons.Nat.Choose