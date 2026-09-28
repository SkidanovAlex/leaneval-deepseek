import Mathlib

namespace Work.ClassCount

theorem sieve_error_le (s w : ℝ) (hs : 3 ≤ s) (hw : 4 ≤ w) :
    w ^ (1 - s) / (s - 1) + w ^ (-s) ≤ 1 / 10 := by
  have hw0 : (0:ℝ) ≤ w := by linarith
  have hw1 : (1:ℝ) ≤ w := by linarith
  -- Monotonicity of `rpow` in the exponent, base `w ≥ 1`.
  have h1 : w ^ (1 - s) ≤ w ^ (-2:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)
  have h2 : w ^ (-s) ≤ w ^ (-3:ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hw1 (by linarith)
  -- `s - 1 ≥ 2`, so dividing by it only decreases the first term.
  have h3 : w ^ (1 - s) / (s - 1) ≤ w ^ (-2:ℝ) / 2 := by
    calc w ^ (1 - s) / (s - 1) ≤ w ^ (1 - s) / 2 :=
          div_le_div_of_nonneg_left (Real.rpow_nonneg hw0 _) (by norm_num) (by linarith)
      _ ≤ w ^ (-2:ℝ) / 2 := div_le_div_of_nonneg_right h1 (by norm_num)
  -- Explicit values of the two negative powers.
  have key2 : w ^ (-2:ℝ) ≤ 1/16 := by
    rw [Real.rpow_neg hw0]
    rw [Real.rpow_ofNat w 2]
    have hw2 : (16:ℝ) ≤ w^2 := by nlinarith
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 16) hw2
    simpa [one_div] using h
  have key3 : w ^ (-3:ℝ) ≤ 1/64 := by
    rw [Real.rpow_neg hw0]
    rw [Real.rpow_ofNat w 3]
    have hw3 : (64:ℝ) ≤ w^3 := by nlinarith [sq_nonneg w, hw]
    have h := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 64) hw3
    simpa [one_div] using h
  have h4 : w ^ (-2:ℝ) / 2 ≤ 1/32 := by
    have := div_le_div_of_nonneg_right key2 (by norm_num : (0:ℝ) ≤ 2)
    linarith [this]
  linarith [h3, h4, h2, key3]

end Work.ClassCount
