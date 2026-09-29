import Mathlib

namespace Work.Resample

/-- For `n ≥ 8`, the linear function `n + 1` is bounded by `(4/3)^n`. -/
lemma natCast_add_one_le_pow_four_thirds (n : ℕ) (hn : 8 ≤ n) :
    (n : ℝ) + 1 ≤ (4 / 3 : ℝ) ^ n := by
  induction n with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 8 with hk | hk
    · have hk7 : k = 7 := by omega
      subst hk7
      norm_num
    · have ihk := ih hk
      have h1 : (k : ℝ) + 2 ≤ (4 / 3 : ℝ) * ((k : ℝ) + 1) := by
        have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 2 ≤ k)
        linarith
      have h2 : (4 / 3 : ℝ) * ((k : ℝ) + 1) ≤ (4 / 3 : ℝ) * (4 / 3 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_left ihk (by norm_num)
      calc ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
        _ ≤ (4 / 3 : ℝ) * ((k : ℝ) + 1) := h1
        _ ≤ (4 / 3 : ℝ) * (4 / 3 : ℝ) ^ k := h2
        _ = (4 / 3 : ℝ) ^ (k + 1) := by rw [pow_succ]; ring

theorem expMulSuccLeFourPow (p : ℕ) (hp : 100 ≤ p) :
    Real.exp (p : ℝ) * ((p : ℝ) + 1) ≤ (2 : ℝ) ^ (2 * p) := by
  have hexp : Real.exp (p : ℝ) ≤ (3 : ℝ) ^ p := by
    rw [show Real.exp (p : ℝ) = Real.exp 1 ^ p from by
      have := Real.exp_nat_mul (1 : ℝ) p
      rwa [mul_one] at this]
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_three) p
  have hlin : (p : ℝ) + 1 ≤ (4 / 3 : ℝ) ^ p :=
    natCast_add_one_le_pow_four_thirds p (by omega)
  calc Real.exp (p : ℝ) * ((p : ℝ) + 1)
      ≤ (3 : ℝ) ^ p * (4 / 3 : ℝ) ^ p :=
        mul_le_mul hexp hlin (by positivity) (by positivity)
    _ = ((3 : ℝ) * (4 / 3)) ^ p := by rw [mul_pow]
    _ = (4 : ℝ) ^ p := by norm_num
    _ = (2 : ℝ) ^ (2 * p) := by rw [pow_mul]; norm_num

end Work.Resample
