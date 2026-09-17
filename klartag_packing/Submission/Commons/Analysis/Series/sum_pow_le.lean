import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Star.Real

namespace Commons.Analysis.Series

theorem sum_pow_le (M k : ℕ) :
    ∑ j ∈ Finset.Icc 1 M, (j : ℝ) ^ k ≤ ((M : ℝ) + 1) ^ (k + 1) / ((k : ℝ) + 1) := by
  have key : ∀ M : ℕ,
      ((k : ℝ) + 1) * ∑ j ∈ Finset.Icc 1 M, (j : ℝ) ^ k ≤ ((M : ℝ) + 1) ^ (k + 1) - 1 := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_Icc_succ_top (a := 1) (b := M) (by omega) (fun j => (j : ℝ) ^ k)]
      have hb : ((M : ℝ) + 1) ^ (k + 1) + ((k : ℝ) + 1) * ((M : ℝ) + 1) ^ k
          ≤ ((M : ℝ) + 1 + 1) ^ (k + 1) := by
        have h := pow_add_mul_le_add_pow (a := (M : ℝ) + 1) (b := 1)
          (by positivity) (by positivity) (k + 1)
        rw [Nat.add_sub_cancel, mul_one, Nat.cast_add, Nat.cast_one] at h
        exact h
      rw [mul_add]
      push_cast
      linarith [ih, hb]
  have hK : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [le_div_iff₀ hK]
  have h := key M
  nlinarith [h]