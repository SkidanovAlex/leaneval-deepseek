import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Nat.Cast.Field

namespace Commons.NumberTheory.Nat

/-- For `n ≥ 2`, the natural number `n (n + 1) / 2 - 1` equals `(n + 2)(n - 1) / 2`, so that
after dividing by `2 (n - 1)` we obtain `(n + 2) / 4`. -/
theorem cast_half_mul_sub_one_div (n : ℕ) (hn : 2 ≤ n) :
    (((n * (n + 1) / 2 - 1 : ℕ)) : ℝ) / (2 * ((n : ℝ) - 1)) = ((n : ℝ) + 2) / 4 := by
  have h2 : 2 ∣ n * (n + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self n)
  have hge2 : 2 ≤ n * (n + 1) := by
    calc 2 = 2 * 1 := by norm_num
      _ ≤ n * (n + 1) := Nat.mul_le_mul hn (by omega)
  have hge : 1 ≤ n * (n + 1) / 2 :=
    Nat.succ_le_of_lt (Nat.div_pos hge2 (by norm_num))
  have hcast : (((n * (n + 1) / 2 - 1 : ℕ)) : ℝ) = (n : ℝ) * ((n : ℝ) + 1) / 2 - 1 := by
    rw [Nat.cast_sub hge, Nat.cast_div h2 (by norm_num : (2:ℝ) ≠ 0)]
    push_cast
    ring
  rw [hcast]
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  rw [div_eq_iff (by positivity : (2 * ((n:ℝ) - 1)) ≠ 0)]
  ring

end Commons.NumberTheory.Nat