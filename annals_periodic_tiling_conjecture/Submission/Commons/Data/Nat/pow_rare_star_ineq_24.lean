import Mathlib
import Submission.Commons.Data.Nat.pow_rare_ineq_24

namespace Commons.Data.Nat

/-- The sum of the two lower-order power terms is dominated by `2 ^ (3 * t)`. -/
private lemma sum_le_two_pow {t : ℕ} :
    12 * 2 ^ (3 * t) + 6 * 2 ^ (2 * t) + 1 ≤ 2 ^ (3 * t + 5) := by
  have hlt23 : 2 * t ≤ 3 * t := by omega
  have hpow23 : 2 ^ (2 * t) ≤ 2 ^ (3 * t) :=
    Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) hlt23
  have hone : 1 ≤ 2 ^ (3 * t) := by
    calc
      1 = 2 ^ 0 := by norm_num
      _ ≤ 2 ^ (3 * t) := Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) (by omega)
  have h6 : 6 * 2 ^ (2 * t) ≤ 6 * 2 ^ (3 * t) := Nat.mul_le_mul_left 6 hpow23
  calc
    12 * 2 ^ (3 * t) + 6 * 2 ^ (2 * t) + 1
        ≤ 12 * 2 ^ (3 * t) + 6 * 2 ^ (2 * t) + 2 ^ (3 * t) := by
            omega
    _ ≤ 12 * 2 ^ (3 * t) + 6 * 2 ^ (3 * t) + 2 ^ (3 * t) := by
            omega
    _ = 19 * 2 ^ (3 * t) := by ring
    _ ≤ 32 * 2 ^ (3 * t) := by
            exact Nat.mul_le_mul_right (2 ^ (3 * t)) (by norm_num : 19 ≤ 32)
    _ = 2 ^ (3 * t + 5) := by
            norm_num [pow_add]
            ring

theorem pow_rare_star_ineq_24 : ∀ t : ℕ, 24 ≤ t →
    3 * t * 128 * (12 * 2 ^ (3 * t) + 6 * 2 ^ (2 * t) + 1) < (2 ^ (2 * t) - 7) * (2 ^ (2 * t) - 7) := by
  intro t ht
  have hmain : 3 * t * 128 * 2 ^ (3 * t + 5) <
      (2 ^ (2 * t) - 7) * (2 ^ (2 * t) - 7) := pow_rare_ineq_24 t ht
  have hmul : 3 * t * 128 * (12 * 2 ^ (3 * t) + 6 * 2 ^ (2 * t) + 1) ≤
      3 * t * 128 * 2 ^ (3 * t + 5) := by
    exact Nat.mul_le_mul_left (3 * t * 128) (sum_le_two_pow (t := t))
  exact lt_of_le_of_lt hmul hmain

end Commons.Data.Nat
