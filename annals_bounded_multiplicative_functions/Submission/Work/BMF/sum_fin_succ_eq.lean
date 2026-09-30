import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- The sum of `1, 2, ..., k` written as a sum over `Fin k` equals `k * (k + 1) / 2`. -/
theorem sum_fin_succ_eq (k : ℕ) : (∑ j : Fin k, ((j : ℕ) + 1)) = k * (k + 1) / 2 := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    rw [show (n + 1) * (n + 2) = n * (n + 1) + 2 * (n + 1) by ring]
    rw [Nat.add_div_of_dvd_left (dvd_mul_right 2 (n + 1))]
    rw [Nat.mul_comm 2 (n + 1), Nat.mul_div_left (n + 1) (by norm_num)]

end Work.BMF
