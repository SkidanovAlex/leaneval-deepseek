import Mathlib
import Submission.Work.TMC14Core.InvSumAux

namespace Work.TMC14Core

theorem pow_inv_eq (ω : ℂ) (m : ℕ) (hω1 : ω ^ (2 * m + 1) = 1) :
    (ω ^ (m * (m + 1) / 2))⁻¹ = ω ^ (m * (3 * m + 1) / 2) := by
  -- `m * (3 * m + 1)` is even
  have hev : Even (m * (3 * m + 1)) := by
    have h : m * (3 * m + 1) = m * (m + 1) + 2 * (m * m) := by ring
    rw [h]
    exact Even.add (Nat.even_mul_succ_self m) ⟨m * m, by ring⟩
  -- the two halves are exact divisions
  have h2a : 2 * (m * (m + 1) / 2) = m * (m + 1) :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_succ_self m))
  have h2b : 2 * (m * (3 * m + 1) / 2) = m * (3 * m + 1) :=
    Nat.mul_div_cancel' (even_iff_two_dvd.mp hev)
  -- the exponents add up (mod-free identity): the two of them sum to `m * (2 * m + 1)`
  have hab : m * (m + 1) / 2 + m * (3 * m + 1) / 2 = m * (2 * m + 1) := by
    apply Nat.mul_left_cancel (show 0 < 2 by norm_num)
    rw [Nat.mul_add, h2a, h2b]
    ring
  -- hence the corresponding powers multiply to `ω ^ (m * (2 * m + 1)) = 1`
  have hpow : ω ^ (m * (m + 1) / 2 + m * (3 * m + 1) / 2) = 1 := by
    rw [hab, Nat.mul_comm m (2 * m + 1), pow_mul, hω1, one_pow]
  have hmul : ω ^ (m * (m + 1) / 2) * ω ^ (m * (3 * m + 1) / 2) = 1 := by
    rw [← pow_add]; exact hpow
  exact inv_eq_of_mul_eq_one_right hmul

end Work.TMC14Core
