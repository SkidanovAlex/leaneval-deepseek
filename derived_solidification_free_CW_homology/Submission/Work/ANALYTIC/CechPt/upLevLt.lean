import Mathlib

namespace Work.ANALYTIC.CechPt

/-- Arithmetic bound used in the levelwise CW comparison: if `a ≤ M < 2^(n+1)` and `n ≤ m`
then `a + (2^(m-n) - 1) * M < 2^(m+1)`. -/
theorem upLevLt (a M n m : ℕ) (h1 : a ≤ M) (h2 : M < 2 ^ (n + 1)) (hm : n ≤ m) :
    a + (2 ^ (m - n) - 1) * M < 2 ^ (m + 1) := by
  have hkpos : 0 < 2 ^ (m - n) := Nat.two_pow_pos _
  have hM : M ≤ 2 ^ (n + 1) - 1 := by omega
  have h2' : M + (2 ^ (m - n) - 1) * M = 2 ^ (m - n) * M := by
    have hk : 1 + (2 ^ (m - n) - 1) = 2 ^ (m - n) := by omega
    calc M + (2 ^ (m - n) - 1) * M = 1 * M + (2 ^ (m - n) - 1) * M := by rw [one_mul]
      _ = (1 + (2 ^ (m - n) - 1)) * M := (Nat.add_mul 1 _ M).symm
      _ = 2 ^ (m - n) * M := by rw [hk]
  have hstep1 : a + (2 ^ (m - n) - 1) * M ≤ 2 ^ (m - n) * M := by
    calc a + (2 ^ (m - n) - 1) * M ≤ M + (2 ^ (m - n) - 1) * M := by omega
      _ = 2 ^ (m - n) * M := h2'
  have hstep2 : 2 ^ (m - n) * M ≤ 2 ^ (m - n) * (2 ^ (n + 1) - 1) :=
    Nat.mul_le_mul_left _ hM
  have hstep3 : 2 ^ (m - n) * (2 ^ (n + 1) - 1) = 2 ^ (m + 1) - 2 ^ (m - n) := by
    rw [Nat.mul_sub_left_distrib, mul_one]
    congr 1
    rw [← Nat.pow_add]
    congr 1
    omega
  have hstep4 : 2 ^ (m + 1) - 2 ^ (m - n) < 2 ^ (m + 1) :=
    Nat.sub_lt (Nat.two_pow_pos _) hkpos
  exact lt_of_le_of_lt (le_trans hstep1 (le_trans hstep2 (le_of_eq hstep3))) hstep4

end Work.ANALYTIC.CechPt
