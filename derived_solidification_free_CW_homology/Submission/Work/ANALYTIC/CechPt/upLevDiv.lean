import Mathlib

namespace Work.ANALYTIC.CechPt

/-- Auxiliary core (with the exponent gap `k = m - n` already subtracted):
the hypotheses `h1, h2` say `M ∈ {a, a+1}`, and for such `M` the "divided by two"
level relation holds.  Indeed `a + (2^(k+1)-1)·M = 2·(a + (2^k-1)·M) + (M - a)`
with `M - a ≤ 1`, and `(2·r + δ)/2 = r` for `δ ≤ 1`. -/
private theorem upLevDiv_key (a M k : ℕ) (h1 : a ≤ M) (h2 : M ≤ a + 1) :
    (a + (2 ^ (k + 1) - 1) * M) / 2 = a + (2 ^ k - 1) * M := by
  have hδ : M - a ≤ 1 := by omega
  have hp : 2 ^ (k + 1) - 1 = 2 * (2 ^ k - 1) + 1 := by
    have h : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num)
    rw [pow_succ]; omega
  have hmain : a + (2 ^ (k + 1) - 1) * M = 2 * (a + (2 ^ k - 1) * M) + (M - a) := by
    rw [hp]
    ring_nf
    omega
  rw [hmain, Nat.mul_add_div (show 0 < 2 by norm_num) (a + (2 ^ k - 1) * M) (M - a)]
  have : (M - a) / 2 = 0 := Nat.div_eq_of_lt (by omega)
  omega

theorem upLevDiv (a M n m : ℕ) (h1 : a ≤ M) (h2 : M ≤ a + 1) (hm : n ≤ m) :
    (a + (2 ^ (m + 1 - n) - 1) * M) / 2 = a + (2 ^ (m - n) - 1) * M := by
  have hk : m + 1 - n = (m - n) + 1 := by omega
  rw [hk]
  exact upLevDiv_key a M (m - n) h1 h2

end Work.ANALYTIC.CechPt
