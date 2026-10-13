import Mathlib

namespace Work.DSM4p

/-- Pure natural-number estimate behind the first case of the monomial estimate
`Work.DSM4p.chartMono_estimate`: for `J ≤ L`, `p^J ≤ I · p^k` and `p^(k+1) · m ≤ c` one has
`p · m · p^L ≤ p^(L-k) + c · I · p^(L-J)`. -/
theorem caseA_bound {p m k c I J L : ℕ} (hJL : J ≤ L)
    (hA : p ^ J ≤ I * p ^ k) (hc : p ^ (k + 1) * m ≤ c) :
    p * m * p ^ L ≤ p ^ (L - k) + c * I * p ^ (L - J) := by
  rcases Nat.eq_zero_or_pos p with hp | hp
  · rw [hp]; simp
  -- p ≥ 1, so `p ^ k > 0` and we may cancel the common factor `p ^ k`.
  have hpk : 0 < p ^ k := pow_pos hp k
  have hJLadd : J + (L - J) = L := Nat.add_sub_of_le hJL
  -- `p^L ≤ I · p^(L-J) · p^k`, via `p^J ≤ I · p^k`.
  have h2 : p ^ L ≤ I * p ^ (L - J) * p ^ k := by
    have this : p ^ J * p ^ (L - J) ≤ (I * p ^ k) * p ^ (L - J) :=
      Nat.mul_le_mul_right _ hA
    calc p ^ L = p ^ J * p ^ (L - J) := by rw [← Nat.pow_add, hJLadd]
      _ ≤ (I * p ^ k) * p ^ (L - J) := this
      _ = I * p ^ (L - J) * p ^ k := by ring
  have h3 : c * p ^ L ≤ c * I * p ^ (L - J) * p ^ k := by
    calc c * p ^ L ≤ c * (I * p ^ (L - J) * p ^ k) := Nat.mul_le_mul_left c h2
      _ = c * I * p ^ (L - J) * p ^ k := by ring
  -- the first summand `p^(L-k)` only helps.
  have h4 : c * I * p ^ (L - J) * p ^ k ≤ (p ^ (L - k) + c * I * p ^ (L - J)) * p ^ k := by
    apply Nat.mul_le_mul_right
    exact Nat.le_add_left _ _
  -- `(p · m · p^L) · p^k = (p^(k+1) · m) · p^L ≤ c · p^L`.
  have h5 : p * m * p ^ L * p ^ k ≤ c * p ^ L := by
    have this : (p ^ (k + 1) * m) * p ^ L ≤ c * p ^ L := Nat.mul_le_mul_right _ hc
    calc p * m * p ^ L * p ^ k = (p ^ (k + 1) * m) * p ^ L := by ring
      _ ≤ c * p ^ L := this
  have hall : p * m * p ^ L * p ^ k ≤ (p ^ (L - k) + c * I * p ^ (L - J)) * p ^ k :=
    le_trans h5 (le_trans h3 h4)
  exact Nat.le_of_mul_le_mul_right hall hpk

end Work.DSM4p
