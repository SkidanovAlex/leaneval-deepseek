import Mathlib

namespace Commons.Data.Nat

/-- For natural numbers `p Q v` with `0 < Q ≤ p` and `v < p`, there is a unique
`u < Q` such that `u*p/Q ≤ v < (u+1)*p/Q`.  Equivalently, the intervals
`[u*p/Q, (u+1)*p/Q)` for `u = 0, …, Q-1` partition `[0, p)`. -/
theorem interval_partition {p Q v : ℕ} (hQ : 0 < Q) (hQp : Q ≤ p) (hv : v < p) :
    ∃! u : ℕ, u < Q ∧ u * p / Q ≤ v ∧ v < (u + 1) * p / Q := by
  have hp : 0 < p := lt_of_lt_of_le hQ hQp
  -- The witness is `M / p` where `M = (v+1)*Q - 1`.
  have hex : ∃ M : ℕ, M = (v + 1) * Q - 1 := ⟨(v + 1) * Q - 1, rfl⟩
  obtain ⟨M, hM⟩ := hex
  have hM1 : M + 1 = (v + 1) * Q := by
    have : 0 < (v + 1) * Q := by positivity
    omega
  have hv1 : v + 1 ≤ p := by omega
  refine ⟨M / p, ⟨?hlt, ?hle, ?hgt⟩, ?huniq⟩
  · -- `M / p < Q`
    rw [Nat.div_lt_iff_lt_mul hp]
    have h2 : (v + 1) * Q ≤ Q * p := by
      calc (v + 1) * Q ≤ p * Q := Nat.mul_le_mul_right Q hv1
        _ = Q * p := by ring
    omega
  · -- `M / p * p / Q ≤ v`
    have hdiv : M / p * p ≤ M := Nat.div_mul_le_self M p
    have h1 : M / p * p < (v + 1) * Q := by omega
    exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul hQ).mpr h1)
  · -- `v < (M / p + 1) * p / Q`
    have hMlt : M < (M / p + 1) * p :=
      (Nat.div_lt_iff_lt_mul hp).mp (Nat.lt_succ_self (M / p))
    have hX : v + 1 ≤ (M / p + 1) * p / Q := by
      rw [Nat.le_div_iff_mul_le hQ]
      omega
    omega
  · -- uniqueness
    intro y hy
    obtain ⟨hyQ, hy1, hy2⟩ := hy
    have ha : y * p < (v + 1) * Q :=
      (Nat.div_lt_iff_lt_mul hQ).mp (lt_of_le_of_lt hy1 (Nat.lt_succ_self v))
    have hb : (v + 1) * Q ≤ (y + 1) * p :=
      (Nat.le_div_iff_mul_le hQ).mp (Nat.succ_le_of_lt hy2)
    have hy_le : y ≤ M / p := by
      rw [Nat.le_div_iff_mul_le hp]
      omega
    have hU_le : M / p ≤ y := by
      have hMs : M / p < y + 1 := by
        rw [Nat.div_lt_iff_lt_mul hp]
        omega
      omega
    omega

end Commons.Data.Nat
