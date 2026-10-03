import Mathlib

namespace Work.KMTAreas.A4

/-- For any `a > 1`, the sequence `(n+1)/a^n` is bounded above: the exponential
`a ^ n` dominates the linear growth `n + 1`. -/
lemma existsMulPowGeNatAddOne {a : ℝ} (ha : 1 < a) :
    ∃ M : ℝ, 0 < M ∧ ∀ n : ℕ, (n : ℝ) + 1 ≤ M * a ^ n := by
  -- Choose `k` with `a ^ k ≥ 2`.
  obtain ⟨k, hk2⟩ : ∃ k : ℕ, 2 ≤ a ^ k := by
    have h := (tendsto_pow_atTop_atTop_of_one_lt ha).eventually
      (Filter.eventually_ge_atTop (2 : ℝ))
    exact h.exists
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hk2; simp at hk2
    · exact h
  -- The constant `M = 2k` works: writing `n = kq + r` with `r < k`, we have
  -- `n + 1 ≤ k(q+1) ≤ k · 2^{q+1} = 2k · 2^q ≤ 2k · a^n`.
  refine ⟨2 * (k : ℝ), by positivity, ?_⟩
  intro m
  obtain ⟨q, r, hr, hm⟩ : ∃ q r : ℕ, r < k ∧ m = k * q + r :=
    ⟨m / k, m % k, Nat.mod_lt m hkpos, (Nat.div_add_mod m k).symm⟩
  rw [hm]
  push_cast
  have ha1 : 1 ≤ a := le_of_lt ha
  have hkr : (r : ℝ) + 1 ≤ (k : ℝ) := by
    have h : r + 1 ≤ k := by omega
    exact_mod_cast h
  have hq : ((q : ℝ) + 1) ≤ 2 ^ (q + 1) := by
    have h : q + 1 ≤ 2 ^ (q + 1) := le_of_lt Nat.lt_two_pow_self
    exact_mod_cast h
  have hpow : 2 ^ q ≤ a ^ (k * q + r) := by
    rw [pow_add, pow_mul]
    calc 2 ^ q ≤ (a ^ k) ^ q * 1 := by
            rw [mul_one]
            exact pow_le_pow_left₀ (by norm_num) hk2 q
      _ ≤ (a ^ k) ^ q * a ^ r :=
            mul_le_mul_of_nonneg_left (one_le_pow₀ ha1)
              (pow_nonneg (pow_nonneg (le_trans (by norm_num) ha1) k) q)
  have hstep1 : (k : ℝ) * (q : ℝ) + (r : ℝ) + 1 ≤ (k : ℝ) * ((q : ℝ) + 1) := by
    nlinarith
  have hstep2 : (k : ℝ) * ((q : ℝ) + 1) ≤ (k : ℝ) * 2 ^ (q + 1) :=
    mul_le_mul_of_nonneg_left hq (by positivity)
  have hstep3 : (k : ℝ) * 2 ^ (q + 1) ≤ 2 * (k : ℝ) * a ^ (k * q + r) := by
    have he : (k : ℝ) * 2 ^ (q + 1) = 2 * (k : ℝ) * 2 ^ q := by
      rw [pow_succ]; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  linarith [hstep1, hstep2, hstep3]

end Work.KMTAreas.A4
