import Mathlib

namespace Commons.NumberTheory.Nat

/-- For a prime `l ≥ 5`, the number `2^l - 1` has a prime divisor that is
different from `3, 5, 7` and `13`. -/
theorem exists_prime_dvd_two_pow_sub_one_notMem_small (l : ℕ) (hl : Nat.Prime l) (hl5 : 5 ≤ l) :
    ∃ q, Nat.Prime q ∧ q ∣ 2 ^ l - 1 ∧ q ∉ ({3, 5, 7, 13} : Finset ℕ) := by
  have hne : 2 ^ l - 1 ≠ 1 := by
    have h32 : 32 ≤ 2 ^ l := by
      have h := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hl5
      norm_num at h ⊢
      exact h
    omega
  obtain ⟨q, hqprime, hqdiv⟩ := Nat.exists_prime_and_dvd hne
  refine ⟨q, hqprime, hqdiv, ?_⟩
  intro hqmem
  -- The multiplicative order of `2` in `ZMod n`, for each `n` in `{3, 5, 7, 13}`.
  have ho3 : orderOf (2 : ZMod 3) = 2 := by
    rw [orderOf_eq_iff (by norm_num : 0 < 2)]
    exact ⟨by decide, by intro m hm hm0; interval_cases m; decide⟩
  have ho5 : orderOf (2 : ZMod 5) = 4 := by
    rw [orderOf_eq_iff (by norm_num : 0 < 4)]
    exact ⟨by decide, by intro m hm hm0; interval_cases m <;> decide⟩
  have ho7 : orderOf (2 : ZMod 7) = 3 := by
    rw [orderOf_eq_iff (by norm_num : 0 < 3)]
    exact ⟨by decide, by intro m hm hm0; interval_cases m <;> decide⟩
  have ho13 : orderOf (2 : ZMod 13) = 12 := by
    rw [orderOf_eq_iff (by norm_num : 0 < 12)]
    exact ⟨by decide, by intro m hm hm0; interval_cases m <;> decide⟩
  -- From `q ∣ 2^l - 1` deduce that `2^l = 1` in `ZMod q`.
  have hz : (2 : ZMod q) ^ l = 1 := by
    have hmod : 1 ≡ 2 ^ l [MOD q] := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr hqdiv
    have : ((2 ^ l : ℕ) : ZMod q) = ((1 : ℕ) : ZMod q) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact hmod.symm
    simpa using this
  -- Hence the order of `2` divides the prime `l`.
  have hdvd : orderOf (2 : ZMod q) ∣ l := orderOf_dvd_iff_pow_eq_one.mpr hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hqmem
  rcases hqmem with rfl | rfl | rfl | rfl
  · rw [ho3] at hdvd
    rcases (Nat.dvd_prime hl).mp hdvd with h | h
    · omega
    · omega
  · rw [ho5] at hdvd
    rcases (Nat.dvd_prime hl).mp hdvd with h | h
    · omega
    · omega
  · rw [ho7] at hdvd
    rcases (Nat.dvd_prime hl).mp hdvd with h | h
    · omega
    · omega
  · rw [ho13] at hdvd
    rcases (Nat.dvd_prime hl).mp hdvd with h | h
    · omega
    · rw [← h] at hl; norm_num at hl

end Commons.NumberTheory.Nat
