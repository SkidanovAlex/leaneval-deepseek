import Mathlib
import Submission.Commons.Data.Finset.two_consecutive_of_large

namespace Commons.Data.Nat

open Commons.Data.Finset

/-- If a set `Z` of natural representatives misses at most one element below
`2 ^ (t - 1)` (`t ≥ 4`), and an affine equation `u + S * k = 0` in
`ZMod (2 ^ t)` holds for every `k ∈ Z`, then both `S` and `u` vanish. -/
theorem class_zeros_many {t : ℕ} (ht : 4 ≤ t) (S u : ZMod (2 ^ t))
    (Z : Finset ℕ) (hZsub : Z ⊆ Finset.range (2 ^ (t - 1)))
    (hZcard : (2 ^ (t - 1)) - 1 ≤ Z.card)
    (hZeros : ∀ k ∈ Z, u + S * (k : ZMod (2 ^ t)) = 0) :
    S = 0 ∧ u = 0 := by
  -- `Z` is a large subset of `{0, ..., 2^(t-1) - 1}`, so it contains two
  -- consecutive numbers.
  have hq8 : 8 ≤ 2 ^ (t - 1) := by
    have h3 : 3 ≤ t - 1 := by omega
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (t - 1) := Nat.pow_le_pow_right (by norm_num : 0 < 2) h3
  have hqcard : 2 ^ (t - 1) - 3 ≤ Z.card := by
    exact le_trans (Nat.sub_le_sub_left (by omega : (1 : ℕ) ≤ 3) (2 ^ (t - 1))) hZcard
  rcases two_consecutive_of_large hq8 Z hZsub hqcard with ⟨j, hjlt, hjZ, hj1Z⟩
  -- The equation holds at both `j` and `j + 1`.
  have hzero_j : u + S * (j : ZMod (2 ^ t)) = 0 := hZeros j hjZ
  have hzero_j1 : u + S * ((j + 1 : ℕ) : ZMod (2 ^ t)) = 0 := hZeros (j + 1) hj1Z
  -- Subtracting the two equations kills `u`, and the consecutive casts kill `j`.
  have hS : S = 0 := by
    have hcast : ((j + 1 : ℕ) : ZMod (2 ^ t)) = (j : ZMod (2 ^ t)) + 1 := by
      norm_num
    have hsub0 : S * (((j + 1 : ℕ) : ZMod (2 ^ t)) - (j : ZMod (2 ^ t))) = 0 := by
      calc
        S * (((j + 1 : ℕ) : ZMod (2 ^ t)) - (j : ZMod (2 ^ t)))
            = S * ((j + 1 : ℕ) : ZMod (2 ^ t)) - S * (j : ZMod (2 ^ t)) := by ring
        _ = (u + S * ((j + 1 : ℕ) : ZMod (2 ^ t))) - (u + S * (j : ZMod (2 ^ t))) := by abel
        _ = 0 := by
          rw [hzero_j1, hzero_j]
          simp
    calc
      S = S * 1 := by simp
      _ = S * (((j + 1 : ℕ) : ZMod (2 ^ t)) - (j : ZMod (2 ^ t))) := by
        rw [hcast]
        ring
      _ = 0 := hsub0
  have hu : u = 0 := by
    simpa [hS] using hZeros j hjZ
  exact ⟨hS, hu⟩

end Commons.Data.Nat
