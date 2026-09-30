import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Symmetric residue modulo a power of two: for every integer `a` there are `r, s ∈ ℤ` with
`a = r + 2^(k+1) * s` and `|r| ≤ 2^k`. -/
theorem kummer_residue (k : ℕ) (a : ℤ) :
    ∃ (r s : ℤ), a = r + 2 ^ (k + 1) * s ∧ |r| ≤ 2 ^ k := by
  -- Work with the modulus `N = 2^(k+1) = 2^k + 2^k`.
  set N : ℤ := 2 ^ (k + 1) with hNdef
  have hNpos : 0 < N := by rw [hNdef]; positivity
  have hNne : N ≠ 0 := ne_of_gt hNpos
  have hN : N = 2 ^ k + 2 ^ k := by rw [hNdef, pow_succ]; ring
  -- Euclidean decomposition `a = m + N * q` with `0 ≤ m < N`.
  set m : ℤ := a % N with hmdef
  set q : ℤ := a / N with hqdef
  have ha : a = m + N * q := by
    rw [hmdef, hqdef]; exact (Int.emod_add_mul_ediv a N).symm
  have hm0 : 0 ≤ m := by rw [hmdef]; exact Int.emod_nonneg a hNne
  have hmlt : m < N := by rw [hmdef]; exact Int.emod_lt_of_pos a hNpos
  by_cases hle : m ≤ 2 ^ k
  · -- Already in the symmetric range.
    refine ⟨m, q, ha, ?_⟩
    rw [abs_of_nonneg hm0]; exact hle
  · -- Shift down by the modulus into the symmetric range.
    have hgt : 2 ^ k < m := not_le.mp hle
    refine ⟨m - N, q + 1, ?_, ?_⟩
    · rw [ha]; ring
    · have hneg : m - N < 0 := by omega
      rw [abs_of_neg hneg]
      have h2 : N - m < 2 ^ k := by omega
      omega

end Work.BW
