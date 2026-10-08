import Mathlib

namespace Work.AUTA7.A7

/-- An even involution on `Fin 7` which is not the identity has cycle type `{2,2}`:
it is a product of exactly two disjoint transpositions (three fixed points).

Proof: `Z ^ 2 = 1` forces every cycle to have length `2` or `1`, i.e. every entry of
`cycleType` is exactly `2` (`Perm.cycleType_of_pow_prime_eq_one`), say `cycleType = replicate k 2`.
The sign of `Z` is the product of the `-(-1)^n` over the cycle type
(`Perm.sign_of_cycleType'`), hence equals `(-1)^k`; being `1` this gives `k` even.
Also `2 * k = cycleType.sum = #support ≤ 7` gives `k ≤ 3`, and `Z ≠ 1` gives `k ≥ 1`.
So `k = 2`. -/
theorem EvenInvolutionCycleType {Z : Equiv.Perm (Fin 7)} (hZ : Z * Z = 1) (hZ1 : Z ≠ 1)
    (hs : Equiv.Perm.sign Z = 1) : Z.cycleType = ({2, 2} : Multiset ℕ) := by
  have hZ2 : Z ^ 2 = 1 := by rw [pow_two]; exact hZ
  -- every cycle has length exactly `2`
  have hct : Z.cycleType = Multiset.replicate Z.cycleType.card 2 :=
    Equiv.Perm.cycleType_of_pow_prime_eq_one hZ2
  -- the sign is `(-1) ^ (card cycleType)`
  have hmap : Multiset.map (fun n => -(-1 : ℤˣ) ^ n) Z.cycleType
      = Multiset.replicate Z.cycleType.card (-1 : ℤˣ) := by
    conv_lhs => rw [hct]
    rw [Multiset.map_replicate]
    congr 1
  have hsign : ((-1 : ℤˣ) ^ Z.cycleType.card) = 1 := by
    have h1 : Equiv.Perm.sign Z = (-1 : ℤˣ) ^ Z.cycleType.card := by
      rw [Equiv.Perm.sign_of_cycleType', hmap, Multiset.prod_replicate]
    rw [← h1, hs]
  have hge : 1 ≤ Z.cycleType.card := by
    have h := Equiv.Perm.card_cycleType_pos.mpr hZ1
    omega
  have hle : Z.cycleType.card ≤ 3 := by
    have hsum : Z.cycleType.sum = 2 * Z.cycleType.card := by
      rw [hct, Multiset.sum_replicate]
      simp [Nat.mul_comm]
    have hsupp : Z.cycleType.sum = Z.support.card := Equiv.Perm.sum_cycleType Z
    have hcard : Z.support.card ≤ 7 := by
      have h := Finset.card_le_univ Z.support
      simpa using h
    omega
  -- parity from the sign: `k` is even, and `1 ≤ k ≤ 3` forces `k = 2`
  have hk2 : Z.cycleType.card = 2 := by
    interval_cases h : Z.cycleType.card
    · exact absurd hsign (by decide)
    · rfl
    · exact absurd hsign (by decide)
  rw [hct, hk2]
  decide

end Work.AUTA7.A7
