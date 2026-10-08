import Mathlib

namespace Work.CORE4

theorem PGroupCentralPrime {H : Type} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    (hH : IsPGroup p H) [Nontrivial H] :
    ∃ z : H, z ∈ Subgroup.center H ∧ orderOf z = p := by
  -- p is prime, so we may use the `Fact` instances of Mathlib's p-group API.
  have hpFact : Fact p.Prime := ⟨hp⟩
  -- The center of a nontrivial finite p-group is nontrivial.
  have hnt : Nontrivial (Subgroup.center H) := IsPGroup.center_nontrivial hH
  obtain ⟨x, hx⟩ := @exists_ne (Subgroup.center H) hnt (1 : Subgroup.center H)
  have hz1 : (x : H) ≠ 1 := fun h => hx (Subtype.ext h)
  have hxc : (x : H) ∈ Subgroup.center H := x.2
  -- So there is a nontrivial central element `x`; its order is `p ^ k` with `k > 0`.
  obtain ⟨k, hk⟩ := IsPGroup.exists_orderOf_eq_pow hH (x : H)
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h, pow_zero] at hk
      exact absurd hk (by rw [orderOf_eq_one_iff]; exact hz1)
    · exact h
  -- Then `x ^ (p ^ (k - 1))` is central and has order exactly `p`.
  refine ⟨(x : H) ^ (p ^ (k - 1)), Subgroup.pow_mem (Subgroup.center H) hxc _, ?_⟩
  apply orderOf_eq_prime
  · rw [← pow_mul, ← pow_succ]
    rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hkpos))]
    rw [← hk]
    exact pow_orderOf_eq_one _
  · intro h
    rw [← orderOf_dvd_iff_pow_eq_one] at h
    rw [hk] at h
    have hle : k ≤ k - 1 := (Nat.pow_dvd_pow_iff_le_right (Nat.Prime.one_lt hp)).mp h
    omega

end Work.CORE4
