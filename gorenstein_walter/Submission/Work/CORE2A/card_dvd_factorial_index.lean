import Mathlib

namespace Work.CORE2A

/-- In a finite simple group `G`, for any proper subgroup `H`, the order of `G` divides the
factorial of the index of `H`. This follows from the permutation representation of `G` on the
cosets `G ⧸ H`: its kernel is `H.normalCore`, which is trivial since `G` is simple and `H ≠ ⊤`. -/
theorem card_dvd_factorial_index {G : Type} [Group G] [Finite G] (hsimple : IsSimpleGroup G)
    (H : Subgroup G) (hH : H ≠ ⊤) : Nat.card G ∣ H.index.factorial := by
  -- The normal core of `H` is a normal subgroup contained in `H ≠ ⊤`, hence trivial.
  have hcore : H.normalCore = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal H.normalCore with h | h
    · exact h
    · exact absurd (le_antisymm le_top (h ▸ Subgroup.normalCore_le H)) hH
  -- `H.normalCore` is the kernel of the action on `G ⧸ H`, and its index divides the factorial.
  have h := H.index_normalCore_dvd_factorial_index
  rw [hcore, Subgroup.index_bot] at h
  exact h

end Work.CORE2A
