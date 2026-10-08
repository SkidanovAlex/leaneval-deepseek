import Mathlib

namespace Work.ZASS2

theorem sylowMapOfNotDvdIndex {G : Type} [Group G] [Finite G] {H : Subgroup G} {r : ℕ}
    [Fact r.Prime] (hr : ¬ r ∣ H.index) (Q : Sylow r ↥H) :
    ∃ Q' : Sylow r G, (Q' : Subgroup G) = Q.map H.subtype := by
  -- The image of `Q` under `H.subtype` is an `r`-subgroup of `G`, and its index
  -- `[G : Q] = [H : Q] * [G : H]` is not divisible by `r` since neither factor is.
  -- Hence it is an `r`-Sylow subgroup of `G`.
  refine ⟨(Q.isPGroup'.map H.subtype).toSylow ?_, rfl⟩
  rw [Subgroup.index_map_subtype]
  exact Nat.Prime.not_dvd_mul Fact.out Q.not_dvd_index hr

end Work.ZASS2
