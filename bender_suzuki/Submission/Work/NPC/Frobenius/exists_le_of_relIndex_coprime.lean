import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Frobenius

/-- Given a `p`-subgroup `T` of a finite group `G` that lies inside a subgroup `H`, there is a
`p`-subgroup `Q` with `T ≤ Q ≤ H` whose relative index `Q.relIndex H` is not divisible by `p`:
take a Sylow `p`-subgroup of `H` containing `T` and view it inside `G`. -/
theorem exists_le_of_relIndex_coprime {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H T : Subgroup G} (hT : T ≤ H) (hpT : IsPGroup p T) :
    ∃ Q : Subgroup G, T ≤ Q ∧ Q ≤ H ∧ IsPGroup p Q ∧ ¬ p ∣ Q.relIndex H := by
  -- Transport `T` into the group `H` and extend it to a Sylow `p`-subgroup of `H`.
  have hpT' : IsPGroup p (T.subgroupOf H) := hpT.comap_subtype
  obtain ⟨S, hS⟩ := hpT'.exists_le_sylow
  refine ⟨S.map H.subtype, ?_, Subgroup.map_subtype_le (H := H) (S : Subgroup H),
    S.isPGroup'.map H.subtype, ?_⟩
  · intro t ht
    exact Subgroup.mem_map.mpr ⟨⟨t, hT ht⟩, hS (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  · -- The relative index of `S.map H.subtype` in `H` is the index of `S` in `H`, which is not
    -- divisible by `p` as `S` is Sylow.
    have hidx : (S.map H.subtype).relIndex H = (S : Subgroup H).index := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [hidx]
    exact S.not_dvd_index

end Work.NPC.Frobenius
