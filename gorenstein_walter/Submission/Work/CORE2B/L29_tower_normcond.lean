import Mathlib

namespace Work.CORE2B

/-- **The normalizer condition for a nilpotent subgroup** (the tower step of `L29_tower`).

If `A ≤ G` is nilpotent and `K ≤ A` is a proper subgroup of `A`, then `K` is strictly
contained in `N_A(K) = A ⊓ N_G(K)`.  Indeed the nilpotent group `↥A` satisfies the normalizer
condition (`Group.normalizerCondition_of_isNilpotent`), applied to the proper subgroup
`K.subgroupOf A < ⊤`; its normalizer in `↥A` is `(N_G(K)).subgroupOf A`
(`Subgroup.subgroupOf_normalizer_eq`), so it contains an element `x` with `(x : G) ∈ A ⊓ N_G(K)`
but `(x : G) ∉ K`. -/
theorem L29_tower_normcond {G : Type*} [Group G] (A K : Subgroup G)
    (hnil : Group.IsNilpotent ↥A) (hK : K ≤ A) (hne : K ≠ A) :
    K < A ⊓ Subgroup.normalizer (K : Set G) := by
  -- the normalizer condition in the nilpotent group `↥A`
  have hnc : NormalizerCondition ↥A :=
    @Group.normalizerCondition_of_isNilpotent ↥A inferInstance hnil
  -- `K.subgroupOf A` is a proper subgroup of `↥A`.
  have hKtop : K.subgroupOf A < ⊤ := by
    refine lt_of_le_of_ne le_top fun h => hne ?_
    exact le_antisymm hK (Subgroup.subgroupOf_eq_top.mp h)
  have hlt : K.subgroupOf A < Subgroup.normalizer (K.subgroupOf A) := hnc _ hKtop
  obtain ⟨x, hxnorm, hxK⟩ := IsConcreteLE.exists_of_lt hlt
  -- transport the normalizer back to `G`
  rw [← Subgroup.subgroupOf_normalizer_eq hK] at hxnorm
  have hxG : (x : G) ∈ A ⊓ Subgroup.normalizer (K : Set G) :=
    ⟨x.2, Subgroup.mem_subgroupOf.mp hxnorm⟩
  have hxnotK : (x : G) ∉ K := fun h => hxK (Subgroup.mem_subgroupOf.mpr h)
  refine lt_of_le_of_ne (le_inf hK Subgroup.le_normalizer) fun heq =>
    hxnotK (by rw [heq]; exact hxG)

end Work.CORE2B
