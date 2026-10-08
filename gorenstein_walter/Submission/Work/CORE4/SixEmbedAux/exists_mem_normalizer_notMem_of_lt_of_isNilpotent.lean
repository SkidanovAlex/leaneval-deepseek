import Mathlib

namespace Work.CORE4.SixEmbedAux

/-- **Normalizers grow in a nilpotent group** (the normalizer condition), transported to the
ambient group: if `T ≤ X` are subgroups of a group `G`, `T ≠ X`, and `↥X` is nilpotent, then some
`g ∈ X` normalises `T` (as a subgroup of `G`) but lies outside `T`.  Apply Mathlib's
`Group.normalizerCondition_of_isNilpotent : NormalizerCondition ↥X` to the proper subgroup
`T.subgroupOf X`, then translate `y ∈ normalizer (T.subgroupOf X)` to
`y.1 ∈ Subgroup.normalizer (T : Set G)` (e.g. via
`Subgroup.subgroupOf_normalizer_eq hTX : (normalizer T).subgroupOf X = normalizer (T.subgroupOf X)`). -/
theorem exists_mem_normalizer_notMem_of_lt_of_isNilpotent {G : Type*} [Group G]
    {X T : Subgroup G} (hnil : Group.IsNilpotent ↥X) (hTX : T ≤ X) (hne : T ≠ X) :
    ∃ g ∈ X, g ∈ Subgroup.normalizer (T : Set G) ∧ g ∉ T := by
  -- `T.subgroupOf X` is a proper subgroup of `↥X`
  have hproper : T.subgroupOf X < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    exact hne (le_antisymm hTX (Subgroup.subgroupOf_eq_top.mp h))
  -- the normalizer condition for the nilpotent group `↥X`
  obtain ⟨y, hy, hyT⟩ :=
    IsConcreteLE.exists_of_lt
      ((Group.normalizerCondition_of_isNilpotent (G := ↥X) (h := hnil))
        (T.subgroupOf X) hproper)
  refine ⟨(y : G), y.2, ?_, ?_⟩
  · have : y ∈ (Subgroup.normalizer (T : Set G)).subgroupOf X := by
      rw [Subgroup.subgroupOf_normalizer_eq hTX]
      exact hy
    exact (Subgroup.mem_subgroupOf).mp this
  · intro hg
    exact hyT ((Subgroup.mem_subgroupOf).2 hg)

end Work.CORE4.SixEmbedAux
