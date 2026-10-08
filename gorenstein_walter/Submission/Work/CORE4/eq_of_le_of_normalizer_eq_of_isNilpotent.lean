import Mathlib

namespace Work.CORE4

/-- In a nilpotent group, a subgroup that is "self-normalizing inside" a larger subgroup
coincides with that larger subgroup.

Here `F ≤ F'` and `F' ⊓ N_G(F) = F`, i.e. the normalizer of `F` inside `F'` is exactly `F`.
Since `F'` is nilpotent (as a subgroup of a nilpotent group) it satisfies the normalizer
condition, which forces `F = F'`. -/
theorem eq_of_le_of_normalizer_eq_of_isNilpotent {G : Type} [Group G] [Group.IsNilpotent G]
    {F F' : Subgroup G} (hFF' : F ≤ F')
    (hN : F' ⊓ Subgroup.normalizer (F : Set G) = F) : F = F' := by
  have : Group.IsNilpotent F' := inferInstance
  -- The normalizer of `F.subgroupOf F'` inside `F'` is `F.subgroupOf F'`.
  have hnorm : Subgroup.normalizer (F.subgroupOf F') = F.subgroupOf F' := by
    rw [← Subgroup.subgroupOf_normalizer_eq hFF']
    rw [Subgroup.subgroupOf_inj]
    rw [inf_comm (Subgroup.normalizer (F : Set G)) F', hN, inf_eq_left.mpr hFF']
  -- Nilpotent groups satisfy the normalizer condition: only the full group is self-normalizing.
  have htop : F.subgroupOf F' = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp
      (Group.normalizerCondition_of_isNilpotent (G := F'))) _ hnorm
  have hF'leF : F' ≤ F := Subgroup.subgroupOf_eq_top.mp htop
  exact le_antisymm hFF' hF'leF

end Work.CORE4
