import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.NPC.Frobenius

/-- A proper subgroup of a finite `p`-group is properly contained in its normalizer
(within the `p`-group). This is the normalizer condition for `p`-groups, which holds because
finite `p`-groups are nilpotent. -/
theorem lt_normalizer_of_lt_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P A : Subgroup G} (hP : IsPGroup p P) (hA : A < P) :
    A < Subgroup.normalizer (A : Set G) ⊓ P := by
  have hAP : A ≤ P := hA.le
  -- `P` is a finite `p`-group, hence nilpotent, hence satisfies the normalizer condition.
  have hnc : NormalizerCondition P :=
    @Group.normalizerCondition_of_isNilpotent P _ hP.isNilpotent
  -- The copy of `A` inside `P` is a proper subgroup of `P`.
  have htop : A.subgroupOf P < ⊤ :=
    lt_top_iff_ne_top.mpr fun h => hA.2 (Subgroup.subgroupOf_eq_top.mp h)
  -- Normalizer condition inside `P`: the copy of `A` is properly contained in its normalizer.
  have hstep : A.subgroupOf P < (Subgroup.normalizer (A : Set G)).subgroupOf P := by
    have h := hnc (A.subgroupOf P) htop
    rwa [← Subgroup.subgroupOf_normalizer_eq hAP] at h
  -- Transport back to `G` along the order embedding `Subgroup.map P.subtype`.
  have hle := Subgroup.map_subtype_le_map_subtype.mpr hstep.1
  have hnotle : ¬ ((Subgroup.normalizer (A : Set G)).subgroupOf P).map P.subtype
      ≤ (A.subgroupOf P).map P.subtype :=
    fun h => hstep.2 (Subgroup.map_subtype_le_map_subtype.mp h)
  rw [Subgroup.map_subgroupOf_eq_of_le hAP, Subgroup.subgroupOf_map_subtype] at hle hnotle
  exact lt_iff_le_not_ge.mpr ⟨hle, hnotle⟩

end Work.NPC.Frobenius
