import Mathlib

namespace Work.ZJB2.Step1

/-- **The normalizer condition for `p`-groups.**  A proper subgroup `H` of a finite `p`-group `P`
is properly contained in its normalizer inside `P`, i.e. `N_P(H) = N_G(H) ⊓ P` strictly contains
`H`.

Proof: `P` is nilpotent (`IsPGroup.isNilpotent`), hence satisfies the normalizer condition
(`Group.normalizerCondition_of_isNilpotent`): every proper subgroup is a proper subgroup of its
own normalizer.  Apply this to `H.subgroupOf P`, the image of `H` in the abstract group `P`, and
compare with the ambient normalizer using `Subgroup.subgroupOf_normalizer_eq`. -/
theorem ltNormalizerInfOfLt {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P H : Subgroup G} (hP : IsPGroup p P) (hH : H < P) :
    H < Subgroup.normalizer (H : Set G) ⊓ P := by
  have hle : H ≤ P := hH.le
  -- `P` is nilpotent, so it satisfies the normalizer condition.
  have hnc : NormalizerCondition P :=
    Group.normalizerCondition_of_isNilpotent (G := P) (h := IsPGroup.isNilpotent hP)
  -- `H` is a proper subgroup of the abstract group `P`.
  have hlt : H.subgroupOf P < (⊤ : Subgroup P) := by
    rw [lt_iff_le_and_ne]
    refine ⟨le_top, fun htop => ?_⟩
    exact ne_of_lt hH (le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop))
  -- The normalizer condition applied inside `P`.
  have hlt2 : H.subgroupOf P < Subgroup.normalizer ((H.subgroupOf P : Subgroup P) : Set P) :=
    hnc (H.subgroupOf P) hlt
  -- Translate back to the ambient group.
  rw [← Subgroup.subgroupOf_normalizer_eq hle] at hlt2
  obtain ⟨x, hxmem, hxnot⟩ := Set.exists_of_ssubset hlt2
  have hxN : (x : G) ∈ Subgroup.normalizer (H : Set G) := Subgroup.mem_subgroupOf.mp hxmem
  have hxP : (x : G) ∈ P := x.2
  refine lt_of_le_of_ne (le_inf Subgroup.le_normalizer hle) ?_
  intro heq
  exact hxnot (Subgroup.mem_subgroupOf.mpr
    (heq.symm ▸ (show (x : G) ∈ Subgroup.normalizer (H : Set G) ⊓ P from ⟨hxN, hxP⟩)))

end Work.ZJB2.Step1
