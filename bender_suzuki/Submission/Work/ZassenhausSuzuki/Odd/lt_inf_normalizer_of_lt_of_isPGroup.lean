import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.Odd

theorem lt_inf_normalizer_of_lt_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Q P : Subgroup G} (hQ : IsPGroup p Q) (hP : P ≤ Q) (hlt : P < Q) :
    P < Subgroup.normalizer (P : Set G) ⊓ Q := by
  -- A `p`-group is nilpotent, hence satisfies the normalizer condition.
  have hnil : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hnc : NormalizerCondition ↥Q := Group.normalizerCondition_of_isNilpotent (G := ↥Q) (h := hnil)
  -- `P` is a proper subgroup of `Q`, i.e. `P.subgroupOf Q < ⊤` inside `↥Q`.
  have hquot_lt : P.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact hlt.ne (le_antisymm hlt.le ((Subgroup.subgroupOf_eq_top).mp htop))
  -- Normalizers grow in a nilpotent group.
  have hltq : P.subgroupOf Q < (Subgroup.normalizer (P : Set G)).subgroupOf Q := by
    have h := hnc (P.subgroupOf Q) hquot_lt
    rwa [← Subgroup.subgroupOf_normalizer_eq hP] at h
  refine lt_of_le_of_ne (le_inf Subgroup.le_normalizer hP) ?_
  intro hEq
  apply hltq.ne
  rw [← Subgroup.inf_subgroupOf_right (Subgroup.normalizer (P : Set G)) Q, ← hEq]

end Work.ZassenhausSuzuki.Odd
