import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.GroupTheory

/-- If `Q ≤ H`, `M ≤ H` and `H` normalizes `Q`, then the index of `M ⊓ Q` in `M` divides the
index of `Q` in `H`.

This is the second isomorphism theorem: `M / (M ⊓ Q) ≃ (M ⊔ Q) / Q ≤ H / Q`. -/
theorem index_inf_subgroupOf_dvd_index_subgroupOf {G : Type} [Group G] {Q H M : Subgroup G}
    (hQH : Q ≤ H) (hMH : M ≤ H) (hN : H ≤ Subgroup.normalizer (Q : Set G)) :
    ((M ⊓ Q).subgroupOf M).index ∣ (Q.subgroupOf H).index := by
  -- `Q` is normal in `H`, since `H` normalizes `Q`.
  have hNorm : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hN
  -- The relative index `Q.relIndex M = [M : M ⊓ Q]` divides the index `Q.index` in `H`,
  -- by `relIndex_dvd_index_of_normal` applied to the normal subgroup `Q.subgroupOf H ≤ H`.
  have hmain : (Q.subgroupOf H).relIndex (M.subgroupOf H) ∣ (Q.subgroupOf H).index :=
    @Subgroup.relIndex_dvd_index_of_normal _ _ (Q.subgroupOf H) (M.subgroupOf H) hNorm
  -- Identify the relative index in `H` with the index of `M ⊓ Q` in `M`.
  have hrel : (Q.subgroupOf H).relIndex (M.subgroupOf H) = ((M ⊓ Q).subgroupOf M).index := by
    rw [Subgroup.relIndex_subgroupOf hMH, Subgroup.relIndex]
    congr 1
    rw [inf_comm, Subgroup.inf_subgroupOf_right]
  rw [hrel] at hmain
  exact hmain

end Work.GroupTheory
