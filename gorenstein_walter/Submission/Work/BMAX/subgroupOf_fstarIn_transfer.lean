import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.Basic

namespace Work.BMAX

open Subgroup

/-- `F*(A) = F(A)·E(A)`, and both factors are normal in `F*(A)` (indeed in `A`): the two
subgroups of `↥F*(A)` obtained by transferring `F(A) = fittingIn A` and `E(A) = layerIn A`
are normal and generate the whole of `↥F*(A)`. This is the `subgroupOf`-form of the
definition `F*(A) = F(A)·E(A)` used when one wants to run an argument inside `F*(A)`. -/
theorem subgroupOf_fstarIn_transfer {G : Type} [Group G] (A : Subgroup G) :
    ((Work.GW2.fittingIn A).subgroupOf (Work.GW2.fstarIn A)).Normal ∧
      ((Work.GW2.layerIn A).subgroupOf (Work.GW2.fstarIn A)).Normal ∧
      ((Work.GW2.fittingIn A).subgroupOf (Work.GW2.fstarIn A) ⊔
        (Work.GW2.layerIn A).subgroupOf (Work.GW2.fstarIn A) = ⊤) := by
  -- A normal subgroup `L` of `↥A`, viewed in `G` through `A.subtype`, is normalised by `A`.
  have hmap_norm : ∀ {L : Subgroup ↥A}, L.Normal →
      A ≤ Subgroup.normalizer (((L.map A.subtype : Subgroup G)) : Set G) := by
    intro L hL
    rw [Subgroup.le_normalizer_iff]
    intro a ha x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨(⟨a, ha⟩ : ↥A) * y * (⟨a, ha⟩ : ↥A)⁻¹, hL.conj_mem y hy ⟨a, ha⟩, rfl⟩
  -- `F(A)` and `E(A)` are normal in `↥A`.
  have hfit_norm : (Work.GW2.fitting A).Normal := by
    rw [Work.GW2.fitting]; exact Subgroup.normalCore_normal _
  have hlayer_norm : (Work.GW2.layer A).Normal :=
    Subgroup.sSup_normal _ (fun _ hH => hH.1)
  refine ⟨?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Work.GW2.fittingIn_le_fstarIn A)]
    exact le_trans (Work.GW2.fstarIn_le_self A) (by
      rw [Work.GW2.fittingIn]; exact hmap_norm hfit_norm)
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Work.GW2.layerIn_le_fstarIn A)]
    exact le_trans (Work.GW2.fstarIn_le_self A) (by
      rw [Work.GW2.layerIn]; exact hmap_norm hlayer_norm)
  · -- `F*(A) = F(A) ⊔ E(A)`, so the two transfers generate everything.
    apply Subgroup.map_injective (Subgroup.subtype_injective (Work.GW2.fstarIn A))
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (Work.GW2.fittingIn_le_fstarIn A),
      inf_eq_left.mpr (Work.GW2.layerIn_le_fstarIn A), Subgroup.map_top,
      Subgroup.range_subtype, ← Work.GW2.fstarIn_eq_sup]

end Work.BMAX
