import Mathlib
import Submission.Work.ThreePoints.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.P3NeBot

/-- For subgroups `H, F ≤ G` and `t ∈ F`, the two-point stabiliser of `t` inside the subgroup
`H.subgroupOf F ≤ F` maps, under `F.subtype`, to `F ⊓ twoPoint H t` (Peterfalvi I Ch. II §4,
`D = H ∩ H^t`). -/
theorem map_subtype_twoPoint_subgroupOf {G : Type} [Group G] {F H : Subgroup G} (t : F) :
    (Submission.Blueprint.twoPoint (H.subgroupOf F) t).map F.subtype =
      F ⊓ Submission.Blueprint.twoPoint H (t : G) := by
  -- Conjugation inside `↥F` is the trace on `F` of conjugation in `G`.
  have hconj : Submission.Blueprint.conj t (H.subgroupOf F)
      = (Submission.Blueprint.conj (t : G) H).subgroupOf F := by
    ext y
    rw [Work.ThreePoints.mem_conj_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        Work.ThreePoints.mem_conj_iff]
    norm_cast
  show (H.subgroupOf F ⊓ Submission.Blueprint.conj t (H.subgroupOf F)).map F.subtype
      = F ⊓ (H ⊓ Submission.Blueprint.conj (t : G) H)
  rw [hconj, Subgroup.map_inf _ _ F.subtype F.subtype_injective,
      Subgroup.subgroupOf_map_subtype H F, Subgroup.subgroupOf_map_subtype _ F]
  ext x
  simp only [Subgroup.mem_inf]
  tauto

end Work.ThreePoints.P3NeBot
