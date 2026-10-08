import Mathlib
import Submission.Work.Hering.Perm.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Step3

open Work.Hering

/-- Every `p`-subgroup `P` of a subgroup `C ≤ G` is contained in a `p`-Sylow subgroup `Q` of `C`
(in the unbundled sense of `Work.Hering.IsSylowSubgroup`). -/
theorem exists_isSylowSubgroup_of_isPGroup_le {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {P C : Subgroup G} (hPC : P ≤ C) (hP : IsPGroup p ↥P) :
    ∃ Q : Subgroup G, P ≤ Q ∧ Q ≤ C ∧ IsSylowSubgroup p Q C := by
  -- view `P` as a `p`-subgroup of `C` and extend it to a Sylow `p`-subgroup of `C`
  have hP' : IsPGroup p ↥(P.subgroupOf C) := hP.comap_subtype
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow hP'
  refine ⟨(S : Subgroup C).map C.subtype, ?_, ?_, ?_⟩
  · -- `P ≤ Q`
    intro x hx
    exact ⟨⟨x, hPC hx⟩, hS (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · -- `Q ≤ C`
    exact Subgroup.map_subtype_le _
  · -- `Q` is a Sylow `p`-subgroup of `C`
    refine ⟨Subgroup.map_subtype_le _, S.isPGroup'.map C.subtype, ?_⟩
    intro R hQR hRC hR
    have hR' : IsPGroup p ↥(R.subgroupOf C) := hR.comap_subtype
    have hSleR' : (S : Subgroup C) ≤ R.subgroupOf C := by
      intro y hy
      exact hQR ⟨y, hy, rfl⟩
    have h := S.is_maximal' hR' hSleR'
    rw [← Subgroup.map_subgroupOf_eq_of_le hRC, h]

end Work.Hering.Step3
