import Mathlib
import Submission.Work.ThmF.Bender.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.Bender

/-- A Sylow `2`-subgroup of `H` is a maximal `2`-subgroup of `H`: if its image in `G`
is contained in a `2`-subgroup `S ≤ H`, then `S` equals that image.  Indeed `S.subgroupOf H`
is a `2`-subgroup of `H` containing `Q`, so `Q.is_maximal'` forces `S.subgroupOf H = Q`,
whence `S = (S.subgroupOf H).map H.subtype = (Q : Subgroup ↥H).map H.subtype`. -/
theorem mapSylowMaximal {G : Type*} [Group G] [Finite G] {H : Subgroup G} (Q : Sylow 2 ↥H) (S : Subgroup G) (hS : IsPGroup 2 S) (hSH : S ≤ H) (hle : (Q : Subgroup ↥H).map H.subtype ≤ S) : S ≤ (Q : Subgroup ↥H).map H.subtype := by
  intro x hx
  have hxH : x ∈ H := hSH hx
  -- `S` viewed inside `H`
  have hxS' : (⟨x, hxH⟩ : H) ∈ S.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
  -- this copy of `S` is again a `2`-group
  have hS'2 : IsPGroup 2 (S.subgroupOf H) := hS.comap_of_injective H.subtype H.subtype_injective
  -- and it contains `Q`
  have hQS' : (Q : Subgroup H) ≤ S.subgroupOf H := by
    intro q hq
    rw [Subgroup.mem_subgroupOf]
    exact hle (Subgroup.mem_map.mpr ⟨q, hq, rfl⟩)
  -- maximality of the Sylow subgroup forces equality
  have heq : S.subgroupOf H = (Q : Subgroup H) := Q.is_maximal' hS'2 hQS'
  have hxQ : (⟨x, hxH⟩ : H) ∈ (Q : Subgroup ↥H) := heq ▸ hxS'
  exact Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, hxQ, rfl⟩

end Work.ThmF.Bender
