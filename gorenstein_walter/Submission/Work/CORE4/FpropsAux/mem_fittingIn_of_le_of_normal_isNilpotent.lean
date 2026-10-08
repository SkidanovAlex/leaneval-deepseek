import Mathlib
import Submission.Work.CORE4.Defs

set_option linter.style.haveILetI false

namespace Work.CORE4.FpropsAux

theorem mem_fittingIn_of_le_of_normal_isNilpotent {G : Type} [Group G] [Finite G]
    {M₀ Y : Subgroup G} (hY : Y ≤ M₀) (hnorm : (Y.subgroupOf M₀).Normal)
    (hnil : Group.IsNilpotent ↥Y) {x : G} (hx : x ∈ Y) : x ∈ Work.GW2.fittingIn M₀ := by
  -- `Y` viewed inside `M₀` is nilpotent, since `Y.subgroupOf M₀ ≃* Y`.
  haveI : Group.IsNilpotent ↥(Y.subgroupOf M₀) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hY).symm
  -- hence it lies in `F(M₀)`, being a normal nilpotent subgroup of `M₀`
  have hle : Y.subgroupOf M₀ ≤ Work.GW2.fitting M₀ := by
    rw [Work.GW2.fitting]
    exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hnorm, inferInstance⟩)
  -- and `F(M₀)` inside `G` is `fittingIn M₀`
  exact Subgroup.mem_map.mpr ⟨⟨x, hY hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

end Work.CORE4.FpropsAux
