import Mathlib.GroupTheory.Frattini
import Submission.Work.Fitting.FittingEqPCore
import Submission.Work.Fitting.isNilpotent_of_isNilpotent_map_quotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.Fitting

set_option linter.style.haveILetI false
open scoped Classical
open Subgroup

variable {G : Type*} [Group G]

/-- The Frattini subgroup of a quotient contains the image of the Frattini subgroup. -/
theorem frattini_map_le (M : Subgroup G) [M.Normal] :
    (frattini G).map (QuotientGroup.mk' M) ≤ frattini (G ⧸ M) :=
  Subgroup.map_le_iff_le_comap.mpr
    (frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective M))

/-- **The Fitting subgroup of a quotient.**  If `M ◁ G` with `M ≤ Φ(G)`, then
`F(G/M) = F(G)M/M`. -/
theorem fitting_map_quotient [Finite G] (M : Subgroup G) [M.Normal] (hM : M ≤ frattini G) :
    (fitting G).map (QuotientGroup.mk' M) = fitting (G ⧸ M) := by
  haveI : Group.IsNilpotent ↥(fitting G) := fitting_nilpotent G
  refine le_antisymm ?_ ?_
  · -- the image of `F(G)` is a nilpotent normal subgroup of `G ⧸ M`
    refine le_fitting (fitting_normal.map (QuotientGroup.mk' M) (QuotientGroup.mk'_surjective M)) ?_
    refine Group.nilpotent_of_surjective
      (MonoidHom.codRestrict ((QuotientGroup.mk' M).comp (fitting G).subtype)
        ((fitting G).map (QuotientGroup.mk' M)) fun x => Subgroup.mem_map_of_mem _ x.2) ?_
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨x, hx⟩, rfl⟩
  · -- `F(G/M)` pulls back to a nilpotent normal subgroup of `G`
    set H : Subgroup G := (fitting (G ⧸ M)).comap (QuotientGroup.mk' M) with hHdef
    haveI hHn : H.Normal := (fitting_normal (G := G ⧸ M)).comap (QuotientGroup.mk' M)
    have hMH : M ≤ H := by
      intro x hx
      rw [hHdef, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
      exact one_mem _
    have hmap : H.map (QuotientGroup.mk' M) = fitting (G ⧸ M) := by
      rw [hHdef]
      exact Subgroup.map_comap_eq_self
        (by rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective M)]; exact le_top)
    have hnil : Group.IsNilpotent ↥(H.map (QuotientGroup.mk' M)) := by
      rw [hmap]
      haveI : Finite (G ⧸ M) := Quotient.finite _
      exact fitting_nilpotent (G ⧸ M)
    have hHnil : Group.IsNilpotent ↥H :=
      isNilpotent_of_isNilpotent_map_quotient M H hMH hHn hM hnil
    calc fitting (G ⧸ M) = H.map (QuotientGroup.mk' M) := hmap.symm
      _ ≤ (fitting G).map (QuotientGroup.mk' M) := Subgroup.map_mono (le_fitting hHn hHnil)

end Work.Fitting
