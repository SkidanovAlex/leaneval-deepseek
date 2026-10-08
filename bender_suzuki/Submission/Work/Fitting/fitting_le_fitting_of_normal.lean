import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.fitting_isNilpotent
import Submission.Work.Fitting.fitting_eq_iSup_pCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `F(N) ≤ F(G)` for a normal subgroup `N ⊴ G`

If `N` is a normal subgroup of a finite group `G`, then the Fitting subgroup of `N`,
viewed as a subgroup of `G` via `N.subtype`, is contained in the Fitting subgroup of `G`:

  `F(N).map N.subtype ≤ F(G)`.

`F(G)` is the supremum of the normal nilpotent subgroups of `G` (`Work.Fitting.fitting`),
so it suffices to show that the image of `F(N)` is a normal nilpotent subgroup of `G`:

* `F(N)` is nilpotent (`Work.Fitting.fitting_isNilpotent`), hence its image under any
  homomorphism is nilpotent (`Work.Fitting.isNilpotent_map`);
* `F(N)` is characteristic in `N` (`Work.Fitting.fitting_characteristic_inst`), and a
  characteristic subgroup of a normal subgroup is normal in the ambient group
  (`Work.Fitting.map_characteristic_normal`).
-/

noncomputable section

open Classical

namespace Work.Fitting

theorem fitting_le_fitting_of_normal {G : Type*} [Group G] [Finite G] {N : Subgroup G} [N.Normal] :
    (Work.Fitting.fitting ↥N).map N.subtype ≤ Work.Fitting.fitting G := by
  have hFnil : Group.IsNilpotent ↥(Work.Fitting.fitting ↥N) := fitting_isNilpotent ↥N
  refine le_fitting ?_ ?_
  · exact map_characteristic_normal (N := N) inferInstance (fitting_characteristic_inst ↥N)
  · exact isNilpotent_map N.subtype (fitting_isNilpotent ↥N)

end Work.Fitting
