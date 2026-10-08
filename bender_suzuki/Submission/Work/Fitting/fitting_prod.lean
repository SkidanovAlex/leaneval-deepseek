import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.map_fitting_le
import Submission.Work.Fitting.fitting_isNilpotent

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Fitting subgroup of a direct product

`F(G × H) = F(G) × F(H)`, where `F(-)` is the Fitting subgroup
(`Work.Fitting.fitting`) and the right hand side is the subgroup `H.prod K` of `G × H`
consisting of the pairs with first component in `F(G)` and second component in `F(H)`.

## The argument

* `F(G) × F(H)` is a normal subgroup of `G × H`: the Fitting subgroup is characteristic,
  hence normal in each factor, and a product of normal subgroups is normal
  (`Subgroup.prod_normal`).
* It is nilpotent: it is isomorphic to `↥F(G) × ↥F(H)` via `Subgroup.prodEquiv`, and a
  product of nilpotent groups is nilpotent (`Group.isNilpotent_prod`).
  Hence `F(G) × F(H) ≤ F(G × H)` by maximality of `F` (`Work.Fitting.le_fitting`).
* Conversely, `F(G × H)` is nilpotent (`Work.Fitting.fitting_isNilpotent`), so its images
  under the two projections are normal nilpotent subgroups of `G` and `H` respectively, hence
  lie in `F(G)` and `F(H)` (`Work.Fitting.map_fitting_le`).  A pair `(x, y) ∈ F(G × H)` is the
  image of itself under both projections, so `x ∈ F(G)` and `y ∈ F(H)`.
-/

noncomputable section

set_option linter.style.haveILetI false

open Classical

namespace Work.Fitting

theorem fitting_prod (G H : Type*) [Group G] [Finite G] [Group H] [Finite H] :
    Work.Fitting.fitting (G × H) =
      (Work.Fitting.fitting G).prod (Work.Fitting.fitting H) := by
  refine le_antisymm ?_ ?_
  · -- `F(G × H) ≤ F(G) × F(H)`: project onto the two factors.
    intro x hx
    rw [Subgroup.mem_prod]
    exact ⟨map_fitting_le (MonoidHom.fst G H) (fun a => ⟨(a, 1), rfl⟩) ⟨x, hx, rfl⟩,
      map_fitting_le (MonoidHom.snd G H) (fun b => ⟨(1, b), rfl⟩) ⟨x, hx, rfl⟩⟩
  · -- `F(G) × F(H) ≤ F(G × H)`: it is a normal nilpotent subgroup.
    haveI := fitting_isNilpotent G
    haveI := fitting_isNilpotent H
    refine le_fitting inferInstance ?_
    exact Group.nilpotent_of_mulEquiv (Subgroup.prodEquiv (fitting G) (fitting H)).symm

end Work.Fitting
