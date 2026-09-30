/-
# The `Δ`-complex of `M̄` and its realization

**Work package W4** of `Submission/Work/NOTES_LEAD_eA.md`: the two objects that the rest of the
area is stated about.

* `mbarSd` — the barycentric subdivision of `M̄` as a `Δ`-complex (`mbarSdOf flagRel_face`);
* `mbarReal` — its realization in `M̄` (`Classical.choice` of `mbarReal_exists`, which is a
  proposition, so the extraction is classical but the object is never computed).

Downstream (`Work.MbarHomology.Mbar.eA`, work package W7) these feed
`Work.PieceHomology.DeltaModel.ofHatcher mbarReal (mbarK_homology)`, whose `iso` is the `eA`
input of `Work.PieceHomology.cuspData_of_concrete`.
-/
import Mathlib
import Submission.Work.MbarHomology.Mbar.Sd
import Submission.Work.MbarHomology.Mbar.flagRel_face
import Submission.Work.MbarHomology.Mbar.mbarReal_exists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

namespace Work.MbarHomology

open CategoryTheory

noncomputable section

/-- **The barycentric subdivision of `M̄`**: the `Δ`-complex whose `k`-simplices are the orbits of
flags of `Q̄₀ ⊔ Q̄₁` under the identification relation `~₁` at their barycentres. -/
noncomputable def mbarSd : Work.DeltaHomology.DeltaCx := mbarSdOf Mbar.flagRel_face

/-- **The realization of the barycentric subdivision of `M̄` in `M̄`.** -/
noncomputable def mbarReal :
    Work.DeltaHomology.DeltaRealization mbarSd (TopCat.of Work.FoldInst.Mbar) :=
  Classical.choice (Mbar.mbarReal_exists Mbar.flagRel_face)

end

end Work.MbarHomology
