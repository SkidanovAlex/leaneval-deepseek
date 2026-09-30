import Mathlib
import Submission.Work.CurveBasics.All
import Submission.Work.CurveBasics.exists_separating_element
import Submission.Work.SpecLin.Chart.Regular
import Submission.Work.SpecLin.Chart.isAffineOpen_regularOpensAux
import Submission.Work.SpecLin.Chart.exists_transcendental_regular

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SpecLin.Chart

open CategoryTheory AlgebraicGeometry in
theorem exists_isAffineOpen_containing {K : Type*} [Field K] (C : Work.CurveBasics.Curve K)
    (S : Set C.left) (hS : S.Finite) :
    ∃ W : C.left.Opens, IsAffineOpen W ∧ S ⊆ (W : Set C.left) := by
  obtain ⟨x, hx, hSx⟩ := exists_transcendental_regular C S hS
  exact ⟨regularOpens C x, isAffineOpen_regularOpensAux C x hx, hSx⟩

end Work.SpecLin.Chart
