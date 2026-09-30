import Mathlib
import Submission.Work.Charts.Core

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.Charts

universe u

open CategoryTheory in
theorem genericPoint_mem_V {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    [Work.SpecLin.DivBase C] {R : Work.Charts.RochData C} [Work.SpecLin.SymGeom C R.g]
    [AlgebraicGeometry.IsIntegral (Work.Charts.Sym C R.g).left]
    (d : Work.Charts.BNData C R) :
    genericPoint (Work.Charts.Sym C R.g).left ∈ d.V := by
  have hne : (d.V : Set (Work.Charts.Sym C R.g).left).Nonempty := by
    by_contra hc
    rw [Set.not_nonempty_iff_eq_empty] at hc
    exact d.V_ne_bot (TopologicalSpace.Opens.ext (by rw [hc]; rfl))
  obtain ⟨x, hx⟩ := hne
  exact (genericPoint_specializes x).mem_open d.V.2 hx

end Work.Charts
