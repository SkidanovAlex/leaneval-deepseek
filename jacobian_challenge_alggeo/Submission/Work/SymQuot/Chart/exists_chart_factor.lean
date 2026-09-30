import Mathlib
import Submission.Work.SymQuot.Quotient
import Submission.Work.SymQuot.Invariants.fixedPoints_lift
import Submission.Work.SymQuot.Invariants.fixedPoints_isLocalization_away
import Submission.Work.SymQuot.Chart.chart_factor_aux
import Submission.Work.SymQuot.Chart.chart_app_injective
import Submission.Work.SymQuot.Chart.exists_basicOpen_invariant_sub
import Submission.Work.SymQuot.Chart.chart_factor_unique
import Submission.Work.SymQuot.Chart.chart_factor_exists

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.SymQuot.Chart

theorem exists_chart_factor {Γ : Type*} [Group Γ] [Fintype Γ] {X : AlgebraicGeometry.Scheme}
    (A : Work.SymQuot.GAction Γ X) {U : X.Opens} (hUa : AlgebraicGeometry.IsAffineOpen U)
    (hUi : A.IsInvariantOpen U) {Z : AlgebraicGeometry.Scheme} (f : X ⟶ Z)
    (hf : A.IsInvariantMorphism f) :
    ∃! g : A.chart U hUi ⟶ Z,
      CategoryTheory.CategoryStruct.comp (A.chartMap U hUi) g =
        CategoryTheory.CategoryStruct.comp U.ι f := by
  obtain ⟨g, hg⟩ := chart_factor_exists A hUa hUi f hf
  exact ⟨g, hg, fun g' hg' => chart_factor_unique A hUa hUi (hg'.trans hg.symm)⟩

end Work.SymQuot.Chart
