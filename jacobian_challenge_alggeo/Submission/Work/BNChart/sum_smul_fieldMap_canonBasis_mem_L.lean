import Mathlib
import Submission.Work.BNChart.Chart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


universe u

namespace Work.BNChart

/-- Any `F`-linear combination of the base-changed basis elements `fieldMap (canonBasis C h j)`
lies in `L (pullK C (rochW C))`. -/
theorem sum_smul_fieldMap_canonBasis_mem_L {K : Type u} [Field K] {C : Work.CurveBasics.Curve K}
    (h : RiemannRoch.Curve.genus C ≠ 0) {F : Type u} [Field F] [Algebra K F]
    (c : Work.BNChart.chartIdx C → F) :
    (∑ j, c j • (Work.CurveBasics.Curve.bcSquare C F).fieldMap.hom
        ((Work.BNChart.canonBasis C h j : C.L (RiemannRoch.Curve.canonical C))
          : C.functionField))
      ∈ (C.baseChange F).L (Work.Charts.pullK C (Work.BNChart.rochW C)) := by
  classical
  -- It suffices to know that each base-changed basis element lies in `L (pullK C (rochW C))`,
  -- since `L` is a submodule.
  have hmem : ∀ j : chartIdx C,
      (Work.CurveBasics.Curve.bcSquare C F).fieldMap.hom
        ((canonBasis C h j : C.L (RiemannRoch.Curve.canonical C)) : C.functionField)
      ∈ (C.baseChange F).L (Work.Charts.pullK C (rochW C)) := by
    intro j
    -- `pullK C (rochW C) = divMap (canonical C)`, and flat base change of `H⁰(O(D))` says
    -- `L (divMap D) = span_F (fieldMap '' L D)`.
    rw [pullK_rochW_bcSquare C F, Work.CurveBasics.Curve.BCSquare.L_divMap]
    exact Submodule.subset_span ⟨_, canonBasis_mem C h j, rfl⟩
  exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hmem j))

end Work.BNChart
