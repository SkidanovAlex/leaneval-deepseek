import Mathlib
import Submission.Work.ThomBordism.doubleFC.seamLocalGeneration

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.ThomBordism.DoubleFC

noncomputable section

variable {n : ℕ} {M : Type} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]

/-- **Local generation at a seam point of the double, given generation at the interior points of
the first copy.**  This is `Work.ThomBordism.doubleFC.seamLocalGeneration`, proved by the chart-ball
propagation of `Work.ThomBordism.doubleFC.isZero_relSubPunctured_chart` and
`Work.ThomBordism.doubleFC.span_relLocClass_iff_of_isZero`. -/
theorem span_localClassAt_seam (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    (cD : (Work.Cohomology.singularChains ℤ (TopCat.of (Double n M))).homology (n + 1))
    (hgenM : ∀ (y : M) (hy : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M),
      Submodule.span ℤ {(Work.ThomBordism.localClassAt (TopCat.of (Double n M)) (n + 1) cD
        (doubleιM (n := n) (M := M) y))} = ⊤)
    (b : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    Submodule.span ℤ {(Work.ThomBordism.localClassAt (TopCat.of (Double n M)) (n + 1) cD
      (doubleιM (n := n) (M := M) b.1))} = ⊤ :=
  Work.ThomBordism.doubleFC.seamLocalGeneration n M cD hgenM b

/-- The same statement at the second copy of a seam point (the two copies have the same image). -/
theorem span_localClassAt_seamN (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    (cD : (Work.Cohomology.singularChains ℤ (TopCat.of (Double n M))).homology (n + 1))
    (hgenM : ∀ (y : M) (hy : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M),
      Submodule.span ℤ {(Work.ThomBordism.localClassAt (TopCat.of (Double n M)) (n + 1) cD
        (doubleιM (n := n) (M := M) y))} = ⊤)
    (b : (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    Submodule.span ℤ {(Work.ThomBordism.localClassAt (TopCat.of (Double n M)) (n + 1) cD
      (doubleιN (n := n) (M := M) b.1))} = ⊤ := by
  have h : doubleιM (n := n) (M := M) b.1 = doubleιN (n := n) (M := M) b.1 :=
    doubleιM_eq_ιN_iff.mpr ⟨b, rfl, rfl⟩
  rw [← h]
  exact Work.ThomBordism.doubleFC.seamLocalGeneration n M cD hgenM b

end

end Work.ThomBordism.DoubleFC
