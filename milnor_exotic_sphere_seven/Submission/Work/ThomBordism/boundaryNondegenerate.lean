import Mathlib
import Submission.Work.ThomBordism.boundaryDualityExplicit
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.nondegenerate_midForm_of_good
import Submission.Work.ThomBordism.goodUnivCharted
import Submission.Work.ThomBordism.compactHomologyFinite
import Submission.Work.ThomBordism.man8Finiteness
import Submission.Work.ThomBordism.sigmaSigmaTypeSum
import Submission.Work.ThomBordism.bdryMidFormNondegenerate
import Submission.Work.Bordism.Middle
import Submission.Work.Bordism.interForm_coprod
import Submission.Work.Surgery.BoundaryInstances

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

/-- **Non-degeneracy of the middle intersection form of the boundary.** For a compact oriented `9`-manifold `W` whose boundary is the disjoint union of the closed oriented `8`-manifolds `F i` (a `Work.ThomBordism.NullBordismFamily`), the middle intersection form `y ↦ ⟨y ⌣ y, [∂W]⟩` of the closed oriented `8`-manifold `∂W` (fundamental class `∂w = Work.Cohomology.hPairδ … W.w`, bundled as `Work.ThomBordism.bdryClosed W`) is non-degenerate. This is (verbatim) the `nondegenerate` field of `Work.ThomBordism.BoundaryDualityExplicit` (`Submission/Work/ThomBordism/boundaryDualityExplicit.lean`), hence one of the three inputs of `Work.ThomBordism.BoundarySigma`. Suggested route: middle-degree Poincaré duality in the form `Work.ThomBordism.nondegenerate_midForm_of_good`, which needs `Good 8 ((hPairδ … W.w)) Set.univ` — from the local generation of `∂w` at the points of `∂W` (`Work.ThomBordism.goodUniv_of_localGen`), which is inherited from the pieces' `Man8.c_fund` through the homeomorphism `W.bdry` and the boundary relation `W.hw` — and finite generation of the integral homology (`Work.ThomBordism.compactHomologyFinite`, again through the pieces: `Work.Bordism.interForm_coprod`, `Work.ThomBordism.sigmaSigmaTypeSum`). Note (`ChartedSpace (EuclideanSpace ℝ (Fin 8))`/`IsManifold` on `∂W`): `Work.Surgery.BoundaryInstances` provides the boundary instances, or transport along `W.bdry` to `Σ i, (F i).pt`. -/
theorem boundaryNondegenerate : ∀ (ι : Type) [Fintype ι] (F : ι → Work.ThomBordism.Man8)
    (W : Work.ThomBordism.NullBordismFamily ι F),
    Work.Bordism.Nondegenerate (Work.Bordism.midForm (k := 4) (Work.ThomBordism.bdryClosed W)) :=
  fun _ _ F W => bdryMidFormNondegenerate F W

end Work.ThomBordism
