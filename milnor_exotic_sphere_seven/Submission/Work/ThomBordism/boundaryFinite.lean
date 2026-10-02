import Mathlib
import Submission.Work.ThomBordism.boundaryDualityExplicit
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.finiteRatCohomology
import Submission.Work.ThomBordism.compactHomologyFinite
import Submission.Work.ThomBordism.goodUnivCharted
import Submission.Work.ThomBordism.sigmaSigmaTypeSum
import Submission.Work.Surgery.BoundaryInstances
import Submission.Work.Bordism.cohomology_coprod_iso
import Submission.Work.ThomBordism.bdryRatCohFinite

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.ThomBordism

/-- **Finiteness of the middle cohomology of the boundary.** For a compact oriented `9`-manifold `W` whose boundary is the disjoint union of the closed oriented `8`-manifolds `F i` (a `Work.ThomBordism.NullBordismFamily`), the rational middle cohomology `H⁴(∂W;ℚ)` is finite dimensional. This is (verbatim) the `finite` field of `Work.ThomBordism.BoundaryDualityExplicit` (`Submission/Work/ThomBordism/boundaryDualityExplicit.lean`), hence one of the three inputs of `Work.ThomBordism.BoundarySigma`. Suggested route: transport along the homeomorphism `W.bdry : ∂W ≃ₜ Σ i, (F i).pt` to the finite coproduct of the pieces, each piece having finite dimensional middle cohomology by `Work.ThomBordism.finiteDimensional_ratCohomology_of_good` (its hypotheses: local generation `Man8.c_fund` and finite generation of the integral homology `Work.ThomBordism.compactHomologyFinite`). Note (`ChartedSpace (EuclideanSpace ℝ (Fin 8))`/`IsManifold` on `∂W`): `Work.Surgery.BoundaryInstances` provides the boundary instances, or work entirely on `Σ i, (F i).pt` through `W.bdry`. -/
theorem boundaryFinite : ∀ (ι : Type) [Fintype ι] (F : ι → Work.ThomBordism.Man8)
    (W : Work.ThomBordism.NullBordismFamily ι F),
    FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology 4
      (TopCat.toSSet.obj (TopCat.of (Work.ThomBordism.bdrySet W.W)))) := by
  intro ι _ F W
  exact bdryRatCohFinite F W

end Work.ThomBordism
