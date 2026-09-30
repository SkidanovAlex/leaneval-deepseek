/-
# Cartan–Hadamard: the main theorems of area `CH`

This is the interface file of the Cartan–Hadamard area.  Under the framework variable block of the
vendored Riemannian-geometry library (`Submission.Work.RiemLib.API`) and the hypotheses

* `hmet : IsMetricCompatible cov` — the connection is metric compatible,
* `htor : cov.torsion = 0` — the connection is torsion free,
* `hK : ∀ K > 0, RauchK.CurvLe cov K` — the sectional curvature is `≤ 0`
  (obtained from a pointwise non-positivity statement by `Work.CartanHadamard.curvLe_all`),

the area provides

* `curvLe_all` — `sec ≤ 0` gives every parametric upper bound `CurvLe cov K`, `K > 0`;
* `isLocalHomeomorph_gexp` — `gexpMap hmet p` is a local homeomorphism;
* `Work.CartanHadamard.isCoveringMap_gexp` (`CartanHadamard/Cover.lean`) — **Cartan–Hadamard**:
  `gexpMap hmet p : E → M` is a covering map (whenever `M` is compact); this is the
  evenly-covered-neighbourhood theorem;
* `aspherical_of_curvLe` — `M` is aspherical: `π_k(M, x)` is a subsingleton for every `k ≥ 2`,
  obtained from the covering `gexpMap hmet p` by the `Aspherical/` area (`S1`), the total space being
  a real normed space.
-/
import Submission.Work.CartanHadamard.Basic
import Submission.Work.CartanHadamard.Cover
import Submission.Work.CartanHadamard.surjective_of_isCoveringMap_of_connectedSpace
import Submission.Work.Aspherical.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open LeanEval.Geometry.SphereTheorem

namespace Work.CartanHadamard

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M] [ConnectedSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-- **`CH` deliverable 2**: `gexpMap hmet p` is a local homeomorphism. -/
theorem isLocalHomeomorph_gexp (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) (p : M) :
    IsLocalHomeomorph (Submission.XuLift.gexpMap (cov := cov) hmet p) :=
  isLocalHomeomorph_gexpMap (cov := cov) hmet htor hK p

open scoped Classical in
/-- **Surjectivity of the exponential map** on a compact connected manifold: the covering
`gexpMap hmet p` is surjective (`Work.CartanHadamard.surjective_of_isCoveringMap_of_connectedSpace`).
Hopf–Rinow gives the same conclusion but needs path connectedness; here connectedness suffices. -/
theorem surjective_gexp (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) (p : M) :
    Function.Surjective (Submission.XuLift.gexpMap (cov := cov) hmet p) :=
  surjective_of_isCoveringMap_of_connectedSpace
    (isCoveringMap_gexp (cov := cov) hmet htor hK p)

/-- **`CH` deliverable 4**: a compact, connected, non-positively curved manifold is aspherical.

The cover is `gexpMap hmet p`, whose total space is the real normed space `E`; the `Aspherical/`
area (`Work.Aspherical`) turns a covering with a normed-space total space into the vanishing of all
higher homotopy groups.  Surjectivity of the covering is automatic because the base is connected
(`Work.CartanHadamard.surjective_of_isCoveringMap_of_connectedSpace`). -/
theorem aspherical_of_curvLe (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) :
    ∀ k : ℕ, 2 ≤ k → ∀ x : M, Subsingleton (HomotopyGroup (Fin k) M x) := by
  classical
  let p : M := Classical.choice (inferInstance : Nonempty M)
  have hcov : IsCoveringMap (Submission.XuLift.gexpMap (cov := cov) hmet p) :=
    isCoveringMap_gexp (cov := cov) hmet htor hK p
  have hsurj : Function.Surjective (Submission.XuLift.gexpMap (cov := cov) hmet p) :=
    surjective_of_isCoveringMap_of_connectedSpace hcov
  exact fun k hk x =>
    Work.Aspherical.subsingleton_homotopyGroup_of_covering_of_normed hcov hsurj k hk x

/-- The packaged form of `aspherical_of_curvLe` in the vocabulary of the `Aspherical/` area. -/
theorem isAspherical_of_curvLe (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) :
    Work.Aspherical.IsAspherical M :=
  fun k hk x => aspherical_of_curvLe (cov := cov) hmet htor hK k hk x

end

end Work.CartanHadamard
