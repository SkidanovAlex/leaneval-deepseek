import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.FarKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vocabulary for the proof of `Work.Diff.C.fb_cap_depth` (far-ball excess bound)

The delegated lemmas of this little chapter are stated against the whole Riemannian-bundle
vocabulary (`fcos`, `rdist`, `rgrad`, `rhess`), and the delegation harness elaborates a submitted
statement in a file containing only the modules listed in `depends_on` and **no `open` commands**.
In that bare context the binders `[RiemannianBundle (fun x ↦ TangentSpace I x)]` /
`[IsContMDiffRiemannianBundle … (fun x ↦ TangentSpace I x)]` (and even the instance
`Inner ℝ (TangentSpace I y)`) are not found, because they live behind the `Bundle` scope.

Following `Submission/Work/Diff/C/geoCrux/Defs.lean`, the statements are therefore packaged as
closed `Prop`-valued `abbrev`s written here with all the `open`s active, so that a submitted
statement `theorem name : Work.Diff.C.FbCap.<Prop> := by sorry` elaborates in the bare context.
Because they are `abbrev`s they unfold definitionally: `intro` (possibly repeated) turns the goal
into the familiar form, one hypothesis per binder.

## The pieces

* `RdistSmoothProp` — where `fcos q` is smooth and satisfies the eikonal identity, the distance
  function `rdist q` is smooth and has a unit gradient;
* `HessNonnegProp` — the Hessian of a smooth function with a global minimum is positive
  semidefinite;
* `RayRdistEqProp` — the distance identities along a **minimising** `GExp`-ray: if the ray from `q`
  in the unit direction `u` reaches `z` at parameter `L` (i.e. `rdist q z = L`), then
  `rdist q (GExp q (t • u)) = t` and `rdist z (GExp q (t • u)) = L - t` for `t ∈ [0, L]`;
* `DiamFinrankOneProp` — in dimension one, if every point is within `π` of `p` then every two
  points are within `π` of each other (the diameter is attained at the antipode of any point).
-/

namespace Work.Diff.C.FbCap

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-- **The distance function is smooth with a unit gradient, on the region where `cos ∘ rdist` is.**
Let `fcos q = cos ∘ rdist q`.  If `0 < rdist q x < π`, `-1 + c < fcos q x`, `fcos q` is smooth
wherever `-1 + c ≤ fcos q`, and `|∇ (fcos q)| ² = 1 - (fcos q)²` wherever `-1 + c < fcos q`, then
`rdist q` is smooth at `x` and `|∇ (rdist q) x|² = 1`. -/
abbrev RdistSmoothProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : IsMetricCompatible cov)
    {c : ℝ} (hc : 0 < c) {q x : M}
    (hx0 : 0 < rdist (I := I) (M := M) q x)
    (hxpi : rdist (I := I) (M := M) q x < Real.pi)
    (hx : -1 + c < fcos (I := I) (M := M) q x)
    (hsmC : ∀ y : M, -1 + c ≤ fcos (I := I) (M := M) q y →
      ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
        (fcos (I := I) (M := M) q) y)
    (hgrad : ∀ y : M, -1 + c < fcos (I := I) (M := M) q y →
      Inner.inner ℝ (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        (rgrad (I := I) (M := M) (fcos (I := I) (M := M) q) y)
        = 1 - (fcos (I := I) (M := M) q y) ^ 2),
    ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat)
        (fun y : M ↦ rdist (I := I) (M := M) q y) x ∧
      Inner.inner ℝ
        (rgrad (I := I) (M := M) (fun y : M ↦ rdist (I := I) (M := M) q y) x)
        (rgrad (I := I) (M := M) (fun y : M ↦ rdist (I := I) (M := M) q y) x)
        = 1

/-- **The covariant Hessian of a smooth function with a global minimum is positive semidefinite.** -/
abbrev HessNonnegProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {F : M → ℝ} {x : M}
    (hF : ContMDiffAt I (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) F x)
    (hmin : ∀ y : M, F x ≤ F y) (V : TangentSpace I x),
    0 ≤ rhess (I := I) (M := M) cov F x V V

/-- **The distance identities along a minimising `GExp`-ray.**  If `u` is a unit vector at `q`,
`L ≥ 0`, the ray from `q` in the direction `u` reaches `z` at parameter `L` (`GExp q (L • u) = z`)
**and** that is the distance (`rdist q z = L`, so the ray is minimising by Hopf–Rinow), then for
every `t ∈ [0, L]` the point `GExp q (t • u)` is at distance `t` from `q` and at distance `L - t`
from `z`.

(The minimising hypothesis is essential: `GExp q (L • u) = z` alone only says the geodesic *passes
through* `z` at time `L`, e.g. on the unit circle with `L` a period one would get
`z = q` and `rdist z (γ t) = t ≠ L - t`.) -/
abbrev RayRdistEqProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q z : M} {u : TangentSpace I q} (hu : ‖u‖ = 1) {L : ℝ} (hL : 0 ≤ L)
    (hz : Submission.GlobalExp.GExp (cov := cov) hmet q (L • u) = z)
    (hmin : rdist (I := I) (M := M) q z = L),
    ∀ t ∈ Set.Icc (0 : ℝ) L,
      rdist (I := I) (M := M) q
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) = t ∧
      rdist (I := I) (M := M) z
          (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u)) = L - t

/-- **The diameter in dimension one.**  In dimension one, if every point is within `π` of the base
point `p` (`rdist p y ≤ π` for all `y`), then every two points are within `π` of each other.
(On a compact one-dimensional manifold the point set is a circle, `max_y rdist p y` is the
diameter for every `p`, and the ray from `p` covers the whole manifold.) -/
abbrev DiamFinrankOneProp : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ((⊤ : ENat) : WithTop ENat) E
      (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ((⊤ : ENat) : WithTop ENat)]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hdim : Module.finrank ℝ E = 1) {p : M}
    (hp : ∀ y : M, rdist (I := I) (M := M) p y ≤ Real.pi)
    (x y : M),
    rdist (I := I) (M := M) x y ≤ Real.pi

end Work.Diff.C.FbCap
