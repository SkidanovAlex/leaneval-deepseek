import Submission.Work.OddBound.LiftKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The reversed-velocity vector at the endpoint of a minimising ray

This module isolates, as a single `Prop`, the statement that the reversed initial velocity of a
minimising geodesic ray, read at the *endpoint* of the ray, lies in the tangential segment domain of
that endpoint.

Concretely: let `ξ` be a unit tangent vector at `x₀` and `γ s := GExp x₀ (s • ξ)` the ray.  If the
exponential map at `x₀` is injective on the ball of radius `r` (`InjAtLeast hmet x₀ r`) and
`0 < m < r`, then the ray is minimising on `[0, r]` (in particular up to `m`), and the *reversed*
ray from `y := γ m` in the direction `ξ̃ := -γ̇(m)` runs back to `x₀` at time `m`.  The claim is that
the corresponding vector `m • ξ̃` (of norm `m`, with `GExp y (m • ξ̃) = x₀`) lies in the tangential
segment domain `D̃_y`, i.e. that the reversed ray is minimising *strictly* beyond `x₀`.

Equivalently (by `SegmentDomain.mem_segmentDomain_iff`): `m < cutTime y ξ̃`, i.e. `x₀` is not a cut
point of `y` along the reversed geodesic.  This is the classical symmetry of the cut locus, applied
along a single minimising geodesic, with the injectivity radius only at the *base point* `x₀`
(where it is available from the hypotheses of `segmentDomain_at_endpoint`).
-/

open scoped ContDiff Manifold
open Bundle

namespace Work.OddBound.polygon

/-- **The hard core of `segmentDomain_at_endpoint`.**  The reversed velocity vector at the endpoint
of a minimising ray lies in the tangential segment domain of the endpoint, provided the injectivity
radius at the base point exceeds the length of the ray. -/
def RevVelocityInSegmentDomain : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x₀ : M} {r m : ℝ} (hm : 0 < m) (hmr : m < r)
    (hinj : Submission.InjRadius.InjAtLeast hmet x₀ r)
    {ξ : TangentSpace I x₀} (hξ : ‖ξ‖ = 1),
    m • (-Submission.Geodesic.curveVelocity (I := I)
        (fun s : ℝ => Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ)) m)
      ∈ Submission.SegmentDomain.segmentDomain hmet
          (Submission.GlobalExp.GExp (cov := cov) hmet x₀ (m • ξ))

/-- **Equivalent form of the hard core**, phrased purely with the Riemannian distance: along a
minimising ray whose base point has injectivity radius `r > m`, the ray stays minimising a little
past the endpoint `m`, on the *left* as well: the geodesic arc `[s,t] ⊆ [-ε, m]` is minimising. -/
def RayMinimisingPastEndpoint : Prop :=
  ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x₀ : M} {r m : ℝ} (hm : 0 < m) (hmr : m < r)
    (hinj : Submission.InjRadius.InjAtLeast hmet x₀ r)
    {ξ : TangentSpace I x₀} (hξ : ‖ξ‖ = 1),
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, -ε ≤ s → s ≤ m → ∀ t : ℝ, s ≤ t → t ≤ m →
      Manifold.riemannianEDist I (Submission.GlobalExp.GExp (cov := cov) hmet x₀ (s • ξ))
        (Submission.GlobalExp.GExp (cov := cov) hmet x₀ (t • ξ))
      = ENNReal.ofReal (t - s)

end Work.OddBound.polygon
