import Mathlib
import Submission.Work.OddBound.LiftKit
import Submission.ConjEnergy
import Submission.Work.OddBound.polygon.riemannianDist_eq_toReal
import Submission.Work.OddBound.polygon.segmentDomain_at_endpoint
import Submission.Work.OddBound.polygon.hasDerivAt_edist_sq_at_endpoint
import Submission.Work.OddBound.polygon.hasDerivAt_riemannianDist_sq_self

namespace Work.OddBound.polygon

open scoped ContDiff Manifold
open Bundle
open ContDiff
open Set
open MeasureTheory
open scoped Interval

/-!
# The derivative of the squared distance along a curve (first variation)

If `y₀ = exp_{x₀} w` is at distance `‖w‖ = d(x₀,y₀) < r`, with `exp_{x₀}` injective on the ball of
radius `r`, then for every smooth curve `v` with `v 0 = x₀`,

  `d(v t, y₀)² = ‖w‖² - 2 t ⟨w, v'(0)⟩ + o(t)`,

i.e. the derivative at `0` of `t ↦ d(v t, y₀)²` is `-2 ⟨w, v'(0)⟩`.  This is the first variation
formula of the distance function; it needs no curvature hypothesis, only that `y₀` is not a cut
point of `x₀` in the reverse direction, which is supplied by `segmentDomain_at_endpoint`.

The proof is assembled from:
* `riemannianDist_eq_toReal` (the bridge between the `sInf`-distance and Mathlib's
  `riemannianEDist`);
* `segmentDomain_at_endpoint` (the reversed vector `U` is in the segment domain at `y₀`, i.e. `x₀`
  is not a cut point of `y₀`);
* `hasDerivAt_edist_sq_at_endpoint` (the first variation formula at such a point);
* `hasDerivAt_riemannianDist_sq_self` (the degenerate case `y₀ = x₀`).
-/

theorem hasDerivAt_riemannianDist_sq_along
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [CovariantDerivative.ContMDiffCovariantDerivative cov ∞]
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {x₀ y₀ : M} {r : ℝ} (hr : 0 < r)
    (hinj : ∀ u v : TangentSpace I x₀, ‖u‖ < r → ‖v‖ < r →
      Submission.GlobalExp.GExp (cov := cov) hmet x₀ u
        = Submission.GlobalExp.GExp (cov := cov) hmet x₀ v → u = v)
    (hd : Submission.Distance.riemannianDist (I := I) x₀ y₀ < r)
    {w : TangentSpace I x₀} (hw : Submission.GlobalExp.GExp (cov := cov) hmet x₀ w = y₀)
    (hwn : ‖w‖ = Submission.Distance.riemannianDist (I := I) x₀ y₀)
    {v : ℝ → M} (hv : ContMDiff 𝓘(ℝ) I ∞ v) (hv0 : v 0 = x₀) :
    HasDerivAt (fun t : ℝ => (Submission.Distance.riemannianDist (I := I) (v t) y₀) ^ 2)
      (-2 * inner ℝ w (Submission.Geodesic.curveVelocity (I := I) v 0)) 0 := by
  classical
  -- `hinj` is precisely `InjAtLeast`
  have hinj' : Submission.InjRadius.InjAtLeast hmet x₀ r := hinj
  -- finiteness of the Riemannian distance (compact, connected)
  have hfin : Manifold.riemannianEDist I x₀ y₀ ≠ ⊤ :=
    (Submission.HopfRinow.riemannianEDist_lt_top (cov := cov) hmet htor x₀ y₀).ne
  -- the `ENNReal` form of `hwn`
  have hedist_eq : Manifold.riemannianEDist I x₀ y₀ = ENNReal.ofReal ‖w‖ := by
    rw [← ENNReal.ofReal_toReal hfin, ← riemannianDist_eq_toReal (I := I) x₀ y₀, ← hwn]
  -- the `ENNReal` form of `hd`
  have hd' : Manifold.riemannianEDist I x₀ y₀ < ENNReal.ofReal r := by
    rw [hedist_eq]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by rw [hwn]; exact hd)
  by_cases hw0 : w = 0
  · -- degenerate case: `y₀ = x₀` and the derivative is `0`
    have hy0 : y₀ = x₀ := by rw [← hw, hw0, Submission.GlobalExp.GExp_zero]
    subst hy0
    have hzero : -2 * inner ℝ w (Submission.Geodesic.curveVelocity (I := I) v 0) = 0 := by
      rw [hw0]
      exact mul_eq_zero_of_right _ (inner_zero_left _)
    rw [hzero]
    exact hasDerivAt_riemannianDist_sq_self (I := I) hv hv0
  · -- main case: `w ≠ 0`; both endpoints are non-degenerate
    obtain ⟨U, hUnorm, hUp, hUseg⟩ :=
      segmentDomain_at_endpoint (cov := cov) hmet htor hr hinj' hw hd' hedist_eq
    have hUne : U ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hUnorm
      exact hw0 (norm_eq_zero.mp hUnorm.symm)
    have h := hasDerivAt_edist_sq_at_endpoint (cov := cov) hmet htor hUne hUseg hUp hw hUnorm.symm hv hv0
    have hfun : (fun t : ℝ => ((Manifold.riemannianEDist I y₀ (v t)).toReal) ^ 2)
        = fun t : ℝ => (Submission.Distance.riemannianDist (I := I) (v t) y₀) ^ 2 := by
      funext t
      rw [riemannianDist_eq_toReal (I := I) (v t) y₀, Manifold.riemannianEDist_comm]
    rw [hfun] at h
    exact h

end Work.OddBound.polygon
