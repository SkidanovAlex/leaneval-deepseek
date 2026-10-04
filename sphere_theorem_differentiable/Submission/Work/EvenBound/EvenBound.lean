import Submission.Work.EvenBound.Core
import Submission.XuReduction
import Submission.Work.EvenBound.Transfer
import Submission.Work.EvenBound.Attain.injSup_attained_of_lt_pi_div_sqrt
import Submission.Work.EvenBound.ThirdGeodesic.no_shorter_closed_of_only_two_minimising

set_option backward.isDefEq.respectTransparency.types false

/-!
# Klingenberg's length bound in even dimensions

The main results of this module:

* `Work.EvenBound.injAllAtLeast_pi_div_sqrt_even` — **the even-dimensional Klingenberg estimate**:
  on a compact, simply connected, even-dimensional Riemannian manifold with sectional curvature
  `K/4 ≤ sec ≤ K` (`0 < K`), the exponential map is injective on the ball of radius `π/√K` at every
  point (so the injectivity radius is `≥ π/√K`);

* `Work.EvenBound.klingenberg_length_bound_even` — **Klingenberg's length bound in even dimensions**:
  every closed geodesic loop has length `≥ 2π/√K`.

The proof of the injectivity-radius estimate is the classical even-dimensional argument (no free
loop space minimax is needed):

1. the global injectivity radius `m = injSup hmet = inf_p inj(p)` is **attained** below the conjugate
   radius (`Work.EvenBound.Attain.injSup_attained_of_lt_pi_div_sqrt`);
2. at the attained point `p` the cut-point step gives two distinct minimising directions `ξ, η`
   whose rays meet at a point `q` at distance `m`, both minimising;
3. Xu's Theorem B at `p` and at `q` (`Submission.KlingenbergEven.ray_periodic_of_two_minimising`)
   glues the two rays into a **closed geodesic of length `2m`**, and shows that the only minimising
   directions at `p` of length `m` are the two directions of that geodesic
   (`Work.EvenBound.FlushData.only_two_directions`);
4. since the dimension is even and `M` is simply connected, Synge's argument gives a parallel
   periodic unit normal field along the closed geodesic
   (`Work.EvenBound.SyngeField.exists_synge_field_periodic`), whose second variation is negative, so
   the geodesic is **shortened** by closed curves of length `< 2m`
   (`Work.EvenBound.SyngeAssembly.exists_shorter_family`);
5. the resulting minimising geodesics from the base points of the shortened curves to their farthest
   points, in the limit, give a **third** minimising direction at `p` of length `m`, contradicting
   step 3 (`Work.EvenBound.ThirdGeodesic.no_shorter_closed_of_only_two_minimising`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.InjRadius
open Submission.CurvatureVec
open Submission.InjSup
open Submission.GlobalExp

namespace Work.EvenBound

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The even-dimensional Klingenberg estimate.**  On a compact, simply connected,
even-dimensional Riemannian manifold whose sectional curvature satisfies `K/4 ≤ sec ≤ K` with
`0 < K`, the exponential map is injective on the ball of radius `π/√K` at every point. -/
theorem injAllAtLeast_pi_div_sqrt_even
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] [SimplyConnectedSpace M]
    (hEven : Even (Module.finrank ℝ E))
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 ≤ inner ℝ (curvVec cov p u v v) u) :
    InjAllAtLeast hmet (Real.pi / Real.sqrt K) := by
  refine injAllAtLeast_pi_div_sqrt_even_of_inputs (I := I) (cov := cov) hmet htor hEven hK hcurv
    (by positivity) hpinch ?_ ?_
  · intro hlt
    exact Work.EvenBound.Attain.injSup_attained_of_lt_pi_div_sqrt (I := I) (cov := cov) hmet htor
      hcurv hK hlt
  · intro p q m hm hinjall hpq γ hγ0 hγhalf hper hγsm hγgeo hsp honly Z hZ1 hZsm d hd hshort
    exact Work.EvenBound.ThirdGeodesic.no_shorter_closed_of_only_two_minimising (I := I)
      (cov := cov) hmet htor hm hinjall hpq hγ0 hγhalf hper hγsm hγgeo hsp honly hZ1 hZsm hd hshort

/-- **Klingenberg's length bound in even dimensions.**  On a compact, simply connected,
even-dimensional Riemannian manifold with sectional curvature `K/4 ≤ sec ≤ K` (`0 < K`), every
closed geodesic loop at every point has length `≥ 2π/√K`. -/
theorem klingenberg_length_bound_even
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] [SimplyConnectedSpace M]
    (hEven : Even (Module.finrank ℝ E))
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 ≤ inner ℝ (curvVec cov p u v v) u)
    {p : M} {T : ℝ} {γ : ℝ → M}
    (hloop : Submission.KlingenbergLemma.IsClosedGeodesicLoopAt hmet p T γ) :
    2 * Real.pi / Real.sqrt K ≤ T :=
  length_bound_of_injAllAtLeast (I := I) (cov := cov) hmet htor
    (injAllAtLeast_pi_div_sqrt_even (I := I) (cov := cov) hmet htor hEven hK hcurv hpinch) hloop

/-- **Klingenberg's length bound in even dimensions, value-closed form.**  The same conclusion for
the weaker (value-closed) notion of geodesic loop used by Xu's Theorem B, i.e. the even-dimensional
case of `Submission.KlingenbergXu.LoopLengthLowerBound`. -/
theorem loopLengthLowerBound_even
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] [SimplyConnectedSpace M]
    (hEven : Even (Module.finrank ℝ E))
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 ≤ inner ℝ (curvVec cov p u v v) u) :
    ∀ (p : M) (T : ℝ) (γ : ℝ → M),
      Submission.GeodesicLoop.IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T := by
  intro p T γ hloop
  have h1 : 2 * (Real.pi / Real.sqrt K) ≤ T :=
    Submission.GeodesicLoop.IsGeodesicLoopAt.two_mul_le_injAtLeast (I := I) (cov := cov) hmet htor
      hloop (Submission.InjRadius.injAtLeast_of_injAllAtLeast (I := I) hmet
        (injAllAtLeast_pi_div_sqrt_even (I := I) (cov := cov) hmet htor hEven hK hcurv hpinch) p)
  calc 2 * Real.pi / Real.sqrt K = 2 * (Real.pi / Real.sqrt K) := by ring
    _ ≤ T := h1

/-- **The even-dimensional half of `Submission.XuReduction.PinchedLoopLengthLowerBound`** (the
pinned Klingenberg length bound `sec ∈ [K/4,K]` for simply connected even-dimensional manifolds). -/
theorem pinchedLoopLengthLowerBound_even
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] [SimplyConnectedSpace M]
    (hEven : Even (Module.finrank ℝ E))
    {K : ℝ} (hK : 0 < K) (hcurv : Submission.RauchK.CurvLe cov K) :
    Submission.XuReduction.PinchedLoopLengthLowerBound (I := I) (cov := cov) hmet K :=
  fun hpinch => loopLengthLowerBound_even (I := I) (cov := cov) hmet htor hEven hK hcurv hpinch

/-- **The even-dimensional diameter estimate `(K2)`.**  Klingenberg's diameter estimate in even
dimensions: a compact, simply connected, even-dimensional manifold with `K/4 ≤ sec ≤ K` (`0 < K < 4`)
has a pair of points at distance `> π/2`.

This is `Submission.KlingenbergXu.diameter_gt_half_pi_of_klingenberg_loop`, whose two inputs are the
proved Klingenberg–Xu step (`Submission.XuReduction.klingenbergLoopStep`) and the even-dimensional
length bound `loopLengthLowerBound_even` above. -/
theorem diameter_gt_half_pi_even
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M] [SimplyConnectedSpace M]
    (hEven : Even (Module.finrank ℝ E))
    {K : ℝ} (hK : 0 < K) (hK4 : K < 4) (hcurv : Submission.RauchK.CurvLe cov K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 ≤ inner ℝ (curvVec cov p u v v) u) :
    ∃ p q : M, ENNReal.ofReal (Real.pi / 2) < Manifold.riemannianEDist I p q :=
  Submission.KlingenbergXu.diameter_gt_half_pi_of_klingenberg_loop (I := I) (cov := cov) hmet htor
    hK hK4 hcurv
    (fun p m hm hinj hmax hcon u v huv hu hv hG =>
      Submission.XuReduction.klingenbergLoopStep (I := I) (cov := cov) hmet htor hcurv hK
        p hm hinj hmax hcon u v huv hu hv hG)
    (fun p T γ hloop =>
      loopLengthLowerBound_even (I := I) (cov := cov) hmet htor hEven hK hcurv hpinch p T γ hloop)

end

end Work.EvenBound
