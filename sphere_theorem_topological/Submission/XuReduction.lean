import Submission.XuTrap
import Submission.KlingenbergXu

/-!
# Xu's Theorem B, installed: the Klingenberg–Xu step is now **proved**

`Submission.XuTrap.xuCornerExcluded` proves **Xu's Theorem B** (arXiv:1401.5549), the sharp form of
Klingenberg's lemma: *at the closest cut point, a minimal geodesic free of conjugate points cannot
meet another minimal geodesic with a genuine corner*.  This file exposes its consequences:

* **`klingenbergLoopStep`** — the **Klingenberg–Xu step** `KlingenbergLoopStep hmet K` is now a
  *theorem*, with no hypothesis beyond `CurvLe cov K` and `0 < K` (the non-conjugacy hypothesis of
  Xu's Theorem B is supplied by Rauch, `ConjCut.not_isConjugateTime_of_lt_pi_div_sqrt`, exactly on
  the range `m < π/√K` in which the step is applied).
* **`diameter_gt_half_pi_of_loopLengthLowerBound`** — therefore `(K2)` (`KlingenbergBound`) is now
  reduced to the **single** classical input `LoopLengthLowerBound` (Klingenberg 1961).

## The counterexample to the unpinched form of `LoopLengthLowerBound`

`Submission.KlingenbergXu.LoopLengthLowerBound hmet K` asserts

> every geodesic loop at every point has length `≥ 2π/√K`, under the sole hypothesis `sec ≤ K`.

**That statement is false as written**, because it carries no *lower* curvature bound.  The
**Berger spheres** `(S³, σ₁² + σ₂² + τ²σ₃²)` refute it: there `sec ∈ [τ², 4 - 3τ²]`, the Hopf fibres
are closed geodesics of length `2πτ`, and `τ = 1` gives the round `S³` (`sec ≡ 1`, fibres of length
`2π` ✓).  For `τ² = 0.3` one has `sec ≤ K := 3.1 < 4`, so `K` is a legitimate upper bound in the
sense of `CurvLevel`/`CurvLe`, but

`2πτ = 2π·0.5477… ≈ 3.4416 < 3.5685… = 2π/√3.1 = 2π/√K`,

so the asserted bound fails (the fibres *are* closed geodesics of that length, so no knowledge of
the *shortest* closed geodesic is needed).  Note `sec ≥ K/4` also fails here (`inf sec = 0.3 < 0.775`),
which is what the classical theorem requires: the correct statement is

> `sec ∈ [K/4, K]` and `M` simply connected ⟹ every geodesic loop has length `≥ 2π/√K`,

i.e. the pinching hypothesis is essential.  `PinchedLoopLengthLowerBound` below is that corrected
statement, and `loopLengthLowerBound_of_pinched` shows that it *implies* the form used by the
reduction — so the reduction theorems of `Submission.KlingenbergXu` remain valid, they simply must
be instantiated under the pinch.  In the application to `(K2)` the ambient hypothesis is
`1 ≤ sec ≤ K` with `K ≥ 1`, so `sec ≥ K/4` holds automatically.

## What is still missing

`PinchedLoopLengthLowerBound` is **Klingenberg 1961** (see `Submission/Roadmap.lean` §§76, 80, 107):
the even-dimensional case follows from Berger's holonomy argument (the parallel transport of the
normal bundle around a closed geodesic lies in `SO(n-1)`, `n-1` odd, hence fixes a vector, giving a
variation with strictly negative second variation), while the **odd**-dimensional case needs the
Morse theory of the free loop space (Palais–Smale condition C + minimax).  With `XuStep`/`XuTrap`
now settled, this is the *only* remaining gap of `Submission.Klingenberg.KlingenbergBound`, and
hence of `Submission.sphere_theorem`.
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
open Submission.GlobalExp
open Submission.InjRadius
open Submission.GeodesicLoop
open Submission.CurvatureVec

namespace Submission.XuReduction

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **THE KLINGENBERG–XU STEP IS PROVED.**  Xu's Theorem B (`Submission.XuTrap.xuCornerExcluded`)
turns the cut-point dichotomy `CutStep3.exists_two_minimising_or_not_locallyInjective` into the
production of a *value-closed geodesic loop* of length `≤ 2m`: at the closest cut point there is no
genuine corner.  The only inputs are `sec ≤ K` (Rauch's non-conjugacy below `π/√K`) and `0 < K`. -/
theorem klingenbergLoopStep (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hK : Submission.RauchK.CurvLe cov K) (hKpos : 0 < K) :
    Submission.KlingenbergXu.KlingenbergLoopStep (I := I) (cov := cov) hmet K :=
  Submission.KlingenbergXu.klingenbergLoopStep_of_xuCornerExcluded (cov := cov) hmet htor
    hK hKpos (Submission.XuTrap.xuCornerExcluded (cov := cov) hmet htor)

/-- **`(K2)` from the Klingenberg length bound alone.**  Since the Klingenberg–Xu step is now a
theorem, the diameter estimate `(K2)` needs only the single classical input
`LoopLengthLowerBound` — Klingenberg 1961. -/
theorem diameter_gt_half_pi_of_loopLengthLowerBound (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hK : 0 < K) (hK4 : K < 4) (hcurv : Submission.RauchK.CurvLe cov K)
    (hdeep : Submission.KlingenbergXu.LoopLengthLowerBound (I := I) (cov := cov) hmet K) :
    ∃ p q : M, ENNReal.ofReal (Real.pi / 2) < Manifold.riemannianEDist I p q :=
  Submission.KlingenbergXu.diameter_gt_half_pi_of_xu (cov := cov) hmet htor hK hK4 hcurv
    (klingenbergLoopStep (cov := cov) hmet htor hcurv hK) hdeep

/-- **The classical Klingenberg length bound, *with* the pinching hypothesis.**

This is the corrected form of `Submission.KlingenbergXu.LoopLengthLowerBound` (see the module
docstring for the Berger-sphere counterexample to the unpinched form): for a metric with
`sec ∈ [K/4, K]`, every geodesic loop has length `≥ 2π/√K`.  Klingenberg 1961. -/
def PinchedLoopLengthLowerBound (hmet : IsMetricCompatible cov) (K : ℝ) : Prop :=
  (∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 ≤ inner ℝ (curvVec cov p u v v) u) →
    ∀ (p : M) (T : ℝ) (γ : ℝ → M),
      Submission.GeodesicLoop.IsGeodesicLoopAt (I := I) (cov := cov) hmet p T γ →
      2 * Real.pi / Real.sqrt K ≤ T

/-- The pinched statement implies the form used by the reduction (`LoopLengthLowerBound`), since the
latter simply forgets the pinching hypothesis. -/
theorem loopLengthLowerBound_of_pinched (hmet : IsMetricCompatible cov) {K : ℝ}
    (h : PinchedLoopLengthLowerBound (I := I) (cov := cov) hmet K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 ≤ inner ℝ (curvVec cov p u v v) u) :
    Submission.KlingenbergXu.LoopLengthLowerBound (I := I) (cov := cov) hmet K :=
  h hpinch

/-- **`(K2)` from the classical (pinched) Klingenberg length bound.** -/
theorem diameter_gt_half_pi_of_pinchedLoopLengthLowerBound (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) [PathConnectedSpace M] [RegularSpace M]
    {K : ℝ} (hK : 0 < K) (hK4 : K < 4) (hcurv : Submission.RauchK.CurvLe cov K)
    (hpinch : ∀ (p : M) (u v : TangentSpace I p), ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      K / 4 ≤ inner ℝ (curvVec cov p u v v) u)
    (hdeep : PinchedLoopLengthLowerBound (I := I) (cov := cov) hmet K) :
    ∃ p q : M, ENNReal.ofReal (Real.pi / 2) < Manifold.riemannianEDist I p q :=
  diameter_gt_half_pi_of_loopLengthLowerBound (cov := cov) hmet htor hK hK4 hcurv
    (loopLengthLowerBound_of_pinched (cov := cov) hmet hdeep hpinch)

end

end Submission.XuReduction
