import Submission.Klingenberg
import Submission.InjRadiusCut

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The interface between Klingenberg's estimate and the diameter bound

`Submission.Klingenberg.KlingenbergBound cov` is stated in **diameter form**: some pair of points is
at distance `> π/2`.  The classical estimates, however, produce an **injectivity-radius** statement
(`inj(p) > π/2` for some `p`), or equivalently — by
`Submission.InjRadiusCut.injAtLeast_iff_forall_cutTime_le` — a statement about **cut times**
(`cutTime p ξ > π/2` for every unit direction `ξ` at some `p`).

This file records the (elementary) bridges:

* `exists_edist_gt_half_pi_of_injAtLeast`: `InjAtLeast hmet p r` with `π/2 < r` produces a point `q`
  at distance `> π/2` from `p` (the radial ray of length `r`, which is minimising up to the
  injectivity radius);
* `exists_edist_gt_half_pi_of_cutTime`: if every unit direction at `p` has cut time `> π/2`, then
  some pair is at distance `> π/2`.

So the remaining gap of `KlingenbergBound` is the *cut-time / injectivity-radius* estimate, which is
the classical statement decomposed by the structure theorem
`inj(p) = min{conj(p), ½ ℓ(p)}` — see `Submission/Roadmap.lean` §78. -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.HopfRinow
open Submission.InjRadius
open Submission.CutTime
open Submission.InjRadiusCut

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.KlingenbergStep

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable [PathConnectedSpace M] [RegularSpace M]

/-- **A positive injectivity radius gives a far-away point.**  If `InjAtLeast hmet p r` and
`π/2 < r`, then there is a point at distance `> π/2` from `p`: the ray in any unit direction, run up
to the injectivity radius, is minimising. -/
theorem exists_edist_gt_half_pi_of_injAtLeast
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {r : ℝ} (hr : Real.pi / 2 < r) (hinj : InjAtLeast hmet p r) :
    ∃ q : M, ENNReal.ofReal (Real.pi / 2) < Manifold.riemannianEDist I p q := by
  classical
  haveI : Nontrivial (TangentSpace I p) := ‹Nontrivial E›
  obtain ⟨v, hv⟩ := exists_ne (0 : TangentSpace I p)
  set ξ : TangentSpace I p := unitOf v hv with hξdef
  have hξ : ‖ξ‖ = 1 := by
    rw [hξdef]
    exact unitOf_norm v hv
  refine ⟨GExp (cov := cov) hmet p (r • ξ), ?_⟩
  rw [edist_GExp_smul_eq_of_injAtLeast (cov := cov) hmet htor hinj hξ
    (by linarith [Real.pi_pos] : (0 : ℝ) ≤ r) le_rfl]
  exact ENNReal.ofReal_lt_ofReal_iff' (p := Real.pi / 2) (q := r) |>.mpr
    ⟨hr, lt_trans (by positivity) hr⟩

/-- **The cut-time form of the estimate implies the diameter bound.**  If some point `p` has all cut
times `≥ r` with `r > π/2`, then some pair of points is at distance `> π/2`.

This is the form in which the structure theorem (`inj(p) = min{conj(p), ½ ℓ(p)}`) delivers
Klingenberg's estimate — with `r = π/√K > π/2` for `sec ≤ K < 4` — so it is the interface used by
the assembly. -/
theorem exists_edist_gt_half_pi_of_cutTime
    (hmet : LeanEval.Geometry.SphereTheorem.IsMetricCompatible cov) (htor : cov.torsion = 0)
    {p : M} {r : ℝ} (hr : Real.pi / 2 < r)
    (h : ∀ ξ : TangentSpace I p, ‖ξ‖ = 1 → r ≤ cutTime (I := I) hmet p ξ) :
    ∃ q : M, ENNReal.ofReal (Real.pi / 2) < Manifold.riemannianEDist I p q :=
  exists_edist_gt_half_pi_of_injAtLeast (cov := cov) hmet htor hr
    ((injAtLeast_iff_forall_cutTime_le (I := I) (cov := cov) hmet htor).mpr h)

end

end Submission.KlingenbergStep
