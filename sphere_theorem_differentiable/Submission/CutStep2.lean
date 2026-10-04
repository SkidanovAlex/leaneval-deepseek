import Submission.GExpBoundary
import Submission.CutPoint

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The cut-point step, with the degenerate case isolated

`InjAtLeast hmet p m` says that `F = GExp p` is injective on the ball of radius `m`; if it fails for
every larger radius, the classical cut-point analysis produces **two distinct minimising vectors of
norm `m`** with the same image.

`Submission.CutStep.exists_two_minimising_of_not_injAtLeast` proves this from a *chart-local* model
of `F` (agreement with `expMap` on a ball whose radius dominates `m + 1`).  That hypothesis is not
dischargeable in general: the ball on which `GExp p` agrees with the chart exponential map
`expMap cov p` has a radius governed by the *chart*, which may be much smaller than `inj(p)`.

This file removes that requirement.  The only input beyond `InjAtLeast` and its failure is

* `LocallyInjectiveAtGExp hmet p w` — `F` is injective on some neighbourhood of `w` — for the
  points `w` of the closed ball of radius `m`.

The proof uses two ingredients:

1. **`Submission.GExpBoundary.tendsto_GExp_of_tendsto_of_norm_le`**: `F` is continuous *at* every
   point of the ball, so the limits `u`, `v` of a witness sequence satisfy `F u = F v`; and
2. the observation that a witness sequence whose limit has norm `< m` (or whose two limits agree)
   contradicts `InjAtLeast` together with the local injectivity hypothesis.

What is **not** here is the discharge of `LocallyInjectiveAtGExp`: that is the statement that the
exponential map is a local diffeomorphism at non-conjugate vectors, and it needs the global smooth
structure of `exp` (the geodesic flow).  See `Submission/Roadmap.lean` §74.
-/

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
open Submission.CutWitness
open Submission.CutPoint
open Submission.GExpBoundary

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.CutStep2

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **Local injectivity of the exponential map at a point of the tangent space.**  This is the
"`v` is not a conjugate vector" statement in the form in which the cut-point argument uses it: `F`
is injective on some neighbourhood of `v`. -/
def LocallyInjectiveAtGExp (hmet : IsMetricCompatible cov) (p : M) (v : TangentSpace I p) : Prop :=
  ∃ s : Set (TangentSpace I p), s ∈ 𝓝 v ∧
    ∀ w ∈ s, ∀ w' ∈ s, GExp (cov := cov) hmet p w = GExp (cov := cov) hmet p w' → w = w'

/-- **The cut-point step.**  Let `m` be the injectivity radius at `p` (`InjAtLeast hmet p m`, and
no larger radius), and assume that the exponential map `F = GExp p` is *locally injective* at every
point of the closed ball of radius `m`.  Then there are two **distinct minimising vectors of length
`m`** with the same image. -/
theorem exists_two_minimising_of_not_injAtLeast
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    [PathConnectedSpace M] [RegularSpace M]
    {p : M} {m : ℝ} (hinj : InjAtLeast hmet p m)
    (hfail : ∀ r : ℝ, m < r → ¬ InjAtLeast hmet p r)
    (hloc : ∀ w : TangentSpace I p, ‖w‖ ≤ m → LocallyInjectiveAtGExp (I := I) hmet p w) :
    ∃ u v : TangentSpace I p, u ≠ v ∧
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v ∧
      ‖u‖ = m ∧ ‖v‖ = m ∧
      Manifold.riemannianEDist I p (GExp (cov := cov) hmet p u) = ENNReal.ofReal m := by
  classical
  have hex : ∀ r : ℝ, m < r → ∃ u v : TangentSpace I p, u ≠ v ∧
      GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v ∧ ‖u‖ < r ∧ ‖v‖ < r := by
    intro r hr
    by_contra hcon
    push Not at hcon
    refine hfail r hr (fun u v hu hv hG => ?_)
    by_contra huv
    exact absurd hv (not_lt.mpr (hcon u v huv hG hu))
  obtain ⟨U, V, u, v, hUV, hGU, hbU, hbV, hUtend, hVtend, hu, hv⟩ :=
    exists_tendsto_witness_sequence (cov := cov) hmet hex
  -- continuity at the limits
  have hFu : Tendsto (fun n : ℕ => GExp (cov := cov) hmet p (U n)) atTop
      (𝓝 (GExp (cov := cov) hmet p u)) :=
    tendsto_GExp_of_tendsto_of_norm_le (cov := cov) hmet htor hinj hUtend hu
  have hFv : Tendsto (fun n : ℕ => GExp (cov := cov) hmet p (V n)) atTop
      (𝓝 (GExp (cov := cov) hmet p v)) :=
    tendsto_GExp_of_tendsto_of_norm_le (cov := cov) hmet htor hinj hVtend hv
  have hGuv : GExp (cov := cov) hmet p u = GExp (cov := cov) hmet p v :=
    tendsto_nhds_unique hFu
      (hFv.congr' (Eventually.of_forall fun n => (hGU n).symm))
  -- the limits are distinct, by local injectivity
  have huv : u ≠ v := by
    intro huv'
    obtain ⟨s, hs, hinj_s⟩ := hloc u hu
    have h1 : ∀ᶠ n : ℕ in atTop, U n ∈ s := hUtend.eventually hs
    have hs' : s ∈ 𝓝 v := by rw [← huv']; exact hs
    have h2 : ∀ᶠ n : ℕ in atTop, V n ∈ s := hVtend.eventually hs'
    obtain ⟨n, hn1, hn2⟩ := (h1.and h2).exists
    exact hUV n (hinj_s (U n) hn1 (V n) hn2 (hGU n))
  obtain ⟨h1, h2, h3, -⟩ :=
    norm_eq_and_minimising_of_witness_pair (cov := cov) hmet htor hinj huv hGuv hu hv
  exact ⟨u, v, huv, hGuv, h1, h2, h3⟩

end

end Submission.CutStep2
