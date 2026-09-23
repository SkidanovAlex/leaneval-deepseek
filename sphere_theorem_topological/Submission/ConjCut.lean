import Submission.SegmentDomain
import Submission.RayConj
import Submission.ConjRadius
import Submission.RauchK

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
open Submission.RauchK
open Submission.ConjRadius

namespace Submission.ConjCut

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

/-- **The classical inequality `σ ≤ κ` (cut time ≤ conjugate time), as a named `Prop`.**

For every point `p`, every *unit* direction `ξ` and every **conjugate time** `t` of the ray
`s ↦ GExp p (s • ξ)` — i.e. `t > 0` and a Jacobi field along the ray, not identically zero, vanishing
at `0` and at `t` (`Submission.ConjRadius.IsConjugateTime`) — the **cut time** of `ξ` is at most `t`:

`cutTime p ξ ≤ t`.

Equivalently: *there is no conjugate point strictly inside the tangential segment domain* `D̃_p`
(`Submission.SegmentDomain.segmentDomain`), because `D̃_p` is exactly the set of vectors whose norm is
strictly below the cut time of their direction.  This is the classical input that upgrades the
injectivity of `GExp p` on `D̃_p` (proved in `Submission/SegmentDomain.lean`) to a **local
diffeomorphism**, and hence — with `Commons.Topology.exists_lift_of_injective_open_nonempty` — to the
diffeomorphism `D̃_p ≅ M ∖ C_p` used in the unique-lifting step of Klingenberg's lemma.  See
`Submission/Roadmap.lean` §91 for the classical proof and the inventory of its pieces. -/
def CutConjInequality (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) : Prop :=
  ∀ (p : M) (ξ : TangentSpace I p), ‖ξ‖ = 1 → ∀ t : ℝ,
    ConjRadius.IsConjugateTime cov (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ)) t →
    Submission.CutTime.cutTime (I := I) hmet p ξ ≤ t

/-- **The κ-side input**: a *singular* differential of `GExp p` at `v ≠ 0` produces a **conjugate
time** at `‖v‖` along the ray of `v`.  This is one half of the classical equivalence "`v` is conjugate
to `p` ⟺ `d exp_p` is singular at `v`"; the proof is the Jacobi-field construction carried out inside
the proof of `RayConj.pi_div_sqrt_le_of_singular_mfderiv` (kernel vector → Jacobi field `J` with
`J 0 = J ‖v‖ = 0`), which currently only records the resulting *length* bound. -/
def SingularImpConjTime (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) : Prop :=
  ∀ (p : M) {v : TangentSpace I p} (hv : v ≠ 0),
    ¬ (mfderiv 𝓘(ℝ, E) I
        (fun u : E => GExp (cov := cov) hmet p (show TangentSpace I p from u))
        (show E from v)).IsInvertible →
    ConjRadius.IsConjugateTime cov (fun s : ℝ => GExp (cov := cov) hmet p (s • unitOf v hv)) ‖v‖

/-- **No conjugate time below `π/√K`** (Rauch's conjugate-radius bound): the `π/√K ≤ κ` half of
`σ ≤ κ`, which is what the library already has. -/
theorem not_isConjugateTime_of_lt_pi_div_sqrt (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) {K : ℝ} (hK : CurvLe cov K) (hKpos : 0 < K)
    {γ : ℝ → M} {t : ℝ} (ht : t < Real.pi / Real.sqrt K) :
    ¬ ConjRadius.IsConjugateTime cov γ t :=
  fun h => absurd (pi_div_sqrt_le_of_isConjugateTime (cov := cov)
    ‹ContMDiffCovariantDerivative cov ∞› hmet hK hKpos htor h) (not_le.mpr ht)

/-- **The differential of `GExp p` is invertible below the conjugate radius** — the contrapositive of
the singular-differential bound of `Submission.RayConj`. -/
theorem isInvertible_mfderiv_GExp_of_norm_lt_pi_div_sqrt (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) {K : ℝ} (hK : CurvLe cov K) (hKpos : 0 < K)
    {p : M} {v : TangentSpace I p} (hv : v ≠ 0) (hvK : ‖v‖ < Real.pi / Real.sqrt K) :
    (mfderiv 𝓘(ℝ, E) I
      (fun u : E => GExp (cov := cov) hmet p (show TangentSpace I p from u))
      (show E from v)).IsInvertible := by
  by_contra hsing
  exact absurd (Submission.RayConj.pi_div_sqrt_le_of_singular_mfderiv (cov := cov) htor hmet hK
    hKpos p v hv hsing) (not_le.mpr hvK)

/-- **Payoff of the two inputs `σ ≤ κ` and the κ-side bridge**: on the tangential segment domain,
`GExp p` has invertible differential at every non-zero vector (so it is a *local diffeomorphism*
there, which together with `SegmentDomain.injOn_GExp_segmentDomain` makes it a diffeomorphism onto its
image and yields the unique lifting of Klingenberg's lemma). -/
theorem isInvertible_mfderiv_of_mem_segmentDomain (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0)
    (hbridge : SingularImpConjTime (I := I) hmet htor)
    (hcc : CutConjInequality (I := I) hmet htor)
    {p : M} {v : TangentSpace I p}
    (hv : v ∈ Submission.SegmentDomain.segmentDomain hmet p) (hv0 : v ≠ 0) :
    (mfderiv 𝓘(ℝ, E) I
      (fun u : E => GExp (cov := cov) hmet p (show TangentSpace I p from u))
      (show E from v)).IsInvertible := by
  by_contra hsing
  have hconj := hbridge p hv0 hsing
  have hle := hcc p (unitOf v hv0) (unitOf_norm v hv0) ‖v‖ hconj
  -- `v ∈ D̃_p` says `‖v‖` is strictly below the cut time
  rcases (Submission.SegmentDomain.mem_segmentDomain_iff (I := I) hmet p v).mp hv with h0 | ⟨hne, hlt⟩
  · exact hv0 h0
  · exact absurd hle (not_le.mpr hlt)

end

end Submission.ConjCut
