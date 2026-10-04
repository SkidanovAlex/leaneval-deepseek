import Submission.Work.OddBound.Defs
import Submission.Work.OddBound.integral_idxAlong_neg_of_shorteningField
import Submission.Work.OddBound.exists_shorter_closed_curve_of_negative_index

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The second-variation shortening engine of the odd case

`Work.OddBound.exists_shorter_closed_curve_of_shorteningField`: along a closed unit-speed geodesic of
length `L` in a manifold with `sec ≥ δ`, a shortening field (periodic, unit, normal, with
`∫₀^L ‖∇V‖² < δ L`) produces **closed** curves of length `< L` near it.

This is `Work.OddBound.integral_idxAlong_neg_of_shorteningField` (the index integral of `V` is
negative) followed by `Work.OddBound.exists_shorter_closed_curve_of_negative_index` (a negative index
integral shortens, by Cauchy--Schwarz on the energy).  It lives in its own module so that both
`Submission.Work.OddBound.OddBound` and `Submission.Work.OddBound.exists_shorter_family_of_rotatingField`
can use it without an import cycle.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open MeasureTheory
open scoped MeasureTheory Interval
open Submission.Geodesic Submission.JacobiGlobal Submission.GlobalExp Submission.Length
open Submission.InjRadius Submission.IndexIntrinsic Submission.CurvatureVec

namespace Work.OddBound

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

/-- **The shortening engine of the odd case.**  Along a closed unit-speed geodesic `γ` of length `L`
in a manifold with `sec ≥ δ`, a shortening field `V` (periodic, unit, normal, with
`∫₀^L ‖∇V‖² < δ L`) produces **closed** curves of length `< L` near `γ`.

This is `Work.OddBound.integral_idxAlong_neg_of_shorteningField` (the index integral of `V` is
negative) followed by `Work.OddBound.exists_shorter_closed_curve_of_negative_index` (a negative index
integral shortens, by Cauchy–Schwarz on the energy).  For a *parallel* field it specialises to
Synge's shortening (`Submission.SyngeShorten.exists_shorter_closed_curve`). -/
theorem exists_shorter_closed_curve_of_shorteningField
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {γ : ℝ → M} (hγsm : ContMDiffOn 𝓘(ℝ) I ∞ γ univ)
    (hgeo : ∀ t : ℝ, IsGeodesicAt (I := I) cov γ t)
    (hne : ∀ t : ℝ, curveVelocity (I := I) γ t ≠ 0)
    {L δ : ℝ} (hL : 0 < L) (hloop : γ L = γ 0)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) L, curveSpeed (I := I) γ t = 1)
    (hδ : 0 < δ) (hV : IsShorteningField cov γ L δ)
    (hcurv : ∀ t ∈ Icc (0 : ℝ) L, ∀ u v : TangentSpace I (γ t), ‖u‖ = 1 → ‖v‖ = 1 →
      inner ℝ u v = 0 → δ ≤ inner ℝ (curvVec cov (γ t) u v v) u) :
    ∃ d : ℝ, 0 < d ∧
      ((∀ᶠ σ in 𝓝[>] (0 : ℝ),
          curveLength (I := I)
            (fun t : ℝ => GExp (cov := cov) hmet (γ t) (σ • (d • hV.field t))) 0 L < L ∧
          GExp (cov := cov) hmet (γ L) (σ • (d • hV.field L))
            = GExp (cov := cov) hmet (γ 0) (σ • (d • hV.field 0))) ∨
        (∀ᶠ σ in 𝓝[<] (0 : ℝ),
          curveLength (I := I)
            (fun t : ℝ => GExp (cov := cov) hmet (γ t) (σ • (d • hV.field t))) 0 L < L ∧
          GExp (cov := cov) hmet (γ L) (σ • (d • hV.field L))
            = GExp (cov := cov) hmet (γ 0) (σ • (d • hV.field 0)))) := by
  have h1 : ∫ t in (0 : ℝ)..L, idxAlong (cov := cov) γ hV.field (covAlong cov hV.field) t < 0 :=
    integral_idxAlong_neg_of_shorteningField (cov := cov) hmet htor hL
      (hγsm.mono (Set.subset_univ _)) (fun t _ => hne t) hspeed hδ hV hcurv
  exact exists_shorter_closed_curve_of_negative_index (cov := cov) hmet htor hγsm hgeo hne hL
    hspeed (fun s hs => hV.smooth s (by simpa using hs)) hV.periodic hloop h1

end

end Work.OddBound
