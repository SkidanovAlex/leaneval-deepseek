import Submission.ExpBound2
import Submission.HopfRinow2

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The backward point of a chosen geodesic is an exponential image

`HopfRinow2.GExp_neg_smul_curveVelocity_geodCurve` says that the global exponential map at a point
`Gp t` of a chosen geodesic segment in the direction `-Gp'(t)` runs back along `Gp`.  Combined with
`GlobalExp.exists_pos_GExp_eq_expMap` (which identifies `GExp` with the chart exponential map for
small velocities) this gives the *chart* form: the backward point `Gp (t - s)` is the exponential
image at `Gp t` of the vector `-s • Gp'(t)`.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartBounds
open Submission.GeodesicSpeed
open Submission.Length
open Submission.Minimal
open Submission.Gauss
open Submission.GlobalExp
open Submission.Distance

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

namespace Submission.GeoBack

noncomputable section

/-- **The backward point is the exponential image of `-s • Gp'(t)`.** -/
theorem geodCurve_sub_eq_expMap [Nontrivial E] [CompactSpace M] (hmet : IsMetricCompatible cov)
    {q : M} {ξ : TangentSpace I q} (hξ : ‖ξ‖ = 1) {T : ℝ} (hT : 0 ≤ T)
    {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ s : ℝ, 0 ≤ s → s < ρ → s ≤ t →
      (geodCurve (cov := cov) hmet T hT q ξ hξ) (t - s)
        = expMap cov ((geodCurve (cov := cov) hmet T hT q ξ hξ) t)
            ((-s) • (show E from curveVelocity (I := I)
              (geodCurve (cov := cov) hmet T hT q ξ hξ) t)) := by
  set Gp : ℝ → M := geodCurve (cov := cov) hmet T hT q ξ hξ with hGpdef
  have hspec := geodCurve_spec (cov := cov) hmet T hT q ξ hξ
  have hsp : ‖curveVelocity (I := I) Gp t‖ = 1 := hspec.2.2.2.2 t
    ⟨by linarith [geodDelta_pos (cov := cov) hmet], by linarith [geodDelta_pos (cov := cov) hmet]⟩
  obtain ⟨ρ, hρ, hGe⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet (Gp t)
  refine ⟨ρ, hρ, fun s hs0 hsρ hst => ?_⟩
  have hb := HopfRinow.GExp_neg_smul_curveVelocity_geodCurve (cov := cov) hmet q hξ hT ht0 htT hs0 hst
  rw [← hGpdef] at hb
  rw [← hb]
  refine hGe ((-s) • curveVelocity (I := I) Gp t) ?_
  rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg hs0, hsp, mul_one]
  exact hsρ

end

end Submission.GeoBack
