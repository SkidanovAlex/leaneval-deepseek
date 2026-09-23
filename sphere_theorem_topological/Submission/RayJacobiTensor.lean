import Submission.GeoChartCurve
import Submission.RauchGen

import Submission.GeoChartCurve
import Submission.RauchGen

/-!
# The Jacobi system along a `GExp`-ray in a *prescribed* chart

`Submission.ChartGeoAt.exists_jacobiSystemOn` produces the Jacobi tensor `(Y, U)` along a **chart
geodesic**; `Submission.GeoChartCurve.hasChartGeodesicOn_GExp` packages a `GExp`-ray as a chart
geodesic in a prescribed chart.  This module is the one-line consequence: the Jacobi system along a
`GExp`-ray in a prescribed chart, for an arbitrary time interval `[0, L]`.

This is step 1 of Roadmap §95.6: with it, the Jacobi *columns* `s ↦ Y s a` are available together
with their derivatives and the chart Jacobi equation
(`Submission.RauchGen.JData.jacobiEquation_col_Ioo`), which is what
`Submission.IndexCorner2.eqOn_zero_of_minimising_chart` consumes.  The remaining steps are the
`IsJacobiAt` bridge for the columns and the minimisation argument.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.ChartCurv
open Submission.ChartConnection
open Submission.ChartGeoAt
open Submission.RauchGlobal
open Submission.Jacobi
open Submission.JacobiVec
open Submission.JacobiTensor
open Submission.JacobiGen
open Submission.Curvature
open Submission.CurvatureVec
open Submission.CurvatureSym
open Submission.IndexForm
open Submission.RauchGen
open Submission.Gauss
open Submission.GeoChartCurve

namespace Submission.RayJT

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

/-- **The Jacobi system along a `GExp`-ray in a prescribed chart.** -/
theorem exists_jacobiSystem_GExp (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (x₀ : M) {p : M} {ξ : TangentSpace I p} (hξ : ξ ≠ 0) {L : ℝ} (hL : 0 < L)
    (hsrc : ∀ s ∈ Icc (-1:ℝ) (L + 1),
      GExp (cov := cov) hmet p (s • ξ) ∈ (chartAt H x₀).source) :
    ∃ Y U : ℝ → E →L[ℝ] E, Y 0 = 0 ∧ U 0 = 1 ∧
      (∀ t ∈ Icc (0:ℝ) L, HasDerivAt Y (U t
        - (gammaOp (cov := cov) x₀ (fun s : ℝ => (extChartAt I x₀)
            (GExp (cov := cov) hmet p (s • ξ)))
            (fun s : ℝ => deriv (fun r : ℝ => (extChartAt I x₀)
              (GExp (cov := cov) hmet p (r • ξ))) s) t).comp (Y t)) t) ∧
      (∀ t ∈ Icc (0:ℝ) L, HasDerivAt U
        (-((gammaOp (cov := cov) x₀ (fun s : ℝ => (extChartAt I x₀)
              (GExp (cov := cov) hmet p (s • ξ)))
              (fun s : ℝ => deriv (fun r : ℝ => (extChartAt I x₀)
                (GExp (cov := cov) hmet p (r • ξ))) s) t).comp (U t))
          - (curvOp (cov := cov) x₀ (fun s : ℝ => (extChartAt I x₀)
              (GExp (cov := cov) hmet p (s • ξ)))
              (fun s : ℝ => deriv (fun r : ℝ => (extChartAt I x₀)
                (GExp (cov := cov) hmet p (r • ξ))) s) t).comp (Y t)) t) := by
  have h0 : (0:ℝ) ∈ Ioo (-1:ℝ) (L + 1) := ⟨by norm_num, by linarith⟩
  have hsrc' : ∀ s ∈ Ioo (-1:ℝ) (L + 1),
      GExp (cov := cov) hmet p ((0 + s) • ξ) ∈ (chartAt H x₀).source := by
    intro s hs
    rw [zero_add]
    exact hsrc s ⟨hs.1.le, hs.2.le⟩
  have hgeo := hasChartGeodesicOn_GExp (cov := cov) hmet x₀ hξ (t₀ := 0) h0 hsrc'
  have habt : Icc (0:ℝ) L ⊆ Ioo (-1:ℝ) (L + 1) := fun s hs => ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨Y, U, hY, hU, hYode, hUode⟩ :=
    Submission.ChartGeoAt.exists_jacobiSystemOn (cov := cov) htor hgeo hL habt ⟨le_refl 0, hL.le⟩
  have hu : (fun s : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p ((0 + s) • ξ)))
      = (fun s : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (s • ξ))) := by
    funext s; rw [zero_add]
  have hw : (fun s : ℝ => deriv (fun r : ℝ => (extChartAt I x₀)
        (GExp (cov := cov) hmet p ((0 + r) • ξ))) s)
      = (fun s : ℝ => deriv (fun r : ℝ => (extChartAt I x₀)
        (GExp (cov := cov) hmet p (r • ξ))) s) := by
    have hf : (fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p ((0 + r) • ξ)))
        = (fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (r • ξ))) := by
      funext r; rw [zero_add]
    rw [hf]
  refine ⟨Y, U, hY, hU, ?_, ?_⟩
  · intro t ht
    have h := hYode t ht
    rw [hu] at h
    exact h
  · intro t ht
    have h := hUode t ht
    rw [hu] at h
    exact h

/-! ## The Jacobi columns are Jacobi fields` -/

/-- The chart image of a `GExp`-ray. -/
abbrev rayU {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (x₀ p : M) (ξ : TangentSpace I p) : ℝ → E :=
  fun s => (extChartAt I x₀) (GExp (cov := cov) hmet p (s • ξ))

/-- The chart velocity of a `GExp`-ray. -/
abbrev rayW {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (x₀ p : M) (ξ : TangentSpace I p) : ℝ → E :=
  deriv (rayU hmet x₀ p ξ)

/-- **The columns of the Jacobi tensor along a `GExp`-ray are Jacobi fields** in the sense of
`Submission.RauchGlobal.IsJacobiAt`. -/
theorem isJacobiAt_rayCol (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (x₀ : M) {p : M} {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) {L : ℝ} (hL : 0 < L)
    (hsrc : ∀ s ∈ Icc (-1:ℝ) (L + 1),
      GExp (cov := cov) hmet p (s • ξ) ∈ (chartAt H x₀).source)
    {Y U : ℝ → E →L[ℝ] E} {a : E} {s₀ : ℝ} (hs₀ : s₀ ∈ Icc (0:ℝ) L)
    (hYode : ∀ t ∈ Ioo (-1:ℝ) (L + 1), HasDerivAt Y
      (U t - (gammaOp (cov := cov) x₀ (rayU hmet x₀ p ξ) (rayW hmet x₀ p ξ) t).comp (Y t)) t)
    (hUode : ∀ t ∈ Ioo (-1:ℝ) (L + 1), HasDerivAt U
      (-((gammaOp (cov := cov) x₀ (rayU hmet x₀ p ξ) (rayW hmet x₀ p ξ) t).comp (U t))
        - (curvOp (cov := cov) x₀ (rayU hmet x₀ p ξ) (rayW hmet x₀ p ξ) t).comp (Y t)) t) :
    IsJacobiAt cov (fun s : ℝ => GExp (cov := cov) hmet p (s • ξ))
      (fun s : ℝ => frameVector (I := I) x₀ (GExp (cov := cov) hmet p (s • ξ)) (Y s a)) s₀ := by
  have hs₀I : s₀ ∈ Ioo (-1:ℝ) (L + 1) := ⟨by linarith [hs₀.1], by linarith [hs₀.2]⟩
  have hEv : ∀ᶠ s : ℝ in 𝓝 s₀, s ∈ Ioo (-1:ℝ) (L + 1) :=
    isOpen_Ioo.mem_nhds hs₀I
  refine ⟨x₀, rayU hmet x₀ p ξ, rayW hmet x₀ p ξ, (fun s : ℝ => Y s a),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hEv] with s hs
    exact (extChartAt I x₀).map_source (by
      rw [extChartAt_source]
      exact hsrc s ⟨hs.1.le, hs.2.le⟩)
  · filter_upwards [hEv] with s hs
    have h := hasDerivAt_chartCurve_GExp (cov := cov) hmet x₀ (by
      intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ) s
      (hsrc s ⟨hs.1.le, hs.2.le⟩)
    simpa only [rayU, rayW] using h
  · filter_upwards [hEv] with s hs
    rw [rayU]
    exact (PartialEquiv.left_inv (extChartAt I x₀) (by
      rw [extChartAt_source]
      exact hsrc s ⟨hs.1.le, hs.2.le⟩)).symm
  · filter_upwards with s
    rfl
  · filter_upwards [hEv] with s hs
    have h := chartGram_chartCurve_GExp (cov := cov) hmet x₀ hξ s (hsrc s ⟨hs.1.le, hs.2.le⟩)
    simpa only [rayU, rayW] using h
  · filter_upwards [hEv] with s hs
    have h := Submission.JacobiTensor.hasDerivAt_jacobiCol (cov := cov) (x₀ := x₀)
      (u := rayU hmet x₀ p ξ) (w := rayW hmet x₀ p ξ) (a := a) (hYode s hs)
    rw [h.deriv]
    exact h
  · filter_upwards [hEv] with s hs
    have h := Submission.RauchGen.JData.hasDerivAt_chartCovDeriv_jacobiCol_Ioo (cov := cov) (x₀ := x₀)
      (u := rayU hmet x₀ p ξ) (w := rayW hmet x₀ p ξ) (Y := Y) (U := U) (a := a)
      (A := -1) (B := L + 1) hs hYode hUode
    rw [h.deriv]
    exact h
  · filter_upwards [hEv] with s hs
    exact Submission.RauchGen.JData.jacobiEquation_col_Ioo (cov := cov) (x₀ := x₀)
      (u := rayU hmet x₀ p ξ) (w := rayW hmet x₀ p ξ) (Y := Y) (U := U) (a := a)
      (A := -1) (B := L + 1) hs hYode hUode
      (by
        rw [rayU]
        exact mem_source_chartCurve (I := I) (u := fun r : ℝ =>
          (extChartAt I x₀) (GExp (cov := cov) hmet p (r • ξ))) (t := s)
          ((extChartAt I x₀).map_source (by
            rw [extChartAt_source]; exact hsrc s ⟨hs.1.le, hs.2.le⟩)))

end

end Submission.RayJT

