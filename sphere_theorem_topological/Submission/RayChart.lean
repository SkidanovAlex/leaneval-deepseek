import Submission.JacobiLinear
import Submission.LensLoop
import Submission.GExpRayZero
import Submission.GExpVelocity

/-!
# The chart of a geodesic around an arbitrary time (the first chart interval of step (ii))

Step (ii) of the globalisation programme (§83 of the roadmap) instantiates the extracted
V1/V2 computation `VariationJacobi.variationField_satisfies_jacobiSys` on the *chart intervals* of
a finite cover of a geodesic ray.  The raw material for that is the classical local statement:

> the chart coordinates of a geodesic satisfy the chart geodesic equation in a neighbourhood of
> **any** time `t₀` (not just near the base point).

The library has this as `GeodesicGlobal.chartODE_of_isGeodesic`, but it needs a *globally smooth*
velocity section agreeing with the velocity near `t₀`; this file supplies that section for the rays
of the exponential map (`CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity`, with the
non-vanishing of the velocity from `norm_curveVelocity_GExp_smul_ne` and
`GExpVelocity.curveVelocity_GExp_smul_zero`) and packages the result as
`exists_pos_chartODE_of_isGeodesic`.

## Contents

* `curveVelocity_GExp_ne_zero` — the velocity of a `GExp`-ray never vanishes (in the
  `s`-parametrisation, for a non-zero direction vector);
* **`exists_pos_chartODE_of_isGeodesic`** — the chart-interval datum at an arbitrary time `t₀` for a
  geodesic with non-vanishing velocity: there is `δ > 0` such that the chart coordinate curve
  `s ↦ (extChartAt I (γ t₀)) (γ s)` and its derivative satisfy the geodesic equation on
  `Ioo (t₀ - δ) (t₀ + δ)`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.GlobalExp
open Submission.CurveField
open Submission.LensLoop

namespace Submission.RayChart

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

/-- **The velocity of a `GExp`-ray never vanishes** (for `v ≠ 0`, in the `s`-parametrisation). -/
theorem curveVelocity_GExp_ne_zero (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) (s : ℝ) :
    curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet x (r • v)) s ≠ 0 := by
  rcases eq_or_ne s 0 with h0 | h0
  · subst h0
    rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet x hv]
    exact hv
  · intro hzero
    have h := Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet x hv h0
    rw [hzero, norm_zero] at h
    exact (norm_ne_zero_iff.mpr hv) h.symm

/-- **The chart interval of a geodesic at an arbitrary time.**  Let `γ` be a geodesic (smooth on all
of `ℝ`, geodesic at every time) whose velocity at `t₀` is non-zero.  Then, in the chart centred at
`γ t₀`, the coordinate curve `s ↦ (extChartAt I (γ t₀)) (γ s)` and its derivative solve the chart
geodesic equation on a neighbourhood `Ioo (t₀ - δ) (t₀ + δ)` of `t₀`. -/
theorem exists_pos_chartODE_of_isGeodesic {γ : ℝ → M} {t₀ : ℝ}
    (hsm : ContMDiffOn 𝓘(ℝ) I ∞ γ univ) (hgeo : ∀ t : ℝ, IsGeodesicAt cov γ t)
    (hne : curveVelocity (I := I) γ t₀ ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ s ∈ Ioo (t₀ - δ) (t₀ + δ),
        HasDerivAt (fun t : ℝ => (extChartAt I (γ t₀)) (γ t))
          (deriv (fun t : ℝ => (extChartAt I (γ t₀)) (γ t)) s) s) ∧
      (∀ s ∈ Ioo (t₀ - δ) (t₀ + δ),
        HasDerivAt (deriv (fun t : ℝ => (extChartAt I (γ t₀)) (γ t)))
          (chartGeodesicVectorField cov (γ t₀) ((extChartAt I (γ t₀)) (γ s),
            deriv (fun t : ℝ => (extChartAt I (γ t₀)) (γ t)) s)) s) := by
  have hsrc : γ t₀ ∈ (chartAt H (γ t₀)).source := mem_chart_source H (γ t₀)
  obtain ⟨Z, hZ, hZeq⟩ :=
    exists_contMDiff_section_eventuallyEq_curveVelocity (I := I) (V := univ) isOpen_univ
      (Set.mem_univ t₀) hsm hne
  obtain ⟨δ, hδ, -, -, hud, hwd⟩ :=
    Submission.GeodesicGlobal.chartODE_of_isGeodesic (cov := cov) (γ t₀) (V := univ)
      isOpen_univ (Set.mem_univ t₀) hsm hsrc (fun t _ => hgeo t) Z hZ hZeq
  exact ⟨δ, hδ, hud, hwd⟩


/-- **The chart interval of a `GExp`-ray at an arbitrary time.**  The concrete form used by step
(ii): for the ray `s ↦ GExp p (s • v)` and any `t₀`, the chart centred at `γ t₀` carries the
geodesic equation on a neighbourhood of `t₀`. -/
theorem exists_pos_chartODE_GExp (hmet : IsMetricCompatible cov) {p : M} {v : TangentSpace I p}
    (hv : v ≠ 0) (t₀ : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ s ∈ Ioo (t₀ - δ) (t₀ + δ),
        HasDerivAt (fun t : ℝ =>
            (extChartAt I (GExp (cov := cov) hmet p (t₀ • v))) (GExp (cov := cov) hmet p (t • v)))
          (deriv (fun t : ℝ =>
            (extChartAt I (GExp (cov := cov) hmet p (t₀ • v))) (GExp (cov := cov) hmet p (t • v))) s)
          s) ∧
      (∀ s ∈ Ioo (t₀ - δ) (t₀ + δ),
        HasDerivAt (deriv (fun t : ℝ =>
            (extChartAt I (GExp (cov := cov) hmet p (t₀ • v))) (GExp (cov := cov) hmet p (t • v))))
          (chartGeodesicVectorField cov (GExp (cov := cov) hmet p (t₀ • v))
            ((extChartAt I (GExp (cov := cov) hmet p (t₀ • v)))
                (GExp (cov := cov) hmet p (s • v)),
              deriv (fun t : ℝ =>
                (extChartAt I (GExp (cov := cov) hmet p (t₀ • v)))
                  (GExp (cov := cov) hmet p (t • v))) s)) s) := by
  have hsm : ContMDiffOn 𝓘(ℝ) I ∞ (fun t : ℝ => GExp (cov := cov) hmet p (t • v)) univ :=
    (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hv).mono (Set.subset_univ _)
  have hgeo : ∀ t : ℝ, IsGeodesicAt cov (fun t : ℝ => GExp (cov := cov) hmet p (t • v)) t :=
    fun t => Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hv t
  have hne : curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • v)) t₀ ≠ 0 :=
    curveVelocity_GExp_ne_zero (cov := cov) hmet p hv t₀
  exact exists_pos_chartODE_of_isGeodesic (cov := cov) hsm hgeo hne

end

end Submission.RayChart
