import Submission.IndexCorner2
import Submission.GeodesicExtend
import Submission.GExpRayZero
import Submission.LensLoop
import Submission.RayChart

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.IndexCorner
open Submission.IndexCorner2
open Submission.GeodesicExtend
open Submission.GlobalBM
open Submission.ChartCurv
open Submission.ChartConnection
open Submission.Distance

/-!
# The chart data of a `GExp`-ray in a *prescribed* chart

`Submission.IndexCorner2.eqOn_zero_of_minimising_chart` proves the chart-level theorem `σ ≤ κ` — a
minimising chart geodesic with an interior conjugate point is impossible — but its hypotheses are
explicit *chart data* (`u`, `w`, `w'`) on a whole interval.  This file supplies that data for the
canonical object the global theory uses, a `GExp`-ray `s ↦ GExp p (s • ξ)`, in a **prescribed** chart
`x₀` (as opposed to the chart `chartAt H (γ t)` used by the local theory of
`Submission.RayChart.exists_pos_chartODE_GExp`).

The key structural input is the **chart-independence of the geodesic equation**
(`Submission.GeodesicExtend.hasDerivAt_deriv_chartCurve_of_isGeodesicAt`): an intrinsic geodesic
satisfies the chart geodesic equation in *every* chart containing it.  Everything else is the chain
rule (`deriv_extChartAt_eq_continuousLinearMapAt_curveVelocity`) and the unit-speed conversion
(`chartGram_continuousLinearMapAt`).

What is *not* here, and what the intrinsic form of `σ ≤ κ` still needs, is the analogous
chart-independence of the **Jacobi** equation; see `Submission/Roadmap.lean` §95.
-/

namespace Submission.GeoChartCurve

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

/-- **The coordinate curve of a `GExp`-ray in a prescribed chart is differentiable.** -/
theorem hasDerivAt_chartCurve_GExp (hmet : IsMetricCompatible cov) (x₀ : M) {p : M}
    {ξ : TangentSpace I p} (hξ : ξ ≠ 0) (s : ℝ)
    (hs : GExp (cov := cov) hmet p (s • ξ) ∈ (chartAt H x₀).source) :
    HasDerivAt (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ)))
      (deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))) s) s := by
  have hsm : ContMDiffAt 𝓘(ℝ) I ∞ (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) s :=
    (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξ).contMDiffAt
      (Filter.univ_mem)
  have hch : ContMDiffAt I 𝓘(ℝ, E) ∞ (fun q : M => (extChartAt I x₀) q)
      (GExp (cov := cov) hmet p (s • ξ)) :=
    (contMDiffOn_extChartAt (I := I) (x := x₀)).contMDiffAt
      ((chartAt H x₀).open_source.mem_nhds hs)
  have hdiff : ContDiffAt ℝ ∞
      (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))) s :=
    (contMDiffAt_iff_contDiffAt).mp (hch.comp s hsm)
  exact (hdiff.differentiableAt (by simp)).hasDerivAt

/-- **The chart geodesic equation holds for a `GExp`-ray in a prescribed chart** (second derivative
form): the derivative of the coordinate velocity is the chart geodesic spray. -/
theorem hasDerivAt_deriv_chartCurve_GExp (hmet : IsMetricCompatible cov) (x₀ : M) {p : M}
    {ξ : TangentSpace I p} (hξ : ξ ≠ 0) (s : ℝ)
    (hs : GExp (cov := cov) hmet p (s • ξ) ∈ (chartAt H x₀).source) :
    HasDerivAt (deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))))
      (chartGeodesicVectorField cov x₀ (((extChartAt I x₀) (GExp (cov := cov) hmet p (s • ξ))),
        deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))) s)) s := by
  refine Submission.GeodesicExtend.hasDerivAt_deriv_chartCurve_of_isGeodesicAt (cov := cov) x₀
    (V := Set.univ) isOpen_univ (Set.mem_univ s)
    (Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξ) hs ?_ ?_
  · exact Submission.GExpRayZero.isGeodesicAt_GExp_smul_all (cov := cov) hmet p hξ s
  · exact Submission.RayChart.curveVelocity_GExp_ne_zero (cov := cov) hmet p hξ s

/-- **The chart geodesic equation in the form `w' + Γ(γ)(w)(w) = 0`** used by
`Submission.IndexCorner2`. -/
theorem chartGeodesicEquation_GExp (hmet : IsMetricCompatible cov) (x₀ : M) {p : M}
    {ξ : TangentSpace I p} (hξ : ξ ≠ 0) (s : ℝ)
    (hs : GExp (cov := cov) hmet p (s • ξ) ∈ (chartAt H x₀).source) :
    deriv (deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ)))) s
      + chrB cov x₀ ((extChartAt I x₀).symm
            ((extChartAt I x₀) (GExp (cov := cov) hmet p (s • ξ))))
          (deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))) s)
          (deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))) s) = 0 := by
  have h := hasDerivAt_deriv_chartCurve_GExp (cov := cov) hmet x₀ hξ s hs
  rw [h.deriv, chartGeodesicVectorField, chrB_apply]
  abel

/-- **Unit speed in the chart**: the chart metric of the coordinate velocity of a `GExp`-ray of a
*unit* direction is `1`. -/
theorem chartGram_chartCurve_GExp (hmet : IsMetricCompatible cov) (x₀ : M) {p : M}
    {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) (s : ℝ)
    (hs : GExp (cov := cov) hmet p (s • ξ) ∈ (chartAt H x₀).source) :
    chartGram (I := I) x₀ ((extChartAt I x₀).symm
        ((extChartAt I x₀) (GExp (cov := cov) hmet p (s • ξ))))
      (deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))) s)
      (deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))) s) = 1 := by
  have hξ0 : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  have hmd : MDifferentiableAt 𝓘(ℝ) I
      (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) s :=
    ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξ0).contMDiffAt
      (Filter.univ_mem)).mdifferentiableAt (by simp)
  have hvel : deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))) s
      = (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
          (GExp (cov := cov) hmet p (s • ξ))
          (curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) s) :=
    deriv_extChartAt_eq_continuousLinearMapAt_curveVelocity (I := I) x₀ hmd hs
  have hsp : ‖curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) s‖ = 1 := by
    rcases eq_or_ne s 0 with h0 | h0
    · subst h0
      rw [Submission.GExpVelocity.curveVelocity_GExp_smul_zero (cov := cov) hmet p hξ0]
      rw [zero_smul, GlobalExp.GExp_zero]
      exact hξ
    · rw [Submission.LensLoop.norm_curveVelocity_GExp_smul_ne (cov := cov) hmet p hξ0 h0]
      exact hξ
  have hsym : (extChartAt I x₀).symm
      ((extChartAt I x₀) (GExp (cov := cov) hmet p (s • ξ)))
      = GExp (cov := cov) hmet p (s • ξ) :=
    PartialEquiv.left_inv (extChartAt I x₀) (by rw [extChartAt_source]; exact hs)
  rw [hsym, hvel, chartGram_continuousLinearMapAt (I := I) x₀
    (GExp (cov := cov) hmet p (s • ξ)) hs, real_inner_self_eq_norm_sq, hsp]
  norm_num

/-- **The complete chart geodesic data of a `GExp`-ray on an interval, in a prescribed chart.**
This is exactly the geodesic half of the hypotheses of
`Submission.IndexCorner2.eqOn_zero_of_minimising_chart`, for the ray whose image lies in the chart
`x₀` on `Icc (-1) (L + 1)`. -/
theorem chartGeodesicData_GExp (hmet : IsMetricCompatible cov) (x₀ : M) {p : M}
    {ξ : TangentSpace I p} (hξ : ‖ξ‖ = 1) {L : ℝ}
    (hsrc : ∀ s ∈ Icc (-1:ℝ) (L + 1),
      GExp (cov := cov) hmet p (s • ξ) ∈ (chartAt H x₀).source) :
    (∀ s ∈ Icc (-1:ℝ) (L + 1),
      HasDerivAt (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ)))
        (deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))) s) s) ∧
    (∀ s ∈ Icc (-1:ℝ) (L + 1),
      HasDerivAt (deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))))
        (chartGeodesicVectorField cov x₀
          (((extChartAt I x₀) (GExp (cov := cov) hmet p (s • ξ))),
            deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))) s)) s) ∧
    (∀ s ∈ Icc (-1:ℝ) (L + 1),
      (extChartAt I x₀) (GExp (cov := cov) hmet p (s • ξ)) ∈ (extChartAt I x₀).target) ∧
    (∀ s ∈ Icc (-1:ℝ) (L + 1),
      deriv (deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ)))) s
        + chrB cov x₀ ((extChartAt I x₀).symm
              ((extChartAt I x₀) (GExp (cov := cov) hmet p (s • ξ))))
            (deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))) s)
            (deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))) s) = 0) ∧
    (∀ s ∈ Icc (-1:ℝ) (L + 1),
      chartGram (I := I) x₀ ((extChartAt I x₀).symm
          ((extChartAt I x₀) (GExp (cov := cov) hmet p (s • ξ))))
        (deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))) s)
        (deriv (fun t : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (t • ξ))) s) = 1) := by
  have hξ0 : ξ ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hξ; norm_num at hξ
  refine ⟨fun s hs => hasDerivAt_chartCurve_GExp (cov := cov) hmet x₀ hξ0 s (hsrc s hs),
    fun s hs => hasDerivAt_deriv_chartCurve_GExp (cov := cov) hmet x₀ hξ0 s (hsrc s hs),
    fun s hs => ?_, fun s hs => chartGeodesicEquation_GExp (cov := cov) hmet x₀ hξ0 s (hsrc s hs),
    fun s hs => chartGram_chartCurve_GExp (cov := cov) hmet x₀ hξ s (hsrc s hs)⟩
  exact (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hsrc s hs)

/-! ## The `HasChartGeodesicOn` bundle for a `GExp`-ray, in a prescribed chart

`Submission.ChartGeoAt.exists_jacobiSystemOn` (the Jacobi tensor along a chart geodesic) takes the
geodesic data in the bundled form `Submission.RauchGen.HasChartGeodesicOn`, whose initial data sits at
parameter `0`.  For a ray one must therefore re-parametrise: `s ↦ (extChartAt I x₀) (GExp p ((t₀+s)•ξ))`.
The bundle below is that datum. -/

/-- **The chart geodesic data of a `GExp`-ray as a `HasChartGeodesicOn` bundle**, initialised at the
time `t₀`.  This is the form consumed by `Submission.ChartGeoAt.exists_jacobiSystemOn`. -/
theorem hasChartGeodesicOn_GExp (hmet : IsMetricCompatible cov) (x₀ : M) {p : M}
    {ξ : TangentSpace I p} (hξ : ξ ≠ 0) {t₀ A B : ℝ}
    (h0 : (0:ℝ) ∈ Ioo A B)
    (hsrc : ∀ s ∈ Ioo A B,
      GExp (cov := cov) hmet p ((t₀ + s) • ξ) ∈ (chartAt H x₀).source) :
    Submission.RauchGen.HasChartGeodesicOn cov x₀
      (GExp (cov := cov) hmet p (t₀ • ξ))
      (curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t₀)
      (fun s : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p ((t₀ + s) • ξ)))
      (fun s : ℝ => deriv (fun r : ℝ =>
        (extChartAt I x₀) (GExp (cov := cov) hmet p ((t₀ + r) • ξ))) s)
      A B := by
  have hstep : curveVelocity (I := I) (fun r : ℝ => GExp (cov := cov) hmet p ((t₀ + r) • ξ)) 0
      = curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t₀ := by
    have hev : (fun r : ℝ => GExp (cov := cov) hmet p ((t₀ + r) • ξ))
        =ᶠ[𝓝 (0:ℝ)]
          (fun r : ℝ => (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) (1 * r + t₀)) := by
      filter_upwards with r
      congr 1
      ring
    have hmd : MDifferentiableAt 𝓘(ℝ) I (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ))
        (1 * 0 + t₀) :=
      ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξ).contMDiffAt
        (Filter.univ_mem)).mdifferentiableAt (by simp)
    have h := Submission.Length.curveVelocity_comp_mul_add (I := I)
      (γ := fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) (c := 1) (d := t₀) (t := 0) hmd
    have harg : (1:ℝ) * 0 + t₀ = t₀ := by ring
    rw [harg] at h
    rw [Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hev]
    simpa only [one_smul] using h
  -- the chain rule for the translation, on the chart curve
  have hw : ∀ s ∈ Ioo A B,
      deriv (fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p ((t₀ + r) • ξ))) s
        = deriv (fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (r • ξ))) (t₀ + s) :=
    fun s hs => (Submission.GlobalBM.hasDerivAt_comp_const_add
      (f := fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (r • ξ)))
      (f' := deriv (fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (r • ξ))))
      (c := t₀) (t := s)
      (hasDerivAt_chartCurve_GExp (cov := cov) hmet x₀ hξ (t₀ + s) (hsrc s hs))).deriv
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (extChartAt I x₀) (GExp (cov := cov) hmet p ((t₀ + 0) • ξ))
      = (extChartAt I x₀) (GExp (cov := cov) hmet p (t₀ • ξ))
    rw [add_zero]
  · have hsrc0 : GExp (cov := cov) hmet p (t₀ • ξ) ∈ (chartAt H x₀).source := by
      have := hsrc 0 h0
      rwa [add_zero] at this
    have hmd : MDifferentiableAt 𝓘(ℝ) I (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t₀ :=
      ((Submission.LensLoop.contMDiffOn_GExp_smul (cov := cov) hmet p hξ).contMDiffAt
        (Filter.univ_mem)).mdifferentiableAt (by simp)
    show deriv (fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p ((t₀ + r) • ξ))) 0
      = (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
          (GExp (cov := cov) hmet p (t₀ • ξ))
          (curveVelocity (I := I) (fun t : ℝ => GExp (cov := cov) hmet p (t • ξ)) t₀)
    rw [hw 0 h0, add_zero,
      deriv_extChartAt_eq_continuousLinearMapAt_curveVelocity (I := I) x₀ hmd hsrc0]
  · intro s hs
    exact (extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hsrc s hs)
  · intro s hs
    have h1 : HasDerivAt (fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (r • ξ)))
        (deriv (fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (r • ξ)))
          (t₀ + s)) (t₀ + s) :=
      hasDerivAt_chartCurve_GExp (cov := cov) hmet x₀ hξ (t₀ + s) (hsrc s hs)
    have h2 := Submission.GlobalBM.hasDerivAt_comp_const_add
      (f := fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (r • ξ)))
      (f' := deriv (fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (r • ξ))))
      (c := t₀) (t := s) h1
    show HasDerivAt (fun s : ℝ =>
        (extChartAt I x₀) (GExp (cov := cov) hmet p ((t₀ + s) • ξ)))
      (deriv (fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p ((t₀ + r) • ξ))) s) s
    rw [hw s hs]
    exact h2
  · intro s hs
    have h1 : HasDerivAt
        (deriv (fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (r • ξ))))
        (chartGeodesicVectorField cov x₀
          (((extChartAt I x₀) (GExp (cov := cov) hmet p ((t₀ + s) • ξ))),
            deriv (fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (r • ξ)))
              (t₀ + s))) (t₀ + s) :=
      hasDerivAt_deriv_chartCurve_GExp (cov := cov) hmet x₀ hξ (t₀ + s) (hsrc s hs)
    have h2 := Submission.GlobalBM.hasDerivAt_comp_const_add
      (f := deriv (fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (r • ξ))))
      (f' := fun t : ℝ => chartGeodesicVectorField cov x₀
        ((fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (r • ξ))) t,
          deriv (fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p (r • ξ))) t))
      (c := t₀) (t := s) h1
    show HasDerivAt (fun s : ℝ => deriv (fun r : ℝ =>
        (extChartAt I x₀) (GExp (cov := cov) hmet p ((t₀ + r) • ξ))) s)
      (chartGeodesicVectorField cov x₀
        ((extChartAt I x₀) (GExp (cov := cov) hmet p ((t₀ + s) • ξ)),
          deriv (fun r : ℝ => (extChartAt I x₀) (GExp (cov := cov) hmet p ((t₀ + r) • ξ))) s)) s
    rw [hw s hs]
    refine h2.congr_of_eventuallyEq ?_
    exact Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hs)
      (fun s' hs' => hw s' hs')

end

end Submission.GeoChartCurve

