import Submission.FlowJacobi
import Submission.RauchUpper
import Submission.BonnetMyers2
import Submission.GeodesicGlobal2

/-!
# The pointwise bound for the differential of the exponential map

The identification of `Submission/FlowJacobi.lean` (`(d exp_{x₀})_v x = frameVector x₀ (exp x₀ v)
((D.Y 1) x)`) together with Rauch's comparison theorem (`Submission/RauchUpper.lean`) bounds the
differential of the exponential map.  This file contains the two bridges needed for that:

* `chartGram_self_const_of_hasChartGeodesic` : the chart speed of a chart geodesic is constant;
* `deriv_fst_eq_smul_mfderiv` : the variation field of the family at parameter `s`, in chart
  coordinates, is `s` times the chart coordinates of `(d exp_{x₀})_{s v} x`.

The final bound and its consequences (the chordal bound and the model bound used by Toponogov) are
the next step; see `Submission/Roadmap.lean` §26.3.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.JacobiTensor
open Submission.Rauch
open Submission.RauchUpper
open Submission.FlowJacobi
open Submission.Distance

namespace Submission.ExpBound

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- The chart metric at its own base point is the square of the norm. -/
lemma chartGram_self_eq_norm_sq (x₀ : M) (v : E) :
    chartGram (I := I) x₀ x₀ v v = ‖(show TangentSpace I x₀ from v)‖ ^ 2 := by
  rw [chartGram_self_apply (I := I) x₀ v v, real_inner_self_eq_norm_sq]

/-- **The chart speed of a chart geodesic is constant** — equal to the norm of the initial
velocity. -/
lemma chartGram_self_const_of_hasChartGeodesic (hmet : IsMetricCompatible cov)
    {x₀ : M} {v : E} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w) :
    ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t)
        = ‖(show TangentSpace I x₀ from v)‖ ^ 2 := by
  intro t ht
  have h0 : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
  have hc := GeodesicGlobal2.chartGram_const_of_chartODE (cov := cov) hmet
    (x₀ := x₀) (u := u) (w := w) (A := -2) (B := 2) h.2.2.1 h.2.2.2.1 h.2.2.2.2 h0
  rw [hc t ht]
  have hsymm : (extChartAt I x₀).symm (u 0) = x₀ := by
    rw [h.1]
    exact (extChartAt I x₀).left_inv (mem_extChartAt_source x₀)
  rw [hsymm, h.2.1, continuousLinearMapAt_trivializationAt_self]
  exact chartGram_self_eq_norm_sq (I := I) x₀ v

/-- **The variation field at parameter `s`, in chart coordinates, is `s` times the chart
coordinates of the differential of `exp` at `s v`.** -/
lemma deriv_fst_eq_smul_mfderiv {x₀ : M} {v x : E} {δ : ℝ} {Φ : ℝ × ℝ → E × E}
    (hδ : 0 < δ)
    (hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2, (Φ (s, t)).1 ∈ (extChartAt I x₀).target)
    (hSM : ∀ s ∈ Ioo (-2 : ℝ) 2, ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0))
    (hEXP : ∀ s : ℝ, |s| ≤ 1 → ∀ t ∈ Ioo (-δ) δ,
      expMap cov x₀ (s • (v + t • x)) = (extChartAt I x₀).symm ((Φ (s, t)).1))
    (hvsm : ∀ w : E, MDifferentiableAt 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) w)
    {s : ℝ} (hs : |s| ≤ 1) (hs' : s ∈ Ioo (-2 : ℝ) 2) :
    deriv (fun t : ℝ => (Φ (s, t)).1) 0
      = s • ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
          (expMap cov x₀ (s • v))
          ((mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) (s • v)) x)) := by
  have h0 : (0 : ℝ) ∈ Ioo (-δ) δ := ⟨by linarith, hδ⟩
  -- the chart curve
  have htgt : (Φ (s, 0)).1 ∈ (extChartAt I x₀).target := hTGT 0 h0 s hs'
  have hstay : ∀ᶠ t in 𝓝 (0 : ℝ), (Φ (s, t)).1 ∈ (extChartAt I x₀).target :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds h0) (fun t ht => hTGT t ht s hs')
  have hu_deriv : HasDerivAt (fun t : ℝ => (Φ (s, t)).1)
      (deriv (fun t : ℝ => (Φ (s, t)).1) 0) 0 := by
    have hcomp : ContDiffAt ℝ ∞ (fun t : ℝ => (Φ (s, t)).1) 0 :=
      ((ContinuousLinearMap.fst ℝ E E).contDiff.contDiffAt.comp (s, 0)
        ((hSM s hs').of_le (by decide))).comp 0
        (contDiffAt_const.prodMk contDiffAt_id)
    exact (hcomp.differentiableAt (by norm_num)).hasDerivAt
  -- the exponential curve agrees with the chart curve near `0`
  have hγeq : (fun t : ℝ => expMap cov x₀ (s • (v + t • x)))
      =ᶠ[𝓝 (0 : ℝ)] (fun t : ℝ => (extChartAt I x₀).symm ((Φ (s, t)).1)) := by
    filter_upwards [isOpen_Ioo.mem_nhds h0] with t ht
    rw [hEXP s hs t ht]
  have hchartdiff : MDifferentiableAt 𝓘(ℝ) I
      (fun t : ℝ => (extChartAt I x₀).symm ((Φ (s, t)).1)) 0 :=
    mdifferentiableAt_chartCurve (I := I) hu_deriv htgt hstay
  have hγdiff : MDifferentiableAt 𝓘(ℝ) I (fun t : ℝ => expMap cov x₀ (s • (v + t • x))) 0 :=
    hchartdiff.congr_of_eventuallyEq hγeq
  have hpoint : (fun t : ℝ => expMap cov x₀ (s • (v + t • x))) 0 = expMap cov x₀ (s • v) := by
    simp only [zero_smul, add_zero]
  have hpt2 : expMap cov x₀ (s • v) = (extChartAt I x₀).symm ((Φ (s, 0)).1) := by
    have hh := hEXP s hs 0 h0
    simpa using hh
  have hsrc : (fun t : ℝ => expMap cov x₀ (s • (v + t • x))) 0 ∈ (chartAt H x₀).source := by
    rw [hpoint, hpt2]
    exact mem_source_chartCurve (I := I) (x₀ := x₀) (u := fun _ => (Φ (s, 0)).1) (t := 0) htgt
  -- the chart derivative
  have hev : (fun t : ℝ => (Φ (s, t)).1) =ᶠ[𝓝 (0 : ℝ)]
      (fun t : ℝ => (extChartAt I x₀) (expMap cov x₀ (s • (v + t • x)))) := by
    filter_upwards [isOpen_Ioo.mem_nhds h0] with t ht
    rw [hEXP s hs t ht]
    exact ((extChartAt I x₀).right_inv (hTGT t ht s hs')).symm
  have hstep : deriv (fun t : ℝ => (Φ (s, t)).1) 0
      = ((trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ
          (expMap cov x₀ (s • v)))
          (curveVelocity (I := I) (fun t : ℝ => expMap cov x₀ (s • (v + t • x))) 0) := by
    rw [hev.deriv_eq]
    have h := CurveField.deriv_extChartAt_comp_eq_continuousLinearMapAt_curveVelocity
      (I := I) (x := x₀) hγdiff hsrc
    rw [← hpoint]
    exact h
  -- the velocity of the exponential curve
  have hσ : HasDerivAt (fun t : ℝ => s • (v + t • x)) (s • x) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => v + t • x) x 0 := by
      have h2 : HasDerivAt (fun t : ℝ => v + t • x) ((0 : E) + (1 : ℝ) • x) 0 :=
        (hasDerivAt_const (x := (0 : ℝ)) (c := v)).add ((hasDerivAt_id (0 : ℝ)).smul_const x)
      rw [zero_add, one_smul] at h2
      exact h2
    have h3 := h1.const_smul s
    have hfun : (s • fun t : ℝ => v + t • x) = fun t : ℝ => s • (v + t • x) := by
      funext t
      rw [Pi.smul_apply]
    rw [hfun] at h3
    exact h3
  have hvel : curveVelocity (I := I) (fun t : ℝ => expMap cov x₀ (s • (v + t • x))) 0
      = (mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) (s • v)) (s • x) := by
    have h := Submission.Minimal.curveVelocity_eq_exp_deriv (cov := cov) (x₀ := x₀)
      (σ := fun t : ℝ => s • (v + t • x)) (σ' := fun _ => s • x)
      (γ := fun t : ℝ => expMap cov x₀ (s • (v + t • x))) (t := 0)
      hσ (by simpa using hvsm (s • v)) (Filter.EventuallyEq.refl _ _)
    rw [show s • (v + (0 : ℝ) • x) = s • v from by rw [zero_smul, add_zero]] at h
    exact h
  rw [hstep, hvel, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul]

end

end Submission.ExpBound
