import Submission.GExpTwoSided
import Submission.ChartConnection
import Submission.GlobalExp
import Submission.GeodesicExtend
import Submission.GExpRay2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The rays of the global exponential map are geodesics at the base parameter

`Submission.GExpTwoSided.isGeodesicAt_GExp_smul` shows that the ray `s ↦ GExp p (s • v)` is a
geodesic at every **positive** parameter, and `…_of_neg` / `…_of_ne` at every **negative** one, by
reflecting in the base point.  This file supplies the missing parameter **`s = 0`**, where the ray
is only `C⁰` in general (the two one-sided geodesics have to be glued), and then packages the result
as the statement that the ray is a geodesic on *all* of `ℝ`.

## Contents

* `isGeodesicAt_expMap_smul_zero`: the rays of the **chart** exponential map are geodesics at `0`.
  The chart geodesic with initial velocity `c • v` for a small `c > 0`
  (`exists_pos_hasChartGeodesic`) is rescaled by `s ↦ s / c` (`expMap_smul`,
  `isGeodesicAt_comp_mul`), which exhibits `s ↦ expMap cov x (s • v)` as a reparametrised chart
  solution near `0`; the smoothness needed for the reparametrisation is
  `Submission.ChartConnection.mdifferentiableAt_chartCurve`.
* `isGeodesicAt_GExp_smul_zero`: the same for `GExp`, by the **two-sided** agreement of `GExp`
  with the chart exponential map (`exists_pos_GExp_smul_eq_expMap`).
* `isGeodesicAt_GExp_smul` (here re-exported as `isGeodesicAt_GExp_smul_all`): for `v ≠ 0` the ray
  is a geodesic at *every* real parameter.

This is the first item of `Submission/Roadmap.lean` §80.5: every continuation/gluing argument for
the global geodesic flow (and hence the cut-point step and Klingenberg's estimate) needs the ray to
be a geodesic *through* the base point, not merely on each side of it.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option autoImplicit false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.GExpRay2
open Submission.GExpTwoSided
open Submission.ChartConnection
open Submission.GeodesicExtend

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GExpRayZero

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The rays of the chart exponential map are geodesics at `0`.**  For `v ≠ 0` the curve
`s ↦ expMap cov x (s • v)` is a chart geodesic near `0` after rescaling the velocity, so the
geodesic equation holds at `s = 0`. -/
theorem isGeodesicAt_expMap_smul_zero (x : M) {v : TangentSpace I x} (hv : v ≠ 0) :
    IsGeodesicAt cov (fun s : ℝ => expMap cov x (s • v)) 0 := by
  classical
  -- a chart geodesic for a small multiple of `v`
  obtain ⟨ρ₀, hρ₀, hex⟩ := exists_pos_hasChartGeodesic (cov := cov) x
  obtain ⟨lam, hlam, hconv⟩ := exists_model_norm_le_fibre_div (I := I) x
  have hsqlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  set c : ℝ := ρ₀ / (‖v‖ / Real.sqrt lam + 1) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; positivity
  have hcm : ‖(show E from (c • v))‖ = c * ‖(show E from v)‖ := by
    have h : (show E from (c • v)) = c • (show E from v) := rfl
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
  have hcρ : ‖(show E from (c • v))‖ ≤ ρ₀ := by
    have hbase : ‖(show E from v)‖ ≤ ‖v‖ / Real.sqrt lam := hconv v
    have hlt : c * ‖(show E from v)‖ < ρ₀ := by
      calc c * ‖(show E from v)‖ ≤ c * (‖v‖ / Real.sqrt lam) :=
            mul_le_mul_of_nonneg_left hbase hcpos.le
        _ < c * (‖v‖ / Real.sqrt lam + 1) :=
            mul_lt_mul_of_pos_left (by linarith) hcpos
        _ = ρ₀ := by rw [hcdef]; field_simp
    rw [hcm]
    exact hlt.le
  obtain ⟨u, w, huw⟩ := hex (show E from (c • v)) hcρ
  -- the expMap ray is the rescaled chart geodesic
  have hagree : ∀ s : ℝ, |s| ≤ c →
      expMap cov x (s • v) = (extChartAt I x).symm (u (s / c)) := by
    intro s hs
    have hsc : |s / c| ≤ 1 := by
      rw [abs_div, abs_of_pos hcpos, div_le_one hcpos]
      exact hs
    have h1 : expMap cov x ((s / c) • (c • v)) = (extChartAt I x).symm (u (s / c)) :=
      expMap_smul (I := I) (x := x) (v := c • v) (u := u) (w := w) (c := s / c) hsc huw
    have h2 : (s / c) • (c • v) = s • v := by
      rw [smul_smul, div_mul_cancel₀ s hcpos.ne']
    rwa [h2] at h1
  -- the chart solution curve is smooth near `0` and geodesic there
  have hgeo0 : IsGeodesicAt cov (fun t : ℝ => (extChartAt I x).symm (u t)) 0 :=
    isGeodesicAt_chartSolution (cov := cov) huw (by norm_num)
  have hmd : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ),
      MDifferentiableAt 𝓘(ℝ) I (fun t : ℝ => (extChartAt I x).symm (u t)) (c⁻¹ * s) := by
    have hcont : Tendsto (fun s : ℝ => c⁻¹ * s) (𝓝 (0 : ℝ)) (𝓝 (c⁻¹ * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at hcont
    have hnear : ∀ᶠ s : ℝ in 𝓝 (0 : ℝ), c⁻¹ * s ∈ Ioo (-2 : ℝ) 2 :=
      hcont.eventually (isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-2) 2))
    filter_upwards [hnear] with s hs
    exact mdifferentiableAt_chartCurve (I := I) (x₀ := x)
      (hu := huw.2.2.2.1 (c⁻¹ * s) hs)
      (htgt := huw.2.2.1 (c⁻¹ * s) hs)
      (hstay := Filter.mem_of_superset (isOpen_Ioo.mem_nhds hs)
        (fun t ht => huw.2.2.1 t ht))
  -- reparametrise the chart geodesic, then transfer to the expMap ray
  have hgeo1 : IsGeodesicAt cov (fun s : ℝ => (extChartAt I x).symm (u (c⁻¹ * s))) 0 :=
    isGeodesicAt_comp_mul (cov := cov)
      (γ := fun t : ℝ => (extChartAt I x).symm (u t)) (c := c⁻¹) (t := 0)
      (inv_ne_zero hcpos.ne') (by simpa using hmd) (by simpa using hgeo0)
  refine (isGeodesicAt_congr_of_eventuallyEq (I := I)
    (γ := fun s : ℝ => expMap cov x (s • v))
    (γ' := fun s : ℝ => (extChartAt I x).symm (u (c⁻¹ * s))) (t := 0) ?_).mpr hgeo1
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hcpos] with s hs
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
  rw [hagree s hs.le, div_eq_mul_inv, mul_comm]

/-- **The rays of the global exponential map are geodesics at the base parameter `0` too.**
The proof uses the *two-sided* agreement of `GExp` with the chart exponential map
(`exists_pos_GExp_smul_eq_expMap`) plus `isGeodesicAt_expMap_smul_zero`. -/
theorem isGeodesicAt_GExp_smul_zero (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) :
    IsGeodesicAt cov (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) 0 := by
  obtain ⟨ρg, hρg, hag⟩ := exists_pos_GExp_smul_eq_expMap (cov := cov) hmet x hv
  have hev : (fun s : ℝ => GExp (cov := cov) hmet x (s • v))
      =ᶠ[𝓝 (0 : ℝ)] (fun s : ℝ => expMap cov x (s • v)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρg] with s hs
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
    exact hag s hs
  exact (isGeodesicAt_congr_of_eventuallyEq (I := I)
    (γ := fun s : ℝ => GExp (cov := cov) hmet x (s • v))
    (γ' := fun s : ℝ => expMap cov x (s • v)) (t := 0) hev).mpr
    (isGeodesicAt_expMap_smul_zero (cov := cov) x hv)

/-- **The rays of the global exponential map are geodesics on all of `ℝ`.**  For `v ≠ 0` the map
`s ↦ GExp p (s • v)` satisfies the geodesic equation at every real parameter: at `t > 0` by
`isGeodesicAt_GExp_smul`, at `t < 0` by `isGeodesicAt_GExp_smul_of_ne` (reflection in the base
point) and at `t = 0` by `isGeodesicAt_GExp_smul_zero`. -/
theorem isGeodesicAt_GExp_smul_all (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) (t : ℝ) :
    IsGeodesicAt cov (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) t := by
  rcases lt_trichotomy t 0 with h | h | h
  · exact isGeodesicAt_GExp_smul_of_neg (cov := cov) hmet x hv h
  · subst h
    exact isGeodesicAt_GExp_smul_zero (cov := cov) hmet x hv
  · exact isGeodesicAt_GExp_smul (cov := cov) hmet x hv h

end

end Submission.GExpRayZero
