import Submission.GExpTwoSided

/-!
# The initial velocity of the rays of `expMap` and `GExp`

`Submission.GlobalExp.GExp hmet x v` is the correct (chart-free) exponential map, defined as the
endpoint of a geodesic segment.  This file computes the **velocity at `0`** of its rays:

* `curveVelocity_expMap_smul_zero`: `s ↦ expMap x (s • v)` has velocity `v` at `s = 0`;
* `curveVelocity_GExp_smul_zero`: `s ↦ GExp x (s • v)` has velocity `v` at `s = 0`.

The second follows from the first by the two-sided agreement
(`GExpTwoSided.exists_pos_GExp_smul_eq_expMap`).

## Why the proof is not a chain rule

The natural proof of `curveVelocity (fun s ↦ expMap x (s • v)) 0 = v` is the chain rule applied to
`(fun w : E ↦ expMap x w) ∘ (fun s : ℝ ↦ s • v)` together with `mfderiv_expMap_zero` (the
differential of `expMap` at `0` is the identity).  That fails in Lean: the intermediate map is
**tangent-space valued**, and instance search cannot build `ChartedSpace E (TangentSpace I x)` (the
tangent space carries its own `NormedAddCommGroup`/`NormedSpace`, not definitionally equal to the
ambient ones), so `HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun s ↦ s • v) 0 _` does not elaborate.

Instead the proof goes through the **chart**, using the *homogeneity* of the chart geodesic
equation (`chartGeodesicVectorField_smul`, degree two in the velocity): if `(u,w)` is a chart
geodesic with initial velocity `c • v` (chosen small enough that a chart geodesic exists), then for
`|s| ≤ c` the curve `t ↦ u (s t / c)` is a chart geodesic with initial velocity `s • v`, and
`expMap_smul` gives `expMap x (s • v) = φ⁻¹(u (s/c))`.  The velocity of the latter at `0` is
`(1/c) • w 0`, and `w 0` is the coordinate image of `c • v`, so `(1/c) • w 0` is the coordinate image
of `v` — that is, `v` itself.
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
open Submission.GExpRay
open Submission.GExpTwoSided
open Submission.GeodesicExtend

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.GExpVelocity

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The initial velocity of the rays of the chart exponential map.** -/
theorem curveVelocity_expMap_smul_zero (x : M) (v : TangentSpace I x) :
    curveVelocity (I := I) (fun s : ℝ => expMap cov x (s • v)) 0 = v := by
  classical
  rcases eq_or_ne v 0 with hv0 | hv
  · subst hv0
    have hone : (fun s : ℝ => expMap cov x (s • (0 : TangentSpace I x))) = fun _ : ℝ => x := by
      funext s
      rw [smul_zero, expMap_zero]
    rw [hone, curveVelocity_const]
  · obtain ⟨ρ₀, hρ₀, hex⟩ := exists_pos_hasChartGeodesic (cov := cov) x
    obtain ⟨lam, hlam, hconv⟩ := Submission.GExpRay2.exists_model_norm_le_fibre_div (I := I) x
    have hsqlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
    have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    -- a scaling `c > 0` making the *model* norm of `c • v` at most `ρ₀`
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
    -- the agreement with the rescaled chart geodesic
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
    have hev : (fun s : ℝ => expMap cov x (s • v)) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ => (extChartAt I x).symm (u (s / c))) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hcpos] with s hs
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
      exact hagree s hs.le
    rw [curveVelocity_congr_of_eventuallyEq (I := I) hev]
    -- the velocity of `s ↦ φ⁻¹ (u (s/c))`
    have htgt : u (0 / c) ∈ (extChartAt I x).target := by
      rw [zero_div]
      exact huw.2.2.1 0 (by norm_num)
    have hstay : ∀ᶠ s in 𝓝 (0 : ℝ), u (s / c) ∈ (extChartAt I x).target := by
      have hcont : Tendsto (fun s : ℝ => s / c) (𝓝 (0 : ℝ)) (𝓝 (0 / c)) :=
        (continuousAt_id.div_const c).tendsto
      rw [zero_div] at hcont
      filter_upwards [hcont.eventually (isOpen_Ioo.mem_nhds (by norm_num : (0:ℝ) ∈ Ioo (-2) 2))]
        with s hs
      exact huw.2.2.1 (s / c) hs
    have hderiv : HasDerivAt (fun s : ℝ => u (s / c)) ((1 / c) • w 0) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => s / c) (1 / c) 0 := by
        have := (hasDerivAt_id (0 : ℝ)).div_const c
        simpa using this
      have hf : HasDerivAt u (w 0) (0 / c) := by
        rw [zero_div]
        exact huw.2.2.2.1 0 (by norm_num : (0:ℝ) ∈ Ioo (-2) 2)
      have h2 := hf.scomp_of_eq (0 : ℝ) h1 (by rw [zero_div])
      simpa only [Function.comp_def] using h2
    have hvel := curveVelocity_extChartAt_symm (I := I) (x₀ := x)
      (u := fun s : ℝ => u (s / c)) (t := 0) (v := (1 / c) • w 0) hderiv htgt hstay
    rw [hvel]
    -- identify the tangent vector
    have hw0 : w 0 = (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x (c • v) :=
      huw.2.1
    have hsymm : (extChartAt I x).symm (u (0 / c)) = x := by
      rw [zero_div, huw.1]
      exact PartialEquiv.left_inv (extChartAt I x) (mem_extChartAt_source x)
    have hcoord : (trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x (c • v)
        = c • ((trivializationAt E (TangentSpace I) x).continuousLinearMapAt ℝ x v) :=
      map_smul _ c v
    rw [hsymm, hw0, hcoord, smul_smul, div_mul_cancel₀ 1 hcpos.ne', one_smul]
    exact Trivialization.symmL_continuousLinearMapAt (R := ℝ) (b := x)
      (e := trivializationAt E (TangentSpace I) x) (by simp) v

/-- **The initial velocity of the rays of the global exponential map.** -/
theorem curveVelocity_GExp_smul_zero (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) :
    curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) 0 = v := by
  obtain ⟨ρ, hρ, hag⟩ := exists_pos_GExp_smul_eq_expMap (cov := cov) hmet x hv
  have hev : (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ => expMap cov x (s • v)) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hρ] with s hs
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hs
    exact hag s hs
  rw [curveVelocity_congr_of_eventuallyEq (I := I) hev]
  exact curveVelocity_expMap_smul_zero (cov := cov) x v

end

end Submission.GExpVelocity
