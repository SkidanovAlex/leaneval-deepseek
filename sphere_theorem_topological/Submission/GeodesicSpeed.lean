import Submission.Gauss
import Submission.EDist
import Submission.ChartBounds

/-!
# The speed of a chart geodesic is constant

For a solution `(u, w)` of the chart geodesic equation with initial data
`u 0 = (extChartAt I x₀) x₀`, `w 0 = v`, the Riemannian speed
`√(chartGram x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t))` is constant in `t`.
This is the standard first integral of the geodesic equation and follows from the product rule for
the chart metric (`hasDerivAt_chartGram_curve`) together with the equation
`w' + Γ(w)(γ') = 0`.

## Main results

* `hasChartGeodesic_speed_const`: the speed is constant;
* `hasChartGeodesic_chartGram_const`: the same statement for the square of the speed;
* `curveSpeed_eq_norm`: the speed is the norm of the velocity;
* `curveSpeed_congr_of_eventuallyEq`: the speed only depends on the germ of the curve;
* `pathELength_geodesic_segment`: the length of the geodesic segment `r ↦ (extChartAt I x₀).symm (u r)`
  on `[0,1]` is `√(chartGram x₀ x₀ v v)`;
* `curveSpeed_expMap_ray`, `pathELength_geodesic_segment`;
* `contMDiffOn_chartCurve_Icc`: the chart curve is `C¹` on `[0,1]`;
* `riemannianEDist_expMap_le`: `riemannianEDist x₀ (expMap x₀ v) ≤ √(chartGram x₀ x₀ v v)`;
* `riemannianEDist_expMap_smul_le`: `riemannianEDist x₀ (expMap x₀ (s • v)) ≤ s √(chartGram x₀ x₀ v v)`
  for `0 ≤ s ≤ 1` (linear growth of the distance along a geodesic ray);
* `contMDiffOn_chartCurve_Icc_of`, `pathELength_geodesic_segment_Icc`,
  `riemannianEDist_geodesic_segment_le`: the same results for an arc `[s,t]` of the chart geodesic
  (`0 ≤ s ≤ t ≤ 1`), i.e. the distance between two points of a geodesic arc is at most
  `(t - s) √(chartGram x₀ x₀ v v)`.
-/
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic
open Submission.Length
open Submission.ChartConnection
open Submission.Variation
open Submission.ChartBounds
open Submission.Gauss

namespace Submission.GeodesicSpeed

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

/-- The initial velocity of a chart geodesic is the velocity vector itself, since the tangent
trivialisation at a point is the identity there. -/
lemma continuousLinearMapAt_self_eq (x₀ : M) (v : TangentSpace I x₀) :
    (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ x₀ v = v := by
  rw [continuousLinearMapAt_trivializationAt_self]
  rfl

/-- **The speed of a chart geodesic is constant.** -/
theorem hasChartGeodesic_chartGram_const
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : IsMetricCompatible cov) (x₀ : M)
    {v : TangentSpace I x₀} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w) :
    ∀ s ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (w s) (w s)
        = chartGram (I := I) x₀ x₀ v v := by
  intro s hs
  -- the derivative of the squared speed vanishes
  have hderiv_zero : ∀ t ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun r : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
        (w r) (w r)) 0 t := by
    intro t ht
    have hstay : ∀ᶠ s' in 𝓝 t, u s' ∈ (extChartAt I x₀).target := by
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s' hs'
      exact h.2.2.1 s' hs'
    have hG : chartGeodesicVectorField cov x₀ (u t, w t)
        = -christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (w t)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)) := rfl
    have hmain := hasDerivAt_chartGram_curve (cov := cov) hmet x₀
      (u := u) (v := w t) (t := t) (h.2.2.2.1 t ht) (h.2.2.1 t ht) hstay
      (h₁ := w) (h₂ := w) (h₁' := chartGeodesicVectorField cov x₀ (u t, w t))
      (h₂' := chartGeodesicVectorField cov x₀ (u t, w t))
      (h.2.2.2.2 t ht) (h.2.2.2.2 t ht)
    convert hmain using 1
    rw [hG, neg_add_cancel]
    rw [chartGram_zero_snd, chartGram_zero_fst, add_zero]
  -- the value at `0`
  have hγ0 : (extChartAt I x₀).symm (u 0) = x₀ := by
    rw [h.1]
    exact (extChartAt I x₀).left_inv (mem_extChartAt_source x₀)
  have hF0 : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) (w 0) (w 0)
      = chartGram (I := I) x₀ x₀ v v := by
    rw [hγ0, h.2.1, continuousLinearMapAt_self_eq]
  -- the constant value
  rcases lt_or_ge (0 : ℝ) s with hs0 | hs0
  · have hval := Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc hs0.le
      (fun x hx => hderiv_zero x ⟨by linarith [hx.1], by linarith [hx.2, hs.2]⟩) s ⟨hs0.le, le_rfl⟩
    exact hval.trans hF0
  · have hval := Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc hs0
      (fun x hx => hderiv_zero x ⟨by linarith [hx.1, hs.1], by linarith [hx.2]⟩) 0 ⟨hs0, le_rfl⟩
    exact hval.symm.trans hF0

/-- **The speed of a chart geodesic is constant** (square-root form). -/
theorem hasChartGeodesic_speed_const
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : IsMetricCompatible cov) (x₀ : M)
    {v : TangentSpace I x₀} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w) :
    ∀ s ∈ Ioo (-2 : ℝ) 2,
      curveSpeed (I := I) (fun r : ℝ => (extChartAt I x₀).symm (u r)) s
        = Real.sqrt (chartGram (I := I) x₀ x₀ v v) := by
  intro s hs
  have hstay : ∀ᶠ s' in 𝓝 s, u s' ∈ (extChartAt I x₀).target := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with s' hs'
    exact h.2.2.1 s' hs'
  rw [curveSpeed_chartCurve (I := I) (h.2.2.2.1 s hs) (h.2.2.1 s hs) hstay,
    hasChartGeodesic_chartGram_const hmet x₀ h s hs]

/-- **The speed is the norm of the velocity.** -/
lemma curveSpeed_eq_norm (γ : ℝ → M) (t : ℝ) :
    curveSpeed (I := I) γ t = ‖curveVelocity (I := I) γ t‖ := by
  rw [curveSpeed_def, real_inner_self_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]

/-- **The length of a chart geodesic segment.**  The `C¹` path `r ↦ (extChartAt I x₀).symm (u r)`
from `x₀` to `expMap cov x₀ v` has length `√(chartGram x₀ x₀ v v)`, because its speed is
constant. -/
theorem pathELength_geodesic_segment
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} (hmet : IsMetricCompatible cov)
    (x₀ : M) {v : TangentSpace I x₀} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w) :
    Manifold.pathELength I (fun r : ℝ => (extChartAt I x₀).symm (u r)) 0 1
      = ENNReal.ofReal (Real.sqrt (chartGram (I := I) x₀ x₀ v v)) := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have hcongr : (∫⁻ (t : ℝ) in Icc (0 : ℝ) 1,
        ‖(mfderiv% (fun r : ℝ => (extChartAt I x₀).symm (u r)) t) 1‖ₑ)
      = ∫⁻ (_ : ℝ) in Icc (0 : ℝ) 1,
          ENNReal.ofReal (Real.sqrt (chartGram (I := I) x₀ x₀ v v)) :=
    MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun t ht => by
      have htIoo : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have hnorm : ‖curveVelocity (I := I) (fun r : ℝ => (extChartAt I x₀).symm (u r)) t‖
          = Real.sqrt (chartGram (I := I) x₀ x₀ v v) := by
        rw [← curveSpeed_eq_norm]
        exact hasChartGeodesic_speed_const hmet x₀ h t htIoo
      calc ‖(mfderiv% (fun r : ℝ => (extChartAt I x₀).symm (u r)) t) 1‖ₑ
          = ‖curveVelocity (I := I) (fun r : ℝ => (extChartAt I x₀).symm (u r)) t‖ₑ := rfl
        _ = ENNReal.ofReal
              ‖curveVelocity (I := I) (fun r : ℝ => (extChartAt I x₀).symm (u r)) t‖ := by
              rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq]; simp
        _ = ENNReal.ofReal (Real.sqrt (chartGram (I := I) x₀ x₀ v v)) := by rw [hnorm])
  rw [hcongr, MeasureTheory.setLIntegral_const, Real.volume_Icc]
  norm_num

/-- The chart curve of a chart geodesic is `C¹` on `[0,1]`. -/
lemma contMDiffOn_chartCurve_Icc
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} {x₀ : M}
    {v : TangentSpace I x₀} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w) :
    CMDiff[Icc (0 : ℝ) 1] 1 (fun r : ℝ => (extChartAt I x₀).symm (u r)) := by
  have hs : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hmem : ∀ t ∈ Icc (0 : ℝ) 1, t ∈ Ioo (-2 : ℝ) 2 :=
    fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hdiff : DifferentiableOn ℝ u (Icc (0 : ℝ) 1) :=
    fun t ht => ((h.2.2.2.1 t (hmem t ht)).differentiableAt).differentiableWithinAt
  have hderiv : EqOn (derivWithin u (Icc (0 : ℝ) 1)) w (Icc (0 : ℝ) 1) :=
    fun t ht => (h.2.2.2.1 t (hmem t ht)).hasDerivWithinAt.derivWithin (hs t ht)
  have hcont : ContinuousOn (derivWithin u (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) :=
    ContinuousOn.congr (fun t ht => (h.2.2.2.2 t (hmem t ht)).continuousAt.continuousWithinAt)
      hderiv
  have hu : ContDiffOn ℝ (1 : ℕ∞ω) u (Icc (0 : ℝ) 1) :=
    (contDiffOn_one_iff_derivWithin hs).mpr ⟨hdiff, hcont⟩
  have hu' : CMDiff[Icc (0 : ℝ) 1] 1 u := contMDiffOn_iff_contDiffOn.mpr hu
  have hmaps : MapsTo u (Icc (0 : ℝ) 1) (extChartAt I x₀).target :=
    fun t ht => h.2.2.1 t (hmem t ht)
  exact (contMDiffOn_extChartAt_symm (I := I) x₀).comp hu' hmaps

/-- **The Riemannian distance to `expMap x₀ v` is at most `√(chartGram x₀ x₀ v v)`.**  This is the
upper bound in the local minimality of geodesics, and the starting point for
`riemannianEDist x₀ (expMap cov x₀ v) = ‖v‖`. -/
theorem riemannianEDist_expMap_le
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov) (x₀ : M)
    {v : TangentSpace I x₀} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w) :
    Manifold.riemannianEDist I x₀ (expMap cov x₀ v)
      ≤ ENNReal.ofReal (Real.sqrt (chartGram (I := I) x₀ x₀ v v)) := by
  have hγ : CMDiff[Icc (0 : ℝ) 1] 1 (fun r : ℝ => (extChartAt I x₀).symm (u r)) :=
    contMDiffOn_chartCurve_Icc (v := v) h
  have h0 : (fun r : ℝ => (extChartAt I x₀).symm (u r)) 0 = x₀ := by
    show (extChartAt I x₀).symm (u 0) = x₀
    rw [h.1]
    exact (extChartAt I x₀).left_inv (mem_extChartAt_source x₀)
  have h1 : (fun r : ℝ => (extChartAt I x₀).symm (u r)) 1 = expMap cov x₀ v :=
    (expMap_eq_of_hasChartGeodesic h).symm
  refine (Manifold.riemannianEDist_le_pathELength hγ h0 h1 zero_le_one).trans_eq ?_
  exact pathELength_geodesic_segment hmet x₀ h

/-- The speed only depends on the germ of the curve. -/
lemma curveSpeed_congr_of_eventuallyEq {γ γ' : ℝ → M} {s : ℝ} (h : γ =ᶠ[𝓝 s] γ') :
    curveSpeed (I := I) γ s = curveSpeed (I := I) γ' s := by
  have hs : γ s = γ' s := h.eq_of_nhds
  rw [curveSpeed_def, curveSpeed_def, hs]
  refine congrArg Real.sqrt (congrArg (fun v => Inner.inner ℝ v v) ?_)
  rw [curveVelocity_apply, curveVelocity_apply, h.mfderiv_eq (I := 𝓘(ℝ)) (I' := I)]
  rfl

/-- **The speed along an `expMap` ray is constant.** -/
theorem curveSpeed_expMap_ray
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (x₀ : M) {v : TangentSpace I x₀} {u w : ℝ → E}
    (h : HasChartGeodesic cov x₀ v u w) (hmet : IsMetricCompatible cov) :
    ∀ s ∈ Ioo (-1 : ℝ) 1,
      curveSpeed (I := I) (fun r : ℝ => expMap cov x₀ (r • v)) s
        = Real.sqrt (chartGram (I := I) x₀ x₀ v v) := by
  intro s hs
  have heq : (fun r : ℝ => expMap cov x₀ (r • v))
      =ᶠ[𝓝 s] (fun r : ℝ => (extChartAt I x₀).symm (u r)) := by
    filter_upwards [Ioo_mem_nhds hs.1 hs.2] with r hr
    exact expMap_smul (cov := cov) (le_of_lt (abs_lt.mpr hr)) h
  rw [curveSpeed_congr_of_eventuallyEq heq]
  exact hasChartGeodesic_speed_const hmet x₀ h s ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- **The Riemannian distance along a geodesic ray grows at most linearly.** -/
theorem riemannianEDist_expMap_smul_le
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov) (x₀ : M)
    {v : TangentSpace I x₀} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    Manifold.riemannianEDist I x₀ (expMap cov x₀ (s • v))
      ≤ ENNReal.ofReal (s * Real.sqrt (chartGram (I := I) x₀ x₀ v v)) := by
  have hc : |s| ≤ 1 := by rw [abs_of_nonneg hs.1]; exact hs.2
  have hscaled : HasChartGeodesic cov x₀ (s • v) (fun τ : ℝ => u (s * τ))
      (fun τ : ℝ => s • w (s * τ)) := hasChartGeodesic_const_smul hc h
  have hbound := riemannianEDist_expMap_le (I := I) hmet x₀ hscaled
  refine hbound.trans (le_of_eq ?_)
  rw [chartGram_smul_smul]
  have h1 : Real.sqrt (s ^ 2 * chartGram (I := I) x₀ x₀ v v)
      = s * Real.sqrt (chartGram (I := I) x₀ x₀ v v) := by
    rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.1]
  rw [h1]

/-- The chart curve of a chart geodesic is `C¹` on any sub-interval `[s,t]` of `[0,1]`. -/
lemma contMDiffOn_chartCurve_Icc_of
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} {x₀ : M}
    {v : TangentSpace I x₀} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    CMDiff[Icc s t] 1 (fun r : ℝ => (extChartAt I x₀).symm (u r)) := by
  have hdiff : UniqueDiffOn ℝ (Icc s t) := uniqueDiffOn_Icc hst
  have hmem : ∀ τ ∈ Icc s t, τ ∈ Ioo (-2 : ℝ) 2 :=
    fun τ hτ => ⟨by linarith [hτ.1, hs], by linarith [hτ.2, ht]⟩
  have hd : DifferentiableOn ℝ u (Icc s t) :=
    fun τ hτ => ((h.2.2.2.1 τ (hmem τ hτ)).differentiableAt).differentiableWithinAt
  have hderiv : EqOn (derivWithin u (Icc s t)) w (Icc s t) :=
    fun τ hτ => (h.2.2.2.1 τ (hmem τ hτ)).hasDerivWithinAt.derivWithin (hdiff τ hτ)
  have hcont : ContinuousOn (derivWithin u (Icc s t)) (Icc s t) :=
    ContinuousOn.congr (fun τ hτ => (h.2.2.2.2 τ (hmem τ hτ)).continuousAt.continuousWithinAt)
      hderiv
  have hu : ContDiffOn ℝ (1 : ℕ∞ω) u (Icc s t) :=
    (contDiffOn_one_iff_derivWithin hdiff).mpr ⟨hd, hcont⟩
  have hu' : CMDiff[Icc s t] 1 u := contMDiffOn_iff_contDiffOn.mpr hu
  have hmaps : MapsTo u (Icc s t) (extChartAt I x₀).target :=
    fun τ hτ => h.2.2.1 τ (hmem τ hτ)
  exact (contMDiffOn_extChartAt_symm (I := I) x₀).comp hu' hmaps

/-- **The length of a chart geodesic arc.**  For `0 ≤ s ≤ t ≤ 1`, the arc of the chart geodesic
between `s` and `t` has length `(t - s) √(chartGram x₀ x₀ v v)`: the speed is constant. -/
theorem pathELength_geodesic_segment_Icc
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} (hmet : IsMetricCompatible cov)
    (x₀ : M) {v : TangentSpace I x₀} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    Manifold.pathELength I (fun r : ℝ => (extChartAt I x₀).symm (u r)) s t
      = ENNReal.ofReal ((t - s) * Real.sqrt (chartGram (I := I) x₀ x₀ v v)) := by
  rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
  have hcongr : (∫⁻ (τ : ℝ) in Icc s t,
        ‖(mfderiv% (fun r : ℝ => (extChartAt I x₀).symm (u r)) τ) 1‖ₑ)
      = ∫⁻ (_ : ℝ) in Icc s t,
          ENNReal.ofReal (Real.sqrt (chartGram (I := I) x₀ x₀ v v)) :=
    MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun τ hτ => by
      have hτIoo : τ ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hτ.1, hs], by linarith [hτ.2, ht]⟩
      have hnorm : ‖curveVelocity (I := I) (fun r : ℝ => (extChartAt I x₀).symm (u r)) τ‖
          = Real.sqrt (chartGram (I := I) x₀ x₀ v v) := by
        rw [← curveSpeed_eq_norm]
        exact hasChartGeodesic_speed_const hmet x₀ h τ hτIoo
      calc ‖(mfderiv% (fun r : ℝ => (extChartAt I x₀).symm (u r)) τ) 1‖ₑ
          = ‖curveVelocity (I := I) (fun r : ℝ => (extChartAt I x₀).symm (u r)) τ‖ₑ := rfl
        _ = ENNReal.ofReal
              ‖curveVelocity (I := I) (fun r : ℝ => (extChartAt I x₀).symm (u r)) τ‖ := by
              rw [enorm_eq_nnnorm, ENNReal.coe_nnreal_eq]; simp
        _ = ENNReal.ofReal (Real.sqrt (chartGram (I := I) x₀ x₀ v v)) := by rw [hnorm])
  rw [hcongr, MeasureTheory.setLIntegral_const, Real.volume_Icc, mul_comm,
    ← ENNReal.ofReal_mul (by linarith : (0:ℝ) ≤ t - s)]

/-- **The Riemannian distance between two points of a geodesic arc grows at most linearly.** -/
theorem riemannianEDist_geodesic_segment_le
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))} (hmet : IsMetricCompatible cov)
    (x₀ : M) {v : TangentSpace I x₀} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    Manifold.riemannianEDist I ((extChartAt I x₀).symm (u s)) ((extChartAt I x₀).symm (u t))
      ≤ ENNReal.ofReal ((t - s) * Real.sqrt (chartGram (I := I) x₀ x₀ v v)) := by
  have hγ : CMDiff[Icc s t] 1 (fun r : ℝ => (extChartAt I x₀).symm (u r)) :=
    contMDiffOn_chartCurve_Icc_of h hs hst ht
  have hle := Manifold.riemannianEDist_le_pathELength hγ rfl rfl hst.le
  rwa [pathELength_geodesic_segment_Icc hmet x₀ h hs hst.le ht] at hle

end

end Submission.GeodesicSpeed
