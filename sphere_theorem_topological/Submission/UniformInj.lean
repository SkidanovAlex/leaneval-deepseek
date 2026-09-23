import Submission.GExpFlow
import Submission.ChartFlowHom
import Submission.ChartFlowJoint
import Submission.InjRadius
import Submission.Commons.Analysis.Calculus.exists_uniform_injective_of_hasStrictFDerivAt
import Submission.Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt

/-!
# The uniform local injectivity radius of the Riemannian metric

The classical fact that the exponential map of a compact Riemannian manifold is *uniformly* locally
injective at the origin is the base case of every globalisation argument on the tangent bundle.

This file proves it in the chart-flow model.  For a chart-flow datum `D` of the chart at `z₀` on a
compact piece `Z` of the chart source, the chart-coordinate model of the exponential map is

  `Hfun D (x, u) = (D.α (x, flowScale D • u) (flowScale D)⁻¹).1 =

and the two ingredients are

* its **joint smoothness** at `(x, 0)` (from `ChartFlowData.hjoint`), and
* the **value of its differential in the velocity variable at velocity zero**, which is the
  identity — this follows from the *homogeneity* of the chart geodesic flow
  (`ChartFlowHom.chartFlowData_homogeneous`) together with the spray equation at time `0`:
  `Hfun D (x, λ • u) = (D.α (x, c • u) (λ * c⁻¹)).1`, whose derivative in `λ` at `0` is
  `c⁻¹ • (c • u) = u`.

The uniform injectivity then follows from the abstract compactness lemma
`Commons.Analysis.Calculus.exists_uniform_injective_of_hasStrictFDerivAt`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.GExpFlow
open Submission.ChartFlowHom
open Submission.ChartBounds
open Submission.ChartConnection
open Submission.InjRadius

namespace Submission.UniformInj

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
variable {z₀ : M} {Z : Set M}

/-! ## The chart-coordinate model of the exponential map -/

/-- The chart-coordinate model of the exponential map attached to the flow data `D`: the time-`c⁻¹`
position of the chart-spray flow started at the phase `(x, c • u)`, where `c = flowScale D`. -/
noncomputable def Hfun (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (p : E × E) : E :=
  (D.α (p.1, flowScale D • p.2) (flowScale D)⁻¹).1

lemma Hfun_apply (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (p : E × E) :
    Hfun D p = (D.α (p.1, flowScale D • p.2) (flowScale D)⁻¹).1 := rfl

/-- The chart spray vanishes at zero velocity. -/
lemma chartSpray_zero (z₀ : M) {x : E} (hx : x ∈ (extChartAt I z₀).target) :
    chartSpray (cov := cov) z₀ (x, 0) = 0 := by
  have hzero : chartGeodesicVectorField (cov := cov) z₀ (x, (0 : E)) = 0 := by
    have h := chartGeodesicVectorField_smul (cov := cov) z₀ (0 : ℝ) (x, (0 : E)) hx
    simpa using h
  rw [chartSpray_apply, hzero]
  rfl

/-- At zero velocity the flow stays at the initial phase. -/
lemma chartFlow_zero {Z : Set M} (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x : E}
    (hxO : (x, 0) ∈ D.O) (hxT : x ∈ (extChartAt I z₀).target) :
    D.α (x, 0) ((flowScale D)⁻¹) = (x, 0) := by
  have hspray := chartSpray_zero (cov := cov) (I := I) (z₀ := z₀) hxT
  have htl : |(flowScale D)⁻¹| ≤ D.ρ := by
    rw [inv_flowScale, abs_of_pos (div_pos D.hρ two_pos)]
    linarith [D.hρ]
  have hode : ∀ t : ℝ, |t| ≤ D.ρ →
      HasDerivAt (fun _ : ℝ => ((x, 0) : E × E)) (chartSpray (cov := cov) z₀ ((x, 0) : E × E)) t := by
    intro t _
    rw [hspray]
    exact hasDerivAt_const t ((x, 0) : E × E)
  have h := D.huniq (x, 0) hxO (fun _ : ℝ => ((x, 0) : E × E)) hode rfl ((flowScale D)⁻¹) htl
  simpa using h.symm

/-- `Hfun D (x, 0) = x`: the exponential map at zero velocity is the identity. -/
lemma Hfun_zero (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x : E}
    (hx : (x, 0) ∈ chartData (I := I) z₀ Z) :
    Hfun D (x, 0) = x := by
  have hxO : (x, 0) ∈ D.O := D.hKO hx
  have hxT : x ∈ (extChartAt I z₀).target := D.hOW hxO |>.1
  have hfun : Hfun D (x, (0 : E)) = (D.α (x, flowScale D • (0 : E)) (flowScale D)⁻¹).1 := rfl
  rw [hfun, smul_zero, chartFlow_zero (cov := cov) D hxO hxT]

/-! ## Joint smoothness -/

/-- `Hfun D` is jointly `C^∞` at every phase of the chart data. -/
theorem contDiffAt_Hfun (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : E}
    (hK : (x, flowScale D • u) ∈ chartData (I := I) z₀ Z) :
    ContDiffAt ℝ ∞ (Hfun D) (x, u) := by
  have ht : |(flowScale D)⁻¹| < D.ρ := by
    rw [inv_flowScale, abs_of_pos (div_pos D.hρ two_pos)]
    linarith [D.hρ]
  have hjoint := D.hjoint (x, flowScale D • u) hK (flowScale D)⁻¹ ht
  have hinner : ContDiffAt ℝ ∞
      (fun zw : E × E => ((zw.1, flowScale D • zw.2), (flowScale D)⁻¹)) (x, u) :=
    (contDiffAt_id.fst.prodMk (contDiffAt_const.smul contDiffAt_id.snd)).prodMk
      (contDiffAt_const (c := (flowScale D)⁻¹))
  have h := ContDiffAt.comp (x := (x, u)) hjoint hinner
  have hres : ContDiffAt ℝ ∞
      (fun p : E × E => (D.α (p.1, flowScale D • p.2) (flowScale D)⁻¹).1) (x, u) :=
    (by simpa only [Function.comp_def] using h : ContDiffAt ℝ ∞
      (fun zw : E × E => D.α (zw.1, flowScale D • zw.2) (flowScale D)⁻¹) (x, u)).fst
  change ContDiffAt ℝ ∞
    (fun p : E × E => (D.α (p.1, flowScale D • p.2) (flowScale D)⁻¹).1) (x, u)
  exact hres

/-- `Hfun D` is jointly `C^∞` at `(x, 0)` whenever the phase `(x, 0)` is in the chart data. -/
theorem contDiffAt_Hfun_zero (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x : E}
    (hx : (x, 0) ∈ chartData (I := I) z₀ Z) :
    ContDiffAt ℝ ∞ (Hfun D) (x, 0) := by
  refine contDiffAt_Hfun (cov := cov) D (u := 0) ?_
  rwa [smul_zero]

/-! ## The derivative of the flow in the initial velocity -/

/-- **The derivative of the flow position in the initial velocity.**  `D.α (x, w)` is the phase of
the chart geodesic starting at `x` with coordinate velocity `w`; at flow time `c⁻¹`
(`c = flowScale D`) its position has derivative `c⁻¹ • w` in `w`, at `w = 0`. -/
theorem hasDerivAt_flowPos (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x w : E}
    (hxO : (x, 0) ∈ D.O) (hwO : (x, w) ∈ D.O) :
    HasDerivAt (fun r : ℝ => (D.α (x, w) (r * (flowScale D)⁻¹)).1)
      ((flowScale D)⁻¹ • w) 0 := by
  have hbase : HasDerivAt (fun s : ℝ => (D.α (x, w) s).1) ((D.α (x, w) 0).2) 0 := by
    have h : HasDerivAt (fun s : ℝ => D.α (x, w) s)
        (chartSpray (cov := cov) z₀ (D.α (x, w) 0)) 0 :=
      D.hode (x, w) hwO 0 (by simpa using D.hρ.le)
    simpa [chartSpray_apply] using h.hasFDerivAt.fst.hasDerivAt
  have h1 : HasDerivAt (fun s : ℝ => (D.α (x, w) s).1) ((D.α (x, w) 0).2)
      ((0 : ℝ) * (flowScale D)⁻¹) := by
    simpa using hbase
  have h2 : HasDerivAt (fun r : ℝ => r * (flowScale D)⁻¹) ((flowScale D)⁻¹) 0 :=
    hasDerivAt_mul_const ((flowScale D)⁻¹)
  have h3 := HasDerivAt.scomp (0 : ℝ) h1 h2
  have h4 : (D.α (x, w) 0).2 = w := by rw [D.h0 (x, w) hwO]
  rw [h4] at h3
  exact h3

/-- **The ray identity at flow-time scale.**  For `r` near `0`, the chart-coordinate exponential
map along the ray `r ↦ r • u` equals the flow position at time `r * c⁻¹` with the *fixed* initial
velocity `c • u`: this is the homogeneity of the chart geodesic flow. -/
theorem Hfun_smul_ray (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : E}
    (hcuO : (x, flowScale D • u) ∈ D.O) (hxO : (x, 0) ∈ D.O) :
    (fun r : ℝ => Hfun D (x, r • u))
      =ᶠ[𝓝 (0 : ℝ)] (fun r : ℝ => (D.α (x, flowScale D • u) (r * (flowScale D)⁻¹)).1) := by
  have htl : |(flowScale D)⁻¹| ≤ D.ρ := by
    rw [inv_flowScale, abs_of_pos (div_pos D.hρ two_pos)]
    linarith [D.hρ]
  have hO : ∀ᶠ r in 𝓝 (0 : ℝ), (x, r • (flowScale D • u)) ∈ D.O := by
    have hc : Continuous (fun r : ℝ => (x, r • (flowScale D • u))) :=
      continuous_const.prodMk (continuous_id.smul continuous_const)
    have hmem : (x, (0 : ℝ) • (flowScale D • u)) ∈ D.O := by simpa using hxO
    have h1 : ∀ᶠ r in 𝓝 (0 : ℝ), (x, r • (flowScale D • u)) ∈ D.O :=
      hc.continuousAt.tendsto.eventually (D.hO.mem_nhds hmem)
    exact h1
  have hone : ∀ᶠ r : ℝ in 𝓝 (0 : ℝ), |r| ≤ 1 := by
    filter_upwards [Icc_mem_nhds (by norm_num : (-1 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1)]
      with r hr
    rw [abs_le]
    exact ⟨hr.1, hr.2⟩
  filter_upwards [hO, hone] with r hrO hr1
  rw [Hfun_apply]
  have hsm : flowScale D • (r • u) = r • (flowScale D • u) := smul_comm _ _ _
  rw [hsm]
  have hhom := chartFlowData_homogeneous (cov := cov) (I := I) D (q := x)
    (v := flowScale D • u) (c := r) (t := (flowScale D)⁻¹) hr1 hrO hcuO htl
  rw [hhom]

/-- **The derivative of `Hfun` along each ray is the direction of the ray.** -/
theorem hasDerivAt_Hfun_along (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x u : E}
    (hcuO : (x, flowScale D • u) ∈ D.O) (hxO : (x, 0) ∈ D.O) :
    HasDerivAt (fun r : ℝ => Hfun D (x, r • u)) u 0 := by
  have hder := hasDerivAt_flowPos (cov := cov) D (x := x) (w := flowScale D • u) hxO hcuO
  have hval : (flowScale D)⁻¹ • (flowScale D • u) = u := by
    rw [smul_smul, inv_mul_cancel₀ (flowScale_ne_zero D), one_smul]
  have hder2 : HasDerivAt (fun r : ℝ => (D.α (x, flowScale D • u) (r * (flowScale D)⁻¹)).1)
      ((flowScale D)⁻¹ • (flowScale D • u)) 0 := hder
  have hder' : HasDerivAt (fun r : ℝ => (D.α (x, flowScale D • u) (r * (flowScale D)⁻¹)).1)
      u 0 := by
    rw [hval] at hder2
    exact hder2
  exact hder'.congr_of_eventuallyEq (Hfun_smul_ray (cov := cov) D hcuO hxO)

/-! ## The differential of `Hfun` in the velocity variable at velocity zero -/

/-- **The differential of the chart-coordinate exponential map in the velocity variable, at zero
velocity, is the identity.**  This is the chart-level form of `d exp₀ = id`. -/
theorem fderiv_Hfun_apply_snd (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {x : E}
    (hx : (x, 0) ∈ chartData (I := I) z₀ Z) :
    ∀ u : E, (fderiv ℝ (Hfun D) (x, 0)) ((0 : E), u) = u := by
  have hxO : (x, 0) ∈ D.O := D.hKO hx
  have hcpos : 0 < flowScale D := flowScale_pos D
  have hH : HasFDerivAt (Hfun D) (fderiv ℝ (Hfun D) (x, 0)) (x, 0) :=
    ((contDiffAt_Hfun_zero (cov := cov) D hx).differentiableAt (by simp)).hasFDerivAt
  -- an openness threshold for the phases of `x`
  obtain ⟨δ, hδ, hδO⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ w : E, ‖w‖ < δ → (x, w) ∈ D.O := by
    have h1 : ∀ᶠ w : E in 𝓝 (0 : E), (x, w) ∈ D.O := by
      have hc : Continuous (fun w : E => (x, w)) := continuous_const.prodMk continuous_id
      have h2 : Tendsto (fun w : E => (x, w)) (𝓝 (0 : E)) (𝓝 (x, (0 : E))) :=
        hc.continuousAt.tendsto
      exact h2.eventually (D.hO.mem_nhds hxO)
    rw [Filter.eventually_iff] at h1
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhds_iff.mp h1
    exact ⟨δ, hδ, fun w hw => hsub (by rwa [Metric.mem_ball, dist_zero_right])⟩
  intro u
  set s : ℝ := min 1 (δ / (2 * (‖flowScale D • u‖ + 1))) with hsdef
  have hspos : 0 < s := lt_min one_pos (div_pos hδ (by positivity))
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hWnonneg : 0 ≤ ‖flowScale D • u‖ := norm_nonneg _
  have hsmall : ‖flowScale D • (s • u)‖ < δ := by
    have hexpr : ‖flowScale D • (s • u)‖ = s * (flowScale D * ‖u‖) := by
      rw [smul_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hcpos hspos)]
      ring
    have hWu : ‖flowScale D • u‖ = flowScale D * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
    rw [hexpr, ← hWu]
    have h1 : s * ‖flowScale D • u‖
        ≤ (δ / (2 * (‖flowScale D • u‖ + 1))) * ‖flowScale D • u‖ :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) hWnonneg
    have h2 : (δ / (2 * (‖flowScale D • u‖ + 1))) * ‖flowScale D • u‖ ≤ δ / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hWnonneg, hδ]
    linarith
  have hphaseO : (x, flowScale D • (s • u)) ∈ D.O := hδO _ hsmall
  have hder1 : HasDerivAt (fun r : ℝ => Hfun D (x, r • (s • u))) (s • u) 0 :=
    hasDerivAt_Hfun_along (cov := cov) D (x := x) (u := s • u) hphaseO hxO
  have hcurve : HasDerivAt (fun r : ℝ => ((x, r • (s • u)) : E × E)) ((0 : E), s • u) 0 := by
    have ha : HasDerivAt (fun _ : ℝ => x) (0 : E) (0 : ℝ) := hasDerivAt_const 0 x
    have hb : HasDerivAt (fun r : ℝ => r • (s • u)) (s • u) (0 : ℝ) := by
      have h : HasDerivAt (fun r : ℝ => r) (1 : ℝ) (0 : ℝ) := hasDerivAt_id' (0 : ℝ)
      simpa using h.smul_const (s • u)
    exact ha.prodMk hb
  have hH' : HasFDerivAt (Hfun D) (fderiv ℝ (Hfun D) (x, 0)) ((x, (0 : ℝ) • (s • u))) := by
    simpa using hH
  have hcomp := hH'.comp_hasDerivAt (0 : ℝ) hcurve
  have huniq : (fderiv ℝ (Hfun D) (x, 0)) ((0 : E), s • u) = s • u :=
    (hder1.unique hcomp).symm
  have hlin : (fderiv ℝ (Hfun D) (x, 0)) ((0 : E), s • u)
      = s • ((fderiv ℝ (Hfun D) (x, 0)) ((0 : E), u)) := by
    have h0 : (((0 : E), s • u) : E × E) = s • (((0 : E), u) : E × E) := by simp
    rw [h0, ContinuousLinearMap.map_smul]
  rw [hlin] at huniq
  have hfin := congrArg (fun v : E => s⁻¹ • v) huniq
  simpa [smul_smul, inv_mul_cancel₀ hsne, one_smul] using hfin

/-! ## Uniform injectivity of the chart-coordinate exponential map -/

/-- **Uniform injectivity of the chart-coordinate exponential map on a compact chart piece.** -/
theorem exists_uniform_injective_Hfun (D : ChartFlowData (cov := cov) (I := I) z₀ Z)
    (hZ : IsCompact Z) (hZsrc : Z ⊆ (chartAt H z₀).source) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ (extChartAt I z₀) '' Z, ∀ u v : E,
      ‖u‖ < ε → ‖v‖ < ε → Hfun D (x, u) = Hfun D (x, v) → u = v := by
  have hsub : Z ⊆ (extChartAt I z₀).source := fun q hq => by simpa using hZsrc hq
  have hK : IsCompact ((extChartAt I z₀) '' Z) :=
    hZ.image_of_continuousOn ((continuousOn_extChartAt (I := I) z₀).mono hsub)
  have hmem : ∀ x ∈ (extChartAt I z₀) '' Z, (x, (0 : E)) ∈ chartData (I := I) z₀ Z := by
    rintro x ⟨q, hq, rfl⟩
    exact ⟨⟨q, hq, rfl⟩, by rw [Metric.mem_closedBall, dist_zero_right]; norm_num⟩
  exact Commons.Analysis.Calculus.exists_uniform_injective_of_hasStrictFDerivAt hK
    (fun x => fderiv ℝ (Hfun D) (x, 0))
    (fun x hx => (contDiffAt_Hfun_zero (cov := cov) D (hmem x hx)).hasStrictFDerivAt (by simp))
    (fun x hx z => fderiv_Hfun_apply_snd (cov := cov) D (hmem x hx) z)

/-! ## From the chart model to the exponential map -/

/-- The chart-flow description of the exponential map, valid also at zero velocity. -/
theorem GExp_eq_symm_Hfun (hmet : IsMetricCompatible cov)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {q : M} (hqZ : q ∈ Z)
    (hqs : q ∈ (extChartAt I z₀).source) {u : E}
    (hu : ((extChartAt I z₀) q, flowScale D • u) ∈ D.O) :
    GExp (cov := cov) hmet q (frameVector (I := I) z₀ q u)
      = (extChartAt I z₀).symm (Hfun D ((extChartAt I z₀) q, u)) := by
  by_cases hu0 : u = 0
  · subst hu0
    have hcd : ((extChartAt I z₀) q, (0 : E)) ∈ chartData (I := I) z₀ Z :=
      ⟨⟨q, hqZ, rfl⟩, by rw [Metric.mem_closedBall, dist_zero_right]; norm_num⟩
    have hzero : Hfun D ((extChartAt I z₀) q, (0 : E)) = (extChartAt I z₀) q :=
      Hfun_zero (cov := cov) D hcd
    rw [frameVector_zero', GExp_zero, hzero]
    exact ((extChartAt I z₀).left_inv hqs).symm
  · exact GExp_eq_chartFlow (cov := cov) hmet D hqs u hu hu0

/-- **From injectivity in the chart model to injectivity of the exponential map on a ball.** -/
theorem injAtLeast_of_chartModel (hmet : IsMetricCompatible cov)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {q : M} (hqZ : q ∈ Z)
    (hqs : q ∈ (extChartAt I z₀).source)
    {lam ε η r : ℝ} (hlam : 0 < lam)
    (hgram : ∀ w : E, lam * ‖w‖ ^ 2 ≤ chartGram (I := I) z₀ q w w)
    (hr : r ≤ min ε η * Real.sqrt lam)
    (hphase : ∀ u : E, ‖u‖ ≤ η → ((extChartAt I z₀) q, flowScale D • u) ∈ D.O)
    (hinj : ∀ x ∈ (extChartAt I z₀) '' Z, ∀ u v : E, ‖u‖ < ε → ‖v‖ < ε →
      Hfun D (x, u) = Hfun D (x, v) → u = v) :
    InjAtLeast hmet q r := by
  have hsqpos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have htinv : |(flowScale D)⁻¹| ≤ D.ρ := by
    rw [inv_flowScale, abs_of_pos (div_pos D.hρ two_pos)]
    linarith [D.hρ]
  intro u v hu hv huv
  set a : E := (trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q u with hadef
  set b : E := (trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q v with hbdef
  have hua : frameVector (I := I) z₀ q a = u := frameVector_clm (I := I) hqs u
  have hvb : frameVector (I := I) z₀ q b = v := frameVector_clm (I := I) hqs v
  have hsqrt : ∀ w : E, ‖w‖ * Real.sqrt lam ≤ ‖frameVector (I := I) z₀ q w‖ := by
    intro w
    have h2 : (Real.sqrt lam * ‖w‖) ^ 2 = lam * ‖w‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hlam.le]
    calc ‖w‖ * Real.sqrt lam = Real.sqrt lam * ‖w‖ := by ring
      _ = Real.sqrt ((Real.sqrt lam * ‖w‖) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ = Real.sqrt (lam * ‖w‖ ^ 2) := by rw [h2]
      _ ≤ Real.sqrt (chartGram (I := I) z₀ q w w) := Real.sqrt_le_sqrt (hgram w)
      _ = ‖frameVector (I := I) z₀ q w‖ := (norm_frameVector (I := I) (z₀ := z₀) (q := q) w).symm
  have key : ∀ w : E, ‖w‖ < min ε η → ‖w‖ < ε ∧ ‖w‖ < η := by
    intro w hw
    exact ⟨lt_of_lt_of_le hw (min_le_left _ _), lt_of_lt_of_le hw (min_le_right _ _)⟩
  have hbnd : ∀ w : E, ‖frameVector (I := I) z₀ q w‖ < r → ‖w‖ < min ε η := by
    intro w hw
    have h1 : ‖w‖ * Real.sqrt lam < r := lt_of_le_of_lt (hsqrt w) hw
    have h2 : ‖w‖ * Real.sqrt lam < min ε η * Real.sqrt lam := lt_of_lt_of_le h1 hr
    exact lt_of_mul_lt_mul_right h2 hsqpos.le
  have haε : ‖a‖ < ε := (key a (hbnd a (by rw [hua]; exact hu))).1
  have haη : ‖a‖ < η := (key a (hbnd a (by rw [hua]; exact hu))).2
  have hbε : ‖b‖ < ε := (key b (hbnd b (by rw [hvb]; exact hv))).1
  have hbη : ‖b‖ < η := (key b (hbnd b (by rw [hvb]; exact hv))).2
  have haO : ((extChartAt I z₀) q, flowScale D • a) ∈ D.O := hphase a haη.le
  have hbO : ((extChartAt I z₀) q, flowScale D • b) ∈ D.O := hphase b hbη.le
  have hIa := GExp_eq_symm_Hfun (cov := cov) hmet D hqZ hqs (u := a) haO
  have hIb := GExp_eq_symm_Hfun (cov := cov) hmet D hqZ hqs (u := b) hbO
  have hueq : GExp (cov := cov) hmet q (frameVector (I := I) z₀ q a)
      = GExp (cov := cov) hmet q (frameVector (I := I) z₀ q b) := by
    rw [hua, hvb]; exact huv
  rw [hIa, hIb] at hueq
  have hmem1 : Hfun D ((extChartAt I z₀) q, a) ∈ (extChartAt I z₀).target :=
    D.htgt ((extChartAt I z₀) q, flowScale D • a) haO (flowScale D)⁻¹ htinv
  have hmem2 : Hfun D ((extChartAt I z₀) q, b) ∈ (extChartAt I z₀).target :=
    D.htgt ((extChartAt I z₀) q, flowScale D • b) hbO (flowScale D)⁻¹ htinv
  have hcong := congrArg (extChartAt I z₀) hueq
  rw [(extChartAt I z₀).right_inv hmem1, (extChartAt I z₀).right_inv hmem2] at hcong
  have hab : a = b := hinj ((extChartAt I z₀) q) ⟨q, hqZ, rfl⟩ a b haε hbε hcong
  rw [← hua, ← hvb, hab]

/-! ## The uniform injectivity radius of the manifold -/

/-- **The exponential map of a compact Riemannian manifold is uniformly injective on a ball of
positive radius around the origin of every tangent space.** -/
theorem exists_pos_injAllAtLeast (hmet : IsMetricCompatible cov) :
    ∃ ρ : ℝ, 0 < ρ ∧ InjAllAtLeast hmet ρ := by
  classical
  obtain ⟨n, z, Z, hZc, hZsrc, hcov⟩ :=
    Commons.Geometry.Manifold.exists_finite_cover_isCompact_subset_chartAt (I := I) (M := M)
  have hsub : ∀ i, Z i ⊆ (extChartAt I (z i)).source :=
    fun i q hq => by simpa using hZsrc i hq
  choose D _ using fun i => exists_chartFlowData (cov := cov) (I := I) (z₀ := z i) (Z := Z i)
    (hZc i) (hZsrc i)
  choose ε hεpos hεinj using fun i =>
    exists_uniform_injective_Hfun (cov := cov) (I := I) (z₀ := z i) (D i) (hZc i) (hZsrc i)
  have hgram : ∀ i, ∃ mu : ℝ, 0 < mu ∧ ∀ q ∈ Z i, ∀ w : E,
      mu * ‖w‖ ^ 2 ≤ chartGram (I := I) (z i) q w w := by
    intro i
    by_cases hne : (Z i).Nonempty
    · obtain ⟨lam, hlam, _Λ, _hΛ, hb⟩ :=
        exists_chartGram_bounds (I := I) (z i) (hZc i) hne (hZsrc i)
      exact ⟨lam, hlam, fun q hq w => (hb q hq w).1⟩
    · exact ⟨1, one_pos, fun q hq _ => absurd ⟨q, hq⟩ hne⟩
  choose lam hlampos hlampos' using hgram
  have hη : ∀ i, ∃ η : ℝ, 0 < η ∧ ∀ q ∈ Z i, ∀ u : E, ‖u‖ ≤ η →
      ((extChartAt I (z i)) q, flowScale (D i) • u) ∈ (D i).O :=
    fun i => exists_pos_phase_mem (cov := cov) (I := I) (z₀ := z i) (D i)
  choose η hηpos hηmem using hη
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    refine ⟨1, one_pos, fun q => ?_⟩
    obtain ⟨i, _⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ q))
    exact Fin.elim0 i
  · haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    let f : Fin n → ℝ := fun i => min (ε i) (η i) * Real.sqrt (lam i)
    let sf : Finset ℝ := (Finset.univ : Finset (Fin n)).image f
    have hfpos : ∀ i, 0 < f i := fun i =>
      mul_pos (lt_min (hεpos i) (hηpos i)) (Real.sqrt_pos.mpr (hlampos i))
    have hne : sf.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
    have hleast : ∀ y ∈ sf, sf.min' hne ≤ y := by
      intro y hy
      exact (Finset.isLeast_min' sf hne).2 hy
    refine ⟨sf.min' hne, ?_, ?_⟩
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem sf hne)
      rw [← hi]; exact hfpos i
    · intro q
      obtain ⟨i, hqi⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ q))
      refine injAtLeast_of_chartModel (cov := cov) hmet (D i) hqi (hsub i hqi) (hlampos i)
        (hlampos' i q hqi) ?_ (hηmem i q hqi) (hεinj i)
      exact hleast (f i) (Finset.mem_image_of_mem f (Finset.mem_univ i))

end

end Submission.UniformInj
