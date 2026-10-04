import Submission.GeodesicGlobal2
import Submission.Minimal
import Submission.ChartBounds
import Submission.GeodesicSpeed
import Submission.Length
import Submission.CurveField
import Submission.GeodesicExtend
import Submission.ChartConnection
import Submission.Commons.Analysis.ODE.secondOrderODE_eqOn_of_contDiffAt

set_option backward.isDefEq.respectTransparency.types false

/-!
# The global exponential map

This module builds the *global* exponential map of a complete (here: compact) Riemannian manifold
out of the local theory of `Submission/Geodesic.lean` and the geodesic-completeness theorem
`Submission.GeodesicGlobal2.exists_geodesic_segment`.

## Contents

* `curveVelocity_comp_mul`, `isGeodesicAt_comp_mul`: affine reparametrisation of the velocity and of
  the geodesic equation.
* `eventuallyEq_of_isGeodesicAt_of_eq`: **local uniqueness** of geodesics with the same initial
  data (position and velocity, the velocity being non-zero), proved from the chart ODE and its
  uniqueness theorem.
* `eqOn_Ioo_of_isGeodesicAt_of_eq`: **global uniqueness** on an interval, by the open-and-closed
  argument on the set where the two curves agree together with their velocities.
* the geodesic selection `geodCurve` coming from `exists_geodesic_segment` and the exponential map
  `GExp`, together with `GExp_zero`, `GExp_apply`, `GExp_spec` and `geodCurve_agree` /
  `geodCurve_agree_of_eq` (consistency of the chosen segments).
* **`exists_pos_GExp_eq_expMap`**: `GExp hmet x v = expMap cov x v` for `‖v‖` small (fibre norm).
  Proof: both sides are unit-speed geodesics with the same initial data, compared on `Ioo (-1) (3/2)`
  with `eqOn_Ioo_of_isGeodesicAt_of_eq`; the conversion between the fibre norm and the model norm of
  the chart uses `exists_chartGram_bounds` at `K = {x}`.  The helpers are
  `curveVelocity_chartCurve_zero` (the velocity of a chart geodesic at time `0`),
  `curveVelocity_ne_zero_of_hasChartGeodesic` (non-vanishing of that velocity),
  `contMDiffOn_chartCurve_small`, `isGeodesicAt_chartCurve_small` (smoothness and the geodesic
  equation for a chart solution on `Ioo (-1) (3/2)`).
* **`exists_pos_riemannianEDist_GExp_eq`**: local minimality of the *global* exponential map,
  `riemannianEDist I x (GExp hmet x v) = ofReal (√(chartGram x x v v))` for small `v`;
  **`exists_pos_riemannianEDist_GExp_smul`**: the same along a ray,
  `riemannianEDist I x (GExp hmet x (t • v)) = ofReal ‖t • v‖` for `t ≥ 0`.
* **`GExp_smul`** (the ray property): for `t ≥ 0`,
  `GExp hmet x (t • v) = (geodCurve hmet (max ‖v‖ (t * ‖v‖)) … x (unitOf v hv) …) (t * ‖v‖)`.
* `sqrt_chartGram_self` (`√(chartGram x x v v) = ‖v‖`), `isGeodesicAt_GExp_smul` and
  `norm_curveVelocity_GExp_smul`: for `0 < t` with `t * ‖v‖` below the uniform geodetic radius, the
  curve `s ↦ GExp hmet x (s • v)` is a geodesic at `t` of speed `‖v‖`.  (The germ comparison is
  one-sided at `t`: the curve for `s < 0` is the reversed ray in the direction `-v`, so the statement
  is not directly available at `t = 0`.)

## Hopf–Rinow: see `Submission/Roadmap.lean` §3.2

The two missing ingredients for Hopf–Rinow are (i) a *uniform* (in `x`) normal radius and (ii) the
local *no-corner* lemma (`d(p,y) = d(y,x) = ε`, `d(p,x) = 2ε` with minimising arcs ⟹ the arcs
align).  §3.2 of the roadmap records the analysis: (ii) reduces to the *equality case of the radial
inequality* `pathELength_ge_radial_of_stays` (or, equivalently, to the injectivity of `(d exp_z)_σ`
on the ball), and (i) needs either a uniform rerun of the analysis of `Minimal.lean` or a
continuity/flow statement for `GExp` in the base point.

## Design notes

The global exponential map is defined through a *chosen* unit-speed geodesic segment; the choices
are consistent by the uniqueness theorem proved here.  This is the input needed for Hopf–Rinow
(existence of minimizing geodesics) and for the geodesic variations used in the second-variation
formula.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.GeodesicGlobal2
open Submission.ChartBounds
open Submission.GeodesicSpeed
open Submission.Length
open Submission.Distance
open Submission.GeodesicExtend

namespace Submission.GlobalExp

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-! ## Affine reparametrisation -/

/-- The velocity of an affinely reparametrised curve. -/
lemma curveVelocity_comp_mul {γ : ℝ → M} {c t : ℝ}
    (hd : MDifferentiableAt 𝓘(ℝ) I γ (c * t)) :
    curveVelocity (I := I) (fun s : ℝ => γ (c * s)) t
      = c • curveVelocity (I := I) γ (c * t) := by
  have h := Submission.Length.curveVelocity_comp_mul_add (I := I) (γ := γ) (c := c) (d := 0)
    (t := t) (by simpa using hd)
  have hfun : (fun s : ℝ => γ (c * s + 0)) = (fun s : ℝ => γ (c * s)) := by
    funext s; rw [add_zero]
  rw [hfun] at h
  have hz : c * t + 0 = c * t := add_zero _
  rw [hz] at h
  exact h

/-- The geodesic equation is invariant under affine reparametrisation `t ↦ c * t` (`c ≠ 0`). -/
lemma isGeodesicAt_comp_mul {γ : ℝ → M} {c t : ℝ} (hc : c ≠ 0)
    (hmd : ∀ᶠ s in 𝓝 t, MDifferentiableAt 𝓘(ℝ) I γ (c * s))
    (hgeo : IsGeodesicAt cov γ (c * t)) :
    IsGeodesicAt cov (fun s : ℝ => γ (c * s)) t := by
  intro W hW hWev
  rw [curveVelocity_comp_mul (I := I) (hd := hmd.self_of_nhds)]
  -- the section `c⁻¹ • W` agrees with `γ'` near `c * t`
  have hW' : CMDiff ∞ (T% (fun x : M => c⁻¹ • W x)) := hW.const_smul_section (a := c⁻¹)
  have hWev' : ∀ᶠ u in 𝓝 (c * t),
      (fun x : M => c⁻¹ • W x) (γ u) = curveVelocity (I := I) γ u := by
    have hcont : Tendsto (fun u : ℝ => u / c) (𝓝 (c * t)) (𝓝 t) := by
      have h : ContinuousAt (fun u : ℝ => u / c) (c * t) := continuousAt_id.div_const c
      have hcalc : (c * t) / c = t := by field_simp
      simpa [hcalc] using h.tendsto
    filter_upwards [hcont.eventually hWev, hcont.eventually hmd] with u hu hs
    have hcs : c * (u / c) = u := by field_simp
    have hvel : curveVelocity (I := I) (fun s : ℝ => γ (c * s)) (u / c)
        = c • curveVelocity (I := I) γ u := by
      rw [curveVelocity_comp_mul (I := I) (hd := hs), hcs]
    rw [hcs] at hu
    rw [hvel] at hu
    rw [hu]
    -- goal: `c⁻¹ • (c • γ' u) = γ' u`
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  have h0 := hgeo (fun x : M => c⁻¹ • W x) hW' hWev'
  have hsmul : cov (fun x : M => c⁻¹ • W x) (γ (c * t))
      = c⁻¹ • cov W (γ (c * t)) :=
    cov.isCovariantDerivativeOn.smul_const c⁻¹ (hW.mdifferentiableAt (by simp))
  rw [hsmul, ContinuousLinearMap.smul_apply, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (inv_ne_zero hc)
  · rw [map_smul, h0, smul_zero]

/-! ## Uniqueness of geodesics with given initial data

The proof uses the chart form of the geodesic equation (`GeodesicGlobal.chartODE_of_isGeodesic`) and
the uniqueness theorem for second order ODEs.  We first prove that two geodesics with the same
position and velocity at a point agree on a neighbourhood of that point, then globalise by a
maximality argument. -/

/-- **Two functions with the same left germ and the same value have the same derivative.** -/
lemma deriv_eq_of_eventuallyEq_nhdsLT {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u w : ℝ → F} {d : ℝ} (hd : u d = w d)
    (hu : HasDerivAt u (deriv u d) d) (hw : HasDerivAt w (deriv w d) d)
    (h : u =ᶠ[𝓝[<] d] w) : deriv u d = deriv w d := by
  have hleft : (slope u d) =ᶠ[𝓝[<] d] (slope w d) := by
    filter_upwards [h] with t ht
    rw [slope_def_module, slope_def_module, ht, hd]
  have t1 : Tendsto (slope u d) (𝓝[<] d) (𝓝 (deriv u d)) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hu).1
  have t2 : Tendsto (slope w d) (𝓝[<] d) (𝓝 (deriv w d)) :=
    (hasDerivAt_iff_tendsto_slope_left_right.mp hw).1
  exact tendsto_nhds_unique t1 (t2.congr' hleft.symm)

/-- **Local uniqueness of geodesics.**  Two geodesics which are `C^∞` on an open set `V`, have the
same position and the same non-zero velocity at a point `t₀ ∈ V`, agree on a neighbourhood of
`t₀`.  (The non-vanishing of the velocity is needed to turn the intrinsic geodesic equation into the
chart ODE through the flow-box construction of
`CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity`.) -/
theorem eventuallyEq_of_isGeodesicAt_of_eq [I.Boundaryless] [ContMDiffCovariantDerivative cov ∞]
    {γ σ : ℝ → M} {V : Set ℝ} (hV : IsOpen V) {t₀ : ℝ} (ht₀ : t₀ ∈ V)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ V) (hσ : ContMDiffOn 𝓘(ℝ) I ∞ σ V)
    (hγgeo : ∀ t ∈ V, IsGeodesicAt cov γ t) (hσgeo : ∀ t ∈ V, IsGeodesicAt cov σ t)
    (hpt : γ t₀ = σ t₀) (hvel : curveVelocity (I := I) γ t₀ = curveVelocity (I := I) σ t₀)
    (hne : curveVelocity (I := I) γ t₀ ≠ 0) :
    γ =ᶠ[𝓝 t₀] σ := by
  classical
  have hneσ : curveVelocity (I := I) σ t₀ ≠ 0 := by rw [← hvel]; exact hne
  obtain ⟨Z, hZ, hZev⟩ :=
    CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity hV ht₀ hγ hne
  obtain ⟨Z', hZ', hZ'ev⟩ :=
    CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity hV ht₀ hσ hneσ
  set x₀ : M := γ t₀ with hx₀
  have hsrcγ : γ t₀ ∈ (chartAt H x₀).source := by rw [hx₀]; exact mem_chart_source H _
  have hsrcσ : σ t₀ ∈ (chartAt H x₀).source := by rw [← hpt, hx₀]; exact mem_chart_source H _
  obtain ⟨δ₁, hδ₁, hsrc₁, -, hder₁, hODE₁⟩ :=
    GeodesicGlobal.chartODE_of_isGeodesic (cov := cov) x₀ hV ht₀ hγ hsrcγ hγgeo Z hZ hZev
  obtain ⟨δ₂, hδ₂, hsrc₂, -, hder₂, hODE₂⟩ :=
    GeodesicGlobal.chartODE_of_isGeodesic (cov := cov) x₀ hV ht₀ hσ hsrcσ hσgeo Z' hZ' hZ'ev
  have hbase : γ t₀ = σ t₀ := hx₀.symm.trans hpt
  -- the coordinate derivatives agree at `t₀`
  have htgt₁ : (extChartAt I x₀) (γ t₀) ∈ (extChartAt I x₀).target := by
    rw [hx₀.symm]
    exact PartialEquiv.map_source (extChartAt I x₀) (mem_extChartAt_source x₀)
  have htgt₂ : (extChartAt I x₀) (σ t₀) ∈ (extChartAt I x₀).target := by
    rw [← hbase, hx₀.symm]
    exact PartialEquiv.map_source (extChartAt I x₀) (mem_extChartAt_source x₀)
  have hstay₁ : ∀ᶠ s in 𝓝 t₀, (extChartAt I x₀) (γ s) ∈ (extChartAt I x₀).target := by
    filter_upwards [Ioo_mem_nhds (a := t₀ - δ₁) (b := t₀ + δ₁) (by linarith) (by linarith)] with s hs
    have hs' : γ s ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hsrc₁ s hs
    exact PartialEquiv.map_source (extChartAt I x₀) hs'
  have hstay₂ : ∀ᶠ s in 𝓝 t₀, (extChartAt I x₀) (σ s) ∈ (extChartAt I x₀).target := by
    filter_upwards [Ioo_mem_nhds (a := t₀ - δ₂) (b := t₀ + δ₂) (by linarith) (by linarith)] with s hs
    have hs' : σ s ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hsrc₂ s hs
    exact PartialEquiv.map_source (extChartAt I x₀) hs'
  have hchartγ : (fun s => (extChartAt I x₀).symm ((extChartAt I x₀) (γ s))) =ᶠ[𝓝 t₀] γ := by
    filter_upwards [Ioo_mem_nhds (a := t₀ - δ₁) (b := t₀ + δ₁) (by linarith) (by linarith)] with s hs
    exact PartialEquiv.left_inv (extChartAt I x₀) (by rw [extChartAt_source]; exact hsrc₁ s hs)
  have hchartσ : (fun s => (extChartAt I x₀).symm ((extChartAt I x₀) (σ s))) =ᶠ[𝓝 t₀] σ := by
    filter_upwards [Ioo_mem_nhds (a := t₀ - δ₂) (b := t₀ + δ₂) (by linarith) (by linarith)] with s hs
    exact PartialEquiv.left_inv (extChartAt I x₀) (by rw [extChartAt_source]; exact hsrc₂ s hs)
  have hcv₁ : curveVelocity (I := I) γ t₀
      = frameVector (I := I) x₀ (γ t₀) (deriv (fun t => (extChartAt I x₀) (γ t)) t₀) := by
    have hleft : (extChartAt I x₀).symm ((extChartAt I x₀) (γ t₀)) = γ t₀ :=
      PartialEquiv.left_inv (extChartAt I x₀) (by rw [extChartAt_source]; exact hsrcγ)
    have h := curveVelocity_chartCurve (I := I) (u := fun s => (extChartAt I x₀) (γ s)) (t := t₀)
      (hder₁ t₀ ⟨by linarith, by linarith⟩) htgt₁ hstay₁
    rw [hleft] at h
    rw [← Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hchartγ]
    exact h
  have hcv₂ : curveVelocity (I := I) σ t₀
      = frameVector (I := I) x₀ (σ t₀) (deriv (fun t => (extChartAt I x₀) (σ t)) t₀) := by
    have hleft : (extChartAt I x₀).symm ((extChartAt I x₀) (σ t₀)) = σ t₀ :=
      PartialEquiv.left_inv (extChartAt I x₀) (by rw [extChartAt_source]; exact hsrcσ)
    have h := curveVelocity_chartCurve (I := I) (u := fun s => (extChartAt I x₀) (σ s)) (t := t₀)
      (hder₂ t₀ ⟨by linarith, by linarith⟩) htgt₂ hstay₂
    rw [hleft] at h
    rw [← Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hchartσ]
    exact h
  have hderEq : deriv (fun t => (extChartAt I x₀) (γ t)) t₀
      = deriv (fun t => (extChartAt I x₀) (σ t)) t₀ := by
    have hkey : frameVector (I := I) x₀ (γ t₀) (deriv (fun t => (extChartAt I x₀) (γ t)) t₀)
        = frameVector (I := I) x₀ (γ t₀) (deriv (fun t => (extChartAt I x₀) (σ t)) t₀) := by
      rw [← hcv₁, hvel, hcv₂]
      rw [show σ t₀ = γ t₀ from hbase.symm]
    have hsub : frameVector (I := I) x₀ (γ t₀)
        (deriv (fun t => (extChartAt I x₀) (γ t)) t₀
          - deriv (fun t => (extChartAt I x₀) (σ t)) t₀) = 0 := by
      have hlin : frameVector (I := I) x₀ (γ t₀)
          (deriv (fun t => (extChartAt I x₀) (γ t)) t₀
            - deriv (fun t => (extChartAt I x₀) (σ t)) t₀)
          = frameVector (I := I) x₀ (γ t₀) (deriv (fun t => (extChartAt I x₀) (γ t)) t₀)
            - frameVector (I := I) x₀ (γ t₀) (deriv (fun t => (extChartAt I x₀) (σ t)) t₀) := by
        simp only [frameVector, map_sub]
      rw [hlin, hkey, sub_self]
    exact sub_eq_zero.mp ((ChartBounds.frameVector_eq_zero_iff (I := I) (x₀ := x₀) hsrcγ _).mp hsub)
  -- the shifted coordinate curves
  set F : E × E → E := chartGeodesicVectorField cov x₀ with hF
  set u₁ : ℝ → E := fun s => (extChartAt I x₀) (γ (t₀ + s)) with hu₁
  set v₁ : ℝ → E := fun s => deriv (fun t => (extChartAt I x₀) (γ t)) (t₀ + s) with hv₁
  set u₂ : ℝ → E := fun s => (extChartAt I x₀) (σ (t₀ + s)) with hu₂
  set v₂ : ℝ → E := fun s => deriv (fun t => (extChartAt I x₀) (σ t)) (t₀ + s) with hv₂
  have hsol₁ : ∀ s ∈ Ioo (-δ₁) δ₁, HasDerivAt u₁ (v₁ s) s ∧ HasDerivAt v₁ (F (u₁ s, v₁ s)) s := by
    intro s hs
    have hs' : t₀ + s ∈ Ioo (t₀ - δ₁) (t₀ + δ₁) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    refine ⟨?_, ?_⟩
    · have hg : HasDerivAt (fun y : ℝ => t₀ + y) 1 s := (hasDerivAt_id s).const_add t₀
      have h := HasDerivAt.scomp s (hder₁ (t₀ + s) hs') hg
      simpa [u₁, v₁, Function.comp_def, one_smul] using h
    · have hg : HasDerivAt (fun y : ℝ => t₀ + y) 1 s := (hasDerivAt_id s).const_add t₀
      have h := HasDerivAt.scomp s (hODE₁ (t₀ + s) hs') hg
      simpa [u₁, v₁, F, Function.comp_def, one_smul] using h
  have hsol₂ : ∀ s ∈ Ioo (-δ₂) δ₂, HasDerivAt u₂ (v₂ s) s ∧ HasDerivAt v₂ (F (u₂ s, v₂ s)) s := by
    intro s hs
    have hs' : t₀ + s ∈ Ioo (t₀ - δ₂) (t₀ + δ₂) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    refine ⟨?_, ?_⟩
    · have hg : HasDerivAt (fun y : ℝ => t₀ + y) 1 s := (hasDerivAt_id s).const_add t₀
      have h := HasDerivAt.scomp s (hder₂ (t₀ + s) hs') hg
      simpa [u₂, v₂, Function.comp_def, one_smul] using h
    · have hg : HasDerivAt (fun y : ℝ => t₀ + y) 1 s := (hasDerivAt_id s).const_add t₀
      have h := HasDerivAt.scomp s (hODE₂ (t₀ + s) hs') hg
      simpa [u₂, v₂, F, Function.comp_def, one_smul] using h
  -- smoothness of the chart spray on the relevant interval
  have hG : ∀ t ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂), ContDiffAt ℝ 1 F (u₁ t, v₁ t) := by
    intro t ht
    have ht₁ : t₀ + t ∈ Ioo (t₀ - δ₁) (t₀ + δ₁) :=
      ⟨by linarith [ht.1, min_le_left δ₁ δ₂], by linarith [ht.2, min_le_left δ₁ δ₂]⟩
    have hmem : ((extChartAt I x₀).target ×ˢ (univ : Set E)) ∈ 𝓝 (u₁ t, v₁ t) := by
      refine (isOpen_extChartAt_target x₀).prod isOpen_univ |>.mem_nhds ⟨?_, trivial⟩
      exact PartialEquiv.map_source (extChartAt I x₀)
        (by rw [extChartAt_source]; exact hsrc₁ (t₀ + t) ht₁)
    have h := (Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray
      (cov := cov) x₀).contDiffAt hmem
    have hle : ((1 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) := WithTop.coe_le_coe.mpr le_top
    have hfun : F = (fun z : E × E =>
        - (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ ((extChartAt I x₀).symm z.1)
          (cov (fun q => (trivializationAt E (TangentSpace I) x₀).symmL ℝ q z.2)
            ((extChartAt I x₀).symm z.1)
            ((trivializationAt E (TangentSpace I) x₀).symmL ℝ ((extChartAt I x₀).symm z.1) z.2))) := by
      funext z
      rfl
    rw [hfun]
    exact h.of_le hle
  have hmin : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have h0eq : u₁ 0 = u₂ 0 ∧ v₁ 0 = v₂ 0 := by
    constructor
    · simp only [u₁, u₂, add_zero]
      rw [hbase]
    · simp only [v₁, v₂, add_zero]
      exact hderEq
  have heqOn : Set.EqOn u₁ u₂ (Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂)) :=
    Commons.Analysis.ODE.secondOrderODE_eqOn_of_contDiffAt (G := F) (ε := min δ₁ δ₂) hmin h0eq
      hG
      (fun t ht => hsol₁ t ⟨by linarith [ht.1, min_le_left δ₁ δ₂],
        by linarith [ht.2, min_le_left δ₁ δ₂]⟩)
      (fun t ht => hsol₂ t ⟨by linarith [ht.1, min_le_right δ₁ δ₂],
        by linarith [ht.2, min_le_right δ₁ δ₂]⟩)
  -- conclude
  have hfin : ∀ t ∈ Ioo (t₀ - min δ₁ δ₂) (t₀ + min δ₁ δ₂), γ t = σ t := by
    intro t ht
    have h1 : t₀ + (t - t₀) = t := by ring
    have hs : t - t₀ ∈ Ioo (-(min δ₁ δ₂)) (min δ₁ δ₂) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have heq := heqOn hs
    simp only [u₁, u₂] at heq
    rw [h1] at heq
    have hmemγ : γ t ∈ (extChartAt I x₀).source := by
      have : t ∈ Ioo (t₀ - δ₁) (t₀ + δ₁) := ⟨by linarith [ht.1, min_le_left δ₁ δ₂],
        by linarith [ht.2, min_le_left δ₁ δ₂]⟩
      rw [extChartAt_source]; exact hsrc₁ t this
    have hmemσ : σ t ∈ (extChartAt I x₀).source := by
      have : t ∈ Ioo (t₀ - δ₂) (t₀ + δ₂) := ⟨by linarith [ht.1, min_le_right δ₁ δ₂],
        by linarith [ht.2, min_le_right δ₁ δ₂]⟩
      rw [extChartAt_source]; exact hsrc₂ t this
    calc γ t = (extChartAt I x₀).symm ((extChartAt I x₀) (γ t)) :=
          (PartialEquiv.left_inv (extChartAt I x₀) hmemγ).symm
      _ = (extChartAt I x₀).symm ((extChartAt I x₀) (σ t)) := by rw [heq]
      _ = σ t := PartialEquiv.left_inv (extChartAt I x₀) hmemσ
  have hmem_nhds : Ioo (t₀ - min δ₁ δ₂) (t₀ + min δ₁ δ₂) ∈ 𝓝 t₀ :=
    Ioo_mem_nhds (by linarith [hmin]) (by linarith [hmin])
  exact Filter.eventuallyEq_of_mem hmem_nhds hfin

/-! ## Global uniqueness on an interval -/

/-- `Ioo a b` is a neighbourhood of `b` from the left (for `a < b`). -/
lemma Ioo_mem_nhdsWithin_lt {a b : ℝ} (hab : a < b) : Ioo a b ∈ 𝓝[<] b := by
  rw [nhdsWithin, Filter.mem_inf_principal]
  filter_upwards [Ioo_mem_nhds (a := a) (b := b + 1) hab (by linarith)] with x hx hxb
  exact ⟨hx.1, hxb⟩

/-- `Ioo a b` is a neighbourhood of `a` from the right (for `a < b`). -/
lemma Ioo_mem_nhdsWithin_gt {a b : ℝ} (hab : a < b) : Ioo a b ∈ 𝓝[>] a := by
  rw [nhdsWithin, Filter.mem_inf_principal]
  filter_upwards [Ioo_mem_nhds (a := a - 1) (b := b) (by linarith) hab] with x hx hxa
  exact ⟨hxa, hx.2⟩

/-- **Uniqueness of geodesics with the same initial data, to the right of the initial time.** -/
theorem eqOn_Ioo_right_of_isGeodesicAt_of_eq [I.Boundaryless] [ContMDiffCovariantDerivative cov ∞]
    {a b : ℝ} {γ σ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo a b)) (hσ : ContMDiffOn 𝓘(ℝ) I ∞ σ (Ioo a b))
    (hγgeo : ∀ t ∈ Ioo a b, IsGeodesicAt cov γ t) (hσgeo : ∀ t ∈ Ioo a b, IsGeodesicAt cov σ t)
    (hneγ : ∀ t ∈ Ioo a b, curveVelocity (I := I) γ t ≠ 0)
    (hneσ : ∀ t ∈ Ioo a b, curveVelocity (I := I) σ t ≠ 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hpt : γ t₀ = σ t₀)
    (hvel : curveVelocity (I := I) γ t₀ = curveVelocity (I := I) σ t₀) :
    EqOn γ σ (Ioo t₀ b) := by
  classical
  set R : Set ℝ := {T | t₀ ≤ T ∧ T ≤ b ∧ EqOn γ σ (Ioo t₀ T)} with hR
  have hRmem : t₀ ∈ R := ⟨le_rfl, ht₀.2.le, fun t ht => absurd ht.1 (not_lt.mpr ht.2.le)⟩
  have hRne : R.Nonempty := ⟨t₀, hRmem⟩
  have hbdd : BddAbove R := ⟨b, fun T hT => hT.2.1⟩
  have hβge : t₀ ≤ sSup R := le_csSup hbdd hRmem
  -- the agreement extends strictly past `t₀` by local uniqueness
  have hβgt : t₀ < sSup R := by
    have hloc₀ : γ =ᶠ[𝓝 t₀] σ := eventuallyEq_of_isGeodesicAt_of_eq (cov := cov) isOpen_Ioo ht₀
      hγ hσ hγgeo hσgeo hpt hvel (hneγ t₀ ht₀)
    obtain ⟨ε₀, hε₀, hε₀sub⟩ := Metric.mem_nhds_iff.mp hloc₀
    have hminpos : (0:ℝ) < min (ε₀ / 2) ((b - t₀) / 2) :=
      lt_min (by linarith) (by linarith [ht₀.2])
    have hmem : t₀ + min (ε₀ / 2) ((b - t₀) / 2) ∈ R := by
      refine ⟨by linarith [hminpos],
        by linarith [min_le_right (ε₀ / 2) ((b - t₀) / 2)], ?_⟩
      intro t ht
      have hdist : dist t t₀ < ε₀ := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [ht.1],
          by linarith [ht.2, min_le_left (ε₀ / 2) ((b - t₀) / 2)]⟩
      exact hε₀sub (Metric.mem_ball.mpr hdist)
    have := le_csSup hbdd hmem
    linarith [hminpos]
  have hβle : sSup R ≤ b := csSup_le hRne fun T hT => hT.2.1
  have hEqOn : EqOn γ σ (Ioo t₀ (sSup R)) := by
    intro t ht
    obtain ⟨T, hTR, htT⟩ := exists_lt_of_lt_csSup hRne ht.2
    exact hTR.2.2 ⟨ht.1, htT⟩
  -- continuity of both at the endpoint
  have hcontγ : ContinuousOn γ (Ioo a b) := hγ.continuousOn
  have hcontσ : ContinuousOn σ (Ioo a b) := hσ.continuousOn
  have hstep : sSup R = b := by
    by_contra hne
    have hβb : sSup R < b := lt_of_le_of_ne hβle hne
    have hβmem : sSup R ∈ Ioo a b := ⟨lt_of_lt_of_le ht₀.1 hβge, hβb⟩
    -- the positions agree at the endpoint
    have hptβ : γ (sSup R) = σ (sSup R) := by
      have hcγ : ContinuousAt γ (sSup R) := hcontγ.continuousAt (isOpen_Ioo.mem_nhds hβmem)
      have hcσ : ContinuousAt σ (sSup R) := hcontσ.continuousAt (isOpen_Ioo.mem_nhds hβmem)
      have hev : γ =ᶠ[𝓝[<] (sSup R)] σ := by
        filter_upwards [Ioo_mem_nhdsWithin_lt (a := t₀) (b := sSup R) hβgt] with t ht
        exact hEqOn ht
      exact tendsto_nhds_unique (hcγ.tendsto.mono_left nhdsWithin_le_nhds)
        ((hcσ.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm)
    -- the velocities agree at the endpoint
    have hvelβ : curveVelocity (I := I) γ (sSup R) = curveVelocity (I := I) σ (sSup R) := by
      set p : M := γ (sSup R) with hp
      have hpσ : σ (sSup R) = p := hptβ.symm
      have hsrcγ : γ (sSup R) ∈ (chartAt H p).source := by rw [hp]; exact mem_chart_source H _
      have hsrcσ : σ (sSup R) ∈ (chartAt H p).source := by rw [hpσ]; exact mem_chart_source H _
      obtain ⟨Z, hZ, hZev⟩ := CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity
        (γ := γ) isOpen_Ioo hβmem hγ (hneγ (sSup R) hβmem)
      obtain ⟨Z', hZ', hZ'ev⟩ := CurveField.exists_contMDiff_section_eventuallyEq_curveVelocity
        (γ := σ) isOpen_Ioo hβmem hσ (hneσ (sSup R) hβmem)
      obtain ⟨δ₁, hδ₁, hsrc₁, -, hder₁, -⟩ :=
        GeodesicGlobal.chartODE_of_isGeodesic (cov := cov) p isOpen_Ioo hβmem hγ hsrcγ hγgeo
          Z hZ hZev
      obtain ⟨δ₂, hδ₂, hsrc₂, -, hder₂, -⟩ :=
        GeodesicGlobal.chartODE_of_isGeodesic (cov := cov) p isOpen_Ioo hβmem hσ hsrcσ hσgeo
          Z' hZ' hZ'ev
      -- the coordinate derivatives agree at the endpoint (one-sided argument)
      have hleft : (fun t => (extChartAt I p) (γ t)) =ᶠ[𝓝[<] (sSup R)] (fun t => (extChartAt I p) (σ t)) := by
        filter_upwards [Ioo_mem_nhdsWithin_lt (a := (t₀ + sSup R) / 2) (b := sSup R)
          (by linarith [hβgt])] with t ht
        rw [hEqOn ⟨by linarith [ht.1], ht.2⟩]
      have hd : (extChartAt I p) (γ (sSup R)) = (extChartAt I p) (σ (sSup R)) :=
        congrArg (fun q : M => (extChartAt I p) q) hptβ
      have hder : deriv (fun t => (extChartAt I p) (γ t)) (sSup R)
          = deriv (fun t => (extChartAt I p) (σ t)) (sSup R) :=
        deriv_eq_of_eventuallyEq_nhdsLT hd (hder₁ (sSup R) ⟨by linarith, by linarith⟩)
          (hder₂ (sSup R) ⟨by linarith, by linarith⟩) hleft
      -- transfer to the intrinsic velocities
      have htgt₁ : (extChartAt I p) (γ (sSup R)) ∈ (extChartAt I p).target :=
        PartialEquiv.map_source (extChartAt I p) (by rw [extChartAt_source]; exact hsrcγ)
      have htgt₂ : (extChartAt I p) (σ (sSup R)) ∈ (extChartAt I p).target :=
        PartialEquiv.map_source (extChartAt I p) (by rw [extChartAt_source]; exact hsrcσ)
      have hstay₁ : ∀ᶠ s in 𝓝 (sSup R), (extChartAt I p) (γ s) ∈ (extChartAt I p).target := by
        filter_upwards [Ioo_mem_nhds (a := sSup R - δ₁) (b := sSup R + δ₁) (by linarith) (by linarith)]
          with s hs
        exact PartialEquiv.map_source (extChartAt I p)
          (by rw [extChartAt_source]; exact hsrc₁ s hs)
      have hstay₂ : ∀ᶠ s in 𝓝 (sSup R), (extChartAt I p) (σ s) ∈ (extChartAt I p).target := by
        filter_upwards [Ioo_mem_nhds (a := sSup R - δ₂) (b := sSup R + δ₂) (by linarith) (by linarith)]
          with s hs
        exact PartialEquiv.map_source (extChartAt I p)
          (by rw [extChartAt_source]; exact hsrc₂ s hs)
      have hchartγ : (fun s => (extChartAt I p).symm ((extChartAt I p) (γ s))) =ᶠ[𝓝 (sSup R)] γ := by
        filter_upwards [Ioo_mem_nhds (a := sSup R - δ₁) (b := sSup R + δ₁) (by linarith) (by linarith)]
          with s hs
        exact PartialEquiv.left_inv (extChartAt I p) (by rw [extChartAt_source]; exact hsrc₁ s hs)
      have hchartσ : (fun s => (extChartAt I p).symm ((extChartAt I p) (σ s))) =ᶠ[𝓝 (sSup R)] σ := by
        filter_upwards [Ioo_mem_nhds (a := sSup R - δ₂) (b := sSup R + δ₂) (by linarith) (by linarith)]
          with s hs
        exact PartialEquiv.left_inv (extChartAt I p) (by rw [extChartAt_source]; exact hsrc₂ s hs)
      have hcv₁ : curveVelocity (I := I) γ (sSup R)
          = frameVector (I := I) p (γ (sSup R)) (deriv (fun t => (extChartAt I p) (γ t)) (sSup R)) := by
        have hleft' : (extChartAt I p).symm ((extChartAt I p) (γ (sSup R))) = γ (sSup R) :=
          PartialEquiv.left_inv (extChartAt I p) (by rw [extChartAt_source]; exact hsrcγ)
        have h := curveVelocity_chartCurve (I := I) (u := fun s => (extChartAt I p) (γ s))
          (t := sSup R) (hder₁ (sSup R) ⟨by linarith, by linarith⟩) htgt₁ hstay₁
        rw [hleft'] at h
        rw [← Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hchartγ]
        exact h
      have hcv₂ : curveVelocity (I := I) σ (sSup R)
          = frameVector (I := I) p (σ (sSup R)) (deriv (fun t => (extChartAt I p) (σ t)) (sSup R)) := by
        have hleft' : (extChartAt I p).symm ((extChartAt I p) (σ (sSup R))) = σ (sSup R) :=
          PartialEquiv.left_inv (extChartAt I p) (by rw [extChartAt_source]; exact hsrcσ)
        have h := curveVelocity_chartCurve (I := I) (u := fun s => (extChartAt I p) (σ s))
          (t := sSup R) (hder₂ (sSup R) ⟨by linarith, by linarith⟩) htgt₂ hstay₂
        rw [hleft'] at h
        rw [← Submission.GeodesicExtend.curveVelocity_congr_of_eventuallyEq (I := I) hchartσ]
        exact h
      have hfr : (frameVector (I := I) p (γ (sSup R))
            (deriv (fun t => (extChartAt I p) (σ t)) (sSup R)) : E)
          = (frameVector (I := I) p (σ (sSup R))
            (deriv (fun t => (extChartAt I p) (σ t)) (sSup R)) : E) :=
        congrArg (fun q : M => (frameVector (I := I) p q
          (deriv (fun t => (extChartAt I p) (σ t)) (sSup R)) : E)) hptβ
      rw [hcv₁, hcv₂, hder]
      exact hfr
    -- extend using the local uniqueness
    have hloc : γ =ᶠ[𝓝 (sSup R)] σ := eventuallyEq_of_isGeodesicAt_of_eq (cov := cov) isOpen_Ioo hβmem
      hγ hσ hγgeo hσgeo hptβ hvelβ (hneγ (sSup R) hβmem)
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hloc
    have hminposR : (0:ℝ) < min (ε / 2) ((b - sSup R) / 2) :=
      lt_min (by linarith) (by linarith [hβb])
    have hmemR : sSup R + min (ε / 2) ((b - sSup R) / 2) ∈ R := by
      refine ⟨by linarith [hminposR],
        by linarith [min_le_right (ε / 2) ((b - sSup R) / 2)], ?_⟩
      intro t ht
      rcases lt_or_ge t (sSup R) with hlt | hge
      · exact hEqOn ⟨ht.1, hlt⟩
      · have hdist : dist t (sSup R) < ε := by
          rw [Real.dist_eq, abs_lt]
          exact ⟨by linarith, by linarith [ht.2, min_le_left (ε / 2) ((b - sSup R) / 2)]⟩
        exact hεsub (Metric.mem_ball.mpr hdist)
    have : sSup R + min (ε / 2) ((b - sSup R) / 2) ≤ sSup R := le_csSup hbdd hmemR
    linarith [hminposR]
  rw [hstep] at hEqOn
  exact hEqOn

/-- **Uniqueness of geodesics with the same initial data on an interval** (two-sided version,
obtained from the right-handed version by reflection `t ↦ -t`). -/
theorem eqOn_Ioo_of_isGeodesicAt_of_eq [I.Boundaryless] [ContMDiffCovariantDerivative cov ∞]
    {a b : ℝ} {γ σ : ℝ → M}
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ (Ioo a b)) (hσ : ContMDiffOn 𝓘(ℝ) I ∞ σ (Ioo a b))
    (hγgeo : ∀ t ∈ Ioo a b, IsGeodesicAt cov γ t) (hσgeo : ∀ t ∈ Ioo a b, IsGeodesicAt cov σ t)
    (hneγ : ∀ t ∈ Ioo a b, curveVelocity (I := I) γ t ≠ 0)
    (hneσ : ∀ t ∈ Ioo a b, curveVelocity (I := I) σ t ≠ 0)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hpt : γ t₀ = σ t₀)
    (hvel : curveVelocity (I := I) γ t₀ = curveVelocity (I := I) σ t₀) :
    EqOn γ σ (Ioo a b) := by
  have hright : EqOn γ σ (Ioo t₀ b) :=
    eqOn_Ioo_right_of_isGeodesicAt_of_eq hγ hσ hγgeo hσgeo hneγ hneσ ht₀ hpt hvel
  -- the reflected curves and the left half
  have hneg : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ) ∞ (fun t : ℝ => -t) (Ioo (-b) (-a)) :=
    (contDiff_neg (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : ℕ∞ω))).contMDiff.contMDiffOn
  have hγr_sm : ContMDiffOn 𝓘(ℝ) I ∞ (fun t : ℝ => γ (-t)) (Ioo (-b) (-a)) :=
    hγ.comp hneg (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hσr_sm : ContMDiffOn 𝓘(ℝ) I ∞ (fun t : ℝ => σ (-t)) (Ioo (-b) (-a)) :=
    hσ.comp hneg (fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩)
  have hfunγ : (fun s : ℝ => γ (-s)) = (fun s : ℝ => γ ((-1 : ℝ) * s)) := by
    funext s; rw [neg_one_mul]
  have hfunσ : (fun s : ℝ => σ (-s)) = (fun s : ℝ => σ ((-1 : ℝ) * s)) := by
    funext s; rw [neg_one_mul]
  have hγr_geo : ∀ t ∈ Ioo (-b) (-a), IsGeodesicAt cov (fun s : ℝ => γ (-s)) t := by
    intro t ht
    have ht' : ((-1 : ℝ) * t) ∈ Ioo a b := by
      rw [neg_one_mul]; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [hfunγ]
    refine isGeodesicAt_comp_mul (cov := cov) (c := -1) (t := t) (by norm_num) ?_
      (hγgeo (-1 * t) ht')
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hs' : (-1 : ℝ) * s ∈ Ioo a b := by
      rw [neg_one_mul]; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    exact (hγ.contMDiffAt (isOpen_Ioo.mem_nhds hs')).mdifferentiableAt (by simp)
  have hσr_geo : ∀ t ∈ Ioo (-b) (-a), IsGeodesicAt cov (fun s : ℝ => σ (-s)) t := by
    intro t ht
    have ht' : ((-1 : ℝ) * t) ∈ Ioo a b := by
      rw [neg_one_mul]; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [hfunσ]
    refine isGeodesicAt_comp_mul (cov := cov) (c := -1) (t := t) (by norm_num) ?_
      (hσgeo (-1 * t) ht')
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hs' : (-1 : ℝ) * s ∈ Ioo a b := by
      rw [neg_one_mul]; exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
    exact (hσ.contMDiffAt (isOpen_Ioo.mem_nhds hs')).mdifferentiableAt (by simp)
  have hmdγ : MDifferentiableAt 𝓘(ℝ) I γ ((-1 : ℝ) * -t₀) :=
    (hγ.contMDiffAt (isOpen_Ioo.mem_nhds (by rw [neg_one_mul, neg_neg]; exact ht₀))).mdifferentiableAt
      (by simp)
  have hmdσ : MDifferentiableAt 𝓘(ℝ) I σ ((-1 : ℝ) * -t₀) :=
    (hσ.contMDiffAt (isOpen_Ioo.mem_nhds (by rw [neg_one_mul, neg_neg]; exact ht₀))).mdifferentiableAt
      (by simp)
  have hγr_ne : ∀ t ∈ Ioo (-b) (-a), curveVelocity (I := I) (fun s : ℝ => γ (-s)) t ≠ 0 := by
    intro t ht
    have ht' : ((-1 : ℝ) * t) ∈ Ioo a b := by
      rw [neg_one_mul]; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hmd : MDifferentiableAt 𝓘(ℝ) I γ ((-1 : ℝ) * t) :=
      (hγ.contMDiffAt (isOpen_Ioo.mem_nhds ht')).mdifferentiableAt (by simp)
    rw [hfunγ, curveVelocity_comp_mul (I := I) hmd]
    intro h0
    rw [smul_eq_zero] at h0
    rcases h0 with h0 | h0
    · norm_num at h0
    · exact hneγ (-1 * t) ht' h0
  have hσr_ne : ∀ t ∈ Ioo (-b) (-a), curveVelocity (I := I) (fun s : ℝ => σ (-s)) t ≠ 0 := by
    intro t ht
    have ht' : ((-1 : ℝ) * t) ∈ Ioo a b := by
      rw [neg_one_mul]; exact ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have hmd : MDifferentiableAt 𝓘(ℝ) I σ ((-1 : ℝ) * t) :=
      (hσ.contMDiffAt (isOpen_Ioo.mem_nhds ht')).mdifferentiableAt (by simp)
    rw [hfunσ, curveVelocity_comp_mul (I := I) hmd]
    intro h0
    rw [smul_eq_zero] at h0
    rcases h0 with h0 | h0
    · norm_num at h0
    · exact hneσ (-1 * t) ht' h0
  have hpt' : (fun s : ℝ => γ (-s)) (-t₀) = (fun s : ℝ => σ (-s)) (-t₀) := by
    simp only [neg_neg]; exact hpt
  have e1 : curveVelocity (I := I) (fun s : ℝ => γ ((-1 : ℝ) * s)) (-t₀)
      = (-1 : ℝ) • curveVelocity (I := I) γ ((-1 : ℝ) * -t₀) :=
    curveVelocity_comp_mul (I := I) hmdγ
  have e2 : curveVelocity (I := I) (fun s : ℝ => σ ((-1 : ℝ) * s)) (-t₀)
      = (-1 : ℝ) • curveVelocity (I := I) σ ((-1 : ℝ) * -t₀) :=
    curveVelocity_comp_mul (I := I) hmdσ
  have hvel'' : curveVelocity (I := I) γ ((-1 : ℝ) * -t₀)
      = curveVelocity (I := I) σ ((-1 : ℝ) * -t₀) := by
    rw [show (-1 : ℝ) * -t₀ = t₀ by ring]
    exact hvel
  have hvel' : curveVelocity (I := I) (fun s : ℝ => γ (-s)) (-t₀)
      = curveVelocity (I := I) (fun s : ℝ => σ (-s)) (-t₀) := by
    rw [hfunγ, hfunσ, e1, e2, hvel'']
  have hleft : EqOn (fun s : ℝ => γ (-s)) (fun s : ℝ => σ (-s)) (Ioo (-t₀) (-a)) :=
    eqOn_Ioo_right_of_isGeodesicAt_of_eq hγr_sm hσr_sm hγr_geo hσr_geo hγr_ne hσr_ne
      (Set.mem_Ioo.mpr ⟨neg_lt_neg ht₀.2, neg_lt_neg ht₀.1⟩) hpt' hvel'
  intro t ht
  rcases lt_trichotomy t t₀ with hlt | heq | hgt
  · have hmem : -t ∈ Ioo (-t₀) (-a) := Set.mem_Ioo.mpr ⟨neg_lt_neg hlt, neg_lt_neg ht.1⟩
    have := hleft hmem
    simpa [neg_neg] using this
  · rw [heq]; exact hpt
  · exact hright ⟨hgt, ht.2⟩

section GExp

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M] [ContMDiffCovariantDerivative cov ∞]

/-- The uniform geodetic radius of `exists_geodesic_segment`. -/
noncomputable def geodDelta (hmet : IsMetricCompatible cov) : ℝ :=
  (exists_geodesic_segment (cov := cov) hmet).choose

lemma geodDelta_pos (hmet : IsMetricCompatible cov) : 0 < geodDelta (cov := cov) hmet :=
  (exists_geodesic_segment (cov := cov) hmet).choose_spec.1

/-- A chosen unit-speed geodesic segment with prescribed length `T ≥ 0`, initial point `x` and
initial unit velocity `ξ`. -/
noncomputable def geodCurve (hmet : IsMetricCompatible cov) (T : ℝ) (hT : 0 ≤ T) (x : M)
    (ξ : TangentSpace I x) (hξ : ‖ξ‖ = 1) : ℝ → M :=
  Classical.choose ((exists_geodesic_segment (cov := cov) hmet).choose_spec.2 T hT x ξ hξ)

lemma geodCurve_spec (hmet : IsMetricCompatible cov) (T : ℝ) (hT : 0 ≤ T) (x : M)
    (ξ : TangentSpace I x) (hξ : ‖ξ‖ = 1) :
    (geodCurve (cov := cov) hmet T hT x ξ hξ) 0 = x ∧
    curveVelocity (I := I) (geodCurve (cov := cov) hmet T hT x ξ hξ) 0 = ξ ∧
    ContMDiffOn 𝓘(ℝ) I ∞ (geodCurve (cov := cov) hmet T hT x ξ hξ)
      (Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet)) ∧
    (∀ t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet),
      IsGeodesicAt cov (geodCurve (cov := cov) hmet T hT x ξ hξ) t) ∧
    (∀ t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet),
      ‖curveVelocity (I := I) (geodCurve (cov := cov) hmet T hT x ξ hξ) t‖ = 1) :=
  Classical.choose_spec ((exists_geodesic_segment (cov := cov) hmet).choose_spec.2 T hT x ξ hξ)

/-- The unit vector in the direction of a non-zero tangent vector. -/
noncomputable def unitOf {x : M} (v : TangentSpace I x) (_hv : v ≠ 0) : TangentSpace I x :=
  ‖v‖⁻¹ • v

lemma unitOf_norm {x : M} (v : TangentSpace I x) (hv : v ≠ 0) : ‖unitOf v hv‖ = 1 := by
  rw [unitOf, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg v),
    inv_mul_cancel₀ (by simpa [norm_eq_zero] using hv)]

/-- **The consistency of the chosen geodesic segments**: segments with the same initial data and
different prescribed lengths agree on the shorter of the two domains. -/
lemma geodCurve_agree (hmet : IsMetricCompatible cov) {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁) (hT₂ : 0 ≤ T₂)
    (h12 : T₁ ≤ T₂) (x : M) (ξ : TangentSpace I x) (hξ : ‖ξ‖ = 1) :
    EqOn (geodCurve (cov := cov) hmet T₁ hT₁ x ξ hξ)
      (geodCurve (cov := cov) hmet T₂ hT₂ x ξ hξ)
      (Ioo (-(geodDelta (cov := cov) hmet)) (T₁ + geodDelta (cov := cov) hmet)) := by
  obtain ⟨h01, hv1, hsm1, hgeo1, hsp1⟩ := geodCurve_spec (cov := cov) hmet T₁ hT₁ x ξ hξ
  obtain ⟨h02, hv2, hsm2, hgeo2, hsp2⟩ := geodCurve_spec (cov := cov) hmet T₂ hT₂ x ξ hξ
  have hle : T₁ + geodDelta (cov := cov) hmet ≤ T₂ + geodDelta (cov := cov) hmet := by linarith
  have hsub : Ioo (-(geodDelta (cov := cov) hmet)) (T₁ + geodDelta (cov := cov) hmet)
      ⊆ Ioo (-(geodDelta (cov := cov) hmet)) (T₂ + geodDelta (cov := cov) hmet) :=
    fun t ht => ⟨ht.1, lt_of_lt_of_le ht.2 hle⟩
  refine eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) (a := -(geodDelta (cov := cov) hmet))
    (b := T₁ + geodDelta (cov := cov) hmet) hsm1 (hsm2.mono hsub)
    hgeo1 (fun t ht => hgeo2 t (hsub ht))
    (fun t ht => by
      intro h0
      have h := hsp1 t ht
      rw [h0, norm_zero] at h
      norm_num at h)
    (fun t ht => by
      intro h0
      have h := hsp2 t (hsub ht)
      rw [h0, norm_zero] at h
      norm_num at h)
    (show (0 : ℝ) ∈ Ioo (-(geodDelta (cov := cov) hmet))
        (T₁ + geodDelta (cov := cov) hmet) from
      Set.mem_Ioo.mpr ⟨by linarith [geodDelta_pos (cov := cov) hmet],
        by linarith [geodDelta_pos (cov := cov) hmet, hT₁]⟩) ?_ ?_
  · rw [h01, h02]
  · rw [hv1, hv2]

/-- **The global exponential map**: the time-one point of the geodesic through `x` with velocity
`v`.  For `v = 0` it is `x` by convention; for `v ≠ 0` it is the endpoint of the chosen unit-speed
segment of length `‖v‖` in the direction of `v`. -/
noncomputable def GExp (hmet : IsMetricCompatible cov) (x : M) (v : TangentSpace I x) : M := by
  classical
  exact if hv : v = 0 then x
    else (geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) x (unitOf v hv) (unitOf_norm v hv)) ‖v‖

@[simp] lemma GExp_zero (hmet : IsMetricCompatible cov) (x : M) :
    GExp (cov := cov) hmet x 0 = x := by
  rw [GExp]; exact dif_pos rfl

lemma GExp_apply (hmet : IsMetricCompatible cov) {x : M} {v : TangentSpace I x} (hv : v ≠ 0) :
    GExp (cov := cov) hmet x v
      = (geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) x (unitOf v hv) (unitOf_norm v hv)) ‖v‖ := by
  rw [GExp]; exact dif_neg hv

/-- The properties of the chosen segment underlying the exponential map. -/
lemma GExp_spec (hmet : IsMetricCompatible cov) {x : M} {v : TangentSpace I x} (hv : v ≠ 0) :
    ContMDiffOn 𝓘(ℝ) I ∞ (geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) x (unitOf v hv)
        (unitOf_norm v hv))
      (Ioo (-(geodDelta (cov := cov) hmet)) (‖v‖ + geodDelta (cov := cov) hmet)) ∧
    (∀ t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (‖v‖ + geodDelta (cov := cov) hmet),
      IsGeodesicAt cov (geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) x (unitOf v hv)
        (unitOf_norm v hv)) t) ∧
    (∀ t ∈ Ioo (-(geodDelta (cov := cov) hmet)) (‖v‖ + geodDelta (cov := cov) hmet),
      ‖curveVelocity (I := I) (geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) x (unitOf v hv)
        (unitOf_norm v hv)) t‖ = 1) :=
  (geodCurve_spec (cov := cov) hmet ‖v‖ (norm_nonneg v) x (unitOf v hv) (unitOf_norm v hv)).2.2

/-! ## Agreement of the global exponential map with the chart exponential map -/

/-- **The velocity at time `0` of the curve of a chart geodesic is the initial tangent vector.** -/
lemma curveVelocity_chartCurve_zero
    {x : M} {v : TangentSpace I x} {u w : ℝ → E}
    (h : HasChartGeodesic cov x v u w) :
    curveVelocity (I := I) (fun s : ℝ => (extChartAt I x).symm (u s)) 0 = v := by
  have htgt : u 0 ∈ (extChartAt I x).target := h.2.2.1 0 (by norm_num)
  have hstay : ∀ᶠ s in 𝓝 (0 : ℝ), u s ∈ (extChartAt I x).target := by
    filter_upwards [isOpen_Ioo.mem_nhds (by norm_num : (0 : ℝ) ∈ Ioo (-2) 2)] with s hs
    exact h.2.2.1 s hs
  have hh := curveVelocity_extChartAt_symm (I := I) (x₀ := x) (u := u) (t := 0) (v := w 0)
    (h.2.2.2.1 0 (by norm_num)) htgt hstay
  rw [hh, h.1, h.2.1, PartialEquiv.left_inv (extChartAt I x) (mem_extChartAt_source x)]
  exact Trivialization.symmL_continuousLinearMapAt (R := ℝ) (b := x)
    (e := trivializationAt E (TangentSpace I) x) (by simp) v

/-- **The velocity of a chart geodesic is nowhere zero** where the initial velocity is nonzero. -/
lemma curveVelocity_ne_zero_of_hasChartGeodesic
    (hmet : IsMetricCompatible cov) (x : M)
    {v : TangentSpace I x} (hv : v ≠ 0) {u w : ℝ → E} (h : HasChartGeodesic cov x v u w)
    {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) :
    curveVelocity (I := I) (fun s : ℝ => (extChartAt I x).symm (u s)) t ≠ 0 := by
  intro h0
  have hgram := hasChartGeodesic_chartGram_const (cov := cov) hmet x h t ht
  have hpos : 0 < chartGram (I := I) x ((extChartAt I x).symm (u t)) (w t) (w t) := by
    rw [hgram]
    exact chartGram_self_pos (I := I) (mem_chart_source H x) (show (v : E) ≠ 0 from hv)
  have hvel : curveVelocity (I := I) (fun s : ℝ => (extChartAt I x).symm (u s)) t
      = frameVector (I := I) x ((extChartAt I x).symm (u t)) (w t) := by
    have htgt : u t ∈ (extChartAt I x).target := h.2.2.1 t ht
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x).target := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact h.2.2.1 s hs
    exact curveVelocity_extChartAt_symm (I := I) (x₀ := x) (u := u) (t := t) (v := w t)
      (h.2.2.2.1 t ht) htgt hstay
  have hgram0 : chartGram (I := I) x ((extChartAt I x).symm (u t)) (w t) (w t) = 0 := by
    rw [chartGram_apply, hvel.symm, h0, inner_zero_right]
  rw [hgram0] at hpos
  exact lt_irrefl 0 hpos

/-- The chart curve of a chart geodesic, restricted to `Ioo (-1) (3/2)`. -/
lemma contMDiffOn_chartCurve_small
    {x : M} {v : TangentSpace I x} {u w : ℝ → E} (h : HasChartGeodesic cov x v u w) :
    ContMDiffOn 𝓘(ℝ) I ∞ (fun s : ℝ => (extChartAt I x).symm (u s)) (Ioo (-1 : ℝ) (3/2)) :=
  GeodesicGlobal.contMDiffOn_chartCurve_of_chartODE (cov := cov) x
    (fun t ht => h.2.2.1 t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (fun t ht => h.2.2.2.1 t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (fun t ht => h.2.2.2.2 t ⟨by linarith [ht.1], by linarith [ht.2]⟩)

/-- The chart curve of a chart geodesic is a geodesic on `Ioo (-1) (3/2)`. -/
lemma isGeodesicAt_chartCurve_small
    {x : M} {v : TangentSpace I x} {u w : ℝ → E} (h : HasChartGeodesic cov x v u w)
    {t : ℝ} (ht : t ∈ Ioo (-1 : ℝ) (3/2)) :
    IsGeodesicAt cov (fun s : ℝ => (extChartAt I x).symm (u s)) t :=
  GeodesicGlobal.isGeodesicAt_of_chartODE cov x (by norm_num : (-1 : ℝ) < 3/2) ht
    (fun t ht => h.2.2.1 t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (fun t ht => h.2.2.2.1 t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (fun t ht => h.2.2.2.2 t ⟨by linarith [ht.1], by linarith [ht.2]⟩)

/-- **The global exponential map agrees with the chart exponential map near the origin.** -/
theorem exists_pos_GExp_eq_expMap (hmet : IsMetricCompatible cov) (x : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : TangentSpace I x, ‖v‖ < ρ →
      GExp (cov := cov) hmet x v = expMap cov x v := by
  classical
  obtain ⟨ρ₀, hρ₀, hex₀⟩ := exists_pos_hasChartGeodesic (cov := cov) x
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := exists_chartGram_bounds (I := I) x
    (K := ({x} : Set M)) isCompact_singleton ⟨x, rfl⟩
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hxsrc)
  have hgd : 0 < geodDelta (cov := cov) hmet := geodDelta_pos (cov := cov) hmet
  have hsqlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  refine ⟨min (Real.sqrt lam * ρ₀) (geodDelta (cov := cov) hmet) / 2, by positivity,
    fun v hv => ?_⟩
  -- the model-space norm of `v` is small (the chart metric at the base point dominates it)
  have hvρ₀ : (fun z : E => ‖z‖) v < ρ₀ := by
    have h1 : lam * ((fun z : E => ‖z‖) v) ^ 2 ≤ chartGram (I := I) x x (v : E) (v : E) :=
      (hbnd x (by simp) (v : E)).1
    have h2 : chartGram (I := I) x x (v : E) (v : E) = ‖v‖ ^ 2 := by
      rw [chartGram_self_apply (I := I) x (v : E) (v : E), real_inner_self_eq_norm_sq]
    have h3 : ‖v‖ < Real.sqrt lam * ρ₀ := by
      have h := hv
      have h1' : min (Real.sqrt lam * ρ₀) (geodDelta (cov := cov) hmet)
          ≤ Real.sqrt lam * ρ₀ := min_le_left _ _
      nlinarith [h, h1', hsqlam, hρ₀]
    have hs : (Real.sqrt lam * ρ₀) ^ 2 = lam * ρ₀ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hlam.le]
    have h5 : lam * ((fun z : E => ‖z‖) v) ^ 2 < lam * ρ₀ ^ 2 :=
      calc lam * ((fun z : E => ‖z‖) v) ^ 2
          ≤ chartGram (I := I) x x (v : E) (v : E) := h1
        _ = ‖v‖ ^ 2 := h2
        _ < (Real.sqrt lam * ρ₀) ^ 2 := by
          have hc : 0 ≤ Real.sqrt lam * ρ₀ := mul_nonneg hsqlam.le hρ₀.le
          have hlt := (mul_self_lt_mul_self_iff (norm_nonneg v) hc).mp h3
          simpa only [pow_two] using hlt
        _ = lam * ρ₀ ^ 2 := hs
    have h6 : ((fun z : E => ‖z‖) v) ^ 2 < ρ₀ ^ 2 := by nlinarith [h5, hlam]
    nlinarith [h6, norm_nonneg ((fun z : E => ‖z‖) v), le_of_lt hρ₀]
  have hvgd : ‖v‖ < geodDelta (cov := cov) hmet := by
    have h := hv
    have h1 : min (Real.sqrt lam * ρ₀) (geodDelta (cov := cov) hmet)
        ≤ geodDelta (cov := cov) hmet := min_le_right _ _
    linarith
  have hmod : (fun z : E => ‖z‖) v ≤ ρ₀ := le_of_lt hvρ₀
  obtain ⟨u, w, huw⟩ := hex₀ v hmod
  by_cases hv0 : v = 0
  · subst hv0; rw [GExp_zero, expMap_zero]
  -- the two curves
  set γ : ℝ → M := fun s : ℝ => (extChartAt I x).symm (u s) with hγdef
  set ξ : TangentSpace I x := unitOf v hv0 with hξdef
  have hξnorm : ‖ξ‖ = 1 := unitOf_norm v hv0
  set η : ℝ → M :=
    fun s : ℝ => (geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) x ξ hξnorm) (‖v‖ * s)
    with hηdef
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  -- the underlying segment of `η`
  obtain ⟨hgc0, hgcv, hgcsm, hgcgeo, hgcspeed⟩ :=
    geodCurve_spec (cov := cov) hmet ‖v‖ (norm_nonneg v) x ξ hξnorm
  have hmem : ∀ s ∈ Ioo (-1 : ℝ) (3/2),
      ‖v‖ * s ∈ Ioo (-(geodDelta (cov := cov) hmet)) (‖v‖ + geodDelta (cov := cov) hmet) := by
    intro s hs
    refine Set.mem_Ioo.mpr ⟨?_, ?_⟩
    · have : ‖v‖ * (-1) = -‖v‖ := by ring
      nlinarith [hs.1, hvpos]
    · nlinarith [hs.2, hvpos, hvgd]
  have hηsm : ContMDiffOn 𝓘(ℝ) I ∞ η (Ioo (-1 : ℝ) (3/2)) := by
    have hlin : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun s : ℝ => ‖v‖ * s) (Ioo (-1 : ℝ) (3/2)) :=
      (contMDiff_const.mul contMDiff_id).contMDiffOn
    have hcomp : ContMDiffOn 𝓘(ℝ) I ∞
        ((geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) x ξ hξnorm) ∘
          fun s : ℝ => ‖v‖ * s) (Ioo (-1 : ℝ) (3/2)) :=
      hgcsm.comp hlin hmem
    simpa only [hηdef, Function.comp_def] using hcomp
  have hηgeo : ∀ t ∈ Ioo (-1 : ℝ) (3/2), IsGeodesicAt cov η t := by
    intro t ht
    have hpre : (fun s : ℝ => ‖v‖ * s) ⁻¹'
        (Ioo (-(geodDelta (cov := cov) hmet)) (‖v‖ + geodDelta (cov := cov) hmet)) ∈ 𝓝 t :=
      (continuousAt_const.mul continuousAt_id).preimage_mem_nhds
        (IsOpen.mem_nhds isOpen_Ioo (hmem t ht))
    have hmd : ∀ᶠ s in 𝓝 t,
        MDifferentiableAt 𝓘(ℝ) I (geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) x ξ hξnorm)
          (‖v‖ * s) := by
      filter_upwards [hpre] with s hs
      exact (hgcsm.contMDiffAt (IsOpen.mem_nhds isOpen_Ioo hs)).mdifferentiableAt (by simp)
    have h := isGeodesicAt_comp_mul (cov := cov) (γ := geodCurve (cov := cov) hmet ‖v‖
      (norm_nonneg v) x ξ hξnorm) (c := ‖v‖) (t := t) (ne_of_gt hvpos) hmd
      (hgcgeo (‖v‖ * t) (hmem t ht))
    simpa only [hηdef] using h
  have hηne : ∀ t ∈ Ioo (-1 : ℝ) (3/2), curveVelocity (I := I) η t ≠ 0 := by
    intro t ht
    have hvelη : curveVelocity (I := I) η t
        = (‖v‖ : ℝ) • curveVelocity (I := I) (geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v)
            x ξ hξnorm) (‖v‖ * t) := by
      rw [hηdef]
      exact curveVelocity_comp_mul (I := I)
        ((hgcsm.contMDiffAt (IsOpen.mem_nhds isOpen_Ioo (hmem t ht))).mdifferentiableAt
          (by simp))
    intro hzero
    have hnorm : ‖curveVelocity (I := I) η t‖ = ‖v‖ := by
      rw [hvelη, norm_smul, Real.norm_eq_abs, abs_of_pos hvpos,
        hgcspeed (‖v‖ * t) (hmem t ht), mul_one]
    rw [hzero, norm_zero] at hnorm
    exact hvpos.ne' hnorm.symm
  have hγne : ∀ t ∈ Ioo (-1 : ℝ) (3/2), curveVelocity (I := I) γ t ≠ 0 := by
    intro t ht
    exact curveVelocity_ne_zero_of_hasChartGeodesic (cov := cov) hmet x hv0 huw
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
  -- the initial data agree
  have hpt : γ 0 = η 0 := by
    have h1 : γ 0 = x := by
      rw [hγdef]
      show (extChartAt I x).symm (u 0) = x
      rw [huw.1]
      exact (extChartAt I x).left_inv (mem_extChartAt_source x)
    have h2 : η 0 = x := by
      rw [hηdef]
      show (geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) x ξ hξnorm) (‖v‖ * 0) = x
      rw [mul_zero, hgc0]
    exact h1.trans h2.symm
  have hvel : curveVelocity (I := I) γ 0 = curveVelocity (I := I) η 0 := by
    have h1E : (curveVelocity (I := I) γ 0 : E) = (v : E) :=
      curveVelocity_chartCurve_zero (I := I) huw
    have h2E : (curveVelocity (I := I) η 0 : E) = (v : E) := by
      have hd : MDifferentiableAt 𝓘(ℝ) I (geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) x ξ
          hξnorm) (‖v‖ * 0) :=
        (hgcsm.contMDiffAt (IsOpen.mem_nhds isOpen_Ioo (hmem 0 (by norm_num)))).mdifferentiableAt
          (by simp)
      have hcomp : (curveVelocity (I := I) η 0 : E)
          = (fun z : E => (‖v‖ : ℝ) • z) (curveVelocity (I := I) (geodCurve (cov := cov) hmet
              ‖v‖ (norm_nonneg v) x ξ hξnorm) (‖v‖ * 0) : E) := by
        rw [hηdef]
        exact curveVelocity_comp_mul (I := I) hd
      have hb : (curveVelocity (I := I) (geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) x ξ
          hξnorm) (‖v‖ * 0) : E) = (ξ : E) := by
        have h1 := congrArg (fun r : ℝ => (curveVelocity (I := I) (geodCurve (cov := cov) hmet
          ‖v‖ (norm_nonneg v) x ξ hξnorm) r : E)) (mul_zero ‖v‖)
        rw [h1]
        exact hgcv
      have hsmT : (‖v‖ : ℝ) • ξ = v := by
        rw [hξdef, unitOf, smul_smul, mul_inv_cancel₀ (ne_of_gt hvpos), one_smul]
      have hsm : (fun z : E => (‖v‖ : ℝ) • z) (ξ : E) = (v : E) := hsmT
      exact hcomp.trans ((congrArg (fun z : E => (‖v‖ : ℝ) • z) hb).trans hsm)
    exact h1E.trans h2E.symm
  have hEqOn := eqOn_Ioo_of_isGeodesicAt_of_eq (cov := cov) (a := (-1 : ℝ)) (b := 3/2)
    (contMDiffOn_chartCurve_small (I := I) huw) hηsm
    (fun t ht => isGeodesicAt_chartCurve_small (I := I) huw ht) hηgeo hγne hηne
    (by norm_num : (0 : ℝ) ∈ Ioo (-1) (3/2)) hpt hvel
  have h1 : γ 1 = η 1 := hEqOn (by norm_num : (1 : ℝ) ∈ Ioo (-1) (3/2))
  have hη1 : η 1 = (geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) x ξ hξnorm) ‖v‖ := by
    rw [hηdef]
    simp only [mul_one]
  have hγ1 : γ 1 = (extChartAt I x).symm (u 1) := by rw [hγdef]
  calc GExp (cov := cov) hmet x v
      = (geodCurve (cov := cov) hmet ‖v‖ (norm_nonneg v) x ξ hξnorm) ‖v‖ :=
        GExp_apply (cov := cov) hmet hv0
    _ = η 1 := hη1.symm
    _ = γ 1 := h1.symm
    _ = (extChartAt I x).symm (u 1) := hγ1
    _ = expMap cov x v := (expMap_eq_of_hasChartGeodesic (cov := cov) huw).symm

/-- **Local minimality for the global exponential map.**  For `v` in a small ball, the Riemannian
distance from `x` to `GExp x v` is exactly the Riemannian length `√(chartGram x x v v)` of `v`
(`= ‖v‖` in the fibre metric).  This transfers `Minimal.riemannianEDist_expMap_eq` to `GExp` via
`exists_pos_GExp_eq_expMap`. -/
theorem exists_pos_riemannianEDist_GExp_eq (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) (x : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v : TangentSpace I x, ‖v‖ < ρ →
      Manifold.riemannianEDist I x (GExp (cov := cov) hmet x v)
        = ENNReal.ofReal (Real.sqrt (chartGram (I := I) x x (v : E) (v : E))) := by
  classical
  haveI : IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x) :=
    Submission.EDist.isContinuousRiemannianBundle_infty (I := I)
  obtain ⟨ρ₁, hρ₁, hagree⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet x
  obtain ⟨ρ₂, hρ₂, hmineq⟩ := Submission.Minimal.riemannianEDist_expMap_eq (I := I) (cov := cov)
    hmet htor x
  have hxsrc : x ∈ (chartAt H x).source := mem_chart_source H x
  obtain ⟨lam, hlam, Lam, hLam, hbnd⟩ := exists_chartGram_bounds (I := I) x
    (K := ({x} : Set M)) isCompact_singleton ⟨x, rfl⟩
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hxsrc)
  have hsqlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  refine ⟨min (Real.sqrt lam * ρ₂) ρ₁ / 2, by positivity, fun v hv => ?_⟩
  have hvρ₁ : ‖v‖ < ρ₁ := by
    have h := hv
    have h1 : min (Real.sqrt lam * ρ₂) ρ₁ ≤ ρ₁ := min_le_right _ _
    linarith
  have hmodel : (fun z : E => ‖z‖) v < ρ₂ := by
    have h1 : lam * ((fun z : E => ‖z‖) v) ^ 2 ≤ chartGram (I := I) x x (v : E) (v : E) :=
      (hbnd x (by simp) (v : E)).1
    have h2 : chartGram (I := I) x x (v : E) (v : E) = ‖v‖ ^ 2 := by
      rw [chartGram_self_apply (I := I) x (v : E) (v : E), real_inner_self_eq_norm_sq]
    have h3 : ‖v‖ < Real.sqrt lam * ρ₂ := by
      have h := hv
      have h1' : min (Real.sqrt lam * ρ₂) ρ₁ ≤ Real.sqrt lam * ρ₂ := min_le_left _ _
      nlinarith [h, h1', hsqlam, hρ₂]
    have h5 : lam * ((fun z : E => ‖z‖) v) ^ 2 < lam * ρ₂ ^ 2 := by
      have hc : 0 ≤ Real.sqrt lam * ρ₂ := mul_nonneg hsqlam.le hρ₂.le
      have hlt : ‖v‖ ^ 2 < (Real.sqrt lam * ρ₂) ^ 2 := by
        have hh := (mul_self_lt_mul_self_iff (norm_nonneg v) hc).mp h3
        simpa only [pow_two] using hh
      have hs : (Real.sqrt lam * ρ₂) ^ 2 = lam * ρ₂ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hlam.le]
      rw [hs] at hlt
      have hle : lam * ((fun z : E => ‖z‖) v) ^ 2 ≤ ‖v‖ ^ 2 := le_trans h1 (le_of_eq h2)
      linarith [hle, hlt]
    have h6 : ((fun z : E => ‖z‖) v) ^ 2 < ρ₂ ^ 2 := by nlinarith [h5, hlam]
    have h7 : 0 ≤ (fun z : E => ‖z‖) v := by positivity
    nlinarith [h6, h7, le_of_lt hρ₂]
  have h1 := hagree v hvρ₁
  have h2 := hmineq (v : E) hmodel
  rw [h1]
  exact h2

/-- **Agreement of geodesic segments starting at the same point with the same initial data**:
segments with equal initial vectors (given as unit vectors) and different prescribed lengths agree
on the shorter of the two domains.  Variant of `geodCurve_agree` where the two unit vectors are
only *propositionally* equal. -/
lemma geodCurve_agree_of_eq (hmet : IsMetricCompatible cov) {x : M} {ξ₁ ξ₂ : TangentSpace I x}
    (heq : ξ₁ = ξ₂) (hξ₁ : ‖ξ₁‖ = 1) (hξ₂ : ‖ξ₂‖ = 1) {T₁ T₂ : ℝ} (hT₁ : 0 ≤ T₁)
    (hT₂ : 0 ≤ T₂) (h12 : T₁ ≤ T₂) :
    EqOn (geodCurve (cov := cov) hmet T₁ hT₁ x ξ₁ hξ₁)
      (geodCurve (cov := cov) hmet T₂ hT₂ x ξ₂ hξ₂)
      (Ioo (-(geodDelta (cov := cov) hmet)) (T₁ + geodDelta (cov := cov) hmet)) := by
  subst heq
  exact geodCurve_agree (cov := cov) hmet hT₁ hT₂ h12 x ξ₁ hξ₁

/-- **The ray property of the global exponential map.**  Along a scaled velocity `t • v` with
`t ≥ 0`, the global exponential map is the value at time `t * ‖v‖` of a *fixed* unit-speed geodesic
segment starting at `x` in the direction of `v`.  (The segment index is chosen large enough so that
the evaluation point lies in its domain.) -/
theorem GExp_smul (hmet : IsMetricCompatible cov) (x : M) {v : TangentSpace I x} (hv : v ≠ 0)
    {t : ℝ} (ht : 0 ≤ t) :
    GExp (cov := cov) hmet x (t • v)
      = (geodCurve (cov := cov) hmet (max ‖v‖ (t * ‖v‖))
          (le_trans (norm_nonneg v) (le_max_left _ _)) x (unitOf v hv)
          (unitOf_norm v hv)) (t * ‖v‖) := by
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0
    have hspec := (geodCurve_spec (cov := cov) hmet (max ‖v‖ (0 * ‖v‖))
      (le_trans (norm_nonneg v) (le_max_left _ _)) x (unitOf v hv) (unitOf_norm v hv)).1
    rw [zero_smul, GExp_zero]
    exact hspec.symm.trans (congrArg (fun s : ℝ => (geodCurve (cov := cov) hmet (max ‖v‖ (0 * ‖v‖))
      (le_trans (norm_nonneg v) (le_max_left _ _)) x (unitOf v hv) (unitOf_norm v hv)) s)
        (zero_mul ‖v‖).symm)
  · have hne : t • v ≠ 0 := smul_ne_zero (ne_of_gt hpos) hv
    have hnorm : ‖t • v‖ = t * ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    have hu : unitOf (t • v) hne = unitOf v hv := by
      rw [unitOf, unitOf, hnorm, smul_smul]
      congr 1
      rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), mul_one]
    rw [GExp_apply (cov := cov) hmet hne]
    have hT₁ : 0 ≤ ‖t • v‖ := norm_nonneg _
    have hT₂ : 0 ≤ max ‖v‖ (t * ‖v‖) := le_trans (norm_nonneg v) (le_max_left _ _)
    have h12 : ‖t • v‖ ≤ max ‖v‖ (t * ‖v‖) := (le_of_eq hnorm).trans (le_max_right _ _)
    have hgd := geodDelta_pos (cov := cov) hmet
    have hmem : t * ‖v‖ ∈ Ioo (-(geodDelta (cov := cov) hmet))
        (‖t • v‖ + geodDelta (cov := cov) hmet) :=
      Set.mem_Ioo.mpr ⟨by have h2 : 0 ≤ t * ‖v‖ := mul_nonneg ht (norm_nonneg v); linarith,
        by linarith⟩
    have hstep1 : (geodCurve (cov := cov) hmet ‖t • v‖ hT₁ x (unitOf (t • v) hne)
          (unitOf_norm (t • v) hne)) ‖t • v‖
        = (geodCurve (cov := cov) hmet ‖t • v‖ hT₁ x (unitOf (t • v) hne)
          (unitOf_norm (t • v) hne)) (t * ‖v‖) :=
      congrArg (fun s : ℝ => (geodCurve (cov := cov) hmet ‖t • v‖ hT₁ x (unitOf (t • v) hne)
        (unitOf_norm (t • v) hne)) s) hnorm
    have hstep2 : (geodCurve (cov := cov) hmet ‖t • v‖ hT₁ x (unitOf (t • v) hne)
          (unitOf_norm (t • v) hne)) (t * ‖v‖)
        = (geodCurve (cov := cov) hmet (max ‖v‖ (t * ‖v‖)) hT₂ x (unitOf v hv)
          (unitOf_norm v hv)) (t * ‖v‖) :=
      geodCurve_agree_of_eq (cov := cov) hmet hu (unitOf_norm (t • v) hne) (unitOf_norm v hv)
        hT₁ hT₂ h12 hmem
    exact hstep1.trans hstep2

/-- The chart metric at its own base point is the square of the norm: `√(chartGram x x v v) = ‖v‖`
(the latter in the metric of the fibre). -/
lemma sqrt_chartGram_self {x : M} (v : E) :
    Real.sqrt (chartGram (I := I) x x v v) = (fun z : TangentSpace I x => ‖z‖) v := by
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  rw [chartGram_self_apply (I := I) x v v, real_inner_self_eq_norm_sq,
    Real.sqrt_sq (norm_nonneg _)]

/-- **The distance along a geodesic ray.**  For a velocity `v` and a time `t ≥ 0`, as long as the
Riemannian length `t * ‖v‖` of the segment stays below the local minimality radius, the Riemannian
distance from `x` to `GExp x (t • v)` is exactly the length `‖t • v‖ = t * ‖v‖` of the segment. -/
theorem exists_pos_riemannianEDist_GExp_smul (hmet : IsMetricCompatible cov)
    (htor : cov.torsion = 0) (x : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (v : TangentSpace I x), v ≠ 0 → ∀ t : ℝ, 0 ≤ t →
      t * ‖v‖ < ρ →
      Manifold.riemannianEDist I x (GExp (cov := cov) hmet x (t • v))
        = ENNReal.ofReal ‖t • v‖ := by
  classical
  obtain ⟨ρ, hρ, hρeq⟩ := exists_pos_riemannianEDist_GExp_eq (cov := cov) hmet htor x
  refine ⟨ρ, hρ, fun v hv t ht htv => ?_⟩
  have hnorm : ‖t • v‖ = t * ‖v‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht]
  have hlt : ‖t • v‖ < ρ := by rw [hnorm]; exact htv
  rw [hρeq (t • v) hlt]
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  rw [show Real.sqrt (chartGram (I := I) x x ((t • v : TangentSpace I x) : E)
      ((t • v : TangentSpace I x) : E)) = ‖(t • v : TangentSpace I x)‖ from by
    rw [chartGram_self_apply (I := I) x ((t • v : TangentSpace I x) : E)
      ((t • v : TangentSpace I x) : E), real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]]

/-- **The rays of the global exponential map are geodesics.**  For every parameter `t > 0`, the
curve `s ↦ GExp x (s • v)` is an intrinsic geodesic at `t`.
(The statement is one-sided in time at `t`; at `t = 0` one has to compare the reversed rays in
the directions `v` and `-v`, which is not needed below.) -/
theorem isGeodesicAt_GExp_smul (hmet : IsMetricCompatible cov) (x : M) {v : TangentSpace I x}
    (hv : v ≠ 0) {t : ℝ} (ht : 0 < t) :
    IsGeodesicAt cov (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) t := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hgd := geodDelta_pos (cov := cov) hmet
  set T : ℝ := max ‖v‖ ((t + 1) * ‖v‖) with hTdef
  have hTnn : 0 ≤ T := le_trans (norm_nonneg v) (le_max_left _ _)
  have hTle : (t + 1) * ‖v‖ ≤ T := by rw [hTdef]; exact le_max_right _ _
  have hTt : t * ‖v‖ ≤ T := by nlinarith [hvpos, hTle]
  have htT : ‖v‖ * t < T + geodDelta (cov := cov) hmet := by rw [mul_comm]; linarith
  set ξ : TangentSpace I x := unitOf v hv with hξdef
  have hξnorm : ‖ξ‖ = 1 := unitOf_norm v hv
  obtain ⟨-, hgcv, hgcsm, hgcgeo, -⟩ := geodCurve_spec (cov := cov) hmet T hTnn x ξ hξnorm
  have hnb : Ioo (t / 2) (t + 1) ∈ 𝓝 t :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hmem : ∀ s ∈ Ioo (t / 2) (t + 1),
      ‖v‖ * s ∈ Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet) := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    refine Set.mem_Ioo.mpr ⟨by linarith [hgd, mul_pos hvpos hs0],
      by nlinarith [hvpos, hTle, hgd, le_of_lt hs.2]⟩
  -- the two curves agree near `t`
  have hev : (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) =ᶠ[𝓝 t]
      (fun s : ℝ => (geodCurve (cov := cov) hmet T hTnn x ξ hξnorm) (‖v‖ * s)) := by
    filter_upwards [hnb] with s hs
    have hs0 : 0 ≤ s := le_of_lt (by linarith [hs.1])
    have hsle : s * ‖v‖ ≤ T := by
      have h1 : s ≤ t + 1 := le_of_lt hs.2
      calc s * ‖v‖ ≤ (t + 1) * ‖v‖ := by nlinarith [hvpos]
        _ ≤ T := hTle
    rw [GExp_smul (cov := cov) hmet x hv hs0, mul_comm ‖v‖ s]
    exact geodCurve_agree (cov := cov) hmet (T₁ := max ‖v‖ (s * ‖v‖)) (T₂ := T)
      (le_trans (norm_nonneg v) (le_max_left _ _)) hTnn (max_le (le_max_left _ _) hsle) x ξ hξnorm
      ⟨by linarith [hgd, mul_nonneg hs0 (norm_nonneg v)],
       by linarith [hgd, le_max_right ‖v‖ (s * ‖v‖)]⟩
  refine (isGeodesicAt_congr_of_eventuallyEq (I := I) hev).mpr ?_
  have hmd : ∀ᶠ s in 𝓝 t,
      MDifferentiableAt 𝓘(ℝ) I (geodCurve (cov := cov) hmet T hTnn x ξ hξnorm) (‖v‖ * s) := by
    filter_upwards [hnb] with s hs
    exact (hgcsm.contMDiffAt (IsOpen.mem_nhds isOpen_Ioo (hmem s hs))).mdifferentiableAt (by simp)
  have hgeo : IsGeodesicAt cov (geodCurve (cov := cov) hmet T hTnn x ξ hξnorm) (‖v‖ * t) :=
    hgcgeo _ (hmem t ⟨by linarith, by linarith⟩)
  have hres := isGeodesicAt_comp_mul (cov := cov)
    (γ := geodCurve (cov := cov) hmet T hTnn x ξ hξnorm) (c := ‖v‖) (t := t)
    (ne_of_gt hvpos) hmd hgeo
  exact hres

/-- **The speed of a ray of the global exponential map.**  For every `t > 0`,
`‖d/dt GExp x (t • v)‖ = ‖v‖`. -/
theorem norm_curveVelocity_GExp_smul (hmet : IsMetricCompatible cov) (x : M) {v : TangentSpace I x}
    (hv : v ≠ 0) {t : ℝ} (ht : 0 < t) :
    ‖curveVelocity (I := I) (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) t‖ = ‖v‖ := by
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hgd := geodDelta_pos (cov := cov) hmet
  set T : ℝ := max ‖v‖ ((t + 1) * ‖v‖) with hTdef
  have hTnn : 0 ≤ T := le_trans (norm_nonneg v) (le_max_left _ _)
  have hTle : (t + 1) * ‖v‖ ≤ T := by rw [hTdef]; exact le_max_right _ _
  have hTt : t * ‖v‖ ≤ T := by nlinarith [hvpos, hTle]
  have htT : ‖v‖ * t < T + geodDelta (cov := cov) hmet := by rw [mul_comm]; linarith
  set ξ : TangentSpace I x := unitOf v hv with hξdef
  have hξnorm : ‖ξ‖ = 1 := unitOf_norm v hv
  obtain ⟨-, hgcv, hgcsm, -, hgcspeed⟩ := geodCurve_spec (cov := cov) hmet T hTnn x ξ hξnorm
  have hnb : Ioo (t / 2) (t + 1) ∈ 𝓝 t :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  have hmem : ∀ s ∈ Ioo (t / 2) (t + 1),
      ‖v‖ * s ∈ Ioo (-(geodDelta (cov := cov) hmet)) (T + geodDelta (cov := cov) hmet) := by
    intro s hs
    have hs0 : 0 < s := by linarith [hs.1]
    refine Set.mem_Ioo.mpr ⟨by linarith [hgd, mul_pos hvpos hs0],
      by nlinarith [hvpos, hTle, hgd, le_of_lt hs.2]⟩
  have hev : (fun s : ℝ => GExp (cov := cov) hmet x (s • v)) =ᶠ[𝓝 t]
      (fun s : ℝ => (geodCurve (cov := cov) hmet T hTnn x ξ hξnorm) (‖v‖ * s)) := by
    filter_upwards [hnb] with s hs
    have hs0 : 0 ≤ s := le_of_lt (by linarith [hs.1])
    have hsle : s * ‖v‖ ≤ T := by
      have h1 : s ≤ t + 1 := le_of_lt hs.2
      calc s * ‖v‖ ≤ (t + 1) * ‖v‖ := by nlinarith [hvpos]
        _ ≤ T := hTle
    rw [GExp_smul (cov := cov) hmet x hv hs0, mul_comm ‖v‖ s]
    exact geodCurve_agree (cov := cov) hmet (T₁ := max ‖v‖ (s * ‖v‖)) (T₂ := T)
      (le_trans (norm_nonneg v) (le_max_left _ _)) hTnn (max_le (le_max_left _ _) hsle) x ξ hξnorm
      ⟨by linarith [hgd, mul_nonneg hs0 (norm_nonneg v)],
       by linarith [hgd, le_max_right ‖v‖ (s * ‖v‖)]⟩
  rw [hev.eq_of_nhds]
  rw [curveVelocity_congr_of_eventuallyEq (I := I) hev]
  have hmd : MDifferentiableAt 𝓘(ℝ) I (geodCurve (cov := cov) hmet T hTnn x ξ hξnorm) (‖v‖ * t) :=
    (hgcsm.contMDiffAt (IsOpen.mem_nhds isOpen_Ioo (hmem t ⟨by linarith, by linarith⟩))).mdifferentiableAt
      (by simp)
  have hcm := curveVelocity_comp_mul (I := I)
    (γ := geodCurve (cov := cov) hmet T hTnn x ξ hξnorm) (c := ‖v‖) (t := t) hmd
  rw [hcm, norm_smul, Real.norm_eq_abs, abs_of_pos hvpos,
    hgcspeed (‖v‖ * t) (hmem t ⟨by linarith, by linarith⟩), mul_one]

end GExp

end

end Submission.GlobalExp