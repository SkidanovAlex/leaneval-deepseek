import Submission.Work.RiemLib.GExpFlow
import Submission.Work.RiemLib.JacobiGauss

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The variation family of the chart flow

The model bound for the chart-flow exponential map `Submission.GExpFlow.chartFlowExp D q`
(the map `u ↦ φ⁻¹((D.α (φ q, c • u) c⁻¹).1)`) needs, for each direction `y`, the two-parameter
family of chart geodesics obtained by varying the initial velocity in the direction `y`.  The block
of the proof of `exists_uniform_chartFlow_rauch_bound_of_data` (in `Submission/GExpFlow.lean`)
constructs exactly this family (for the direction `x`); this file extracts it into a structure
`ChartFlowVariation`, proves its existence (`exists_chartFlowVariation`), and derives the two
consequences needed later:

* `mfderiv_chartFlowExp` — the differential of the chart-flow exponential map at `u` in the
  direction `y` is the time-`1` value of the Jacobi field of the variation;
* `chartGram_chartFlow_gauss` — Gauss's lemma in chart coordinates:
  `⟨(d F)_u u, (d F)_u y⟩_p = ⟨u, y⟩_q`;
* `chartGram_chartFlow_radial` — the radial Jacobi field is the velocity:
  `⟨(d F)_u u, (d F)_u u⟩_p = ⟨u, u⟩_q`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal InnerProductSpace
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.Curvature
open Submission.Rauch
open Submission.JacobiTensor
open Submission.RauchGen
open Submission.Gauss
open Submission.GlobalExp
open Submission.GeodesicGlobal
open Submission.ChartGeoAt
open Submission.FlowJacobi
open Submission.RauchChart
open Submission.GExpFlow
open Submission.JacobiGauss

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.ChartFlowVar

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

variable {z₀ : M} {Z : Set M}

/-- A chart geodesic on a subinterval (monotonicity of `HasChartGeodesicOn` in the interval). -/
lemma hasChartGeodesicOn_mono {x q : M} {v : E} {u w : ℝ → E} {A B A' B' : ℝ}
    (h : HasChartGeodesicOn cov x q v u w A B) (hA : A ≤ A') (hB : B' ≤ B) :
    HasChartGeodesicOn cov x q v u w A' B' :=
  ⟨h.1, h.2.1,
    fun t ht => h.2.2.1 t ⟨lt_of_le_of_lt hA ht.1, lt_of_lt_of_le ht.2 hB⟩,
    fun t ht => h.2.2.2.1 t ⟨lt_of_le_of_lt hA ht.1, lt_of_lt_of_le ht.2 hB⟩,
    fun t ht => h.2.2.2.2 t ⟨lt_of_le_of_lt hA ht.1, lt_of_lt_of_le ht.2 hB⟩⟩

/-- The chart-geodesic curve of the flow data `D` through `q` with coordinate velocity `u` (the
`s ↦ (D.α (φ q, c • u) (c⁻¹ s)).1` slice of the flow).  All variation families of `D` at `(q,u)`
have this same base curve (see the fields `hgcBase`, `hgvBase`). -/
noncomputable def cfCurve (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (q : M) (u : E) : ℝ → E :=
  fun s => (D.α (((extChartAt I z₀) q), flowScale D • u) ((flowScale D)⁻¹ * s)).1

/-- The chart velocity of the base curve `cfCurve D q u`. -/
noncomputable def cfVel (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (q : M) (u : E) : ℝ → E :=
  fun s => (flowScale D)⁻¹ • (D.α (((extChartAt I z₀) q), flowScale D • u)
    ((flowScale D)⁻¹ * s)).2

/-- **The variation family of the chart flow.**  All the data produced by the construction of the
one-parameter family `Φ` of chart geodesics obtained by varying the initial coordinate velocity
`u` in the direction `y` (the family whose time-`c⁻¹` slice is `chartFlowExp D q (u + t • y)`),
together with its Jacobi tensor. -/
structure ChartFlowVariation (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (q : M)
    (u y : E) : Type _ where
  /-- the half-width of the parameter interval -/
  δ : ℝ
  hδ : 0 < δ
  /-- the two-parameter family of phases -/
  Φ : ℝ × ℝ → E × E
  hΦ0 : ∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).1 = (extChartAt I z₀) q
  hΦv : ∀ t ∈ Ioo (-δ) δ, (Φ (0, t)).2 = u + t • y
  hTGT : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2, (Φ (s, t)).1 ∈ (extChartAt I z₀).target
  hODE : ∀ t ∈ Ioo (-δ) δ, ∀ s ∈ Ioo (-2 : ℝ) 2,
    HasDerivAt (fun s' : ℝ => Φ (s', t))
      ((Φ (s, t)).2, chartGeodesicVectorField cov z₀ (Φ (s, t))) s
  hSM : ∀ s ∈ Ioo (-2 : ℝ) 2, ContDiffAt ℝ ∞ (fun p : ℝ × ℝ => Φ p) (s, 0)
  hstay : ∀ s ∈ Ioo (-2 : ℝ) 2, (gc Φ) s ∈ (extChartAt I z₀).target
  hu0 : ∀ s ∈ Ioo (-2 : ℝ) 2, HasDerivAt (gc Φ) (gv Φ s) s
  hw0 : ∀ s ∈ Ioo (-2 : ℝ) 2,
    HasDerivAt (gv Φ) (chartGeodesicVectorField cov z₀ (gc Φ s, gv Φ s)) s
  hEXP : ∀ t ∈ Ioo (-δ) δ,
    chartFlowExp (cov := cov) D q (u + t • y) = (extChartAt I z₀).symm ((Φ (1, t)).1)
  hgc : HasChartGeodesicOn cov z₀ q (frameVector (I := I) z₀ q u) (gc Φ) (gv Φ) (-(2 : ℝ)) 2
  /-- the base curve is the canonical flow curve -/
  hgcBase : gc Φ = cfCurve (cov := cov) (I := I) D q u
  /-- the base velocity is the canonical flow velocity -/
  hgvBase : gv Φ = cfVel (cov := cov) (I := I) D q u
  hspeed : ∀ t ∈ Ioo (-(2 : ℝ)) 2,
    chartGram (I := I) z₀ ((extChartAt I z₀).symm ((gc Φ) t)) ((gv Φ) t) ((gv Φ) t)
      = chartGram (I := I) z₀ q u u
  Y : ℝ → E →L[ℝ] E
  U : ℝ → E →L[ℝ] E
  hY0 : Y 0 = 0
  hU0 : U 0 = 1
  hY : ∀ t ∈ Icc (-(3 / 2) : ℝ) (3 / 2),
    HasDerivAt Y (U t - (gammaOp (cov := cov) z₀ (gc Φ) (gv Φ) t).comp (Y t)) t
  hU : ∀ t ∈ Icc (-(3 / 2) : ℝ) (3 / 2),
    HasDerivAt U (-((gammaOp (cov := cov) z₀ (gc Φ) (gv Φ) t).comp (U t))
      - (curvOp (cov := cov) z₀ (gc Φ) (gv Φ) t).comp (Y t)) t

variable [Nontrivial E] [CompactSpace M]

/-- **Existence of the variation family of the chart flow.**  For `q ∈ Z`, a coordinate velocity
`u` with `flowScale D · ‖u‖ < 1` and any direction `y` there is a `ChartFlowVariation`; this is
exactly the block proved inside `exists_uniform_chartFlow_rauch_bound_of_data`. -/
theorem exists_chartFlowVariation (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hZsrc : Z ⊆ (chartAt H z₀).source)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) {q : M} (hq : q ∈ Z) (u y : E)
    (huO : flowScale D * ‖u‖ < 1) :
    ∃ V : ChartFlowVariation (cov := cov) (I := I) D q u y, True := by
  classical
  have hcpos : 0 < flowScale D := flowScale_pos D
  have hcinvpos : 0 < (flowScale D)⁻¹ := inv_pos.mpr hcpos
  have hqs : q ∈ (extChartAt I z₀).source := by simpa using hZsrc hq
  set c : ℝ := flowScale D with hcdef
  have hcpos' : 0 < c := by rw [hcdef]; exact hcpos
  have hcne : c ≠ 0 := ne_of_gt hcpos'
  have hcinv : c⁻¹ = D.ρ / 2 := by rw [hcdef]; exact inv_flowScale D
  have huc : c * ‖u‖ < 1 := by rw [hcdef]; exact huO
  -- the phase of the flow
  set p₀ : E × E := ((extChartAt I z₀) q, c • u) with hp₀def
  have hp₀K : p₀ ∈ chartData (I := I) z₀ Z :=
    ⟨⟨q, hq, rfl⟩, by
      rw [mem_closedBall, dist_zero_right, hp₀def]
      simp only [Prod.snd, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos']
      exact huc.le⟩
  have hp₀O : p₀ ∈ D.O := D.hKO hp₀K
  -- the one-parameter family of phases
  set pt : ℝ → E × E := fun t => ((extChartAt I z₀) q, c • (u + t • y)) with hptdef
  set hδ0 : ℝ := min (1:ℝ) ((1 - c * ‖u‖) / (2 * (1 + c * ‖y‖))) with hδ0def
  have hδ0pos : 0 < hδ0 := by
    rw [hδ0def]
    exact lt_min one_pos (div_pos (by linarith [huc]) (by positivity))
  have hδ0le : hδ0 ≤ 1 := by rw [hδ0def]; exact min_le_left _ _
  have hpt0eq : pt 0 = p₀ := by
    rw [hptdef, hp₀def]
    simp only [zero_smul, add_zero]
  have hptK : ∀ t ∈ Ioo (-hδ0) hδ0, pt t ∈ chartData (I := I) z₀ Z := by
    intro t ht
    rw [hptdef]
    refine ⟨⟨q, hq, rfl⟩, ?_⟩
    rw [mem_closedBall, dist_zero_right]
    simp only [Prod.snd, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos']
    have htab : |t| < hδ0 := abs_lt.mpr ⟨ht.1, ht.2⟩
    have ht2 : |t| < (1 - c * ‖u‖) / (2 * (1 + c * ‖y‖)) :=
      lt_of_lt_of_le htab (by rw [hδ0def]; exact min_le_right _ _)
    have h1 : c * ‖u + t • y‖ ≤ c * (‖u‖ + |t| * ‖y‖) := by
      refine mul_le_mul_of_nonneg_left ?_ hcpos'.le
      calc ‖u + t • y‖ ≤ ‖u‖ + ‖t • y‖ := norm_add_le _ _
        _ = ‖u‖ + |t| * ‖y‖ := by rw [norm_smul, Real.norm_eq_abs]
    have h3 : |t| * ‖y‖ ≤ (1 - c * ‖u‖) / (2 * (1 + c * ‖y‖)) * ‖y‖ :=
      mul_le_mul_of_nonneg_right ht2.le (norm_nonneg y)
    have h4 : c * ((1 - c * ‖u‖) / (2 * (1 + c * ‖y‖)) * ‖y‖) ≤ (1 - c * ‖u‖) / 2 := by
      have h4a : c * ((1 - c * ‖u‖) / (2 * (1 + c * ‖y‖)) * ‖y‖)
          = c * (1 - c * ‖u‖) * ‖y‖ / (2 * (1 + c * ‖y‖)) := by ring
      rw [h4a, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith [norm_nonneg y, hcpos'.le, huc]
    have h5 : c * (|t| * ‖y‖) ≤ (1 - c * ‖u‖) / 2 := by
      have h6 := mul_le_mul_of_nonneg_left h3 hcpos'.le
      have h6' : c * ((1 - c * ‖u‖) / (2 * (1 + c * ‖y‖)) * ‖y‖)
          = c * ((1 - c * ‖u‖) / (2 * (1 + c * ‖y‖))) * ‖y‖ := by ring
      linarith [h6, h4, h6']
    have h7 : c * (‖u‖ + |t| * ‖y‖) ≤ c * ‖u‖ + (1 - c * ‖u‖) / 2 := by
      have h8 : c * (‖u‖ + |t| * ‖y‖) = c * ‖u‖ + c * (|t| * ‖y‖) := by ring
      rw [h8]
      linarith [h5]
    have h9 : c * ‖u‖ + (1 - c * ‖u‖) / 2 < 1 := by linarith [huc]
    linarith [h1, h7, h9]
  have hptO : ∀ t ∈ Ioo (-hδ0) hδ0, pt t ∈ D.O := fun t ht => D.hKO (hptK t ht)
  set Φ : ℝ × ℝ → E × E :=
    fun p' => ((D.α (pt p'.2) (c⁻¹ * p'.1)).1, c⁻¹ • (D.α (pt p'.2) (c⁻¹ * p'.1)).2) with hΦdef
  -- the chart geodesic of the family at `t = 0`, with velocity `frameVector z₀ q u`
  have hgc : HasChartGeodesicOn cov z₀ q (frameVector (I := I) z₀ q u) (gc Φ) (gv Φ)
      (-(2 : ℝ)) 2 := by
    have hsub : ∀ s ∈ Ioo (-(2 : ℝ)) 2, c⁻¹ * s ∈ Ioo (-D.ρ) D.ρ := by
      intro s hs
      have hs2 : |s| < 2 := abs_lt.mpr ⟨hs.1, hs.2⟩
      have hlt : |c⁻¹ * s| < D.ρ := by
        rw [abs_mul, abs_of_pos hcinvpos, hcinv]
        nlinarith [abs_nonneg s, D.hρ, hs2]
      exact mem_Ioo.mpr (abs_lt.mp hlt)
    have hpt0O : pt 0 ∈ D.O := hptO 0 ⟨by linarith [hδ0pos], by linarith [hδ0pos]⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show (D.α (pt 0) (c⁻¹ * 0)).1 = (extChartAt I z₀) q
      rw [mul_zero, D.h0 (pt 0) hpt0O, hptdef]
    · show c⁻¹ • (D.α (pt 0) (c⁻¹ * 0)).2
          = (trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ q
              (frameVector (I := I) z₀ q u)
      rw [clm_frameVector (I := I) hqs, mul_zero, D.h0 (pt 0) hpt0O, hptdef]
      simp only [Prod.snd, smul_smul, inv_mul_cancel₀ hcne, one_smul, zero_smul, add_zero]
    · intro s hs
      exact D.htgt (pt 0) hpt0O (c⁻¹ * s)
        (le_of_lt (abs_lt.mpr ⟨(hsub s hs).1, (hsub s hs).2⟩))
    · intro s hs
      have hφ : HasDerivAt (fun s' : ℝ => c⁻¹ * s') c⁻¹ s := by
        simpa using (hasDerivAt_id s).const_mul c⁻¹
      have h1 := (Submission.Gauss.hasDerivAt_fst (D.hode (pt 0) hpt0O (c⁻¹ * s)
        (le_of_lt (abs_lt.mpr ⟨(hsub s hs).1, (hsub s hs).2⟩)))).scomp s hφ
      have h1' : HasDerivAt (fun s' : ℝ => (D.α (pt 0) (c⁻¹ * s')).1)
          (c⁻¹ • (D.α (pt 0) (c⁻¹ * s)).2) s := by
        simpa [Function.comp_def] using h1
      show HasDerivAt (fun s' : ℝ => (D.α (pt 0) (c⁻¹ * s')).1)
        (c⁻¹ • (D.α (pt 0) (c⁻¹ * s)).2) s
      exact h1'
    · intro s hs
      have htgt := D.htgt (pt 0) hpt0O (c⁻¹ * s)
        (le_of_lt (abs_lt.mpr ⟨(hsub s hs).1, (hsub s hs).2⟩))
      have hφ : HasDerivAt (fun s' : ℝ => c⁻¹ * s') c⁻¹ s := by
        simpa using (hasDerivAt_id s).const_mul c⁻¹
      have h1 : HasDerivAt (fun s' : ℝ => (D.α (pt 0) (c⁻¹ * s')).2)
          (c⁻¹ • chartGeodesicVectorField cov z₀ (D.α (pt 0) (c⁻¹ * s))) s := by
        have h := (Submission.Gauss.hasDerivAt_snd (D.hode (pt 0) hpt0O (c⁻¹ * s)
          (le_of_lt (abs_lt.mpr ⟨(hsub s hs).1, (hsub s hs).2⟩)))).scomp s hφ
        simpa [Function.comp_def, chartSpray_apply] using h
      have h2 := h1.const_smul c⁻¹
      have hpair : (gc Φ s, gv Φ s)
          = ((D.α (pt 0) (c⁻¹ * s)).1, c⁻¹ • (D.α (pt 0) (c⁻¹ * s)).2) := by
        rw [hΦdef]
        rfl
      have hsm := chartGeodesicVectorField_smul cov z₀ c⁻¹ (D.α (pt 0) (c⁻¹ * s)) htgt
      show HasDerivAt (fun s' : ℝ => c⁻¹ • (D.α (pt 0) (c⁻¹ * s')).2)
        (chartGeodesicVectorField cov z₀ (gc Φ s, gv Φ s)) s
      rw [hpair, hsm, pow_two, ← smul_smul]
      exact h2
  -- the Jacobi tensor along it
  obtain ⟨Y, U, hY0, hU0, hY, hU⟩ :=
    exists_jacobiSystemOn (cov := cov) htor hgc (by norm_num : (-(3 / 2) : ℝ) < 3 / 2)
      (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      (by norm_num : (0 : ℝ) ∈ Icc (-(3 / 2)) (3 / 2))
  -- the constancy of the chart speed
  have hspeed : ∀ t ∈ Ioo (-(2 : ℝ)) 2,
      chartGram (I := I) z₀ ((extChartAt I z₀).symm ((D.α (pt 0) (c⁻¹ * t)).1))
        (c⁻¹ • (D.α (pt 0) (c⁻¹ * t)).2) (c⁻¹ • (D.α (pt 0) (c⁻¹ * t)).2)
        = chartGram (I := I) z₀ q u u := by
    intro t ht
    have h := Submission.GeodesicGlobal2.chartGram_const_of_chartODE (cov := cov) hmet
      (x₀ := z₀) (u := fun s : ℝ => (D.α (pt 0) (c⁻¹ * s)).1)
      (w := fun s : ℝ => c⁻¹ • (D.α (pt 0) (c⁻¹ * s)).2)
      (fun s hs => hgc.2.2.1 s hs) (fun s hs => hgc.2.2.2.1 s hs)
      (fun s hs => hgc.2.2.2.2 s hs) (t₀ := 0) (by norm_num) t ht
    have h0 : chartGram (I := I) z₀ ((extChartAt I z₀).symm ((D.α (pt 0) (c⁻¹ * 0)).1))
        (c⁻¹ • (D.α (pt 0) (c⁻¹ * 0)).2) (c⁻¹ • (D.α (pt 0) (c⁻¹ * 0)).2)
        = chartGram (I := I) z₀ q u u := by
      have hpt : (extChartAt I z₀).symm ((D.α (pt 0) (c⁻¹ * 0)).1) = q := by
        rw [mul_zero, D.h0 (pt 0) (hptO 0 ⟨by linarith [hδ0pos], by linarith [hδ0pos]⟩), hptdef]
        simp only [Prod.fst]
        exact (extChartAt I z₀).left_inv hqs
      have hvel : c⁻¹ • (D.α (pt 0) (c⁻¹ * 0)).2 = u := by
        rw [mul_zero, D.h0 (pt 0) (hptO 0 ⟨by linarith [hδ0pos], by linarith [hδ0pos]⟩), hptdef]
        simp only [Prod.snd, smul_smul, inv_mul_cancel₀ hcne, one_smul, zero_smul, add_zero]
      rw [hpt, hvel]
    rw [h]
    exact h0
  have hspeed' : ∀ t ∈ Ioo (-(2 : ℝ)) 2,
      chartGram (I := I) z₀ ((extChartAt I z₀).symm ((gc Φ) t)) ((gv Φ) t) ((gv Φ) t)
        = chartGram (I := I) z₀ q u u := by
    intro t ht
    have hgc' : (gc Φ) t = (D.α (pt 0) (c⁻¹ * t)).1 := by rw [hΦdef]; rfl
    have hgv' : (gv Φ) t = c⁻¹ • (D.α (pt 0) (c⁻¹ * t)).2 := by rw [hΦdef]; rfl
    rw [hgc', hgv']
    exact hspeed t ht
  -- the variation data
  have hΦ0 : ∀ t ∈ Ioo (-hδ0) hδ0, (Φ (0, t)).1 = (extChartAt I z₀) q := by
    intro t ht
    show (D.α (pt t) (c⁻¹ * 0)).1 = (extChartAt I z₀) q
    rw [mul_zero, D.h0 (pt t) (hptO t ht), hptdef]
  have hΦv : ∀ t ∈ Ioo (-hδ0) hδ0, (Φ (0, t)).2 = u + t • y := by
    intro t ht
    show c⁻¹ • (D.α (pt t) (c⁻¹ * 0)).2 = u + t • y
    rw [mul_zero, D.h0 (pt t) (hptO t ht), hptdef]
    simp only [Prod.snd, smul_smul, inv_mul_cancel₀ hcne, one_smul]
  have hΦTGT : ∀ t ∈ Ioo (-hδ0) hδ0, ∀ s ∈ Ioo (-2 : ℝ) 2,
      (Φ (s, t)).1 ∈ (extChartAt I z₀).target := by
    intro t ht s hs
    refine D.htgt (pt t) (hptO t ht) (c⁻¹ * s) ?_
    rw [abs_mul, abs_of_pos hcinvpos, hcinv]
    have hs2 : |s| < 2 := abs_lt.mpr ⟨hs.1, hs.2⟩
    nlinarith [D.hρ, abs_nonneg s]
  have hΦODE : ∀ t ∈ Ioo (-hδ0) hδ0, ∀ s ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun s' : ℝ => Φ (s', t))
        ((Φ (s, t)).2, chartGeodesicVectorField cov z₀ (Φ (s, t))) s := by
    intro t ht s hs
    have hsub' : ∀ s' ∈ Ioo (-(2 : ℝ)) 2, c⁻¹ * s' ∈ Ioo (-D.ρ) D.ρ := by
      intro s' hs'
      have hs2 : |s'| < 2 := abs_lt.mpr ⟨hs'.1, hs'.2⟩
      have hlt : |c⁻¹ * s'| < D.ρ := by
        rw [abs_mul, abs_of_pos hcinvpos, hcinv]
        nlinarith [abs_nonneg s', D.hρ, hs2]
      exact mem_Ioo.mpr (abs_lt.mp hlt)
    have hφ : HasDerivAt (fun s' : ℝ => c⁻¹ * s') c⁻¹ s := by
      simpa using (hasDerivAt_id s).const_mul c⁻¹
    have h1 := (Submission.Gauss.hasDerivAt_fst (D.hode (pt t) (hptO t ht) (c⁻¹ * s)
      (le_of_lt (abs_lt.mpr ⟨(hsub' s hs).1, (hsub' s hs).2⟩)))).scomp s hφ
    have h1' : HasDerivAt (fun s' : ℝ => (D.α (pt t) (c⁻¹ * s')).1)
        (c⁻¹ • (D.α (pt t) (c⁻¹ * s)).2) s := by
      simpa [Function.comp_def] using h1
    have htgt := D.htgt (pt t) (hptO t ht) (c⁻¹ * s)
      (le_of_lt (abs_lt.mpr ⟨(hsub' s hs).1, (hsub' s hs).2⟩))
    have h2 := (Submission.Gauss.hasDerivAt_snd (D.hode (pt t) (hptO t ht) (c⁻¹ * s)
      (le_of_lt (abs_lt.mpr ⟨(hsub' s hs).1, (hsub' s hs).2⟩)))).scomp s hφ
    have h2' : HasDerivAt (fun s' : ℝ => c⁻¹ • (D.α (pt t) (c⁻¹ * s')).2)
        (c⁻¹ • c⁻¹ • chartGeodesicVectorField cov z₀ (D.α (pt t) (c⁻¹ * s))) s := by
      have h2a : HasDerivAt (fun s' : ℝ => (D.α (pt t) (c⁻¹ * s')).2)
          (c⁻¹ • chartGeodesicVectorField cov z₀ (D.α (pt t) (c⁻¹ * s))) s :=
        h2.congr_of_eventuallyEq (by filter_upwards with r; rfl)
      exact (h2a.const_smul c⁻¹).congr_deriv rfl
    have hpair : Φ (s, t)
        = ((D.α (pt t) (c⁻¹ * s)).1, c⁻¹ • (D.α (pt t) (c⁻¹ * s)).2) := by
      rw [hΦdef]
    have h4 : chartGeodesicVectorField cov z₀ ((D.α (pt t) (c⁻¹ * s)).1,
        c⁻¹ • (D.α (pt t) (c⁻¹ * s)).2)
        = c⁻¹ • c⁻¹ • chartGeodesicVectorField cov z₀ (D.α (pt t) (c⁻¹ * s)) := by
      simpa [pow_two, smul_smul] using
        chartGeodesicVectorField_smul cov z₀ c⁻¹ (D.α (pt t) (c⁻¹ * s)) htgt
    rw [hpair, h4]
    exact h1'.prodMk h2'
  have hΦSM : ∀ s ∈ Ioo (-2 : ℝ) 2, ContDiffAt ℝ ∞ (fun p' : ℝ × ℝ => Φ p') (s, 0) := by
    intro s hs
    have hsρ : |c⁻¹ * s| < D.ρ := by
      rw [abs_mul, abs_of_pos hcinvpos, hcinv]
      have hs2 : |s| < 2 := abs_lt.mpr ⟨hs.1, hs.2⟩
      nlinarith [D.hρ, abs_nonneg s]
    have hjoint := D.hjoint (pt 0) (hptK 0 ⟨by linarith [hδ0pos], by linarith [hδ0pos]⟩)
      (c⁻¹ * s) hsρ
    have hinner : ContDiffAt ℝ ∞ (fun p' : ℝ × ℝ => (pt p'.2, c⁻¹ * p'.1)) (s, 0) := by
      have h1 : ContDiffAt ℝ ∞ (fun p' : ℝ × ℝ =>
          (((extChartAt I z₀) q, c • (u + p'.2 • y)), c⁻¹ * p'.1)) (s, 0) := by fun_prop
      refine h1.congr_of_eventuallyEq ?_
      filter_upwards with p'
      rw [hptdef]
    have h1 := hjoint.comp (s, 0) hinner
    have hpair := h1.fst.prodMk (h1.snd.const_smul c⁻¹)
    refine hpair.congr_of_eventuallyEq ?_
    filter_upwards with p'
    rfl
  have hΦstay : ∀ s ∈ Ioo (-2 : ℝ) 2, (gc Φ) s ∈ (extChartAt I z₀).target :=
    fun s hs => hgc.2.2.1 s hs
  have hΦu0 : ∀ s ∈ Ioo (-2 : ℝ) 2, HasDerivAt (gc Φ) (gv Φ s) s :=
    fun s hs => hgc.2.2.2.1 s hs
  have hΦw0 : ∀ s ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (gv Φ) (chartGeodesicVectorField cov z₀ (gc Φ s, gv Φ s)) s :=
    fun s hs => hgc.2.2.2.2 s hs
  have hΦEXP : ∀ t ∈ Ioo (-hδ0) hδ0,
      chartFlowExp (cov := cov) D q (u + t • y) = (extChartAt I z₀).symm ((Φ (1, t)).1) := by
    intro t ht
    rw [chartFlowExp_apply, ← hcdef]
    simp only [hΦdef, hptdef, Prod.fst, mul_one]
  have hgcBase : gc Φ = cfCurve (cov := cov) (I := I) D q u := by
    funext s
    simp only [gc_apply, cfCurve, hΦdef, hptdef, zero_smul, add_zero, hcdef]
  have hgvBase : gv Φ = cfVel (cov := cov) (I := I) D q u := by
    funext s
    simp only [gv_apply, cfVel, hΦdef, hptdef, zero_smul, add_zero, hcdef]
  exact ⟨⟨hδ0, hδ0pos, Φ, hΦ0, hΦv, hΦTGT, hΦODE, hΦSM, hΦstay, hΦu0, hΦw0, hΦEXP,
    hgc, hgcBase, hgvBase, hspeed', Y, U, hY0, hU0, hY, hU⟩, trivial⟩

/-- **The differential of the chart-flow exponential map.**  At a point whose phase lies in the
flow domain, the differential of `chartFlowExp D q` in the direction `y` is the time-`1` value of
the Jacobi field of the variation in the direction `y`. -/
theorem mfderiv_chartFlowExp (htor : cov.torsion = 0)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (q : M) (u y : E)
    (huK : ((extChartAt I z₀) q, flowScale D • u) ∈ chartData (I := I) z₀ Z)
    (V : ChartFlowVariation (cov := cov) (I := I) D q u y) :
    (mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) y
      = frameVector (I := I) z₀ (chartFlowExp (cov := cov) D q u) ((V.Y 1) y) := by
  refine mfderiv_of_eq_chartFlow (cov := cov) htor (δ := V.δ) (Φ := V.Φ)
    (f := chartFlowExp (cov := cov) D q) (v := u) (x := y) V.hδ V.hΦ0 V.hΦv V.hTGT
    V.hODE V.hSM V.hstay V.hu0 V.hw0 V.hEXP
    ((chartFlowExp_contMDiffAt (cov := cov) D huK).mdifferentiableAt (by simp))
    (fun t (ht : t ∈ Icc (-1 : ℝ) 1) => V.hY t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    (fun t (ht : t ∈ Icc (-1 : ℝ) 1) => V.hU t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    V.hY0 V.hU0

/-- **Gauss's lemma for the chart-flow exponential map.**  `⟨(d F)_u u, (d F)_u y⟩_p = ⟨u, y⟩_q`
where `p = F u`, `F = chartFlowExp D q`. -/
theorem chartGram_chartFlow_gauss (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} (hqs : q ∈ (extChartAt I z₀).source)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (u y : E)
    (V : ChartFlowVariation (cov := cov) (I := I) D q u y) :
    chartGram (I := I) z₀ (chartFlowExp (cov := cov) D q u) ((V.Y 1) u) ((V.Y 1) y)
      = chartGram (I := I) z₀ q u y := by
  have hgeo := hasChartGeodesicOn_mono (cov := cov) V.hgc (by norm_num : (-(2 : ℝ)) ≤ -(3 / 2)) (by norm_num : (3 / 2 : ℝ) ≤ 2)
  have hY : ∀ t ∈ Ioo (-(3 / 2) : ℝ) (3 / 2),
      HasDerivAt V.Y (V.U t - (gammaOp (cov := cov) z₀ (gc V.Φ) (gv V.Φ) t).comp (V.Y t)) t :=
    fun t ht => V.hY t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hU : ∀ t ∈ Ioo (-(3 / 2) : ℝ) (3 / 2),
      HasDerivAt V.U (-((gammaOp (cov := cov) z₀ (gc V.Φ) (gv V.Φ) t).comp (V.U t))
        - (curvOp (cov := cov) z₀ (gc V.Φ) (gv V.Φ) t).comp (V.Y t)) t :=
    fun t ht => V.hU t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hmain := chartFlow_gauss (cov := cov) (x₀ := z₀) (q := q) (u := u) (y := y)
    (δ := V.δ) (Φ := V.Φ) (Y := V.Y) (U := V.U) V.hδ htor hmet hqs V.hΦ0 V.hΦv hgeo hY hU
    V.hY0 V.hU0
  have hone : (extChartAt I z₀).symm ((gc V.Φ) 1) = chartFlowExp (cov := cov) D q u := by
    have h0 : (0 : ℝ) ∈ Ioo (-V.δ) V.δ := ⟨by linarith [V.hδ], V.hδ⟩
    have h := V.hEXP 0 h0
    rw [zero_smul, add_zero] at h
    rw [h]
    rfl
  rw [hone] at hmain
  exact hmain

/-- **The radial column of the variation is the flow velocity.**  For any variation family at
`(q,u)`, the Jacobi field evaluated on the initial velocity `u` is the velocity of the base curve:
`(Y 1) u = cfVel D q u 1`.  In particular this column is *independent of the varying direction*. -/
lemma radial_col (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} (hqs : q ∈ (extChartAt I z₀).source)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (u y : E)
    (V : ChartFlowVariation (cov := cov) (I := I) D q u y) :
    (V.Y 1) u = cfVel (cov := cov) (I := I) D q u 1 := by
  obtain ⟨hVY, hVU⟩ : (∀ t ∈ Ioo (-(3 / 2) : ℝ) (3 / 2),
        HasDerivAt V.Y (V.U t - (gammaOp (cov := cov) z₀ (gc V.Φ) (gv V.Φ) t).comp (V.Y t)) t)
      ∧ (∀ t ∈ Ioo (-(3 / 2) : ℝ) (3 / 2),
        HasDerivAt V.U (-((gammaOp (cov := cov) z₀ (gc V.Φ) (gv V.Φ) t).comp (V.U t))
          - (curvOp (cov := cov) z₀ (gc V.Φ) (gv V.Φ) t).comp (V.Y t)) t) :=
    ⟨fun t ht => V.hY t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
     fun t ht => V.hU t ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩
  have hgeo := hasChartGeodesicOn_mono (cov := cov) V.hgc
    (by norm_num : (-(2 : ℝ)) ≤ -(3 / 2)) (by norm_num : (3 / 2 : ℝ) ≤ 2)
  have h1 : (1 : ℝ) ∈ Ioo (-(3 / 2) : ℝ) (3 / 2) := ⟨by norm_num, by norm_num⟩
  have hv := jacobi_velocity (cov := cov) (v := frameVector (I := I) z₀ q u)
    (hA := by norm_num) (hB := by norm_num) htor hmet hgeo hVY hVU V.hY0 V.hU0 h1
  have hw0 : (gv V.Φ) 0 = u := by
    rw [V.hgc.2.1, clm_frameVector (I := I) (z₀ := z₀) hqs u]
  rw [hw0, one_smul] at hv
  rw [hv, V.hgvBase]

/-- **Gauss's lemma for the chart-flow variation: the full pairing.**  For a variation family at
`(q,u)` with coordinate velocity `u` and any direction `b`,
`⟨(Y 1) u, (Y 1) b⟩_p = ⟨u, b⟩_q`.  The radial column `(Y 1) u` is the velocity of the base
geodesic (`jacobi_velocity`), so this includes the radial case `b = u`. -/
lemma gauss_col (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} (hqs : q ∈ (extChartAt I z₀).source)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (u y : E)
    (V : ChartFlowVariation (cov := cov) (I := I) D q u y) (b : E) :
    chartGram (I := I) z₀ (chartFlowExp (cov := cov) D q u) ((V.Y 1) u) ((V.Y 1) b)
      = chartGram (I := I) z₀ q u b := by
  obtain ⟨hVY, hVU⟩ : (∀ t ∈ Ioo (-(3 / 2) : ℝ) (3 / 2),
        HasDerivAt V.Y (V.U t - (gammaOp (cov := cov) z₀ (gc V.Φ) (gv V.Φ) t).comp (V.Y t)) t)
      ∧ (∀ t ∈ Ioo (-(3 / 2) : ℝ) (3 / 2),
        HasDerivAt V.U (-((gammaOp (cov := cov) z₀ (gc V.Φ) (gv V.Φ) t).comp (V.U t))
          - (curvOp (cov := cov) z₀ (gc V.Φ) (gv V.Φ) t).comp (V.Y t)) t) :=
    ⟨fun t ht => V.hY t ⟨le_of_lt ht.1, le_of_lt ht.2⟩,
     fun t ht => V.hU t ⟨le_of_lt ht.1, le_of_lt ht.2⟩⟩
  have hgeo := hasChartGeodesicOn_mono (cov := cov) V.hgc
    (by norm_num : (-(2 : ℝ)) ≤ -(3 / 2)) (by norm_num : (3 / 2 : ℝ) ≤ 2)
  have h1 : (1 : ℝ) ∈ Ioo (-(3 / 2) : ℝ) (3 / 2) := ⟨by norm_num, by norm_num⟩
  have hv := jacobi_velocity (cov := cov) (v := frameVector (I := I) z₀ q u)
    (hA := by norm_num) (hB := by norm_num) htor hmet hgeo hVY hVU V.hY0 V.hU0 h1
  have hw0 : (gv V.Φ) 0 = u := by
    rw [V.hgc.2.1, clm_frameVector (I := I) (z₀ := z₀) hqs u]
  rw [hw0, one_smul] at hv
  have hg := jacobi_gauss (cov := cov) (x₀ := z₀) (q := q) (v := frameVector (I := I) z₀ q u)
    (a := b) (hA := by norm_num) (hB := by norm_num) htor hmet hgeo hVY hVU V.hY0 V.hU0
    (t := 1) h1
  have hpt0 : (extChartAt I z₀).symm ((gc V.Φ) 0) = q := by
    rw [V.hgc.1]
    exact (extChartAt I z₀).left_inv hqs
  have hpt1 : (extChartAt I z₀).symm ((gc V.Φ) 1) = chartFlowExp (cov := cov) D q u := by
    rw [V.hgcBase, chartFlowExp_apply]
    congr 1
    simp only [cfCurve, mul_one]
  rw [hpt0, hw0, one_mul] at hg
  calc chartGram (I := I) z₀ (chartFlowExp (cov := cov) D q u) ((V.Y 1) u) ((V.Y 1) b)
      = chartGram (I := I) z₀ ((extChartAt I z₀).symm ((gc V.Φ) 1)) ((gv V.Φ) 1) ((V.Y 1) b) := by
        rw [← hpt1, hv]
    _ = chartGram (I := I) z₀ ((extChartAt I z₀).symm ((gc V.Φ) 1)) ((V.Y 1) b) ((gv V.Φ) 1) :=
        chartGram_comm (I := I) _ _ _ _
    _ = chartGram (I := I) z₀ q b u := hg
    _ = chartGram (I := I) z₀ q u b := chartGram_comm (I := I) _ _ _ _

/-- **The radial Jacobi field is the velocity** in the chart-flow normalisation:
`⟨(d F)_u u, (d F)_u u⟩_p = ⟨u, u⟩_q` where `p = F u`, `F = chartFlowExp D q`. -/
theorem chartGram_chartFlow_radial (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} (hqs : q ∈ (extChartAt I z₀).source)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) (u : E)
    (V : ChartFlowVariation (cov := cov) (I := I) D q u u) :
    chartGram (I := I) z₀ (chartFlowExp (cov := cov) D q u) ((V.Y 1) u) ((V.Y 1) u)
      = chartGram (I := I) z₀ q u u := by
  have hgeo := hasChartGeodesicOn_mono (cov := cov) V.hgc (by norm_num : (-(2 : ℝ)) ≤ -(3 / 2)) (by norm_num : (3 / 2 : ℝ) ≤ 2)
  have hY : ∀ t ∈ Ioo (-(3 / 2) : ℝ) (3 / 2),
      HasDerivAt V.Y (V.U t - (gammaOp (cov := cov) z₀ (gc V.Φ) (gv V.Φ) t).comp (V.Y t)) t :=
    fun t ht => V.hY t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have hU : ∀ t ∈ Ioo (-(3 / 2) : ℝ) (3 / 2),
      HasDerivAt V.U (-((gammaOp (cov := cov) z₀ (gc V.Φ) (gv V.Φ) t).comp (V.U t))
        - (curvOp (cov := cov) z₀ (gc V.Φ) (gv V.Φ) t).comp (V.Y t)) t :=
    fun t ht => V.hU t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
  have h1 : (1 : ℝ) ∈ Ioo (-(3 / 2) : ℝ) (3 / 2) := ⟨by norm_num, by norm_num⟩
  -- the radial identity
  have hrad : (V.Y 1) u = (gv V.Φ) 1 := by
    have hv := jacobi_velocity (cov := cov) (v := frameVector (I := I) z₀ q u)
      (hA := by norm_num) (hB := by norm_num) htor hmet hgeo hY hU V.hY0 V.hU0 (t := 1) h1
    have hv0 : (gv V.Φ) 0 = u := by
      have h0 : (0 : ℝ) ∈ Ioo (-V.δ) V.δ := ⟨by linarith [V.hδ], V.hδ⟩
      have h := V.hΦv 0 h0
      rw [zero_smul, add_zero] at h
      exact h
    rw [hv0, one_smul] at hv
    exact hv
  -- the chart speed at `t = 1`
  have hsp := V.hspeed 1 (by norm_num)
  have hone : (extChartAt I z₀).symm ((gc V.Φ) 1) = chartFlowExp (cov := cov) D q u := by
    have h0 : (0 : ℝ) ∈ Ioo (-V.δ) V.δ := ⟨by linarith [V.hδ], V.hδ⟩
    have h := V.hEXP 0 h0
    rw [zero_smul, add_zero] at h
    rw [h]
    rfl
  rw [← hone, hrad]
  exact hsp

end

end Submission.ChartFlowVar
