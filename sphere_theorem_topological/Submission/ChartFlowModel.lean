import Submission.ChartFlowVar
import Submission.ModelBound

/-!
# The model bound for the chart-flow exponential map

This file transcribes `Submission.ModelBound.mfderiv_expMap_model_bound` from `expMap` to the
chart-flow exponential map `Submission.GExpFlow.chartFlowExp D q` of a compact chart piece, where
all the ingredients (smoothness, Rauch's bound, Gauss's lemma) are *uniform* over `q ∈ Z`:

* `exists_uniform_chartFlow_model_bound` — the model differential bound
  `‖(dF)_u x‖² ≤ ⟨u,x⟩²/⟨u,u⟩ + (sin r/r)²(⟨x,x⟩ - ⟨u,x⟩²/⟨u,u⟩)`, `F = chartFlowExp D q`,
  `r = √⟨u,u⟩`, all inner products the chart metric at `z₀` based at `q`;
* `chartFlow_model_bound_polar` — the polar form
  `‖(dF)_{r e}(r' e + r e')‖² ≤ r'² + sin²r ⟨e',e'⟩` for `⟨e,e⟩ = 1`, `⟨e,e'⟩ = 0`.
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
open Submission.ChartFlowVar
open Submission.ModelBound
open Submission.ExpBound2

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.ChartFlowModel

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]
variable [Nontrivial E] [CompactSpace M]
variable {z₀ : M} {Z : Set M}

/-- **The model differential bound for the chart-flow exponential map.**  Uniform over the compact
chart piece `Z`: there is `ρ > 0` such that for every `q ∈ Z` and every chart velocity `u` with
`0 < √⟨u,u⟩ < ρ` and every `x`,

`‖(d chartFlowExp_q)_u x‖² ≤ ⟨u,x⟩²/⟨u,u⟩ + (sin r/r)² (⟨x,x⟩ - ⟨u,x⟩²/⟨u,u⟩)`,  `r = √⟨u,u⟩`,

all inner products being the chart metric of the chart at `z₀` based at `q`. -/
theorem exists_uniform_chartFlow_model_bound
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (hZsrc : Z ⊆ (chartAt H z₀).source)
    {lam : ℝ} (hlam : 0 < lam)
    (hlam_bnd : ∀ q ∈ Z, ∀ w : E, lam * ‖w‖ ^ 2 ≤ chartGram (I := I) z₀ q w w)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ Z, ∀ u x : E,
      0 < Real.sqrt (chartGram (I := I) z₀ q u u) →
      Real.sqrt (chartGram (I := I) z₀ q u u) < ρ →
      ‖(mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) x‖ ^ 2
        ≤ (chartGram (I := I) z₀ q u x) ^ 2 / (chartGram (I := I) z₀ q u u)
          + (Real.sin (Real.sqrt (chartGram (I := I) z₀ q u u))
              / Real.sqrt (chartGram (I := I) z₀ q u u)) ^ 2
            * (chartGram (I := I) z₀ q x x
                - (chartGram (I := I) z₀ q u x) ^ 2 / (chartGram (I := I) z₀ q u u)) := by
  classical
  obtain ⟨ρ₁, hρ₁, hsharp⟩ := exists_uniform_chartFlow_rauch_bound_of_data
    (cov := cov) hmet htor hpinch hZsrc hlam hlam_bnd D
  obtain ⟨η, hη, hphase⟩ := exists_pos_phase_mem (cov := cov) (I := I) (z₀ := z₀) (Z := Z) D
  have hslpos : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hcpos0 : 0 < flowScale D := flowScale_pos D
  have h2c0 : (0 : ℝ) < 2 * flowScale D := mul_pos two_pos hcpos0
  refine ⟨min ρ₁ (Real.sqrt lam * min η (1 / (2 * flowScale D))),
    lt_min hρ₁ (mul_pos hslpos (lt_min hη (div_pos one_pos h2c0))), ?_⟩
  intro q hq u x hu_pos hu_lt
  have hqs : q ∈ (extChartAt I z₀).source := by simpa using hZsrc hq
  have huρ₁ : Real.sqrt (chartGram (I := I) z₀ q u u) < ρ₁ :=
    lt_of_lt_of_le hu_lt (min_le_left _ _)
  have hsmall : Real.sqrt (chartGram (I := I) z₀ q u u)
      < Real.sqrt lam * min η (1 / (2 * flowScale D)) := lt_of_lt_of_le hu_lt (min_le_right _ _)
  have hun : ‖u‖ < min η (1 / (2 * flowScale D)) := by
    have h1 : lam * ‖u‖ ^ 2 ≤ chartGram (I := I) z₀ q u u := hlam_bnd q hq u
    have h2 : Real.sqrt lam * ‖u‖ ≤ Real.sqrt (chartGram (I := I) z₀ q u u) := by
      rw [← Real.sqrt_sq (norm_nonneg u), ← Real.sqrt_mul hlam.le]
      exact Real.sqrt_le_sqrt h1
    exact lt_of_mul_lt_mul_left (lt_of_le_of_lt h2 hsmall) hslpos.le
  have hunη : ‖u‖ < η := lt_of_lt_of_le hun (min_le_left _ _)
  have h2c : (0 : ℝ) < 2 * flowScale D := mul_pos two_pos (flowScale_pos D)
  have hunc : flowScale D * ‖u‖ < 1 := by
    have h : ‖u‖ < 1 / (2 * flowScale D) := lt_of_lt_of_le hun (min_le_right _ _)
    rw [lt_div_iff₀ h2c] at h
    linarith
  -- the phase of the flow
  set p₀ : E × E := ((extChartAt I z₀) q, flowScale D • u) with hp₀def
  have huK : p₀ ∈ chartData (I := I) z₀ Z := by
    refine ⟨⟨q, hq, ?_⟩, ?_⟩
    · rw [hp₀def]
    · rw [mem_closedBall, dist_zero_right, hp₀def]
      simp only [Prod.snd, norm_smul, Real.norm_eq_abs, abs_of_pos (flowScale_pos D)]
      exact hunc.le
  -- the two variation families needed: in the direction `x` and in the direction `u`
  obtain ⟨Vx, -⟩ := exists_chartFlowVariation (cov := cov) (I := I) (z₀ := z₀) (Z := Z)
    hmet htor hZsrc D hq u x hunc
  obtain ⟨Vu, -⟩ := exists_chartFlowVariation (cov := cov) (I := I) (z₀ := z₀) (Z := Z)
    hmet htor hZsrc D hq u u hunc
  set p : M := chartFlowExp (cov := cov) D q u with hpdef
  have hp_chart : p ∈ (chartAt H z₀).source := by
    have h0 : (0 : ℝ) ∈ Ioo (-Vu.δ) Vu.δ := ⟨by linarith [Vu.hδ], Vu.hδ⟩
    have h1 : (1 : ℝ) ∈ Ioo (-2 : ℝ) 2 := ⟨by norm_num, by norm_num⟩
    have htgt := Vu.hTGT 0 h0 1 h1
    have hEXP0 : chartFlowExp (cov := cov) D q u
        = (extChartAt I z₀).symm ((Vu.Φ (1, 0)).1) := by
      simpa only [zero_smul, add_zero] using Vu.hEXP 0 h0
    rw [hpdef, hEXP0]
    exact mem_source_chartCurve (I := I) (x₀ := z₀)
      (u := fun _ => (Vu.Φ (1, 0)).1) (t := 0) htgt
  have hp_src : p ∈ (extChartAt I z₀).source := by rwa [extChartAt_source]
  have hp_base : p ∈ (trivializationAt E (TangentSpace I) z₀).baseSet := hp_chart
  -- the coordinates of the differential
  set φc : TangentSpace I p →L[ℝ] E :=
    (trivializationAt E (TangentSpace I) z₀).continuousLinearMapAt ℝ p with hφcdef
  set Dv : E → E :=
    fun y => φc ((mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) y) with hDvdef
  have hDvYx : Dv x = (Vx.Y 1) x := by
    simp only [hDvdef]
    rw [mfderiv_chartFlowExp (cov := cov) htor D q u x huK Vx]
    exact clm_frameVector (I := I) (z₀ := z₀) hp_src ((Vx.Y 1) x)
  have hDvYu : Dv u = (Vu.Y 1) u := by
    simp only [hDvdef]
    rw [mfderiv_chartFlowExp (cov := cov) htor D q u u huK Vu]
    exact clm_frameVector (I := I) (z₀ := z₀) hp_src ((Vu.Y 1) u)
  have hcfu : Dv u = cfVel (cov := cov) (I := I) D q u 1 :=
    hDvYu.trans (radial_col (cov := cov) hmet htor hqs D u u Vu)
  have hVxu : (Vx.Y 1) u = Dv u :=
    (radial_col (cov := cov) hmet htor hqs D u x Vx).trans hcfu.symm
  have hframe : ∀ y : E, frameVector (I := I) z₀ p (Dv y)
      = (mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) y := by
    intro y
    simp only [hDvdef]
    exact frameVector_clm (I := I) (z₀ := z₀) hp_src _
  -- Gauss's lemma in the two cases used
  have hGu : chartGram (I := I) z₀ p (Dv u) (Dv u) = chartGram (I := I) z₀ q u u := by
    rw [hDvYu]
    exact gauss_col (cov := cov) (z₀ := z₀) hmet htor hqs D u u Vu u
  have hGx : chartGram (I := I) z₀ p (Dv u) (Dv x) = chartGram (I := I) z₀ q u x := by
    rw [← hVxu, hDvYx]
    exact gauss_col (cov := cov) (z₀ := z₀) hmet htor hqs D u x Vx x
  -- the decomposition of `x`
  set α : ℝ := chartGram (I := I) z₀ q u x / chartGram (I := I) z₀ q u u with hαdef
  set xp : E := α • u with hxpdef
  set xo : E := x - xp with hxodef
  have hvvne : chartGram (I := I) z₀ q u u ≠ 0 := ne_of_gt (Real.sqrt_pos.mp hu_pos)
  have ho : chartGram (I := I) z₀ q u xo = 0 := by
    rw [hxodef, chartGram_sub_snd', hxpdef, chartGram_smul_snd, hαdef]
    field_simp
    ring
  have hx : x = xp + xo := by rw [hxodef]; abel
  -- the coordinates of the two parts
  have hDsmul : ∀ (s : ℝ) (w : E), Dv (s • w) = s • Dv w := by
    intro s w
    have h1 : (mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) (s • w)
        = s • (mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) w :=
      ContinuousLinearMap.map_smul _ s w
    have h2 : φc (s • (mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) w)
        = s • φc ((mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) w) :=
      ContinuousLinearMap.map_smul _ s _
    rw [hDvdef]
    exact (congrArg φc h1).trans h2
  have hDadd : ∀ (a b : E), Dv (a + b) = Dv a + Dv b := by
    intro a b
    have h1 : (mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) (a + b)
        = (mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) a
          + (mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) b :=
      ContinuousLinearMap.map_add _ a b
    have h2 : φc ((mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) a
          + (mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) b)
        = φc ((mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) a)
          + φc ((mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) b) :=
      ContinuousLinearMap.map_add _ _ _
    rw [hDvdef]
    exact (congrArg φc h1).trans h2
  have hDsub : ∀ (a b : E), Dv (a - b) = Dv a - Dv b := by
    intro a b
    have hab : a - b = a + (-1 : ℝ) • b := by rw [neg_smul, one_smul]; abel
    rw [hab, hDadd, hDsmul, neg_smul, one_smul, sub_eq_add_neg]
  have hDp : Dv xp = α • Dv u := by rw [hxpdef]; exact hDsmul α u
  have hDxo : Dv xo = Dv x - Dv xp := by rw [hxodef]; exact hDsub x xp
  have hDx : Dv x = Dv xp + Dv xo := by rw [hDxo]; abel
  have hcross : chartGram (I := I) z₀ p (Dv u) (Dv xo) = 0 := by
    rw [hDxo, chartGram_sub_snd', hGx, hDp, chartGram_smul_snd, hGu, hαdef]
    field_simp
    ring
  have hcross2 : chartGram (I := I) z₀ p (Dv xp) (Dv xo) = 0 := by
    rw [hDp, chartGram_smul_fst, hcross, mul_zero]
  have hcross3 : chartGram (I := I) z₀ p (Dv xo) (Dv xp) = 0 := by
    rw [chartGram_comm, hcross2]
  -- the parallel part has exactly the right norm
  have hpar : chartGram (I := I) z₀ p (Dv xp) (Dv xp) = chartGram (I := I) z₀ q xp xp := by
    rw [hDp, chartGram_smul_fst, chartGram_smul_snd, hGu, hxpdef, chartGram_smul_fst,
      chartGram_smul_snd]
  -- the orthogonal part obeys the **sharp** model bound
  have horth : chartGram (I := I) z₀ p (Dv xo) (Dv xo)
      ≤ (Real.sin (Real.sqrt (chartGram (I := I) z₀ q u u))
          / Real.sqrt (chartGram (I := I) z₀ q u u)) ^ 2
        * chartGram (I := I) z₀ q xo xo := by
    have hb := hsharp q hq u xo hu_pos huρ₁ ho
    have h2 : 0 ≤ chartGram (I := I) z₀ q xo xo :=
      Submission.Minimal.chartGram_self_nonneg (I := I) z₀ q xo
    have hsq : (‖(mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) xo‖) ^ 2
        ≤ ((Real.sin (Real.sqrt (chartGram (I := I) z₀ q u u))
              / Real.sqrt (chartGram (I := I) z₀ q u u))
            * Real.sqrt (chartGram (I := I) z₀ q xo xo)) ^ 2 := by
      rw [sq, sq]
      exact mul_le_mul hb hb (norm_nonneg _) (le_trans (norm_nonneg _) hb)
    rw [mul_pow, Real.sq_sqrt h2] at hsq
    have h1 : chartGram (I := I) z₀ p (Dv xo) (Dv xo)
        = ‖(mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) xo‖ ^ 2 := by
      rw [chartGram_apply, hframe xo, real_inner_self_eq_norm_sq]
    rw [h1]
    exact hsq
  -- Pythagoras at `p` and at `q`
  have hpyth : chartGram (I := I) z₀ p (Dv x) (Dv x)
      = chartGram (I := I) z₀ p (Dv xp) (Dv xp) + chartGram (I := I) z₀ p (Dv xo) (Dv xo) := by
    rw [hDx, chartGram_add_snd, chartGram_add_fst, chartGram_add_fst, hcross2, hcross3]
    ring
  have hcrossb2 : chartGram (I := I) z₀ q xp xo = 0 := by
    rw [hxpdef, chartGram_smul_fst, ho, mul_zero]
  have hcrossb3 : chartGram (I := I) z₀ q xo xp = 0 := by rw [chartGram_comm, hcrossb2]
  have hbase : chartGram (I := I) z₀ q x x
      = chartGram (I := I) z₀ q xp xp + chartGram (I := I) z₀ q xo xo := by
    conv_lhs => rw [hx]
    rw [chartGram_add_snd, chartGram_add_fst, chartGram_add_fst, hcrossb2, hcrossb3]
    ring
  -- the two parallel/orthogonal inner products in terms of `⟨u,x⟩` and `⟨u,u⟩`
  have hparval : chartGram (I := I) z₀ q xp xp
      = (chartGram (I := I) z₀ q u x) ^ 2 / chartGram (I := I) z₀ q u u := by
    rw [hxpdef, chartGram_smul_fst, chartGram_smul_snd, hαdef]
    field_simp
  have hkey : chartGram (I := I) z₀ q xo xo
      = chartGram (I := I) z₀ q x x
        - (chartGram (I := I) z₀ q u x) ^ 2 / chartGram (I := I) z₀ q u u := by
    rw [hbase, hparval]
    ring
  -- conclusion
  have hnorm : ‖(mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) u) x‖ ^ 2
      = chartGram (I := I) z₀ p (Dv x) (Dv x) := by
    rw [← hframe x, chartGram_apply, real_inner_self_eq_norm_sq]
  rw [hnorm, hpyth, hpar, hparval]
  rw [hkey] at horth
  linarith [horth]

/-- **The model differential bound in polar form** for the chart-flow exponential map: for
`⟨e,e⟩ = 1`, `⟨e,e'⟩ = 0`, `0 < r < ρ`,
`‖(dF)_{r e}(r' e + r e')‖² ≤ r'² + sin²r ⟨e',e'⟩`. -/
theorem chartFlow_model_bound_polar
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (hZsrc : Z ⊆ (chartAt H z₀).source)
    {lam : ℝ} (hlam : 0 < lam)
    (hlam_bnd : ∀ q ∈ Z, ∀ w : E, lam * ‖w‖ ^ 2 ≤ chartGram (I := I) z₀ q w w)
    (D : ChartFlowData (cov := cov) (I := I) z₀ Z) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ q ∈ Z, ∀ (r r' : ℝ) (e e' : E),
      0 < r → r < ρ →
      chartGram (I := I) z₀ q e e = 1 →
      chartGram (I := I) z₀ q e e' = 0 →
      ‖(mfderiv 𝓘(ℝ, E) I (chartFlowExp (cov := cov) D q) (r • e)) (r' • e + r • e')‖ ^ 2
        ≤ r' ^ 2 + (Real.sin r) ^ 2 * chartGram (I := I) z₀ q e' e' := by
  obtain ⟨ρ, hρ, hb⟩ := exists_uniform_chartFlow_model_bound
    (cov := cov) hmet htor hpinch hZsrc hlam hlam_bnd D
  refine ⟨ρ, hρ, fun q hq r r' e e' hr hrρ he hee' => ?_⟩
  have hrr : chartGram (I := I) z₀ q (r • e) (r • e) = r ^ 2 := by
    rw [chartGram_smul_fst, chartGram_smul_snd, he, mul_one]
    ring
  have hpos : 0 < chartGram (I := I) z₀ q (r • e) (r • e) := by
    rw [hrr]; positivity
  have hsqrt : Real.sqrt (chartGram (I := I) z₀ q (r • e) (r • e)) = r := by
    rw [hrr, Real.sqrt_sq hr.le]
  have hvx : chartGram (I := I) z₀ q (r • e) (r' • e + r • e') = r * r' := by
    rw [chartGram_smul_fst, chartGram_add_snd, chartGram_smul_snd, chartGram_smul_snd, he,
      hee', mul_zero, mul_one, add_zero]
  have hxx : chartGram (I := I) z₀ q (r' • e + r • e') (r' • e + r • e')
      = r' ^ 2 + r ^ 2 * chartGram (I := I) z₀ q e' e' := by
    rw [chartGram_add_fst, chartGram_add_snd, chartGram_add_snd, chartGram_smul_fst,
      chartGram_smul_snd, chartGram_smul_fst, chartGram_smul_snd,
      chartGram_smul_fst, chartGram_smul_snd, chartGram_smul_fst, chartGram_smul_snd,
      he, hee']
    have h1 : chartGram (I := I) z₀ q e' e = 0 := by
      rw [chartGram_comm (I := I) z₀ q e' e]; exact hee'
    rw [h1]
    ring
  have h := hb q hq (r • e) (r' • e + r • e') (by rw [hsqrt]; exact hr)
    (by rw [hsqrt]; exact hrρ)
  rw [hvx, hrr, hxx] at h
  rw [Real.sqrt_sq hr.le] at h
  have heq : (r * r') ^ 2 / r ^ 2 + (Real.sin r / r) ^ 2
        * (r' ^ 2 + r ^ 2 * chartGram (I := I) z₀ q e' e' - (r * r') ^ 2 / r ^ 2)
      = r' ^ 2 + (Real.sin r) ^ 2 * chartGram (I := I) z₀ q e' e' := by
    field_simp
    ring
  exact h.trans_eq heq

end

end Submission.ChartFlowModel
