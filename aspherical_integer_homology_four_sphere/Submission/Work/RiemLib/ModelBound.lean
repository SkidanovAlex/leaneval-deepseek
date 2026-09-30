import Submission.Work.RiemLib.ExpBound2

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The model bound for the exponential map (route (M) to Toponogov's hinge comparison)

This file contains the first step of the "model bound" route to Toponogov's hinge comparison
(see `Submission/Roadmap.lean` §28.4, route (M)):

* `mfderiv_expMap_model_bound` — the **model differential bound**: the differential of the
  exponential map at `v` is controlled by the model metric `dr² + sin²r dθ²` of the unit sphere in
  geodesic polar coordinates;
* `mfderiv_expMap_model_bound_polar` — the same bound in the polar form used for the length
  integral along a great circle: for a unit vector `e` (in the chart metric at `x₀`), a vector
  `e' ⊥ e` and reals `r > 0`, `r'`,
  `‖(d exp_{x₀})_{r e}(r' e + r e')‖² ≤ r'² + sin²r ‖e'‖²`.

The remaining steps (the great-circle path on the unit sphere, its polar decomposition in `T_x₀M`,
and the length integral) are in `Submission/ModelPath.lean`.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.ChartCurv
open Submission.Curvature
open Submission.ChartBounds
open Submission.Gauss
open Submission.ExpBound
open Submission.ExpBound2

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.ModelBound

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The model differential bound for the exponential map.**  There is `ρ > 0` such that for every
`v` with `0 < chartGram x₀ x₀ v v` and `√(chartGram x₀ x₀ v v) < ρ` and every `x`, the square of the
norm of `(d exp_{x₀})_v x` is at most the square of the model norm of `x` at `v`, namely
`⟨x,v⟩²/⟨v,v⟩ + (sin r/r)² (⟨x,x⟩ - ⟨x,v⟩²/⟨v,v⟩)` with `r = √⟨v,v⟩` (all inner products the chart
metric at `x₀`). -/
theorem mfderiv_expMap_model_bound [Nontrivial E]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ v x : E,
      0 < chartGram (I := I) x₀ x₀ v v →
      Real.sqrt (chartGram (I := I) x₀ x₀ v v) < ρ →
      ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) x‖ ^ 2
        ≤ (chartGram (I := I) x₀ x₀ v x) ^ 2 / (chartGram (I := I) x₀ x₀ v v)
          + (Real.sin (Real.sqrt (chartGram (I := I) x₀ x₀ v v))
              / Real.sqrt (chartGram (I := I) x₀ x₀ v v)) ^ 2
            * (chartGram (I := I) x₀ x₀ x x
                - (chartGram (I := I) x₀ x₀ v x) ^ 2 / (chartGram (I := I) x₀ x₀ v v)) := by
  obtain ⟨ρ₁, hρ₁, hsharp⟩ := exists_expMap_mfderiv_norm_bound (cov := cov) hmet htor hpinch x₀
  obtain ⟨ρg, hρg, hgauss⟩ := Submission.Gauss.gauss_lemma_fderiv (cov := cov) hmet htor x₀
  obtain ⟨ρc, hρc, hchartgeo⟩ := exists_pos_hasChartGeodesic (cov := cov) x₀
  obtain ⟨lam, hlam, Lam, hLam, hgram⟩ := Submission.ChartBounds.exists_chartGram_bounds (I := I)
    (x₀ := x₀) (K := {x₀}) isCompact_singleton (singleton_nonempty x₀) (by
      intro p hp
      rw [Set.mem_singleton_iff] at hp
      rw [hp]
      exact mem_chart_source H x₀)
  have hsqrtlam : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  refine ⟨Real.sqrt lam * min ρ₁ (min ρg ρc),
    mul_pos hsqrtlam (lt_min hρ₁ (lt_min hρg hρc)), fun v x hvpos hv => ?_⟩
  have hvn : ‖v‖ < min ρ₁ (min ρg ρc) := by
    have hle := (hgram x₀ (by simp) v).1
    have h1 : Real.sqrt lam * ‖v‖ ≤ Real.sqrt (chartGram (I := I) x₀ x₀ v v) := by
      rw [← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul hlam.le]
      exact Real.sqrt_le_sqrt hle
    have h2 : Real.sqrt lam * ‖v‖ < Real.sqrt lam * min ρ₁ (min ρg ρc) := lt_of_le_of_lt h1 hv
    exact lt_of_mul_lt_mul_left h2 (Real.sqrt_nonneg lam)
  have hvb : ‖v‖ < ρ₁ := lt_of_lt_of_le hvn (min_le_left _ _)
  have hvamb : ‖v‖ < min ρg ρc := lt_of_lt_of_le hvn (min_le_right _ _)
  have hvρg : ‖v‖ < ρg := lt_of_lt_of_le hvamb (min_le_left _ _)
  have hvρc : ‖v‖ < ρc := lt_of_lt_of_le hvamb (min_le_right _ _)
  -- the manifold point and its membership in the chart
  set p : M := expMap cov x₀ v with hpdef
  have hp_src : p ∈ (chartAt H x₀).source := by
    obtain ⟨u, w, hgc⟩ := hchartgeo v hvρc.le
    have hexp : expMap cov x₀ v = (extChartAt I x₀).symm (u 1) :=
      expMap_eq_of_hasChartGeodesic (cov := cov) hgc
    rw [hpdef, hexp]
    exact mem_source_chartCurve (I := I) (hgc.2.2.1 1 (by norm_num))
  have hp_base : p ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := hp_src
  -- the coordinates of the differential in the chart at `x₀`
  set φ : E →L[ℝ] E := (trivializationAt E (TangentSpace I) x₀).continuousLinearMapAt ℝ p
    with hφdef
  set D : E →L[ℝ] E := φ.comp (mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) with hDdef
  have hframe : ∀ y : E, frameVector (I := I) x₀ p (D y)
      = (mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) y := by
    intro y
    have h1 := Trivialization.symmL_continuousLinearMapAt (R := ℝ)
      (e := trivializationAt E (TangentSpace I) x₀) hp_base
      ((mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) y)
    show (Trivialization.symmL ℝ (trivializationAt E (TangentSpace I) x₀) p) (D y) = _
    rw [hDdef, ContinuousLinearMap.comp_apply]
    exact h1
  -- Gauss's lemma in coordinates
  have hG : ∀ y : E, chartGram (I := I) x₀ p (D v) (D y) = chartGram (I := I) x₀ x₀ v y := by
    intro y
    rw [chartGram_apply, hframe v, hframe y]
    exact hgauss v hvρg y
  -- the decomposition of `x`
  set α : ℝ := chartGram (I := I) x₀ x₀ v x / chartGram (I := I) x₀ x₀ v v with hαdef
  set xp : E := α • v with hxpdef
  set xo : E := x - xp with hxodef
  have hvvne : chartGram (I := I) x₀ x₀ v v ≠ 0 := ne_of_gt hvpos
  have ho : chartGram (I := I) x₀ x₀ v xo = 0 := by
    rw [hxodef, chartGram_sub_snd', hxpdef, chartGram_smul_snd, hαdef]
    field_simp
    ring
  have hx : x = xp + xo := by rw [hxodef]; abel
  -- the coordinates of the two parts
  have hDp : D xp = α • D v := by rw [hxpdef, map_smul]
  have hDxo : D xo = D x - D xp := by rw [hxodef, map_sub]
  have hDx : D x = D xp + D xo := by rw [hxodef, map_sub]; abel
  have hcross : chartGram (I := I) x₀ p (D v) (D xo) = 0 := by
    rw [hDxo, chartGram_sub_snd', hG x, hDp, chartGram_smul_snd, hG v, hαdef]
    field_simp
    ring
  have hcross2 : chartGram (I := I) x₀ p (D xp) (D xo) = 0 := by
    rw [hDp, chartGram_smul_fst, hcross, mul_zero]
  have hcross3 : chartGram (I := I) x₀ p (D xo) (D xp) = 0 := by
    rw [chartGram_comm, hcross2]
  -- the parallel part has exactly the right norm
  have hpar : chartGram (I := I) x₀ p (D xp) (D xp) = chartGram (I := I) x₀ x₀ xp xp := by
    rw [hDp, chartGram_smul_fst, chartGram_smul_snd, hG v, hxpdef, chartGram_smul_fst,
      chartGram_smul_snd]
  -- the orthogonal part obeys the **sharp** model bound
  have horth : chartGram (I := I) x₀ p (D xo) (D xo)
      ≤ (Real.sin (Real.sqrt (chartGram (I := I) x₀ x₀ v v))
          / Real.sqrt (chartGram (I := I) x₀ x₀ v v)) ^ 2
        * chartGram (I := I) x₀ x₀ xo xo := by
    have hb := hsharp v xo hvb ho
    have h1 : chartGram (I := I) x₀ p (D xo) (D xo)
        = ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) xo‖ ^ 2 := by
      rw [chartGram_apply, hframe xo, real_inner_self_eq_norm_sq]
    rw [h1]
    have h2 : 0 ≤ chartGram (I := I) x₀ x₀ xo xo := by
      rw [chartGram_apply]
      exact real_inner_self_nonneg
    have hcpos : 0 < Real.sqrt (chartGram (I := I) x₀ x₀ v v) := Real.sqrt_pos.mpr hvpos
    have hL : 0 ≤ Real.sqrt (chartGram (I := I) x₀ x₀ v v)
        * ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) xo‖ := by positivity
    have hsq := mul_self_le_mul_self hL hb
    rw [div_pow, div_mul_eq_mul_div,
      le_div_iff₀ (by positivity : (0:ℝ) < Real.sqrt (chartGram (I := I) x₀ x₀ v v) ^ 2)]
    nlinarith [hsq, Real.sq_sqrt hvpos.le, Real.sq_sqrt h2]
  -- Pythagoras at `p` and at `x₀`
  have hpyth : chartGram (I := I) x₀ p (D x) (D x)
      = chartGram (I := I) x₀ p (D xp) (D xp) + chartGram (I := I) x₀ p (D xo) (D xo) := by
    rw [hDx, chartGram_add_snd, chartGram_add_fst, chartGram_add_fst, hcross2, hcross3]
    ring
  have hcrossb2 : chartGram (I := I) x₀ x₀ xp xo = 0 := by
    rw [hxpdef, chartGram_smul_fst, ho, mul_zero]
  have hcrossb3 : chartGram (I := I) x₀ x₀ xo xp = 0 := by rw [chartGram_comm, hcrossb2]
  have hbase : chartGram (I := I) x₀ x₀ x x
      = chartGram (I := I) x₀ x₀ xp xp + chartGram (I := I) x₀ x₀ xo xo := by
    conv_lhs => rw [hx]
    rw [chartGram_add_snd, chartGram_add_fst, chartGram_add_fst, hcrossb2, hcrossb3]
    ring
  -- the two parallel/orthogonal inner products in terms of `⟨v,x⟩` and `⟨v,v⟩`
  have hparval : chartGram (I := I) x₀ x₀ xp xp
      = (chartGram (I := I) x₀ x₀ v x) ^ 2 / chartGram (I := I) x₀ x₀ v v := by
    rw [hxpdef, chartGram_smul_fst, chartGram_smul_snd, hαdef]
    field_simp
  have hkey : chartGram (I := I) x₀ x₀ xo xo
      = chartGram (I := I) x₀ x₀ x x
        - (chartGram (I := I) x₀ x₀ v x) ^ 2 / chartGram (I := I) x₀ x₀ v v := by
    rw [hbase, hparval]
    ring
  -- conclusion
  have hnorm : ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) v) x‖ ^ 2
      = chartGram (I := I) x₀ p (D x) (D x) := by
    rw [← hframe x, chartGram_apply, real_inner_self_eq_norm_sq]
  rw [hnorm, hpyth, hpar, hparval]
  rw [hkey] at horth
  linarith [horth]

/-- At the base point the chart metric is the square of the (Riemannian) norm. -/
lemma chartGram_self_eq_norm_sq_fiber (x₀ : M) (v : TangentSpace I x₀) :
    chartGram (I := I) x₀ x₀ v v = ‖v‖ ^ 2 :=
  Submission.ExpBound.chartGram_self_eq_norm_sq (I := I) x₀ v

/-- At the base point the chart metric of two vectors is their inner product (in the fibre). -/
lemma chartGram_self_eq_inner_fiber (x₀ : M) (e e' : TangentSpace I x₀) :
    chartGram (I := I) x₀ x₀ e e' = inner ℝ e e' :=
  Submission.Distance.chartGram_self_apply (I := I) x₀ e e'

/-- **The model differential bound in polar form.**  There is `ρ > 0` such that for all `r > 0`,
`r < ρ`, all unit `e` (in the chart metric at `x₀`), all `e'` orthogonal to `e` and all real `r'`,

`‖(d exp_{x₀})_{r e}(r' e + r e')‖² ≤ r'² + sin²r ‖e'‖²`.

This is the form in which the bound is applied along the great-circle path in `T_{x₀}M`: there
`e` is the azimuth and `r'`, `e'` are the radial and azimuthal velocities. -/
theorem mfderiv_expMap_model_bound_polar [Nontrivial E]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0) (hpinch : QuarterPinched cov)
    (x₀ : M) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ (r r' : ℝ) (e e' : TangentSpace I x₀),
      0 < r → r < ρ →
      chartGram (I := I) x₀ x₀ e e = 1 →
      chartGram (I := I) x₀ x₀ e e' = 0 →
      ‖(mfderiv 𝓘(ℝ, E) I (fun z : E => expMap cov x₀ z) (r • e)) (r' • e + r • e')‖ ^ 2
        ≤ r' ^ 2 + (Real.sin r) ^ 2 * ‖e'‖ ^ 2 := by
  obtain ⟨ρ, hρ, hb⟩ := mfderiv_expMap_model_bound (cov := cov) hmet htor hpinch x₀
  refine ⟨ρ, hρ, fun r r' e e' hr hrρ he hee' => ?_⟩
  have hrr : chartGram (I := I) x₀ x₀ (r • e) (r • e) = r ^ 2 := by
    rw [chartGram_smul_fst, chartGram_smul_snd, he, mul_one]
    ring
  have hpos : 0 < chartGram (I := I) x₀ x₀ (r • e) (r • e) := by
    rw [hrr]; positivity
  have hsqrt : Real.sqrt (chartGram (I := I) x₀ x₀ (r • e) (r • e)) = r := by
    rw [hrr, Real.sqrt_sq hr.le]
  have hvx : chartGram (I := I) x₀ x₀ (r • e) (r' • e + r • e') = r * r' := by
    rw [chartGram_smul_fst, chartGram_add_snd, chartGram_smul_snd, chartGram_smul_snd, he,
      hee', mul_zero, mul_one, add_zero]
  have hxx : chartGram (I := I) x₀ x₀ (r' • e + r • e') (r' • e + r • e')
      = r' ^ 2 + r ^ 2 * ‖e'‖ ^ 2 := by
    rw [chartGram_add_fst, chartGram_add_snd, chartGram_add_snd, chartGram_smul_fst,
      chartGram_smul_snd, chartGram_smul_fst, chartGram_smul_snd,
      chartGram_smul_fst, chartGram_smul_snd, chartGram_smul_fst, chartGram_smul_snd,
      he, hee']
    have h1 : chartGram (I := I) x₀ x₀ e' e = 0 := by
      rw [chartGram_comm (I := I) x₀ x₀ e' e]; exact hee'
    rw [h1, chartGram_self_eq_norm_sq_fiber (I := I) x₀ e']
    ring
  have h := hb (r • e) (r' • e + r • e') hpos (by rw [hsqrt]; exact hrρ)
  rw [hvx, hrr, hxx] at h
  rw [Real.sqrt_sq hr.le] at h
  have heq : (r * r') ^ 2 / r ^ 2 + (Real.sin r / r) ^ 2
        * (r' ^ 2 + r ^ 2 * ‖e'‖ ^ 2 - (r * r') ^ 2 / r ^ 2)
      = r' ^ 2 + (Real.sin r) ^ 2 * ‖e'‖ ^ 2 := by
    field_simp
    ring
  exact h.trans_eq heq

end

end Submission.ModelBound
