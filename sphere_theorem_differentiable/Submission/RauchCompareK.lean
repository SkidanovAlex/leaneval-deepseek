import Submission.RauchK
import Submission.IndexForm
import Submission.Minimal
import Submission.Commons.Analysis.ODE.sturm_model_lower_bound_general

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Rauch's comparison theorem: the norm lower bound

The Sturm comparison lemma `Commons.Analysis.ODE.sturm_model_lower_bound` says that a positive
solution `h` of `h'' + 4 h ≥ 0` on `(0,T)`, `T ≤ π/2`, whose Wronskian with the model
`t ↦ sin (2 t)/2` vanishes at `0⁺` and whose ratio to the model tends to `1` at `0⁺`, dominates the
model.  This file feeds the Rauch inequality (`Submission.RauchLocal.rauch_sturm_ready_of_hasDerivAt`)
into it and thereby proves **Rauch's comparison theorem** in the form used later:

> along a unit-speed geodesic whose curvature is at most `4`, the norm of a Jacobi field with
> `J(0) = 0` and unit initial derivative grows at least as fast as `sin (2 t)/2`.

## Contents

* `rauch_sturm_ready_explicit`: the Sturm data of Rauch's inequality in explicit form (the
  functions whose derivatives occur are written out, so that the limit hypotheses of
  `sturm_model_lower_bound` can be stated in terms of them);
* `rauch_norm_compare_of_tendsto`: the comparison with the two limit hypotheses supplied;
* `tendsto_sqrt_chartGram_div`: the initial asymptotics `√⟨y,y⟩ / t → ‖y'(0)‖`;
* `rauch_norm_compare`: the comparison with the limits derived from `y 0 = 0` and `|y'(0)| = 1`.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Curvature
open Submission.CurvatureVec
open Submission.Rauch
open Submission.RauchK
open Submission.RauchLocal
open Submission.ChartBounds
open Commons.Analysis.ODE
open Submission.IndexForm
open Submission.Minimal

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.RauchCompareK

noncomputable section

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable {K : ℝ}

/-- The model Jacobi field of the space form of curvature `K`: `t ↦ sin (√K t)/√K`. -/
noncomputable def modelK (K t : ℝ) : ℝ := Real.sin (Real.sqrt K * t) / Real.sqrt K

lemma modelK_apply (K t : ℝ) : modelK K t = Real.sin (Real.sqrt K * t) / Real.sqrt K := rfl

/-- `√⟨y,y⟩ / t → ‖y'(0)‖`: the initial asymptotics of a Jacobi field vanishing at `0`.  Here
`‖·‖` is the chart norm at the base point of the coordinate curve; the hypothesis `hy` is the
differentiability of `y` at `0`. -/
theorem tendsto_sqrt_chartGram_div (hmet : IsMetricCompatible cov)
    {x₀ : M} {u w y : ℝ → E}
    (hu : HasDerivAt u (w 0) 0) (hutgt : u 0 ∈ (extChartAt I x₀).target)
    (hy : HasDerivAt y (deriv y 0) 0) (hy0 : y 0 = 0) :
    Tendsto (fun t : ℝ =>
        Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) / t)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0))
        (deriv y 0) (deriv y 0)))) := by
  -- the slope of `y` at `0` tends to the derivative
  have hslope' : Tendsto (fun t : ℝ => t⁻¹ • y t) (𝓝[>] (0 : ℝ)) (𝓝 (deriv y 0)) := by
    have h1 := hy.tendsto_slope_zero_right (x := (0 : ℝ))
    simpa only [zero_add, hy0, sub_zero] using h1
  -- the coordinate curve is continuous at `0`
  have huc : Tendsto (fun t : ℝ => (extChartAt I x₀).symm (u t)) (𝓝[>] (0 : ℝ))
      (𝓝 ((extChartAt I x₀).symm (u 0))) :=
    ((continuousAt_extChartAt_symm'' hutgt).comp hu.continuousAt).tendsto.mono_left
      nhdsWithin_le_nhds
  -- joint continuity of the chart metric in `(p, a, b)`
  have hgram := continuousAt_chartGram_prod3 (I := I) x₀
    (mem_source_chartCurve (I := I) hutgt) (deriv y 0) (deriv y 0)
  have hpair : Tendsto (fun t : ℝ =>
      ((extChartAt I x₀).symm (u t), (t⁻¹ • y t, t⁻¹ • y t))) (𝓝[>] (0 : ℝ))
      (𝓝 ((extChartAt I x₀).symm (u 0), (deriv y 0, deriv y 0))) := by
    have h := huc.prodMk (hslope'.prodMk hslope')
    simpa only [← nhds_prod_eq] using h
  have hmain : Tendsto (fun t : ℝ =>
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (t⁻¹ • y t) (t⁻¹ • y t))
      (𝓝[>] (0 : ℝ))
      (𝓝 (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) (deriv y 0) (deriv y 0))) :=
    (hgram.tendsto.comp hpair).congr (by simp)
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hmain
  have hev : (fun t : ℝ => Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (t⁻¹ • y t) (t⁻¹ • y t)))
      =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t : ℝ => Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (y t) (y t)) / t) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    rw [chartGram_smul_fst, chartGram_smul_snd]
    rw [show t⁻¹ * (t⁻¹ * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))
        = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) / t ^ 2 by ring]
    rw [Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ t ^ 2),
      Real.sqrt_sq (le_of_lt htpos)]
  exact Filter.Tendsto.congr' hev hsqrt

open Submission.RauchCompare (tendsto_sqrt_chartGram_div)

/-- **Rauch's comparison theorem for a chart geodesic, with an arbitrary curvature bound.**  Let
`(u,w)` be a unit-speed geodesic in the chart at `x₀` and let `y` be a Jacobi field along it with
`y 0 = 0` and `|y'(0)| = 1` (the chart norm at `u 0`).  If `sec ≤ K` and the squared norm of `y` is
positive on `(0,T)` with `T ≤ π/√K`, then `‖y(t)‖ ≥ sin (√K t)/√K`: the norm of a Jacobi field
grows at least as fast as in the space form of curvature `K`.

This is the **parametric Rauch I (norm lower bound)** of `Submission.Roadmap.lean` §126.4 item 2: it
is what makes the conjugate-radius lift of a curve of length `< π/√K` exist, i.e. the geometric input
of the long homotopy lemma. -/
theorem rauch_norm_compare_of_curvLe
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hKc : CurvLe cov K) (hKpos : 0 < K) (htor : cov.torsion = 0)
    {x₀ : M} {u w y : ℝ → E} {T : ℝ}
    (hutgt : ∀ t ∈ Ioo (-1 : ℝ) (T + 1), u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Ioo (-1 : ℝ) (T + 1), HasDerivAt u (w t) t)
    (hunit : ∀ t ∈ Ioo (-1 : ℝ) (T + 1),
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    (hy : ∀ t ∈ Ioo (-1 : ℝ) (T + 1), HasDerivAt y (deriv y t) t)
    (hDy : ∀ t ∈ Ioo (-1 : ℝ) (T + 1), HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Ioo (-1 : ℝ) (T + 1),
      chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
        + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hT : 0 < T) (hTπ : T ≤ Real.pi / Real.sqrt K)
    (hpos : ∀ t ∈ Ioo (0 : ℝ) T,
      0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))
    (hy0 : y 0 = 0)
    (hinit : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0)) (deriv y 0) (deriv y 0) = 1) :
    ∀ t ∈ Ioo (0 : ℝ) T,
      modelK K t ≤ Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) := by
  have h0mem : (0 : ℝ) ∈ Ioo (-1 : ℝ) (T + 1) := ⟨by norm_num, by linarith⟩
  set H : ℝ → ℝ := fun s => Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
    (y s) (y s)) with hHdef
  set c : ℝ → ℝ := fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
    (chartCovDeriv cov x₀ u w y s) (y s) with hcdef
  set Kloc : ℝ → ℝ := fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
      (chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) s) (y s)
    + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
      (chartCovDeriv cov x₀ u w y s) (chartCovDeriv cov x₀ u w y s) with hKdef
  -- ### the Sturm data
  have hHderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt H (c t / H t) t := by
    intro t ht
    have ht' : t ∈ Ioo (-1 : ℝ) (T + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      ((hu t ht').continuousAt).preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hutgt t ht'))
    simpa only [H, c] using hasDerivAt_sqrt_chartGram_self_of_hasDerivAt (cov := cov) hmet
      (hu t ht') (hutgt t ht') hstay (hy t ht') (hpos t ht)
  have hcderiv : ∀ t ∈ Ioo (0 : ℝ) T, HasDerivAt c (Kloc t) t := by
    intro t ht
    have ht' : t ∈ Ioo (-1 : ℝ) (T + 1) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      ((hu t ht').continuousAt).preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hutgt t ht'))
    simpa only [c, Kloc] using hasDerivAt_deriv_chartGram_self_of_hasDerivAt (cov := cov) hmet
      (hu t ht') (hutgt t ht') hstay (hy t ht') (hDy t ht')
  have hg2 : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun s : ℝ => c s / H s) (Kloc t / H t - (c t) ^ 2 / (H t) ^ 3) t := by
    intro t ht
    have hHpos : 0 < H t := Real.sqrt_pos.mpr (hpos t ht)
    have hdiv := (hcderiv t ht).div (hHderiv t ht) (ne_of_gt hHpos)
    refine hdiv.congr_deriv ?_
    have hid : (Kloc t * H t - c t * (c t / H t)) / H t ^ 2
        = Kloc t / H t - (c t) ^ 2 / (H t) ^ 3 := by
      field_simp
    simp only [hid]
  have hineq : ∀ t ∈ Ioo (0 : ℝ) T,
      0 ≤ Kloc t / H t - (c t) ^ 2 / (H t) ^ 3 + K * H t := by
    intro t ht
    have hHpos : 0 < H t := Real.sqrt_pos.mpr (hpos t ht)
    have hH2 : H t ^ 2 = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) :=
      Real.sq_sqrt (le_of_lt (hpos t ht))
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      ((hu t ⟨by linarith [ht.1], by linarith [ht.2]⟩).continuousAt).preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hutgt t ⟨by linarith [ht.1], by linarith [ht.2]⟩))
    have hrauch := (rauch_inequality_of_hasDerivAt_of_curvLe (cov := cov) hcov hmet hKc hKpos.le htor
      (x₀ := x₀) (u := u) (w := w) (y := y) (a := 0) (b := T)
      (fun s hs => hutgt s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (fun s hs => hu s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (fun s hs => hunit s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (fun s hs => hy s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (fun s hs => hDy s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      (fun s hs => hjac s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      hpos) t ht
    have hderivg : deriv (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (y s) (y s)) t = 2 * c t := by
      have hg1 := hasDerivAt_chartGram_self_of_hasDerivAt (cov := cov) hmet
        (hu t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        (hutgt t ⟨by linarith [ht.1], by linarith [ht.2]⟩) hstay (hy t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
      rw [hg1.deriv]
    have hcongr : (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          (y r) (y r)) s) =ᶠ[𝓝 t] (fun s => 2 * c s) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      have hstay' : ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target :=
        ((hu s ⟨by linarith [hs.1], by linarith [hs.2]⟩).continuousAt).preimage_mem_nhds
          ((isOpen_extChartAt_target x₀).mem_nhds (hutgt s ⟨by linarith [hs.1], by linarith [hs.2]⟩))
      rw [(hasDerivAt_chartGram_self_of_hasDerivAt (cov := cov) hmet
        (hu s ⟨by linarith [hs.1], by linarith [hs.2]⟩)
        (hutgt s ⟨by linarith [hs.1], by linarith [hs.2]⟩) hstay'
        (hy s ⟨by linarith [hs.1], by linarith [hs.2]⟩)).deriv]
    have hderiv2 : deriv (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          (y r) (y r)) s) t = 2 * Kloc t := by
      rw [Filter.EventuallyEq.deriv_eq hcongr]
      have h2 := (hasDerivAt_deriv_chartGram_self_of_hasDerivAt (cov := cov) hmet
        (hu t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        (hutgt t ⟨by linarith [ht.1], by linarith [ht.2]⟩) hstay
        (hy t ⟨by linarith [ht.1], by linarith [ht.2]⟩)
        (hDy t ⟨by linarith [ht.1], by linarith [ht.2]⟩)).const_mul (2 : ℝ)
      rw [h2.deriv]
    rw [hderivg, hderiv2, ← hH2] at hrauch
    have heq2 : (2 * c t) ^ 2 / (2 * H t ^ 2) = 2 * ((c t) ^ 2 / H t ^ 2) := by
      field_simp
    rw [heq2] at hrauch
    have hKineq : (c t) ^ 2 / H t ^ 2 - K * H t ^ 2 ≤ Kloc t := by linarith
    have hH3pos : 0 < H t ^ 3 := by positivity
    have hkey : (Kloc t / H t - (c t) ^ 2 / (H t) ^ 3 + K * H t) * H t ^ 3
        = Kloc t * H t ^ 2 - (c t) ^ 2 + K * H t ^ 4 := by
      field_simp
    have hpoly : 0 ≤ Kloc t * H t ^ 2 - (c t) ^ 2 + K * H t ^ 4 := by
      have hmul : ((c t) ^ 2 / H t ^ 2 - K * H t ^ 2) * H t ^ 2 ≤ Kloc t * H t ^ 2 :=
        mul_le_mul_of_nonneg_right hKineq (by positivity)
      have heq : ((c t) ^ 2 / H t ^ 2 - K * H t ^ 2) * H t ^ 2 = (c t) ^ 2 - K * H t ^ 4 := by
        field_simp
      rw [heq] at hmul
      linarith
    have hprod : 0 ≤ (Kloc t / H t - (c t) ^ 2 / (H t) ^ 3 + K * H t) * H t ^ 3 := by
      rw [hkey]
      exact hpoly
    exact nonneg_of_mul_nonneg_right (by rw [mul_comm]; exact hprod) hH3pos
  -- ### the initial asymptotics `H t / t → 1`
  have hHdiv : Tendsto (fun t : ℝ => H t / t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := tendsto_sqrt_chartGram_div (cov := cov) hmet (hu 0 h0mem) (hutgt 0 h0mem)
      (hy 0 h0mem) hy0
    have h1 : Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0))
        (deriv y 0) (deriv y 0)) = 1 := by
      rw [hinit, Real.sqrt_one]
    simpa only [H, h1] using h
  have hH0 : Tendsto H (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h := hid.mul hHdiv
    have h1 : (0 : ℝ) * 1 = 0 := by ring
    rw [h1] at h
    refine Filter.Tendsto.congr' ?_ h
    filter_upwards [self_mem_nhdsWithin] with t ht
    have h3 : t * (H t / t) = H t := by
      rw [← mul_div_assoc]
      exact mul_div_cancel_left₀ (H t) (ne_of_gt ht)
    exact h3
  have hHpos_ev : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < H t := by
    filter_upwards [Ioo_mem_nhdsGT hT] with t ht
    exact Real.sqrt_pos.mpr (hpos t ht)
  -- ### boundedness of the covariant derivative near `0`
  have hDyc : ContinuousAt (chartCovDeriv cov x₀ u w y) 0 := (hDy 0 h0mem).continuousAt
  have huc : ContinuousAt (fun t : ℝ => (extChartAt I x₀).symm (u t)) 0 :=
    (continuousAt_extChartAt_symm'' (hutgt 0 h0mem)).comp (hu 0 h0mem).continuousAt
  set Mbd : ℝ := Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0))
    (chartCovDeriv cov x₀ u w y 0) (chartCovDeriv cov x₀ u w y 0)) + 1 with hMdef
  have hgramcont : ContinuousAt (fun t : ℝ => Real.sqrt (chartGram (I := I) x₀
      ((extChartAt I x₀).symm (u t)) (chartCovDeriv cov x₀ u w y t)
      (chartCovDeriv cov x₀ u w y t))) 0 := by
    have hpair : ContinuousAt (fun t : ℝ => ((extChartAt I x₀).symm (u t),
        (chartCovDeriv cov x₀ u w y t, chartCovDeriv cov x₀ u w y t))) 0 := by
      have h := huc.tendsto.prodMk (hDyc.tendsto.prodMk hDyc.tendsto)
      simp only [← nhds_prod_eq] at h
      exact h
    have h2 : ContinuousAt (fun q : M × E × E => chartGram (I := I) x₀ q.1 q.2.1 q.2.2)
        ((extChartAt I x₀).symm (u 0),
          (chartCovDeriv cov x₀ u w y 0, chartCovDeriv cov x₀ u w y 0)) :=
      continuousAt_chartGram_prod3 (I := I) x₀
        (mem_source_chartCurve (I := I) (hutgt 0 h0mem))
        (chartCovDeriv cov x₀ u w y 0) (chartCovDeriv cov x₀ u w y 0)
    have h3 : ContinuousAt (fun t : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (chartCovDeriv cov x₀ u w y t) (chartCovDeriv cov x₀ u w y t)) 0 :=
      ContinuousAt.comp (f := fun t : ℝ => ((extChartAt I x₀).symm (u t),
        (chartCovDeriv cov x₀ u w y t, chartCovDeriv cov x₀ u w y t))) (x := 0) h2 hpair
    exact Real.continuous_sqrt.continuousAt.comp h3
  have hbnd : ∀ᶠ t in 𝓝[>] (0 : ℝ), Real.sqrt (chartGram (I := I) x₀
      ((extChartAt I x₀).symm (u t)) (chartCovDeriv cov x₀ u w y t)
      (chartCovDeriv cov x₀ u w y t)) ≤ Mbd := by
    have hb : ∀ᶠ t in 𝓝 (0 : ℝ), dist (Real.sqrt (chartGram (I := I) x₀
        ((extChartAt I x₀).symm (u t)) (chartCovDeriv cov x₀ u w y t)
        (chartCovDeriv cov x₀ u w y t)))
        (Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u 0))
          (chartCovDeriv cov x₀ u w y 0) (chartCovDeriv cov x₀ u w y 0))) < 1 :=
      (Metric.tendsto_nhds.mp hgramcont.tendsto) 1 one_pos
    filter_upwards [hb.filter_mono nhdsWithin_le_nhds] with t ht
    rw [Real.dist_eq] at ht
    have h2 := (abs_lt.mp ht).2
    rw [hMdef]
    linarith
  -- ### the two limits
  have hcH : Tendsto (fun t : ℝ => (c t / H t) * modelK K t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun t : ℝ => Mbd * |modelK K t|) ?_ ?_
    · filter_upwards [hbnd, hHpos_ev] with t hb hHp
      have hcs : |c t| ≤ Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (chartCovDeriv cov x₀ u w y t) (chartCovDeriv cov x₀ u w y t)) * H t := by
        have h2 := chartGram_sq_le (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (chartCovDeriv cov x₀ u w y t) (y t)
        have h3 := Real.abs_le_sqrt h2
        rwa [Real.sqrt_mul
          (chartGram_self_nonneg (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (chartCovDeriv cov x₀ u w y t))] at h3
      have h1 : |c t / H t| ≤ Mbd := by
        rw [abs_div, abs_of_pos hHp, div_le_iff₀ hHp]
        nlinarith [hcs, hb, hHp]
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    · have hmod : Tendsto (fun t : ℝ => |modelK K t|) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hcont : Continuous (fun t : ℝ => |modelK K t|) :=
          continuous_abs.comp ((Real.continuous_sin.comp
            (continuous_const.mul continuous_id)).div_const (Real.sqrt K))
        have h : Tendsto (fun t : ℝ => |modelK K t|) (𝓝 (0 : ℝ)) (𝓝 (|modelK K 0|)) :=
          hcont.continuousAt.tendsto
        have h' : Tendsto (fun t : ℝ => |modelK K t|) (𝓝[>] (0 : ℝ)) (𝓝 (|modelK K 0|)) :=
          h.mono_left nhdsWithin_le_nhds
        simpa only [modelK_apply, mul_zero, Real.sin_zero, zero_div, abs_zero] using h'
      have h := hmod.const_mul Mbd
      simpa using h
  have hHcos : Tendsto (fun t : ℝ => H t * Real.cos (Real.sqrt K * t)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcos : Tendsto (fun t : ℝ => Real.cos (Real.sqrt K * t)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have h : Tendsto (fun t : ℝ => Real.cos (Real.sqrt K * t)) (𝓝 (0 : ℝ)) (𝓝 (Real.cos (Real.sqrt K * 0))) :=
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    have h := hH0.mul hcos
    simpa using h
  have hlim : Tendsto (fun t : ℝ => (c t / H t) * modelK K t - H t * Real.cos (Real.sqrt K * t))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hcH.sub hHcos
    simpa using h
  have htmodel : Tendsto (fun t : ℝ => t / modelK K t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hsinc : Tendsto (fun t : ℝ => Real.sinc (Real.sqrt K * t)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have h : Tendsto (fun t : ℝ => Real.sinc (Real.sqrt K * t)) (𝓝 (0 : ℝ)) (𝓝 (Real.sinc (Real.sqrt K * 0))) :=
        (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    have hinv : Tendsto (fun t : ℝ => (Real.sinc (Real.sqrt K * t))⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have h := hsinc.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
      simpa only [inv_one] using h
    refine Filter.Tendsto.congr' ?_ hinv
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hr0 : Real.sqrt K ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos hKpos)
    have h2 : Real.sqrt K * t ≠ 0 := mul_ne_zero hr0 (ne_of_gt ht)
    simp only [modelK_apply]
    rw [Real.sinc_of_ne_zero h2]
    by_cases hsin : Real.sin (Real.sqrt K * t) = 0
    · simp [hsin]
    · field_simp
  have hlim2 : Tendsto (fun t : ℝ => H t / modelK K t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hev : (fun t : ℝ => (H t / t) * (t / modelK K t)) =ᶠ[𝓝[>] (0 : ℝ)]
        (fun t : ℝ => H t / modelK K t) := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      rw [div_mul_div_comm, mul_comm (H t) t]
      rw [mul_div_mul_left _ _ (ne_of_gt ht)]
    have h := hHdiv.mul htmodel
    have h1 : (1 : ℝ) * 1 = 1 := by ring
    rw [h1] at h
    exact Filter.Tendsto.congr' hev h
  -- ### the model bound
  have hh2 : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivAt (fun s : ℝ => c s / H s) (deriv (fun s : ℝ => c s / H s) t) t := by
    intro t ht
    rw [(hg2 t ht).deriv]
    exact hg2 t ht
  have hineq' : ∀ t ∈ Ioo (0 : ℝ) T,
      0 ≤ deriv (fun s : ℝ => c s / H s) t + K * H t := by
    intro t ht
    rw [(hg2 t ht).deriv]
    exact hineq t ht
  have hkey := sturm_model_lower_bound_general (h := H) (h' := fun s : ℝ => c s / H s) (K := K)
    hKpos hT hTπ hHderiv hh2 hineq' (by simpa only [modelK_apply] using hlim)
    (by simpa only [modelK_apply] using hlim2)
  intro t ht
  simpa only [modelK_apply, H] using hkey t ht

end

end Submission.RauchCompareK
