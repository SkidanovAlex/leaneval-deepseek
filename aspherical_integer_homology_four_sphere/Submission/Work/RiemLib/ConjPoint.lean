import Submission.Work.RiemLib.Rauch
import Submission.Work.RiemLib.ChartBounds
import Submission.Work.RiemLib.Commons.Analysis.ODE.sturm_eqOn_zero_of_second_deriv_add_nonneg
import Submission.Work.RiemLib.Commons.Analysis.ODE.sturm_eqOn_zero_of_second_deriv_add_nonneg_endpoint
import Submission.Work.RiemLib.Commons.Analysis.ODE.sturm_eqOn_zero_Icc
import Submission.Work.RiemLib.Commons.Topology.Order.sInf_mem_of_isClosed_of_nonempty

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Rauch's theorem: no conjugate point before `π/2`

This file closes the gap between the differential inequality `Rauch.rauch_inequality`
(`(√g)'' + 4 √g ≥ 0` for a Jacobi field on a unit-speed chart geodesic) and the Sturm comparison
lemma `Commons.Analysis.ODE.sturm_eqOn_zero_of_second_deriv_add_nonneg`, and then states **Rauch's
theorem** in the chart-local form used by the project:

> a Jacobi field `y` along a unit-speed chart geodesic with `y 0 = 0` has no zero in `(0, π/2)`
> unless it vanishes identically.

## Contents

* `hasDerivAt_sqrt_chartGram_self`: `(√⟨y,y⟩)' = ⟨Dy,y⟩ / √⟨y,y⟩`;
* `hasDerivAt_deriv_sqrt_chartGram_self`: the second derivative, `(⟨Dy,y⟩/√⟨y,y⟩)'`;
* `rauch_sturm_ready`: the inequality `0 ≤ g2 t + 4 √⟨y,y⟩` for the first and second derivatives of
  `√⟨y,y⟩`, i.e. exactly the hypothesis of the Sturm lemma with `λ = 4`.
-/

set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Jacobi
open Submission.ChartCurv
open Submission.Curvature
open Submission.CurvatureVec
open Submission.Rauch
open Submission.ChartBounds
open Commons.Analysis.ODE

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.ConjPoint

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- **The derivative of `√⟨y,y⟩`.** -/
theorem hasDerivAt_sqrt_chartGram_self
    (hmet : IsMetricCompatible cov) {x₀ : M} {v : E} {u w : ℝ → E}
    (h : HasChartGeodesic cov x₀ v u w) {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) {y : ℝ → E}
    (hy : HasDerivAt y (deriv y t) t)
    (hpos : 0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) :
    HasDerivAt (fun s => Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (y s) (y s)))
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (chartCovDeriv cov x₀ u w y t) (y t)
        / Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))) t := by
  have hg := hasDerivAt_chartGram_self (cov := cov) hmet h ht hy
  have hsqrt := hg.sqrt (ne_of_gt hpos)
  have hval : (2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (chartCovDeriv cov x₀ u w y t) (y t))
        / (2 * Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)))
      = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (chartCovDeriv cov x₀ u w y t) (y t)
        / Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) := by
    rw [mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [hval] at hsqrt
  exact hsqrt

/-- **The second derivative of `√⟨y,y⟩`.**  If `c = ⟨Dy, y⟩` and `c' = K`, then
`(c/√g)' = (K √g - c (c/√g)) / g`. -/
theorem hasDerivAt_deriv_sqrt_chartGram_self
    (hmet : IsMetricCompatible cov) {x₀ : M} {v : E} {u w : ℝ → E}
    (h : HasChartGeodesic cov x₀ v u w) {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) {y : ℝ → E}
    (hy : HasDerivAt y (deriv y t) t)
    (hpos : 0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))
    {K : ℝ}
    (hc : HasDerivAt (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
      (chartCovDeriv cov x₀ u w y s) (y s)) K t) :
    HasDerivAt (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (chartCovDeriv cov x₀ u w y s) (y s)
        / Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s)))
      ((K * Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))
          - chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
              (chartCovDeriv cov x₀ u w y t) (y t)
            * (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
                (chartCovDeriv cov x₀ u w y t) (y t)
              / Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))))
        / (Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))) ^ 2) t := by
  have hsqrt := hasDerivAt_sqrt_chartGram_self (cov := cov) hmet h ht hy hpos
  exact hc.div hsqrt (ne_of_gt (Real.sqrt_pos.mpr hpos))

/-- **The Rauch inequality in the form needed by Sturm comparison, with a speed parameter.**  For a
Jacobi field `y` along a chart geodesic of constant squared speed `c²` whose squared norm `⟨y,y⟩` is
positive on `(a,b)`, the function `h = √⟨y,y⟩` has first and second derivatives `g1`, `g2` satisfying
`0 ≤ g2 + 4 c² h`, i.e. the hypothesis of
`Commons.Analysis.ODE.sturm_eqOn_zero_of_second_deriv_add_nonneg` with `λ = 4c²`. -/
theorem rauch_sturm_ready_speed
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) (htor : cov.torsion = 0)
    {x₀ : M} {v : E} {u w y : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    {c : ℝ}
    (hspeed : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = c ^ 2)
    {a b : ℝ} (ha : -2 < a) (hb : b < 2)
    (hy : ∀ t ∈ Ioo a b, HasDerivAt y (deriv y t) t)
    (hDy : ∀ t ∈ Ioo a b, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Ioo a b, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hpos : ∀ t ∈ Ioo a b,
      0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) :
    ∃ (g1 g2 : ℝ → ℝ),
      (∀ t ∈ Ioo a b, HasDerivAt (fun s => Real.sqrt (chartGram (I := I) x₀
          ((extChartAt I x₀).symm (u s)) (y s) (y s))) (g1 t) t) ∧
      (∀ t ∈ Ioo a b, HasDerivAt g1 (g2 t) t) ∧
      (∀ t ∈ Ioo a b, 0 ≤ g2 t + 4 * c ^ 2 * Real.sqrt (chartGram (I := I) x₀
          ((extChartAt I x₀).symm (u t)) (y t) (y t))) := by
  classical
  haveI : ContMDiffCovariantDerivative cov ∞ := hcov
  set H : ℝ → ℝ := fun s => Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
    (y s) (y s)) with hHdef
  set ct : ℝ → ℝ := fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
    (chartCovDeriv cov x₀ u w y s) (y s) with hcdef
  set Kloc : ℝ → ℝ := fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
      (chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) s) (y s)
    + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
      (chartCovDeriv cov x₀ u w y s) (chartCovDeriv cov x₀ u w y s) with hKdef
  have hHderiv : ∀ t ∈ Ioo a b, HasDerivAt H (ct t / H t) t := by
    intro t ht
    have ht2 : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1, ha], by linarith [ht.2, hb]⟩
    have hsqrt := hasDerivAt_sqrt_chartGram_self (cov := cov) hmet h ht2 (hy t ht) (hpos t ht)
    simpa only [H, ct] using hsqrt
  have hcderiv : ∀ t ∈ Ioo a b, HasDerivAt ct (Kloc t) t := by
    intro t ht
    have ht2 : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1, ha], by linarith [ht.2, hb]⟩
    simpa only [ct, Kloc] using hasDerivAt_deriv_chartGram_self (cov := cov) hmet h ht2
      (hy t ht) (hDy t ht)
  refine ⟨fun t => ct t / H t, fun t => Kloc t / H t - (ct t) ^ 2 / (H t) ^ 3,
    hHderiv, ?_, ?_⟩
  · -- the second derivative of `H`
    intro t ht
    have hHpos : 0 < H t := Real.sqrt_pos.mpr (hpos t ht)
    have hHne : H t ≠ 0 := ne_of_gt hHpos
    have hdiv := (hcderiv t ht).div (hHderiv t ht) hHne
    refine hdiv.congr_deriv ?_
    have hid : (Kloc t * H t - ct t * (ct t / H t)) / H t ^ 2
        = Kloc t / H t - (ct t) ^ 2 / (H t) ^ 3 := by
      field_simp
    simp only [hid]
  · -- the inequality `0 ≤ g2 t + 4 c² √⟨y,y⟩`
    intro t ht
    have ht2 : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1, ha], by linarith [ht.2, hb]⟩
    have hHpos : 0 < H t := Real.sqrt_pos.mpr (hpos t ht)
    have hH2 : H t ^ 2 = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) :=
      Real.sq_sqrt (le_of_lt (hpos t ht))
    -- Rauch's inequality
    have hrauch := rauch_inequality_speed (cov := cov) (c := c) hcov hmet hpinch htor h hspeed
      ha hb hy hDy hjac hpos t ht
    have hderivg : deriv (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (y s) (y s)) t = 2 * ct t := by
      have hg1 := hasDerivAt_chartGram_self (cov := cov) hmet h ht2 (hy t ht)
      rw [hg1.deriv]

    have hcongr : (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          (y r) (y r)) s) =ᶠ[𝓝 t] (fun s => 2 * ct s) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      have hs2 : s ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hs.1, ha], by linarith [hs.2, hb]⟩
      rw [(hasDerivAt_chartGram_self (cov := cov) hmet h hs2 (hy s hs)).deriv]

    have hderiv2 : deriv (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          (y r) (y r)) s) t = 2 * Kloc t := by
      rw [Filter.EventuallyEq.deriv_eq hcongr]
      have h2 := (hasDerivAt_deriv_chartGram_self (cov := cov) hmet h ht2 (hy t ht)
        (hDy t ht)).const_mul (2 : ℝ)
      rw [h2.deriv]
    rw [hderivg, hderiv2, ← hH2] at hrauch
    -- `hrauch : (2 ct)² / (2 H²) - 8 c² H² ≤ 2 K`
    have hrauch' : 2 * ((ct t) ^ 2 / H t ^ 2) - 8 * c ^ 2 * H t ^ 2 ≤ 2 * Kloc t := by
      convert hrauch using 2
      field_simp
    have hK : (ct t) ^ 2 / H t ^ 2 - 4 * c ^ 2 * H t ^ 2 ≤ Kloc t := by linarith
    have hH3pos : 0 < H t ^ 3 := by positivity
    have hkey : (Kloc t / H t - (ct t) ^ 2 / (H t) ^ 3 + 4 * c ^ 2 * H t) * H t ^ 3
        = Kloc t * H t ^ 2 - (ct t) ^ 2 + 4 * c ^ 2 * H t ^ 4 := by
      field_simp
    have hpoly : 0 ≤ Kloc t * H t ^ 2 - (ct t) ^ 2 + 4 * c ^ 2 * H t ^ 4 := by
      have hmul : ((ct t) ^ 2 / H t ^ 2 - 4 * c ^ 2 * H t ^ 2) * H t ^ 2
          ≤ Kloc t * H t ^ 2 :=
        mul_le_mul_of_nonneg_right hK (by positivity)
      have heq : ((ct t) ^ 2 / H t ^ 2 - 4 * c ^ 2 * H t ^ 2) * H t ^ 2
          = (ct t) ^ 2 - 4 * c ^ 2 * H t ^ 4 := by
        field_simp
      rw [heq] at hmul
      linarith
    have hprod : 0 ≤ (Kloc t / H t - (ct t) ^ 2 / (H t) ^ 3 + 4 * c ^ 2 * H t) * H t ^ 3 := by
      rw [hkey]
      exact hpoly
    have hfin : 0 ≤ Kloc t / H t - (ct t) ^ 2 / (H t) ^ 3 + 4 * c ^ 2 * H t :=
      nonneg_of_mul_nonneg_right (by rw [mul_comm]; exact hprod) hH3pos
    simpa only [H] using hfin

/-- **The Rauch inequality in the form needed by Sturm comparison.**  For a Jacobi field `y` along
a unit-speed chart geodesic whose squared norm `⟨y,y⟩` is positive on `(0,T)`, the function
`h = √⟨y,y⟩` has first and second derivatives `g1`, `g2` satisfying `0 ≤ g2 + 4 h`, i.e. the
hypothesis of `Commons.Analysis.ODE.sturm_eqOn_zero_of_second_deriv_add_nonneg` with `λ = 4`. -/
theorem rauch_sturm_ready
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) (htor : cov.torsion = 0)
    {x₀ : M} {v : E} {u w y : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    (hunit : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    {a b : ℝ} (ha : -2 < a) (hb : b < 2)
    (hy : ∀ t ∈ Ioo a b, HasDerivAt y (deriv y t) t)
    (hDy : ∀ t ∈ Ioo a b, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Ioo a b, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hpos : ∀ t ∈ Ioo a b,
      0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) :
    ∃ (g1 g2 : ℝ → ℝ),
      (∀ t ∈ Ioo a b, HasDerivAt (fun s => Real.sqrt (chartGram (I := I) x₀
          ((extChartAt I x₀).symm (u s)) (y s) (y s))) (g1 t) t) ∧
      (∀ t ∈ Ioo a b, HasDerivAt g1 (g2 t) t) ∧
      (∀ t ∈ Ioo a b, 0 ≤ g2 t + 4 * Real.sqrt (chartGram (I := I) x₀
          ((extChartAt I x₀).symm (u t)) (y t) (y t))) :=
  by
  simpa only [one_pow, mul_one] using
    rauch_sturm_ready_speed (cov := cov) (c := 1) hcov hmet hpinch htor h
      (fun t ht => by rw [hunit t ht, one_pow]) ha hb hy hDy hjac hpos

/-- The chart metric is positive definite: `⟨a,a⟩ = 0` iff `a = 0`. -/
lemma chartGram_self_eq_zero_iff {x₀ p : M} (hp : p ∈ (chartAt H x₀).source) (a : E) :
    chartGram (I := I) x₀ p a a = 0 ↔ a = 0 := by
  rw [chartGram_apply, real_inner_self_eq_norm_sq]
  constructor
  · intro h
    have h2 : ‖frameVector (I := I) x₀ p a‖ = 0 := by
      have h3 := sq_eq_zero_iff.mp h
      simpa using h3
    exact (frameVector_eq_zero_iff (I := I) hp a).mp (norm_eq_zero.mp h2)
  · intro h
    rw [h, frameVector_zero', norm_zero]
    norm_num

/-- **Rauch's theorem, no-interior-zero case.**  If a Jacobi field `y` along a unit-speed chart
geodesic vanishes at `0` and at `T < π/2` and is nowhere zero in between, then it vanishes
everywhere on `[0,T]`. -/
theorem eqOn_zero_of_jacobi_of_pos
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) (htor : cov.torsion = 0)
    {x₀ : M} {v : E} {u w y : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    (hunit : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    {T : ℝ} (hT1 : 0 < T) (hT2 : T < Real.pi / 2)
    (hy : ∀ t ∈ Ioo 0 T, HasDerivAt y (deriv y t) t)
    (hDy : ∀ t ∈ Ioo 0 T, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Ioo 0 T, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hcont : ContinuousOn (fun t => Real.sqrt (chartGram (I := I) x₀
      ((extChartAt I x₀).symm (u t)) (y t) (y t))) (Icc 0 T))
    (hy0 : y 0 = 0)
    (hpos : ∀ t ∈ Ioo 0 T, 0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))
    (hT0 : y T = 0) :
    ∀ t ∈ Icc 0 T, y t = 0 := by
  obtain ⟨g1, g2, hg1, hg2, hineq⟩ := rauch_sturm_ready (cov := cov) hcov hmet hpinch htor h hunit
    (by norm_num : (-2 : ℝ) < 0) (by linarith [hT2, Real.pi_lt_four]) hy hDy hjac hpos
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hzero := sturm_eqOn_zero_of_second_deriv_add_nonneg_endpoint (lam := 4)
    (by norm_num) hT1 (by rw [hsqrt4]; exact hT2) hcont
    (by simp only [hy0, chartGram_apply, frameVector_zero', inner_zero_left, Real.sqrt_zero])
    (fun t _ => Real.sqrt_nonneg _) hg1 hg2 hineq
    (by simp only [hT0, chartGram_apply, frameVector_zero', inner_zero_left, Real.sqrt_zero])
  intro t ht
  have h1 : Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) = 0 :=
    hzero ht
  have hGnn : 0 ≤ chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) := by
    rw [chartGram_apply, real_inner_self_eq_norm_sq]
    positivity
  have h2 : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) = 0 :=
    le_antisymm (Real.sqrt_eq_zero'.mp h1) hGnn
  have ht2 : t ∈ Ioo (-2 : ℝ) 2 :=
    ⟨by linarith [ht.1], by linarith [ht.2, hT2, Real.pi_lt_four]⟩
  exact (chartGram_self_eq_zero_iff (mem_source_chartCurve (I := I) (h.2.2.1 t ht2)) (y t)).mp h2

/-- **Rauch's theorem, no-interior-zero case, on an arbitrary interval.**  If a Jacobi field `y`
along a unit-speed chart geodesic vanishes at `a` and at `b` with `b - a < π/2` and is nowhere zero
in between, then it vanishes on `[a,b]`. -/
theorem eqOn_zero_Icc_of_pos
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) (htor : cov.torsion = 0)
    {x₀ : M} {v : E} {u w y : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    (hunit : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    {a b : ℝ} (ha2 : -2 < a) (hb2 : b < 2) (hab : a < b) (habπ : b - a < Real.pi / 2)
    (hy : ∀ t ∈ Ioo a b, HasDerivAt y (deriv y t) t)
    (hDy : ∀ t ∈ Ioo a b, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Ioo a b, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hcont : ContinuousOn (fun t => Real.sqrt (chartGram (I := I) x₀
      ((extChartAt I x₀).symm (u t)) (y t) (y t))) (Icc a b))
    (hya : y a = 0)
    (hpos : ∀ t ∈ Ioo a b, 0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))
    (hyb : y b = 0) :
    ∀ t ∈ Icc a b, y t = 0 := by
  obtain ⟨g1, g2, hg1, hg2, hineq⟩ := rauch_sturm_ready (cov := cov) hcov hmet hpinch htor h hunit
    ha2 hb2 hy hDy hjac hpos
  have hsqrt4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hsqrt_a : Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u a)) (y a) (y a)) = 0 := by
    rw [hya, chartGram_apply, frameVector_zero', inner_zero_left, Real.sqrt_zero]
  have hsqrt_b : Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u b)) (y b) (y b)) = 0 := by
    rw [hyb, chartGram_apply, frameVector_zero', inner_zero_left, Real.sqrt_zero]
  have hzero := sturm_eqOn_zero_Icc (lam := 4) (by norm_num) hab (by rw [hsqrt4]; exact habπ)
    hcont hsqrt_a (fun t _ => Real.sqrt_nonneg _) hg1 hg2 hineq hsqrt_b
  intro t ht
  have hta : a ≤ t := ht.1
  have htb : t ≤ b := ht.2
  have h1 : Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) = 0 :=
    hzero ht
  have hGnn : 0 ≤ chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) := by
    rw [chartGram_apply, real_inner_self_eq_norm_sq]
    positivity
  have h2 : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) = 0 :=
    le_antisymm (Real.sqrt_eq_zero'.mp h1) hGnn
  have ht2 : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith, by linarith⟩
  exact (chartGram_self_eq_zero_iff (mem_source_chartCurve (I := I) (h.2.2.1 t ht2)) (y t)).mp h2

/-- **Rauch's theorem (chart-local form).**  A Jacobi field `y` along a unit-speed chart geodesic
with `y 0 = 0` and `y t₁ = 0` for some `t₁ ∈ (0, π/2)` vanishes on all of `[0, t₁]`; equivalently,
there are no conjugate points of the geodesic before `π/2 = π/√K_max`. -/
theorem eqOn_zero_of_jacobi
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) (htor : cov.torsion = 0)
    {x₀ : M} {v : E} {u w y : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    (hunit : ∀ t ∈ Ioo (-2 : ℝ) 2,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    {t₁ : ℝ} (ht₁pos : 0 < t₁) (ht₁π : t₁ < Real.pi / 2)
    (hy : ∀ t ∈ Ioo 0 t₁, HasDerivAt y (deriv y t) t)
    (hDy : ∀ t ∈ Ioo 0 t₁, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Ioo 0 t₁, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hcont : ContinuousOn (fun t => Real.sqrt (chartGram (I := I) x₀
      ((extChartAt I x₀).symm (u t)) (y t) (y t))) (Icc 0 t₁))
    (hy0 : y 0 = 0) (ht₁0 : y t₁ = 0) :
    ∀ t ∈ Icc 0 t₁, y t = 0 := by
  intro t ht
  by_contra hyt
  have ht0 : 0 < t := by
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · exact absurd (h0 ▸ hy0) hyt
    · exact h0
  have htt₁ : t < t₁ := by
    rcases eq_or_lt_of_le ht.2 with h0 | h0
    · exact absurd (h0 ▸ ht₁0) hyt
    · exact h0
  set A : Set ℝ := {s | s ∈ Icc (0:ℝ) t₁ ∧ y s = 0 ∧ s < t} with hAdef
  set B : Set ℝ := {s | s ∈ Icc (0:ℝ) t₁ ∧ y s = 0 ∧ t < s} with hBdef
  have hAne : A.Nonempty := ⟨0, by refine ⟨⟨le_refl 0, ht₁pos.le⟩, hy0, ht0⟩⟩
  have hBne : B.Nonempty := ⟨t₁, by refine ⟨⟨ht₁pos.le, le_refl t₁⟩, ht₁0, htt₁⟩⟩
  have hAbdd : BddAbove A := ⟨t, fun s hs => le_of_lt hs.2.2⟩
  have hBbdd : BddBelow B := ⟨t, fun s hs => le_of_lt hs.2.2⟩
  set a : ℝ := sSup A with hadef
  set b : ℝ := sInf B with hbdef
  have ha_le : a ≤ t := csSup_le hAne (fun s hs => le_of_lt hs.2.2)
  have hb_le : t ≤ b := le_csInf hBne (fun s hs => le_of_lt hs.2.2)
  have h0A : (0:ℝ) ∈ A := ⟨⟨le_refl 0, ht₁pos.le⟩, hy0, ht0⟩
  have ha0 : 0 ≤ a := le_csSup hAbdd h0A
  have hb1 : b ≤ t₁ := csInf_le ⟨t, fun s hs => le_of_lt hs.2.2⟩
    (by refine ⟨⟨ht₁pos.le, le_refl t₁⟩, ht₁0, htt₁⟩)
  -- `a` and `b` lie in the zero set
  have ha_mem : y a = 0 := by
    rcases eq_or_lt_of_le ha0 with h0 | h0
    · rw [← h0]; exact hy0
    · have haIoo : a ∈ Ioo (0:ℝ) t₁ := ⟨h0, lt_of_le_of_lt ha_le htt₁⟩
      have hcont_a : ContinuousAt y a := (hy a haIoo).continuousAt
      have hclosure : a ∈ closure A := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨s, hsA, hsa⟩ := exists_lt_of_lt_csSup hAne (show a - ε < a by linarith)
        have hsa' : s ≤ a := le_csSup hAbdd hsA
        exact ⟨s, hsA, by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hsa, hsA.2.2]⟩
      by_contra hne
      have hnbhd : {x : ℝ | y x ≠ 0} ∈ 𝓝 a :=
        hcont_a (isOpen_ne.mem_nhds hne)
      obtain ⟨s, hst, hsA⟩ := mem_closure_iff_nhds.mp hclosure {x : ℝ | y x ≠ 0} hnbhd
      exact hst hsA.2.1
  have hb_mem : y b = 0 := by
    rcases eq_or_lt_of_le hb1 with h0 | h0
    · rw [h0]; exact ht₁0
    · have hbIoo : b ∈ Ioo (0:ℝ) t₁ := ⟨lt_of_lt_of_le ht0 hb_le, h0⟩
      have hcont_b : ContinuousAt y b := (hy b hbIoo).continuousAt
      have hclosure : b ∈ closure B := by
        rw [Metric.mem_closure_iff]
        intro ε hε
        obtain ⟨s, hsB, hbs⟩ := exists_lt_of_csInf_lt hBne (show b < b + ε by linarith)
        have hbs' : b ≤ s := csInf_le hBbdd hsB
        exact ⟨s, hsB, by rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hbs, hsB.2.2]⟩
      by_contra hne
      have hnbhd : {x : ℝ | y x ≠ 0} ∈ 𝓝 b :=
        hcont_b (isOpen_ne.mem_nhds hne)
      obtain ⟨s, hst, hsB⟩ := mem_closure_iff_nhds.mp hclosure {x : ℝ | y x ≠ 0} hnbhd
      exact hst hsB.2.1
  -- between consecutive zeros the field does not vanish
  have ha_lt : a < t := lt_of_le_of_ne ha_le (fun h0 => hyt (h0 ▸ ha_mem))
  have hlt_b : t < b := lt_of_le_of_ne hb_le (Ne.symm (fun h0 => hyt (h0 ▸ hb_mem)))
  have hpos : ∀ s ∈ Ioo a b, 0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
      (y s) (y s) := by
    intro s hs
    have hsne : y s ≠ 0 := by
      intro hsy
      rcases lt_trichotomy s t with hst | hst | hst
      · have hsA : s ∈ A :=
          ⟨⟨le_trans ha0 hs.1.le, (lt_trans hst htt₁).le⟩, hsy, hst⟩
        have := le_csSup hAbdd hsA
        linarith [this, hs.1]
      · exact hyt (hst ▸ hsy)
      · have hsB : s ∈ B := ⟨⟨(lt_trans ht0 hst).le, le_trans hs.2.le hb1⟩, hsy, hst⟩
        have := csInf_le hBbdd hsB
        linarith [this, hs.2]
    have hGnn : 0 ≤ chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s) := by
      rw [chartGram_apply, real_inner_self_eq_norm_sq]
      positivity
    have hp' : (extChartAt I x₀).symm (u s) ∈ (chartAt H x₀).source := by
      have hs2 : s ∈ Ioo (-2 : ℝ) 2 :=
        ⟨by linarith [hs.1, ha0], by linarith [hs.2, hb1, ht₁π, Real.pi_lt_four]⟩
      exact mem_source_chartCurve (I := I) (h.2.2.1 s hs2)
    have hne : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s) ≠ 0 :=
      fun hz => hsne ((chartGram_self_eq_zero_iff hp' (y s)).mp hz)
    exact lt_of_le_of_ne hGnn (fun h0 => hne h0.symm)
  -- apply the no-interior-zero case on `[a,b]`
  have hbπ : b - a < Real.pi / 2 := by linarith
  have hcase1 := eqOn_zero_Icc_of_pos (cov := cov) (hcov := hcov) (hmet := hmet)
    (hpinch := hpinch) (htor := htor) (h := h) (hunit := hunit) (a := a) (b := b)
    (by linarith : (-2 : ℝ) < a) (by linarith [hb1, ht₁π, Real.pi_lt_four] : b < 2)
    (ha_lt.trans hlt_b) hbπ
    (fun s hs => hy s ⟨lt_of_le_of_lt ha0 hs.1, lt_of_lt_of_le hs.2 hb1⟩)
    (fun s hs => hDy s ⟨lt_of_le_of_lt ha0 hs.1, lt_of_lt_of_le hs.2 hb1⟩)
    (fun s hs => hjac s ⟨lt_of_le_of_lt ha0 hs.1, lt_of_lt_of_le hs.2 hb1⟩)
    (hcont.mono (Icc_subset_Icc ha0 hb1)) ha_mem hpos hb_mem
  exact hyt (hcase1 t ⟨ha_lt.le, hlt_b.le⟩)

end

end Submission.ConjPoint
