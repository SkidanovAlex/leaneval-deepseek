import Submission.Rauch
import Submission.ConjPoint

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Rauch's theorem with *local* (germ-level) hypotheses

The chart-local Rauch theorem `Submission.ConjPoint.eqOn_zero_of_jacobi` is stated for a chart
geodesic `(u,w)` given by `Submission.Geodesic.HasChartGeodesic`, i.e. a solution of the chart
geodesic equation on the *whole* interval `Ioo (-2) 2` (this is the normalisation used by the
exponential map).

For the **globalisation** of Rauch's theorem (no conjugate point before `π/2` along *any*
unit-speed geodesic of the manifold, see `Submission/RauchGlobal`) one glues chart pieces, and on
each piece only the *germ* of the geodesic and of the Jacobi field is available.  This file
therefore restates the whole Rauch chain with local hypotheses:

* `hasDerivAt_chartGram_self_of_hasDerivAt`, `hasDerivAt_deriv_chartGram_self_of_hasDerivAt`:
  the first and second derivative of the squared norm of a coordinate field along a chart curve,
  given only `HasDerivAt u (w t) t` and `u t ∈ target`;
* `rauch_inequality_of_hasDerivAt`: the Rauch/Sturm inequality `(√g)'' + 4 √g ≥ 0`;
* `rauch_sturm_ready_of_hasDerivAt`: its Sturm-ready form (first and second derivatives of `√g`).

Every statement has the same shape as its counterpart in `Submission/Rauch` /
`Submission/ConjPoint`, with the hypothesis `HasChartGeodesic cov x₀ v u w` replaced by

* `∀ t ∈ Ioo a b, u t ∈ (extChartAt I x₀).target` (the curve is in the chart), and
* `∀ t ∈ Ioo a b, HasDerivAt u (w t) t` (the derivative of the coordinate curve is `w`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
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
open Submission.ChartBounds

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.RauchLocal

noncomputable section

variable [I.Boundaryless]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-! ## 1. Derivatives of the squared norm along a chart curve -/

/-- **First derivative of the squared norm**, with local hypotheses. -/
theorem hasDerivAt_chartGram_self_of_hasDerivAt
    (hmet : IsMetricCompatible cov) {x₀ : M} {u w y : ℝ → E} {t : ℝ}
    (hu : HasDerivAt u (w t) t) (hutgt : u t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target)
    (hy : HasDerivAt y (deriv y t) t) :
    HasDerivAt (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s))
      (2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (chartCovDeriv cov x₀ u w y t) (y t)) t := by
  have hprod := hasDerivAt_chartGram_chartCovDeriv (cov := cov) hmet x₀ hu hutgt hstay hy hy
  have hval : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (chartCovDeriv cov x₀ u w y t) (y t)
      + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t)
        (chartCovDeriv cov x₀ u w y t)
      = 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (chartCovDeriv cov x₀ u w y t) (y t) := by
    rw [chartGram_comm (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t)
      (chartCovDeriv cov x₀ u w y t)]
    ring
  rw [hval] at hprod
  exact hprod

/-- **Second derivative of the squared norm**, with local hypotheses. -/
theorem hasDerivAt_deriv_chartGram_self_of_hasDerivAt
    (hmet : IsMetricCompatible cov) {x₀ : M} {u w y : ℝ → E} {t : ℝ}
    (hu : HasDerivAt u (w t) t) (hutgt : u t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target)
    (hy : HasDerivAt y (deriv y t) t)
    (hDy : HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t) :
    HasDerivAt (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (chartCovDeriv cov x₀ u w y s) (y s))
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t) (y t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (chartCovDeriv cov x₀ u w y t) (chartCovDeriv cov x₀ u w y t)) t := by
  exact hasDerivAt_chartGram_chartCovDeriv (cov := cov) hmet x₀ hu hutgt hstay hDy hy

/-! ## 2. The Rauch inequality with local hypotheses -/

/-- **The Rauch (Sturm) inequality**, with local hypotheses. -/
theorem rauch_inequality_of_hasDerivAt
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) (htor : cov.torsion = 0)
    {x₀ : M} {u w y : ℝ → E} {a b : ℝ}
    (hutgt : ∀ t ∈ Ioo a b, u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Ioo a b, HasDerivAt u (w t) t)
    (hunit : ∀ t ∈ Ioo a b,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
    (hy : ∀ t ∈ Ioo a b, HasDerivAt y (deriv y t) t)
    (hDy : ∀ t ∈ Ioo a b, HasDerivAt (chartCovDeriv cov x₀ u w y)
      (deriv (chartCovDeriv cov x₀ u w y) t) t)
    (hjac : ∀ t ∈ Ioo a b, chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      + chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) = 0)
    (hpos : ∀ t ∈ Ioo a b,
      0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) :
    ∀ t ∈ Ioo a b,
      (deriv (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s)) t) ^ 2
          / (2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))
        - 8 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)
        ≤ deriv (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
            (y r) (y r)) s) t := by
  intro t ht
  have hp : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    mem_source_chartCurve (I := I) (hutgt t ht)
  have hnb : Ioo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
  have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
    ((hu t ht).continuousAt).preimage_mem_nhds
      ((isOpen_extChartAt_target x₀).mem_nhds (hutgt t ht))
  have hun : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1 := hunit t ht
  have hgt : 0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) := hpos t ht
  -- the first derivative of the squared norm
  have hg1 := hasDerivAt_chartGram_self_of_hasDerivAt (cov := cov) hmet (hu t ht) (hutgt t ht)
    hstay (hy t ht)
  have hderivg :
      deriv (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s)) t
        = 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
            (chartCovDeriv cov x₀ u w y t) (y t) := hg1.deriv
  -- `deriv` of the squared norm agrees near `t` with the explicit expression
  have hcongr : (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
        (y r) (y r)) s) =ᶠ[𝓝 t]
      (fun s => 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (chartCovDeriv cov x₀ u w y s) (y s)) := by
    filter_upwards [hnb] with s hs
    have hstay' : ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target :=
      ((hu s hs).continuousAt).preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hutgt s hs))
    exact (hasDerivAt_chartGram_self_of_hasDerivAt (cov := cov) hmet (hu s hs) (hutgt s hs)
      hstay' (hy s hs)).deriv
  -- the second derivative
  have hg2 := hasDerivAt_deriv_chartGram_self_of_hasDerivAt (cov := cov) hmet (hu t ht)
    (hutgt t ht) hstay (hy t ht) (hDy t ht)
  have hderiv2 :
      deriv (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          (y r) (y r)) s) t
        = 2 * (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
              (chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t) (y t)
            + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
              (chartCovDeriv cov x₀ u w y t) (chartCovDeriv cov x₀ u w y t)) := by
    rw [Filter.EventuallyEq.deriv_eq hcongr]
    have h2 := hg2.const_mul (2 : ℝ)
    exact h2.deriv
  -- the Jacobi equation identifies the second covariant derivative
  have hD : chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t
      = -chartCurv cov x₀ ((extChartAt I x₀).symm (u t)) (y t) (w t) :=
    eq_neg_of_add_eq_zero_left (hjac t ht)
  -- the curvature bound
  have hcurv := chartGram_chartCurv_le hcov hmet hpinch htor x₀ hp (y t) (w t)
  rw [hun, mul_one] at hcurv
  -- Cauchy–Schwarz
  have hcs := chartGram_sq_le (I := I) x₀ ((extChartAt I x₀).symm (u t))
    (chartCovDeriv cov x₀ u w y t) (y t)
  rw [hderivg, hderiv2, hD, chartGram_neg_fst]
  rw [sub_le_iff_le_add]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * chartGram (I := I) x₀
    ((extChartAt I x₀).symm (u t)) (y t) (y t))]
  nlinarith [hcurv, hcs, hgt]


/-! ## 3. The square root of the squared norm and the Sturm-ready form -/

/-- **The derivative of `√⟨y,y⟩`**, with local hypotheses. -/
theorem hasDerivAt_sqrt_chartGram_self_of_hasDerivAt
    (hmet : IsMetricCompatible cov) {x₀ : M} {u w y : ℝ → E} {t : ℝ}
    (hu : HasDerivAt u (w t) t) (hutgt : u t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target)
    (hy : HasDerivAt y (deriv y t) t)
    (hpos : 0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)) :
    HasDerivAt (fun s => Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (y s) (y s)))
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (chartCovDeriv cov x₀ u w y t) (y t)
        / Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))) t := by
  have hg := hasDerivAt_chartGram_self_of_hasDerivAt (cov := cov) hmet hu hutgt hstay hy
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

/-- **The second derivative of `√⟨y,y⟩`**, with local hypotheses. -/
theorem hasDerivAt_deriv_sqrt_chartGram_self_of_hasDerivAt
    (hmet : IsMetricCompatible cov) {x₀ : M} {u w y : ℝ → E} {t : ℝ}
    (hu : HasDerivAt u (w t) t) (hutgt : u t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target)
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
  have hsqrt := hasDerivAt_sqrt_chartGram_self_of_hasDerivAt (cov := cov) hmet hu hutgt hstay hy hpos
  exact hc.div hsqrt (ne_of_gt (Real.sqrt_pos.mpr hpos))

/-- **The Rauch inequality in the Sturm-ready form**, with local hypotheses. -/
theorem rauch_sturm_ready_of_hasDerivAt
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) (htor : cov.torsion = 0)
    {x₀ : M} {u w y : ℝ → E} {a b : ℝ}
    (hutgt : ∀ t ∈ Ioo a b, u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Ioo a b, HasDerivAt u (w t) t)
    (hunit : ∀ t ∈ Ioo a b,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = 1)
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
          ((extChartAt I x₀).symm (u t)) (y t) (y t))) := by
  classical
  haveI : ContMDiffCovariantDerivative cov ∞ := hcov
  set H : ℝ → ℝ := fun s => Real.sqrt (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
    (y s) (y s)) with hHdef
  set c : ℝ → ℝ := fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
    (chartCovDeriv cov x₀ u w y s) (y s) with hcdef
  set Kloc : ℝ → ℝ := fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
      (chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) s) (y s)
    + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
      (chartCovDeriv cov x₀ u w y s) (chartCovDeriv cov x₀ u w y s) with hKdef
  have hHderiv : ∀ t ∈ Ioo a b, HasDerivAt H (c t / H t) t := by
    intro t ht
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      ((hu t ht).continuousAt).preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hutgt t ht))
    have hsqrt := hasDerivAt_sqrt_chartGram_self_of_hasDerivAt (cov := cov) hmet (hu t ht)
      (hutgt t ht) hstay (hy t ht) (hpos t ht)
    simpa only [H, c] using hsqrt
  have hcderiv : ∀ t ∈ Ioo a b, HasDerivAt c (Kloc t) t := by
    intro t ht
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      ((hu t ht).continuousAt).preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hutgt t ht))
    simpa only [c, Kloc] using hasDerivAt_deriv_chartGram_self_of_hasDerivAt (cov := cov) hmet
      (hu t ht) (hutgt t ht) hstay (hy t ht) (hDy t ht)
  refine ⟨fun t => c t / H t, fun t => Kloc t / H t - (c t) ^ 2 / (H t) ^ 3,
    hHderiv, ?_, ?_⟩
  · -- the second derivative of `H`
    intro t ht
    have hHpos : 0 < H t := Real.sqrt_pos.mpr (hpos t ht)
    have hHne : H t ≠ 0 := ne_of_gt hHpos
    have hdiv := (hcderiv t ht).div (hHderiv t ht) hHne
    refine hdiv.congr_deriv ?_
    have hid : (Kloc t * H t - c t * (c t / H t)) / H t ^ 2
        = Kloc t / H t - (c t) ^ 2 / (H t) ^ 3 := by
      field_simp
    simp only [hid]
  · -- the inequality `0 ≤ g2 t + 4 √⟨y,y⟩`
    intro t ht
    have hHpos : 0 < H t := Real.sqrt_pos.mpr (hpos t ht)
    have hH2 : H t ^ 2 = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) :=
      Real.sq_sqrt (le_of_lt (hpos t ht))
    have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
      ((hu t ht).continuousAt).preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds (hutgt t ht))
    -- Rauch's inequality
    have hrauch := (rauch_inequality_of_hasDerivAt (cov := cov) hcov hmet hpinch htor hutgt hu
      hunit hy hDy hjac hpos) t ht
    have hderivg : deriv (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (y s) (y s)) t = 2 * c t := by
      have hg1 := hasDerivAt_chartGram_self_of_hasDerivAt (cov := cov) hmet (hu t ht)
        (hutgt t ht) hstay (hy t ht)
      rw [hg1.deriv]
    have hcongr : (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          (y r) (y r)) s) =ᶠ[𝓝 t] (fun s => 2 * c s) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      have hstay' : ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target :=
        ((hu s hs).continuousAt).preimage_mem_nhds
          ((isOpen_extChartAt_target x₀).mem_nhds (hutgt s hs))
      rw [(hasDerivAt_chartGram_self_of_hasDerivAt (cov := cov) hmet (hu s hs) (hutgt s hs)
        hstay' (hy s hs)).deriv]
    have hderiv2 : deriv (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
          (y r) (y r)) s) t = 2 * Kloc t := by
      rw [Filter.EventuallyEq.deriv_eq hcongr]
      have h2 := (hasDerivAt_deriv_chartGram_self_of_hasDerivAt (cov := cov) hmet (hu t ht)
        (hutgt t ht) hstay (hy t ht) (hDy t ht)).const_mul (2 : ℝ)
      rw [h2.deriv]
    rw [hderivg, hderiv2, ← hH2] at hrauch
    -- `hrauch : (2 c)² / (2 H²) - 8 H² ≤ 2 K`
    have hrauch' : 2 * ((c t) ^ 2 / H t ^ 2) - 8 * H t ^ 2 ≤ 2 * Kloc t := by
      convert hrauch using 2
      field_simp
    have hK : (c t) ^ 2 / H t ^ 2 - 4 * H t ^ 2 ≤ Kloc t := by linarith
    have hH3pos : 0 < H t ^ 3 := by positivity
    have hkey : (Kloc t / H t - (c t) ^ 2 / (H t) ^ 3 + 4 * H t) * H t ^ 3
        = Kloc t * H t ^ 2 - (c t) ^ 2 + 4 * H t ^ 4 := by
      field_simp
    have hpoly : 0 ≤ Kloc t * H t ^ 2 - (c t) ^ 2 + 4 * H t ^ 4 := by
      have hmul : ((c t) ^ 2 / H t ^ 2 - 4 * H t ^ 2) * H t ^ 2 ≤ Kloc t * H t ^ 2 :=
        mul_le_mul_of_nonneg_right hK (by positivity)
      have heq : ((c t) ^ 2 / H t ^ 2 - 4 * H t ^ 2) * H t ^ 2 = (c t) ^ 2 - 4 * H t ^ 4 := by
        field_simp
      rw [heq] at hmul
      linarith
    have hprod : 0 ≤ (Kloc t / H t - (c t) ^ 2 / (H t) ^ 3 + 4 * H t) * H t ^ 3 := by
      rw [hkey]
      exact hpoly
    have hfin : 0 ≤ Kloc t / H t - (c t) ^ 2 / (H t) ^ 3 + 4 * H t :=
      nonneg_of_mul_nonneg_right (by rw [mul_comm]; exact hprod) hH3pos
    simpa only [H] using hfin

end

end Submission.RauchLocal
