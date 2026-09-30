import Submission.Work.RiemLib.Pinch
import Submission.Work.RiemLib.ChartCurv
import Submission.Work.RiemLib.CurvatureVec
import Submission.Work.RiemLib.Jacobi

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Rauch comparison: the curvature bounds, the chart Jacobi equation and the norm identities

This file opens the *comparison theory* chapter.  It contains the tools that every route to the
sphere theorem needs and that Mathlib does not have:

* the **general (not necessarily orthonormal) pinching bounds** for the curvature form,
  `curvFormVec cov x u v ≤ 4 ‖u‖²‖v‖²` (and its lower counterpart), obtained from
  `quarterPinched_curvForm_bounds` by the basis-independence of the sectional curvature;
* `chartCurv`: the coordinate vector of `R(σ_X, σ_Y)σ_Y` in a chart, together with its
  identification with `curvVec` (`curvVec_eq_chart`);
* the **first and second derivatives of the squared norm** `g(t) = ⟨y(t), y(t)⟩` of a coordinate
  field along a chart geodesic,
  `g' = 2⟨Dy, y⟩`, `g'' = 2‖Dy‖² + 2⟨D(Dy), y⟩`,
  where `D = chartCovDeriv` is the covariant derivative along the geodesic;
* the **Rauch/Sturm inequality** `(‖y‖)'' + 4 ‖y‖ ≥ 0` for a Jacobi field `y` (i.e. a solution of
  `D(Dy) + R(y, w)w = 0`) along a unit-speed chart geodesic, in the project's normalisation
  `K ≤ 4`.  Combined with the (pure analysis) Sturm comparison lemma
  `Commons.Analysis.ODE.sturm_eqOn_zero_of_second_deriv_add_nonneg` this yields **Rauch's
  theorem**: a Jacobi field along a unit-speed geodesic with `y 0 = 0` does not vanish again
  before `π/2 = π/√K_max`.

## Conventions

Along the chart geodesic `γ t = (extChartAt I x₀).symm (u t)` with velocity `w` (so `u' = w`),
a coordinate field `y` represents the tangent field `t ↦ frameVector x₀ (γ t) (y t)` and
`D y = y' + Γ(y)(w)` is its covariant derivative (`Submission.Jacobi.chartCovDeriv`).  The
curvature term in the Jacobi equation is `chartCurv cov x₀ (γ t) (y t) (w t)`, the coordinate vector
of `R(Y, γ')γ'`.
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

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

namespace Submission.Rauch

noncomputable section

variable [I.Boundaryless]

/-! ## 1. The pinching bounds for the curvature form on arbitrary vectors -/

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- The curvature form is the inner product of `R(u,v)v` with `u`. -/
lemma curvFormVec_eq_inner_curvVec
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u v : TangentSpace I x) :
    curvFormVec cov x u v = inner ℝ (curvVec cov x u v v) u :=
  (inner_curvVec_self cov hcov x u v).symm

/-- `curvVec` is homogeneous of degree two in its second argument (together with the third). -/
lemma curvVec_smul_middle_last
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (c : ℝ) (u v : TangentSpace I x) :
    curvVec cov x u (c • v) (c • v) = c ^ 2 • curvVec cov x u v v := by
  rw [curvVec_smul_middle cov hcov x c u v (c • v), curvVec_smul_right cov hcov x c u v v,
    smul_smul]
  ring_nf

/-- The curvature form is homogeneous of degree two in its second argument. -/
lemma curvFormVec_smul_right
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (c : ℝ) (u v : TangentSpace I x) :
    curvFormVec cov x u (c • v) = c ^ 2 * curvFormVec cov x u v := by
  have h1 := curvVec_smul_middle_last hcov x c u v
  calc curvFormVec cov x u (c • v)
      = inner ℝ (curvVec cov x u (c • v) (c • v)) u :=
        (inner_curvVec_self cov hcov x u (c • v)).symm
    _ = inner ℝ (c ^ 2 • curvVec cov x u v v) u := by rw [h1]
    _ = c ^ 2 * inner ℝ (curvVec cov x u v v) u := real_inner_smul_left _ _ _
    _ = c ^ 2 * curvFormVec cov x u v := by rw [inner_curvVec_self cov hcov x u v]

/-- The curvature form vanishes on a degenerate pair. -/
lemma curvFormVec_self
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u : TangentSpace I x) :
    curvFormVec cov x u u = 0 := by
  have h := curvVec_antisymm cov hcov x u u u
  have h3 : (2 : ℝ) • curvVec cov x u u u = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    abel
  have hz : curvVec cov x u u u = 0 := by
    rcases smul_eq_zero.mp h3 with h4 | h4
    · norm_num at h4
    · exact h4
  rw [curvFormVec_eq_inner_curvVec hcov x u u, hz, inner_zero_left]

/-- The curvature form vanishes when the second argument is zero. -/
lemma curvFormVec_zero_right
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (u : TangentSpace I x) :
    curvFormVec cov x u 0 = 0 := by
  have := curvFormVec_smul_right hcov x (0 : ℝ) u u
  simpa using this

/-- The curvature form is homogeneous of degree two in its first argument. -/
lemma curvFormVec_smul_left
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (c : ℝ) (u v : TangentSpace I x) :
    curvFormVec cov x (c • u) v = c ^ 2 * curvFormVec cov x u v := by
  have h1 : curvVec cov x (c • u) v v = c • curvVec cov x u v v :=
    curvVec_smul_left cov hcov x c u v v
  calc curvFormVec cov x (c • u) v
      = inner ℝ (curvVec cov x (c • u) v v) (c • u) :=
        (inner_curvVec_self cov hcov x (c • u) v).symm
    _ = inner ℝ (c • curvVec cov x u v v) (c • u) := by rw [h1]
    _ = c * inner ℝ (curvVec cov x u v v) (c • u) := real_inner_smul_left _ _ _
    _ = c * (c * inner ℝ (curvVec cov x u v v) u) := by rw [real_inner_smul_right]
    _ = c ^ 2 * curvFormVec cov x u v := by
        rw [inner_curvVec_self cov hcov x u v]; ring

/-- The curvature form vanishes when the first argument is zero. -/
lemma curvFormVec_zero_left
    (hcov : ContMDiffCovariantDerivative cov ∞) (x : M) (v : TangentSpace I x) :
    curvFormVec cov x 0 v = 0 := by
  have := curvFormVec_smul_left hcov x (0 : ℝ) (0 : TangentSpace I x) v
  simpa using this

/-- The upper pinching bound for unit vectors (not necessarily orthogonal). -/
private lemma curvFormVec_le_four_of_unit
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) (x : M) {u w : TangentSpace I x}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    curvFormVec cov x u w ≤ 4 := by
  rcases eq_or_ne (gramFormVec x u w) 0 with hG | hG
  · -- then `u` and `w` are unit vectors with `‖u‖²‖w‖² = ⟪u,w⟫²`, hence `w = ±u`
    have hsq : (inner ℝ u w) ^ 2 = (1 : ℝ) ^ 2 := by
      have h := hG
      unfold gramFormVec at h
      rw [hu, hw] at h
      norm_num at h
      linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
    · have hdep : ‖w‖ • u = ‖u‖ • w := by
        have h2 : inner ℝ u w = ‖u‖ * ‖w‖ := by rw [hu, hw, mul_one]; exact heq
        exact (inner_eq_norm_mul_iff_real).mp h2
      have hwu : w = u := by
        rw [hw, hu, one_smul, one_smul] at hdep
        exact hdep.symm
      rw [hwu, curvFormVec_self hcov x u]
      norm_num
    · have hdep : ‖w‖ • u = ‖u‖ • (-w) := by
        have h2 : inner ℝ u (-w) = ‖u‖ * ‖(-w)‖ := by
          have hwu : ‖u‖ * ‖(-w)‖ = 1 := by rw [norm_neg, hu, hw, mul_one]
          rw [inner_neg_right, hwu]
          linarith
        simpa using (inner_eq_norm_mul_iff_real).mp h2
      have hwu : -w = u := by
        rw [hw, hu, one_smul, one_smul] at hdep
        exact hdep.symm
      have hw' : w = (-1 : ℝ) • u := by
        rw [neg_smul, one_smul]
        rw [← hwu, neg_neg]
      rw [hw', curvFormVec_smul_right hcov x (-1) u u, curvFormVec_self hcov x u]
      norm_num
  · obtain ⟨U, hU, hUx⟩ :=
      Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
    obtain ⟨W, hW, hWx⟩ :=
      Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) w
    have hb := (quarterPinched_curvForm_bounds cov hcov hmet hpinch hU hW
      (by rwa [hUx, hWx])).2
    rw [← curvFormVec_eq cov hcov hU hW hUx hWx, hUx, hWx] at hb
    have hle : gramFormVec x u w ≤ 1 := by
      unfold gramFormVec
      rw [hu, hw]
      nlinarith [sq_nonneg (inner ℝ u w)]
    linarith

/-- **The general upper pinching bound.**  For *any* pair of tangent vectors,
`⟪R(u,v)v, u⟫ ≤ 4 ‖u‖² ‖v‖²`. -/
theorem curvFormVec_le_four_mul
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) (x : M) (u v : TangentSpace I x) :
    curvFormVec cov x u v ≤ 4 * ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
  rcases eq_or_ne ‖u‖ 0 with hu0 | hu0
  · have huz : u = 0 := norm_eq_zero.mp hu0
    rw [huz, curvFormVec_zero_left hcov x v]
    positivity
  rcases eq_or_ne ‖v‖ 0 with hv0 | hv0
  · have hvz : v = 0 := norm_eq_zero.mp hv0
    rw [hvz, curvFormVec_zero_right hcov x u]
    positivity
  -- scale both vectors to unit length
  have hreg : ‖u‖⁻¹ * ‖v‖⁻¹ ≠ 0 := by
    simp [inv_ne_zero hu0, inv_ne_zero hv0]
  have hbc := curvFormVec_basis_change cov hcov hmet (u := u) (v := v)
    (‖u‖⁻¹) 0 0 (‖v‖⁻¹)
  simp at hbc
  have hu' : ‖(‖u‖⁻¹ : ℝ) • u‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖u‖⁻¹),
      inv_mul_cancel₀ hu0]
  have hv' : ‖(‖v‖⁻¹ : ℝ) • v‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖v‖⁻¹),
      inv_mul_cancel₀ hv0]
  have hle := curvFormVec_le_four_of_unit hcov hmet hpinch x hu' hv'
  have hscale : curvFormVec cov x ((‖u‖⁻¹ : ℝ) • u) ((‖v‖⁻¹ : ℝ) • v)
      = (‖u‖⁻¹ * ‖v‖⁻¹) ^ 2 * curvFormVec cov x u v := hbc
  have hpos : (0:ℝ) < (‖u‖⁻¹ * ‖v‖⁻¹) ^ 2 := by positivity
  have h2 : (‖u‖⁻¹ * ‖v‖⁻¹) ^ 2 * curvFormVec cov x u v ≤ 4 := by rw [← hscale]; exact hle
  have h3 : ((‖u‖⁻¹ * ‖v‖⁻¹) ^ 2)⁻¹ * ((‖u‖⁻¹ * ‖v‖⁻¹) ^ 2 * curvFormVec cov x u v)
      = curvFormVec cov x u v := by
    field_simp
  calc curvFormVec cov x u v
      = ((‖u‖⁻¹ * ‖v‖⁻¹) ^ 2)⁻¹ * ((‖u‖⁻¹ * ‖v‖⁻¹) ^ 2 * curvFormVec cov x u v) := h3.symm
    _ ≤ ((‖u‖⁻¹ * ‖v‖⁻¹) ^ 2)⁻¹ * 4 := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 4 * ‖u‖ ^ 2 * ‖v‖ ^ 2 := by
        field_simp

/-- **The general lower pinching bound.**  For a nondegenerate pair of tangent vectors,
`‖u‖²‖v‖² - ⟪u,v⟫² ≤ ⟪R(u,v)v, u⟫`. -/
theorem gramFormVec_le_curvFormVec
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) (x : M) (u v : TangentSpace I x)
    (hG : gramFormVec x u v ≠ 0) :
    gramFormVec x u v ≤ curvFormVec cov x u v := by
  obtain ⟨U, hU, hUx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) u
  obtain ⟨V, hV, hVx⟩ :=
    Commons.Geometry.Manifold.VectorField.exists_contMDiff_section_apply_eq (I := I) (M := M) v
  have hb := (quarterPinched_curvForm_bounds cov hcov hmet hpinch hU hV (by rwa [hUx, hVx])).1
  rw [← curvFormVec_eq cov hcov hU hV hUx hVx, hUx, hVx] at hb
  exact le_of_lt hb

/-! ## 2. The curvature vector in coordinates and the norm identities -/

/-- The coordinate vector of `R(σ_X, σ_Y)σ_Y` in the chart at `x₀`, i.e. of the curvature term in
the Jacobi equation `D(Dy) + R(y, w)w = 0`. -/
noncomputable def chartCurv (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ p : M) (X Y : E) : E :=
  dB cov x₀ p X Y Y - dB cov x₀ p Y Y X + chrB cov x₀ p (chrB cov x₀ p Y Y) X
    - chrB cov x₀ p (chrB cov x₀ p Y X) Y

/-- `chartCurv` computes the curvature of the frame fields. -/
theorem curvVec_frameVector_eq [ContMDiffCovariantDerivative cov ∞] (htor : cov.torsion = 0)
    (x₀ : M) {p : M} (hp : p ∈ (chartAt H x₀).source) (X Y : E) :
    curvVec cov p (frameVector (I := I) x₀ p X) (frameVector (I := I) x₀ p Y)
        (frameVector (I := I) x₀ p Y)
      = frameVector (I := I) x₀ p (chartCurv cov x₀ p X Y) := by
  have h := curvVec_eq_chart (cov := cov) htor x₀ p Y Y X hp
  simpa only [chartCurv] using h

/-- **The chart Gram form of the curvature term.** -/
theorem chartGram_chartCurv_le
    (hcov : ContMDiffCovariantDerivative cov ∞) (hmet : IsMetricCompatible cov)
    (hpinch : QuarterPinched cov) (htor : cov.torsion = 0) (x₀ : M) {p : M}
    (hp : p ∈ (chartAt H x₀).source) (X Y : E) :
    chartGram (I := I) x₀ p (chartCurv cov x₀ p X Y) X
      ≤ 4 * chartGram (I := I) x₀ p X X * chartGram (I := I) x₀ p Y Y := by
  haveI : ContMDiffCovariantDerivative cov ∞ := hcov
  have h3 : ‖frameVector (I := I) x₀ p X‖ ^ 2 = chartGram (I := I) x₀ p X X := by
    rw [chartGram_apply, real_inner_self_eq_norm_sq]
  have h4 : ‖frameVector (I := I) x₀ p Y‖ ^ 2 = chartGram (I := I) x₀ p Y Y := by
    rw [chartGram_apply, real_inner_self_eq_norm_sq]
  have h2 := curvFormVec_le_four_mul hcov hmet hpinch p (frameVector (I := I) x₀ p X)
    (frameVector (I := I) x₀ p Y)
  rw [h3, h4] at h2
  calc chartGram (I := I) x₀ p (chartCurv cov x₀ p X Y) X
      = inner ℝ (curvVec cov p (frameVector (I := I) x₀ p X) (frameVector (I := I) x₀ p Y)
          (frameVector (I := I) x₀ p Y)) (frameVector (I := I) x₀ p X) := by
        rw [chartGram_apply, curvVec_frameVector_eq (cov := cov) htor x₀ hp X Y]
    _ = curvFormVec cov p (frameVector (I := I) x₀ p X) (frameVector (I := I) x₀ p Y) :=
        inner_curvVec_self cov hcov p _ _
    _ ≤ 4 * chartGram (I := I) x₀ p X X * chartGram (I := I) x₀ p Y Y := h2

/-- **First derivative of the squared norm** of a coordinate field along a chart geodesic. -/
theorem hasDerivAt_chartGram_self
    (hmet : IsMetricCompatible cov) {x₀ : M} {v : E} {u w : ℝ → E}
    (h : HasChartGeodesic cov x₀ v u w) {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) {y : ℝ → E}
    (hy : HasDerivAt y (deriv y t) t) :
    HasDerivAt (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s))
      (2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (chartCovDeriv cov x₀ u w y t) (y t)) t := by
  have hutgt : u t ∈ (extChartAt I x₀).target := h.2.2.1 t ht
  have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
    (h.2.2.2.1 t ht).continuousAt.preimage_mem_nhds ((isOpen_extChartAt_target x₀).mem_nhds hutgt)
  have hprod := hasDerivAt_chartGram_chartCovDeriv (cov := cov) hmet x₀
    (h.2.2.2.1 t ht) hutgt hstay hy hy
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

/-- **Second derivative of the squared norm** of a coordinate field along a chart geodesic. -/
theorem hasDerivAt_deriv_chartGram_self
    (hmet : IsMetricCompatible cov) {x₀ : M} {v : E} {u w : ℝ → E}
    (h : HasChartGeodesic cov x₀ v u w) {t : ℝ} (ht : t ∈ Ioo (-2 : ℝ) 2) {y : ℝ → E}
    (hy : HasDerivAt y (deriv y t) t)
    (hDy : HasDerivAt (chartCovDeriv cov x₀ u w y) (deriv (chartCovDeriv cov x₀ u w y) t) t) :
    HasDerivAt (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s))
        (chartCovDeriv cov x₀ u w y s) (y s))
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (chartCovDeriv cov x₀ u w (chartCovDeriv cov x₀ u w y) t) (y t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (chartCovDeriv cov x₀ u w y t) (chartCovDeriv cov x₀ u w y t)) t := by
  have hutgt : u t ∈ (extChartAt I x₀).target := h.2.2.1 t ht
  have hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target :=
    (h.2.2.2.1 t ht).continuousAt.preimage_mem_nhds ((isOpen_extChartAt_target x₀).mem_nhds hutgt)
  exact hasDerivAt_chartGram_chartCovDeriv (cov := cov) hmet x₀ (h.2.2.2.1 t ht) hutgt hstay hDy hy


/-! ## 3. The Rauch (Sturm) inequality -/

/-- The chart Gram form is additive-negative in its first argument. -/
lemma chartGram_neg_fst (x₀ p : M) (a b : E) :
    chartGram (I := I) x₀ p (-a) b = -chartGram (I := I) x₀ p a b := by
  rw [chartGram_apply, chartGram_apply, ← neg_one_smul ℝ a, frameVector_smul, real_inner_smul_left]
  ring

/-- Cauchy–Schwarz for the chart Gram form. -/
lemma chartGram_sq_le (x₀ p : M) (a b : E) :
    (chartGram (I := I) x₀ p a b) ^ 2
      ≤ chartGram (I := I) x₀ p a a * chartGram (I := I) x₀ p b b := by
  rw [chartGram_apply, chartGram_apply, chartGram_apply]
  have h := abs_real_inner_le_norm (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p b)
  have h2 : Inner.inner ℝ (frameVector (I := I) x₀ p a) (frameVector (I := I) x₀ p b) ^ 2
      ≤ (‖frameVector (I := I) x₀ p a‖ * ‖frameVector (I := I) x₀ p b‖) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have h3 : (‖frameVector (I := I) x₀ p a‖ * ‖frameVector (I := I) x₀ p b‖) ^ 2
      = ‖frameVector (I := I) x₀ p a‖ ^ 2 * ‖frameVector (I := I) x₀ p b‖ ^ 2 := by ring
  rw [h3, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq] at h2
  exact h2

/-- **The Rauch inequality, with a speed parameter.**  Along a chart geodesic `(u,w)` of constant
squared speed `c²`, for a coordinate field `y` satisfying the Jacobi equation
`D(Dy) + R(y,w)w = 0`, the squared norm `g = ⟨y,y⟩` satisfies
`(g')²/(2g) - 8 c² g ≤ g''` (equivalently `(√g)'' + 4 c² √g ≥ 0`), the differential inequality
behind Rauch's comparison theorem in the project's normalisation `K ≤ 4`. -/
theorem rauch_inequality_speed
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
    ∀ t ∈ Ioo a b,
      (deriv (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s)) t) ^ 2
          / (2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))
        - 8 * c ^ 2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)
        ≤ deriv (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
            (y r) (y r)) s) t := by
  intro t ht
  have ht2 : t ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [ht.1, ha], by linarith [ht.2, hb]⟩
  have hp : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
    mem_source_chartCurve (I := I) (h.2.2.1 t ht2)
  have hnb : Ioo a b ∈ 𝓝 t := isOpen_Ioo.mem_nhds ht
  have hun : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t) (w t) = c ^ 2 :=
    hspeed t ht2
  have hgt : 0 < chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t) := hpos t ht
  -- the first derivative of the squared norm
  have hg1 := hasDerivAt_chartGram_self (cov := cov) hmet h ht2 (hy t ht)
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
    have hs2 : s ∈ Ioo (-2 : ℝ) 2 := ⟨by linarith [hs.1, ha], by linarith [hs.2, hb]⟩
    exact (hasDerivAt_chartGram_self (cov := cov) hmet h hs2 (hy s hs)).deriv
  -- the second derivative
  have hg2 := hasDerivAt_deriv_chartGram_self (cov := cov) hmet h ht2 (hy t ht) (hDy t ht)
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
  rw [hun] at hcurv
  -- Cauchy–Schwarz
  have hcs := chartGram_sq_le (I := I) x₀ ((extChartAt I x₀).symm (u t))
    (chartCovDeriv cov x₀ u w y t) (y t)
  rw [hderivg, hderiv2, hD, chartGram_neg_fst]
  rw [sub_le_iff_le_add]
  rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * chartGram (I := I) x₀
    ((extChartAt I x₀).symm (u t)) (y t) (y t))]
  nlinarith [hcurv, hcs, hgt]

/-- **The Rauch inequality.**  Along a unit-speed chart geodesic `(u,w)`, for a coordinate field `y`
satisfying the Jacobi equation `D(Dy) + R(y,w)w = 0`, the squared norm `g = ⟨y,y⟩` satisfies
`(g')²/(2g) - 8 g ≤ g''` (equivalently `(√g)'' + 4 √g ≥ 0`), the differential inequality behind
Rauch's comparison theorem in the project's normalisation `K ≤ 4`. -/
theorem rauch_inequality
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
    ∀ t ∈ Ioo a b,
      (deriv (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y s) (y s)) t) ^ 2
          / (2 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t))
        - 8 * chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)
        ≤ deriv (fun s => deriv (fun r => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
            (y r) (y r)) s) t := by
  simpa using rauch_inequality_speed (cov := cov) (c := 1) hcov hmet hpinch htor h
    (fun t ht => by rw [hunit t ht, one_pow]) ha hb hy hDy hjac hpos

end

end Submission.Rauch
