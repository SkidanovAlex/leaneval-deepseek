import Submission.Jacobi
import Submission.ChartBounds
import Submission.Commons.LinearAlgebra.exists_ne_zero_orthogonal_of_finrank_two_le

/-!
# A parallel unit field orthogonal to the velocity of a chart geodesic

The Bonnet–Myers comparison argument needs, along a chart geodesic, a field `Y` with

* `Y` parallel (`D Y = 0`), so that `∇_tY = 0`;
* `|Y| = 1` and `⟪Y, γ'⟫ = 0` (so that the test field `sin(π t/L) · Y` has `|∇_t(sin · Y)| = |π/L · cos|`
  and the index form estimate applies).

This file produces such a field from the existence of a nonzero vector orthogonal to the velocity in
the chart metric (`Commons.LinearAlgebra.exists_ne_zero_orthogonal_of_finrank_two_le`, which needs
`2 ≤ finrank ℝ E`) and from parallel transport preserving the metric
(`Jacobi.chartGram_parallel_const`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic
open Submission.Jacobi
open Submission.ChartConnection
open Submission.ChartBounds

namespace Submission.Jacobi

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

noncomputable section

/-- **A parallel field of unit length orthogonal to the velocity of a chart geodesic.**  If `E` has
dimension at least `2` and the chart geodesic (`h : HasChartGeodesic cov x₀ v u w`) is unit speed at
`t = 0`, there is a field `Y` along it which is parallel, of chart length `1` and orthogonal to the
velocity `w`. -/
theorem exists_parallel_unit_orthogonal [I.Boundaryless]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {x₀ : M} {v : E} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w)
    (hwunit : chartGram (I := I) x₀ x₀ (w 0) (w 0) = 1)
    {a b : ℝ} (hab : a < b) (habt : Icc a b ⊆ Ioo (-2 : ℝ) 2) (h0 : (0 : ℝ) ∈ Icc a b) :
    ∃ Y : ℝ → E,
      (∀ t ∈ Icc a b, HasDerivAt Y (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (Y t)) t) ∧
      (∀ t ∈ Icc a b, chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t) (Y t) = 1) ∧
      (∀ t ∈ Icc a b, chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w t) = 0) := by
  classical
  set B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (chartGram (I := I) x₀ x₀)
      (fun a₁ a₂ b => chartGram_add_fst x₀ x₀ a₁ a₂ b)
      (fun c a b => chartGram_smul_fst x₀ x₀ c a b)
      (fun a b₁ b₂ => chartGram_add_snd x₀ x₀ a b₁ b₂)
      (fun c a b => chartGram_smul_snd x₀ x₀ c a b) with hB
  have hBeq : ∀ y z : E, B y z = chartGram (I := I) x₀ x₀ y z := fun y z => rfl
  have hBpos : ∀ y : E, 0 ≤ B y y := by
    intro y
    rw [hBeq]
    rcases eq_or_ne y 0 with h0 | h0
    · rw [h0]; simp
    · exact (chartGram_self_pos (I := I) (x₀ := x₀) (p := x₀) (mem_chart_source H x₀) h0).le
  have hBdef : ∀ y : E, B y y = 0 → y = 0 := by
    intro y hy
    by_contra hne
    have := chartGram_self_pos (I := I) (x₀ := x₀) (p := x₀) (mem_chart_source H x₀) hne
    rw [hBeq] at hy
    rw [hy] at this
    exact lt_irrefl _ this
  have hwunit' : B (w 0) (w 0) = 1 := by rw [hBeq]; exact hwunit
  obtain ⟨Y₀, hY₀norm, hY₀orth⟩ :=
    Commons.LinearAlgebra.exists_ne_zero_orthogonal_of_finrank_two_le hdim B hBpos hBdef (w 0) hwunit'
  obtain ⟨Y, hY0, hYODE, -⟩ :=
    exists_parallel_field_Icc (cov := cov) htor (h := h) hab habt h0 Y₀
  have hbase0 : (extChartAt I x₀).symm (u 0) = x₀ := by
    rw [h.1]
    exact (extChartAt I x₀).left_inv (by rw [extChartAt_source]; exact mem_chart_source H x₀)
  refine ⟨Y, hYODE, ?_, ?_⟩
  · intro t ht
    have hc := chartGram_parallel_self_const (cov := cov) hmet (h := h) hab.le habt h0 hYODE t ht
    rw [hc, hY0, hbase0]
    rw [hBeq] at hY₀norm
    exact hY₀norm
  · have hwODE : ∀ t ∈ Icc a b, HasDerivAt w (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (w t)) t :=
      fun t ht => hasDerivAt_velocity_of_hasChartGeodesic (cov := cov) h t (habt ht)
    intro t ht
    have hc := chartGram_parallel_const (cov := cov) hmet (h := h) hab.le habt h0 hYODE hwODE t ht
    rw [hc, hY0, hbase0]
    rw [hBeq] at hY₀orth
    exact hY₀orth

end

end Submission.Jacobi
