import Submission.Jacobi
import Submission.JacobiOrth

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The covariant derivative along a chart geodesic on an arbitrary interval

`Submission/Jacobi.lean` develops parallel transport along a `HasChartGeodesic`, i.e. along a
solution of the chart geodesic equation on `Ioo (-2) 2`.  For Bonnet–Myers one needs parallel
transport along a (possibly long) chart geodesic, defined by the chart equation on an arbitrary
interval `Ioo A B`.  This file records the generalisation: the Christoffel symbol and its operator
form are continuous along any solution of the chart equation, parallel fields exist, and parallel
transport preserves the chart metric.

Everything here is literally the same proof as in `Submission/Jacobi.lean` with the interval
`Ioo (-2) 2` replaced by `Ioo A B` and the structure `HasChartGeodesic` replaced by its three
hypotheses (`hstay`, `hu`, `hw`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric MeasureTheory
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Gauss
open Submission.Jacobi
open Submission.ChartBounds

namespace Submission.JacobiGen

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless]

noncomputable section

variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}

/-- **Continuity of the Christoffel symbol along a solution of the chart equation** on an arbitrary
interval (generalises `Jacobi.continuousOn_christoffelEval_entry`). -/
lemma continuousOn_christoffelEval_entry_Ioo [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {A B : ℝ}
    (hstay : ∀ t ∈ Ioo A B, u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Ioo A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Ioo A B, HasDerivAt w (chartGeodesicVectorField cov x₀ (u t, w t)) t)
    (a : E) :
    ContinuousOn (fun t : ℝ => christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (Ioo A B) := by
  have hspray : ∀ t ∈ Ioo A B, ∀ c : E,
      ContinuousAt (chartGeodesicVectorField cov x₀) (u t, c) := by
    intro t ht c
    have hz : (u t, c) ∈ (extChartAt I x₀).target ×ˢ (Set.univ : Set E) :=
      ⟨hstay t ht, Set.mem_univ _⟩
    have hnb : (extChartAt I x₀).target ×ˢ (Set.univ : Set E) ∈ 𝓝 (u t, c) :=
      ((isOpen_extChartAt_target x₀).prod isOpen_univ).mem_nhds hz
    exact (((Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray
      (cov := cov) x₀) (u t, c) hz).contDiffAt hnb).continuousAt
  have hu' : ∀ t ∈ Ioo A B, ContinuousAt u t := fun t ht => (hu t ht).continuousAt
  have hw' : ∀ t ∈ Ioo A B, ContinuousAt w t := fun t ht => (hw t ht).continuousAt
  have key : ∀ t ∈ Ioo A B,
      christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
        = (1/2 : ℝ) • (- chartGeodesicVectorField cov x₀ (u t, a + w t)
            + chartGeodesicVectorField cov x₀ (u t, a)
            + chartGeodesicVectorField cov x₀ (u t, w t)) := by
    intro t ht
    have hp : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (hstay t ht)
    have hpol := christoffelEval_polarize (cov := cov) htor hp a (w t)
    have hstep : christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
        = (1/2 : ℝ) • (christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (a + w t)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (a + w t))
          - christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) a)
          - christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (w t)
            (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) := by
      rw [← hpol]; module
    rw [hstep]
    simp only [chartGeodesicVectorField]
    module
  refine ContinuousOn.congr ?_ (fun t ht => (key t ht))
  refine ContinuousOn.const_smul ?_ _
  refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.neg ?_) ?_) ?_
  · exact fun t ht => (ContinuousAt.comp (f := fun s : ℝ => (u s, a + w s))
      (hspray t ht (a + w t))
      ((hu' t ht).prodMk (continuousAt_const.add (hw' t ht)))).continuousWithinAt
  · exact fun t ht => (ContinuousAt.comp (f := fun s : ℝ => (u s, a))
      (hspray t ht a)
      ((hu' t ht).prodMk continuousAt_const)).continuousWithinAt
  · exact fun t ht => (ContinuousAt.comp (f := fun s : ℝ => (u s, w s))
      (hspray t ht (w t))
      ((hu' t ht).prodMk (hw' t ht))).continuousWithinAt

/-- **Continuity of the Christoffel operator along a solution of the chart equation** on an
arbitrary interval. -/
lemma continuousOn_christoffelLM_along_Ioo [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {A B : ℝ}
    (hstay : ∀ t ∈ Ioo A B, u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Ioo A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Ioo A B, HasDerivAt w (chartGeodesicVectorField cov x₀ (u t, w t)) t) :
    ContinuousOn (fun t : ℝ => christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (Ioo A B) := by
  have hsum : ∀ t : ℝ, christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
      = ∑ i : Fin (Module.finrank ℝ E),
          (((Module.finBasis ℝ E).coord i).toContinuousLinearMap).smulRight
            (christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) ((Module.finBasis ℝ E) i)
              (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) :=
    fun t => rfl
  simp only [hsum]
  refine continuousOn_finsetSum _ (fun i _ => ?_)
  exact (ContinuousLinearMap.smulRightL ℝ E E
      (((Module.finBasis ℝ E).coord i).toContinuousLinearMap)).continuous.comp_continuousOn
    (continuousOn_christoffelEval_entry_Ioo (cov := cov) htor hstay hu hw ((Module.finBasis ℝ E) i))

/-- **Existence of parallel fields along a solution of the chart equation** on an arbitrary
interval (generalises `Jacobi.exists_parallel_field_Icc`). -/
theorem exists_parallel_field_Ioo [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) {x₀ : M} {u w : ℝ → E} {A B a b t₀ : ℝ} (hab : a < b)
    (habt : Icc a b ⊆ Ioo A B)
    (hstay : ∀ t ∈ Ioo A B, u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Ioo A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Ioo A B, HasDerivAt w (chartGeodesicVectorField cov x₀ (u t, w t)) t)
    (ht₀ : t₀ ∈ Icc a b) (y₀ : E) :
    ∃ y : ℝ → E, y t₀ = y₀ ∧
      (∀ t ∈ Icc a b, HasDerivAt y (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (y t)) t) ∧
      ∀ t ∈ Icc a b, chartCovDeriv cov x₀ u w y t = 0 := by
  have hA : ContinuousOn (fun t : ℝ => -(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)))) (Icc a b) :=
    (continuousOn_christoffelLM_along_Ioo (cov := cov) htor hstay hu hw).neg.mono habt
  obtain ⟨y, hy₀, hyODE, -⟩ :=
    Commons.Analysis.ODE.exists_linearODE_solution_Icc (E := E) hab hA ht₀ y₀
  exact ⟨y, hy₀, hyODE, fun t ht => chartCovDeriv_eq_zero_of_hasDerivAt (hyODE t ht)⟩

/-- **Parallel transport preserves the metric** (general-interval version). -/
theorem chartGram_parallel_const_Ioo
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : IsMetricCompatible cov) {x₀ : M} {u w : ℝ → E} {A B : ℝ}
    (hstay : ∀ t ∈ Ioo A B, u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Ioo A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Ioo A B, HasDerivAt w (chartGeodesicVectorField cov x₀ (u t, w t)) t)
    {a b t₀ : ℝ} (hab : a ≤ b)
    (habt : Icc a b ⊆ Ioo A B) (ht₀ : t₀ ∈ Icc a b)
    {y₁ y₂ : ℝ → E}
    (hy₁ : ∀ t ∈ Icc a b, HasDerivAt y₁ (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (y₁ t)) t)
    (hy₂ : ∀ t ∈ Icc a b, HasDerivAt y₂ (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (y₂ t)) t) :
    ∀ t ∈ Icc a b,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y₁ t) (y₂ t)
        = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (y₁ t₀) (y₂ t₀) := by
  intro t ht
  have hderiv : ∀ s ∈ Icc a b,
      HasDerivAt (fun r : ℝ => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u r))
        (y₁ r) (y₂ r)) 0 s := by
    intro s hs
    have hutgt : u s ∈ (extChartAt I x₀).target := hstay s (habt hs)
    have hstayn : ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target :=
      (hu s (habt hs)).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds hutgt)
    have hprod := hasDerivAt_chartGram_chartCovDeriv (cov := cov) hmet x₀
      (hu s (habt hs)) hutgt hstayn
      (hy₁ s hs).differentiableAt.hasDerivAt (hy₂ s hs).differentiableAt.hasDerivAt
    have h1 : chartCovDeriv cov x₀ u w y₁ s = 0 := chartCovDeriv_eq_zero_of_hasDerivAt (hy₁ s hs)
    have h2 : chartCovDeriv cov x₀ u w y₂ s = 0 := chartCovDeriv_eq_zero_of_hasDerivAt (hy₂ s hs)
    rw [h1, h2, chartGram_zero_fst, chartGram_zero_snd, add_zero] at hprod
    exact hprod
  have hconst := Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc hab hderiv
  rw [hconst t ht, hconst t₀ ht₀]

/-- A parallel field has constant squared norm (general-interval version). -/
theorem chartGram_parallel_self_const_Ioo
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : IsMetricCompatible cov) {x₀ : M} {u w : ℝ → E} {A B : ℝ}
    (hstay : ∀ t ∈ Ioo A B, u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Ioo A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Ioo A B, HasDerivAt w (chartGeodesicVectorField cov x₀ (u t, w t)) t)
    {a b t₀ : ℝ} (hab : a ≤ b)
    (habt : Icc a b ⊆ Ioo A B) (ht₀ : t₀ ∈ Icc a b)
    {y : ℝ → E}
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (y t)) t) :
    ∀ t ∈ Icc a b,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)
        = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (y t₀) (y t₀) :=
  chartGram_parallel_const_Ioo (cov := cov) hmet hstay hu hw hab habt ht₀ hy hy

/-- The velocity field of a solution of the chart equation is parallel (general interval). -/
lemma hasDerivAt_velocity_Ioo
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {x₀ : M} {u w : ℝ → E} {A B : ℝ}
    (hu : ∀ t ∈ Ioo A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Ioo A B, HasDerivAt w (chartGeodesicVectorField cov x₀ (u t, w t)) t)
    (hstay : ∀ t ∈ Ioo A B, u t ∈ (extChartAt I x₀).target) :
    ∀ t ∈ Ioo A B, HasDerivAt w (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (w t)) t := by
  intro t ht
  have hsrc := mem_source_chartCurve (I := I) (x₀ := x₀) (hstay t ht)
  refine (hw t ht).congr_deriv ?_
  rw [chartGeodesicVectorField, christoffelLM_apply (cov := cov) hsrc]

/-- **A parallel field of unit length orthogonal to the velocity** along a solution of the chart
equation on an arbitrary interval (generalises `Jacobi.exists_parallel_unit_orthogonal`). -/
theorem exists_parallel_unit_orthogonal_Ioo
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞] (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {x₀ : M} {u w : ℝ → E} {A B : ℝ}
    (hstay : ∀ t ∈ Ioo A B, u t ∈ (extChartAt I x₀).target)
    (hu : ∀ t ∈ Ioo A B, HasDerivAt u (w t) t)
    (hw : ∀ t ∈ Ioo A B, HasDerivAt w (chartGeodesicVectorField cov x₀ (u t, w t)) t)
    {a b t₀ : ℝ} (hab : a < b) (habt : Icc a b ⊆ Ioo A B) (ht₀ : t₀ ∈ Icc a b)
    (hwunit : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (w t₀) (w t₀) = 1) :
    ∃ Y : ℝ → E,
      (∀ t ∈ Icc a b, HasDerivAt Y (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (Y t)) t) ∧
      (∀ t ∈ Icc a b, chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t) (Y t) = 1) ∧
      (∀ t ∈ Icc a b, chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (Y t) (w t) = 0) := by
  classical
  have hp₀ : (extChartAt I x₀).symm (u t₀) ∈ (chartAt H x₀).source :=
    mem_source_chartCurve (I := I) (hstay t₀ (habt ht₀))
  set B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)))
      (fun a₁ a₂ b => chartGram_add_fst x₀ _ a₁ a₂ b)
      (fun c a b => chartGram_smul_fst x₀ _ c a b)
      (fun a b₁ b₂ => chartGram_add_snd x₀ _ a b₁ b₂)
      (fun c a b => chartGram_smul_snd x₀ _ c a b) with hB
  have hBeq : ∀ y z : E, B y z = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) y z :=
    fun y z => rfl
  have hBpos : ∀ y : E, 0 ≤ B y y := by
    intro y
    rw [hBeq]
    rcases eq_or_ne y 0 with h0 | h0
    · rw [h0]; simp
    · exact (chartGram_self_pos (I := I) (x₀ := x₀) (p := _) hp₀ h0).le
  have hBdef : ∀ y : E, B y y = 0 → y = 0 := by
    intro y hy
    by_contra hne
    have := chartGram_self_pos (I := I) (x₀ := x₀) (p := _) hp₀ hne
    rw [hBeq] at hy
    rw [hy] at this
    exact lt_irrefl _ this
  have hwunit' : B (w t₀) (w t₀) = 1 := by rw [hBeq]; exact hwunit
  obtain ⟨Y₀, hY₀norm, hY₀orth⟩ :=
    Commons.LinearAlgebra.exists_ne_zero_orthogonal_of_finrank_two_le hdim B hBpos hBdef
      (w t₀) hwunit'
  obtain ⟨Y, hY0, hYODE, -⟩ :=
    exists_parallel_field_Ioo (cov := cov) htor hab habt hstay hu hw ht₀ Y₀
  refine ⟨Y, hYODE, ?_, ?_⟩
  · intro t ht
    have hc := chartGram_parallel_self_const_Ioo (cov := cov) hmet hstay hu hw hab.le habt ht₀ hYODE t ht
    rw [hc, hY0]
    rw [hBeq] at hY₀norm
    exact hY₀norm
  · have hwODE : ∀ t ∈ Icc a b, HasDerivAt w (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (w t)) t :=
      fun t ht => hasDerivAt_velocity_Ioo hu hw hstay t (habt ht)
    intro t ht
    have hc := chartGram_parallel_const_Ioo (cov := cov) hmet hstay hu hw hab.le habt ht₀ hYODE hwODE t ht
    rw [hc, hY0]
    rw [hBeq] at hY₀orth
    exact hY₀orth

end

end Submission.JacobiGen
