import Submission.Gauss
import Submission.CurvatureVec
import Submission.Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray
import Submission.Commons.Analysis.ODE.exists_linearODE_solution_Icc

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The covariant derivative along a geodesic; Jacobi fields

This file starts the chapter of the proof that computes the second variation of the energy: the
**covariant derivative along a chart geodesic** and the **Jacobi equation**.

## Contents

* `christoffelLM`: the Christoffel symbol `Γ` as a continuous linear map in its first (field)
  argument, together with `christoffelLM_apply`;
* `chartCurve`, `chartCovDeriv`: the coordinate curve and the covariant derivative along it,
  `D y = y' + Γ(y)(γ')`;
* `chartCovDeriv_add`, `chartCovDeriv_const_smul`: `D` is `ℝ`-linear;
* `chartCovDeriv_geodesic`: for a chart geodesic `(u,w)`, `D w = 0`;
* `hasDerivAt_chartGram_chartCovDeriv`: metric compatibility `d/dt ⟪y₁,y₂⟫ = ⟪D y₁,y₂⟫ + ⟪y₁,D y₂⟫`.

## Notation and conventions

Along the chart curve `t ↦ (extChartAt I x₀).symm (u t)` a coordinate field `y : ℝ → E` represents
the tangent field `t ↦ frameVector x₀ (γ t) (y t)`.  With the velocity `w` (so that `u' = w`),
the covariant derivative of that field along `γ` has coordinates `y' + Γ(y)(w)`, where
`Γ(v)(w) = christoffelEval cov x₀ (γ t) v (frameVector x₀ (γ t) w)`.  This is the convention of
`Submission.ChartConnection.hasDerivAt_chartGram_curve`.
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

variable [I.Boundaryless]

/-- The Christoffel symbol `Γ` as a continuous linear map in its first (field) argument, defined
through the basis expansion `v ↦ ∑ i, (b.coord i v) • Γ(b i)(w)`. -/
noncomputable def christoffelLM (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ p : M) (w : TangentSpace I p) : E →L[ℝ] E :=
  ∑ i : Fin (Module.finrank ℝ E),
    (((Module.finBasis ℝ E).coord i).toContinuousLinearMap).smulRight
      (christoffelEval cov x₀ p ((Module.finBasis ℝ E) i) w)

/-- `christoffelLM` computes the Christoffel symbol. -/
lemma christoffelLM_apply {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {x₀ p : M} {w : TangentSpace I p} (hp : p ∈ (chartAt H x₀).source) (v : E) :
    christoffelLM cov x₀ p w v = christoffelEval cov x₀ p v w := by
  classical
  have h1 : christoffelEval cov x₀ p v w
      = ∑ i, ((Module.finBasis ℝ E).repr v) i
          • christoffelEval cov x₀ p ((Module.finBasis ℝ E) i) w := by
    conv_lhs => rw [← (Module.finBasis ℝ E).sum_repr v]
    rw [christoffelEval_sum_left _ cov x₀ p (fun i => ((Module.finBasis ℝ E).repr v) i)
      (fun i => (Module.finBasis ℝ E) i) w hp]
  have hkey : christoffelEval cov x₀ p v w
      = ∑ i, (Module.finBasis ℝ E).coord i v
          • christoffelEval cov x₀ p ((Module.finBasis ℝ E) i) w := by
    rw [h1]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Module.Basis.coord_apply]
  rw [hkey, christoffelLM, sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ContinuousLinearMap.smulRight_apply]
  rfl


/-- **Polarization of the Christoffel symbol.**  For a torsion-free connection the Christoffel
symbol `Γ(a)(b) = christoffelEval cov x₀ p a (frameVector x₀ p b)` is a symmetric bilinear form,
hence determined by its diagonal:
`2 Γ(a)(b) = Γ(a+b)(a+b) - Γ(a)(a) - Γ(b)(b)`. -/
lemma christoffelEval_polarize {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (htor : cov.torsion = 0) {x₀ p : M} (hp : p ∈ (chartAt H x₀).source) (a b : E) :
    2 • christoffelEval cov x₀ p a (frameVector (I := I) x₀ p b)
      = christoffelEval cov x₀ p (a + b) (frameVector (I := I) x₀ p (a + b))
        - christoffelEval cov x₀ p a (frameVector (I := I) x₀ p a)
        - christoffelEval cov x₀ p b (frameVector (I := I) x₀ p b) := by
  have hc1 : christoffelEval cov x₀ p (a + b) (frameVector (I := I) x₀ p a)
      = christoffelEval cov x₀ p a (frameVector (I := I) x₀ p (a + b)) :=
    christoffelEval_comm htor x₀ p hp (a + b) a
  have hc2 : christoffelEval cov x₀ p (a + b) (frameVector (I := I) x₀ p b)
      = christoffelEval cov x₀ p b (frameVector (I := I) x₀ p (a + b)) :=
    christoffelEval_comm htor x₀ p hp (a + b) b
  have hc3 : christoffelEval cov x₀ p b (frameVector (I := I) x₀ p a)
      = christoffelEval cov x₀ p a (frameVector (I := I) x₀ p b) :=
    christoffelEval_comm htor x₀ p hp b a
  rw [frameVector_add, christoffelEval_add_right, hc1, hc2, frameVector_add,
    christoffelEval_add_right, christoffelEval_add_right, hc3]
  module


/-- **Continuity of the Christoffel symbol along a chart geodesic.**  For a fixed coordinate
vector `a` the function
`t ↦ Γ(a)(w t) = christoffelEval cov x₀ (γ t) a (frameVector x₀ (γ t) (w t))` is continuous along
the geodesic.  This is the polarization identity
`2Γ(a)(b) = Γ(a+b)(a+b) - Γ(a)(a) - Γ(b)(b)` combined with the smoothness of the chart spray
`chartGeodesicVectorField` at the points of the geodesic. -/
lemma continuousOn_christoffelEval_entry
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) {x₀ : M} {v : E} {u w : ℝ → E}
    (h : HasChartGeodesic cov x₀ v u w) (a : E) :
    ContinuousOn (fun t : ℝ => christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (Ioo (-2 : ℝ) 2) := by
  have hspray : ∀ t ∈ Ioo (-2 : ℝ) 2, ∀ c : E,
      ContinuousAt (chartGeodesicVectorField cov x₀) (u t, c) := by
    intro t ht c
    have hz : (u t, c) ∈ (extChartAt I x₀).target ×ˢ (Set.univ : Set E) :=
      ⟨h.2.2.1 t ht, Set.mem_univ _⟩
    have hnb : (extChartAt I x₀).target ×ˢ (Set.univ : Set E) ∈ 𝓝 (u t, c) :=
      ((isOpen_extChartAt_target x₀).prod isOpen_univ).mem_nhds hz
    exact (((Commons.Geometry.Manifold.VectorBundle.CovariantDerivative.contDiffOn_chartSpray
      (cov := cov) x₀) (u t, c) hz).contDiffAt hnb).continuousAt
  have hu : ∀ t ∈ Ioo (-2 : ℝ) 2, ContinuousAt u t :=
    fun t ht => (h.2.2.2.1 t ht).continuousAt
  have hw : ∀ t ∈ Ioo (-2 : ℝ) 2, ContinuousAt w t :=
    fun t ht => (h.2.2.2.2 t ht).continuousAt
  have key : ∀ t ∈ Ioo (-2 : ℝ) 2,
      christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) a
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
        = (1/2 : ℝ) • (- chartGeodesicVectorField cov x₀ (u t, a + w t)
            + chartGeodesicVectorField cov x₀ (u t, a)
            + chartGeodesicVectorField cov x₀ (u t, w t)) := by
    intro t ht
    have hp : (extChartAt I x₀).symm (u t) ∈ (chartAt H x₀).source :=
      mem_source_chartCurve (I := I) (h.2.2.1 t ht)
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
      ((hu t ht).prodMk (continuousAt_const.add (hw t ht)))).continuousWithinAt
  · exact fun t ht => (ContinuousAt.comp (f := fun s : ℝ => (u s, a))
      (hspray t ht a)
      ((hu t ht).prodMk continuousAt_const)).continuousWithinAt
  · exact fun t ht => (ContinuousAt.comp (f := fun s : ℝ => (u s, w s))
      (hspray t ht (w t))
      ((hu t ht).prodMk (hw t ht))).continuousWithinAt

/-- **Continuity of the Christoffel operator along a chart geodesic.** -/
lemma continuousOn_christoffelLM_along
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) {x₀ : M} {v : E} {u w : ℝ → E}
    (h : HasChartGeodesic cov x₀ v u w) :
    ContinuousOn (fun t : ℝ => christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (Ioo (-2 : ℝ) 2) := by
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
    (continuousOn_christoffelEval_entry (cov := cov) htor h ((Module.finBasis ℝ E) i))


/-- The coordinate curve attached to a coordinate curve `u` in the chart at `x₀`. -/
def chartCurve (x₀ : M) (u : ℝ → E) : ℝ → M := fun t => (extChartAt I x₀).symm (u t)

/-- **The covariant derivative along a chart curve**, in coordinates:
`D y = y' + Γ(y)(w)`, where `w` is the velocity of the coordinate curve and `Γ` is the Christoffel
symbol (the convention of `hasDerivAt_chartGram_curve`). -/
noncomputable def chartCovDeriv (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (x₀ : M) (u w y : ℝ → E) : ℝ → E :=
  fun t => deriv y t + christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)) (y t)

/-- `chartCovDeriv` in terms of `christoffelEval`. -/
lemma chartCovDeriv_apply {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {x₀ : M} {u w y : ℝ → E} {t : ℝ} (htgt : u t ∈ (extChartAt I x₀).target) :
    chartCovDeriv cov x₀ u w y t
      = deriv y t + christoffelEval cov x₀ ((extChartAt I x₀).symm (u t)) (y t)
          (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)) := by
  rw [chartCovDeriv,
    christoffelLM_apply (mem_source_chartCurve (I := I) htgt)]

/-- The derivative of a pointwise sum. -/
lemma deriv_add_fun {y₁ y₂ : ℝ → E} {t : ℝ}
    (hy₁ : DifferentiableAt ℝ y₁ t) (hy₂ : DifferentiableAt ℝ y₂ t) :
    deriv (fun s => y₁ s + y₂ s) t = deriv y₁ t + deriv y₂ t := by
  rw [show (fun s => y₁ s + y₂ s) = y₁ + y₂ from rfl]
  exact deriv_add hy₁ hy₂

/-- The derivative of a pointwise scalar multiple. -/
lemma deriv_const_smul_fun {y : ℝ → E} {t c : ℝ} (hy : DifferentiableAt ℝ y t) :
    deriv (fun s => c • y s) t = c • deriv y t := by
  rw [show (fun s => c • y s) = c • y from rfl]
  exact deriv_const_smul c hy

/-- `chartCovDeriv` is additive in the field (for differentiable fields). -/
lemma chartCovDeriv_add {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {x₀ : M} {u w y₁ y₂ : ℝ → E} {t : ℝ}
    (htgt : u t ∈ (extChartAt I x₀).target)
    (hy₁ : DifferentiableAt ℝ y₁ t) (hy₂ : DifferentiableAt ℝ y₂ t) :
    chartCovDeriv cov x₀ u w (fun s => y₁ s + y₂ s) t
      = chartCovDeriv cov x₀ u w y₁ t + chartCovDeriv cov x₀ u w y₂ t := by
  rw [chartCovDeriv_apply (I := I) htgt, chartCovDeriv_apply (I := I) htgt,
    chartCovDeriv_apply (I := I) htgt]
  rw [deriv_add_fun hy₁ hy₂,
    christoffelEval_add_left cov x₀ ((extChartAt I x₀).symm (u t)) (y₁ t) (y₂ t)
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
      (mem_source_chartCurve (I := I) htgt)]
  abel

/-- `chartCovDeriv` is `ℝ`-homogeneous in the field (for differentiable fields). -/
lemma chartCovDeriv_const_smul {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {x₀ : M} {u w y : ℝ → E} {t c : ℝ}
    (htgt : u t ∈ (extChartAt I x₀).target) (hy : DifferentiableAt ℝ y t) :
    chartCovDeriv cov x₀ u w (fun s => c • y s) t
      = c • chartCovDeriv cov x₀ u w y t := by
  rw [chartCovDeriv_apply (I := I) htgt, chartCovDeriv_apply (I := I) htgt]
  rw [deriv_const_smul_fun hy,
    christoffelEval_smul_left cov x₀ ((extChartAt I x₀).symm (u t)) c (y t)
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))
      (mem_source_chartCurve (I := I) htgt), smul_add]

/-- **Metric compatibility along a chart curve.**  For a coordinate curve `u` with velocity `w` and
differentiable fields `y₁`, `y₂`,
`d/dt ⟪y₁,y₂⟫ = ⟪D y₁, y₂⟫ + ⟪y₁, D y₂⟫`. -/
theorem hasDerivAt_chartGram_chartCovDeriv
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : IsMetricCompatible cov) (x₀ : M)
    {u w y₁ y₂ : ℝ → E} {t : ℝ} (hu : HasDerivAt u (w t) t)
    (htgt : u t ∈ (extChartAt I x₀).target)
    (hstay : ∀ᶠ s in 𝓝 t, u s ∈ (extChartAt I x₀).target)
    (hy₁ : HasDerivAt y₁ (deriv y₁ t) t) (hy₂ : HasDerivAt y₂ (deriv y₂ t) t) :
    HasDerivAt (fun s => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u s)) (y₁ s) (y₂ s))
      (chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
          (chartCovDeriv cov x₀ u w y₁ t) (y₂ t)
        + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y₁ t)
          (chartCovDeriv cov x₀ u w y₂ t)) t := by
  have h := hasDerivAt_chartGram_curve (cov := cov) hmet x₀ hu htgt hstay hy₁ hy₂
  rw [chartCovDeriv_apply (I := I) htgt, chartCovDeriv_apply (I := I) htgt]
  exact h

/-- **The geodesic equation as a statement about `chartCovDeriv`**: for a chart geodesic `(u,w)`,
the velocity field is parallel, `D w = 0`. -/
theorem chartCovDeriv_geodesic {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {x₀ : M} {v : E} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w) :
    ∀ t ∈ Ioo (-2 : ℝ) 2, chartCovDeriv cov x₀ u w w t = 0 := by
  intro t ht
  have htgt : u t ∈ (extChartAt I x₀).target := h.2.2.1 t ht
  rw [chartCovDeriv_apply (I := I) htgt]
  have hderiv : deriv w t = chartGeodesicVectorField cov x₀ (u t, w t) :=
    (h.2.2.2.2 t ht).deriv
  rw [hderiv]
  simp only [chartGeodesicVectorField, neg_add_cancel]

/-- The parallel condition: a field whose derivative is `-Γ(y)(w)` has vanishing covariant
derivative. -/
lemma chartCovDeriv_eq_zero_of_hasDerivAt
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {x₀ : M} {u w y : ℝ → E} {t : ℝ}
    (hy : HasDerivAt y (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (y t)) t) :
    chartCovDeriv cov x₀ u w y t = 0 := by
  simp only [chartCovDeriv, hy.deriv, ContinuousLinearMap.neg_apply, neg_add_cancel]

/-- **Existence of parallel fields along a chart geodesic.**  For any initial value `y₀` at a time
`t₀ ∈ [a,b]` there is a field `y` along the geodesic with `D y = 0` and `y t₀ = y₀`.  This is the
linear ODE `y' = -Γ(y)(γ')`. -/
theorem exists_parallel_field_Icc
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (htor : cov.torsion = 0) {x₀ : M} {v : E} {u w : ℝ → E}
    (h : HasChartGeodesic cov x₀ v u w) {a b t₀ : ℝ} (hab : a < b)
    (habt : Icc a b ⊆ Ioo (-2 : ℝ) 2) (ht₀ : t₀ ∈ Icc a b) (y₀ : E) :
    ∃ y : ℝ → E, y t₀ = y₀ ∧
      (∀ t ∈ Icc a b, HasDerivAt y (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (y t)) t) ∧
      ∀ t ∈ Icc a b, chartCovDeriv cov x₀ u w y t = 0 := by
  have hA : ContinuousOn (fun t : ℝ => -(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t)))) (Icc a b) :=
    (continuousOn_christoffelLM_along (cov := cov) htor h).neg.mono habt
  obtain ⟨y, hy₀, hyODE, -⟩ :=
    Commons.Analysis.ODE.exists_linearODE_solution_Icc (E := E) hab hA ht₀ y₀
  exact ⟨y, hy₀, hyODE, fun t ht => chartCovDeriv_eq_zero_of_hasDerivAt (hyODE t ht)⟩


/-- **Parallel transport preserves the metric.**  If `y₁` and `y₂` are parallel fields along a chart
geodesic (i.e. `D y_i = 0`), then their scalar product is constant. -/
theorem chartGram_parallel_const
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : IsMetricCompatible cov) {x₀ : M} {v : E} {u w : ℝ → E}
    (h : HasChartGeodesic cov x₀ v u w) {a b t₀ : ℝ} (hab : a ≤ b)
    (habt : Icc a b ⊆ Ioo (-2 : ℝ) 2) (ht₀ : t₀ ∈ Icc a b)
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
    have hutgt : u s ∈ (extChartAt I x₀).target := h.2.2.1 s (habt hs)
    have hstay : ∀ᶠ r in 𝓝 s, u r ∈ (extChartAt I x₀).target :=
      (h.2.2.2.1 s (habt hs)).continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_target x₀).mem_nhds hutgt)
    have hprod := hasDerivAt_chartGram_chartCovDeriv (cov := cov) hmet x₀
      (h.2.2.2.1 s (habt hs)) hutgt hstay
      (hy₁ s hs).differentiableAt.hasDerivAt (hy₂ s hs).differentiableAt.hasDerivAt
    have h1 : chartCovDeriv cov x₀ u w y₁ s = 0 := chartCovDeriv_eq_zero_of_hasDerivAt (hy₁ s hs)
    have h2 : chartCovDeriv cov x₀ u w y₂ s = 0 := chartCovDeriv_eq_zero_of_hasDerivAt (hy₂ s hs)
    rw [h1, h2, chartGram_zero_fst, chartGram_zero_snd, add_zero] at hprod
    exact hprod
  have hconst := Commons.Analysis.Calculus.eqOn_of_hasDerivAt_eq_zero_Icc hab hderiv
  rw [hconst t ht, hconst t₀ ht₀]


/-- A parallel field has constant squared norm. -/
theorem chartGram_parallel_self_const
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    (hmet : IsMetricCompatible cov) {x₀ : M} {v : E} {u w : ℝ → E}
    (h : HasChartGeodesic cov x₀ v u w) {a b t₀ : ℝ} (hab : a ≤ b)
    (habt : Icc a b ⊆ Ioo (-2 : ℝ) 2) (ht₀ : t₀ ∈ Icc a b)
    {y : ℝ → E}
    (hy : ∀ t ∈ Icc a b, HasDerivAt y (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
        (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (y t)) t) :
    ∀ t ∈ Icc a b,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (y t) (y t)
        = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₀)) (y t₀) (y t₀) :=
  chartGram_parallel_const (cov := cov) hmet h hab habt ht₀ hy hy

/-- The velocity field of a chart geodesic is parallel. -/
lemma hasDerivAt_velocity_of_hasChartGeodesic
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    {x₀ : M} {v : E} {u w : ℝ → E} (h : HasChartGeodesic cov x₀ v u w) :
    ∀ t ∈ Ioo (-2 : ℝ) 2, HasDerivAt w (-(christoffelLM cov x₀ ((extChartAt I x₀).symm (u t))
      (frameVector (I := I) x₀ ((extChartAt I x₀).symm (u t)) (w t))) (w t)) t := by
  intro t ht
  have hsrc := mem_source_chartCurve (I := I) (x₀ := x₀) (h.2.2.1 t ht)
  refine (h.2.2.2.2 t ht).congr_deriv ?_
  rw [chartGeodesicVectorField, christoffelLM_apply (cov := cov) hsrc]

end

end Submission.Jacobi
