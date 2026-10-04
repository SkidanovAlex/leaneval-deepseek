import Submission.CoeffSmooth2
import Submission.JacobiGlobal
import Submission.Commons.Analysis.ODE.exists_linearODE_solution_Icc

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
/-!
# Parallel fields along a chart curve

The **parallel transport** equation along a curve `∇_{γ'}X = 0` is the first-order linear ODE
`X' = -Γ̂X` on the chart coordinates.  Mathlib has no parallel transport at all; this file provides
the chart-local theory, which is the first rung of the **Synge / holonomy** chapter
(`Submission/Roadmap.lean` §78.2 step 3 and §107): along a closed geodesic in an *even*-dimensional
orientable manifold the holonomy of the normal bundle is a special orthogonal map of an
odd-dimensional space, hence (commons lemma
`Commons.LinearAlgebra.Orthogonal.odd_dim_det_one_fixed_vector`) fixes a vector, which yields a
*periodic* parallel unit normal field and a shortening second variation.

Contents (all in namespace `Submission.ParallelField`):

* **`chartCovDeriv_eq_zero_iff`** — `∇_{γ'}X = 0` in coordinates is exactly
  `HasDerivAt X (-(Γ̂_t (X t))) t`;
* **`exists_parallelFieldOn`** — existence and **uniqueness** of the parallel field on `[a,b]` with
  prescribed value at a prescribed time (the commons ODE lemma
  `Commons.Analysis.ODE.exists_linearODE_solution_Icc`, together with `C^∞` smoothness of the
  Christoffel operator `t ↦ Γ̂_t` from `Submission.Coeff.contDiffOn_gammaOp_along_Ioo`);
* **`chartGram_parallelField_eq`** — **parallel transport is an isometry**: the scalar product of two
  parallel fields is *constant* (metric compatibility,
  `Submission.Jacobi.hasDerivAt_chartGram_chartCovDeriv`);
* **`chartGram_self_parallelField_eq`** — a parallel field has constant (chart-)norm.

The *global* statement — a parallel field along a `GExp`-ray, glued over a finite chart cover, and
the resulting holonomy — is the next rung and is not done here; it needs the cover/gluing pattern of
`Submission.JacobiCover`/`Submission.SmoothFieldCover` (`exists_isJacobiPiece_cover`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.ChartConnection
open Submission.Gauss
open Submission.Jacobi
open Submission.JacobiTensor

namespace Submission.ParallelField

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable [I.Boundaryless] [Nontrivial E] [CompactSpace M]
variable {cov : CovariantDerivative I E (TangentSpace I (M := M))}
variable [ContMDiffCovariantDerivative cov ∞]

/-- **The covariant derivative along the chart curve vanishes exactly when the field solves the
linear ODE `y' = -Γ̂ y`.** -/
theorem chartCovDeriv_eq_zero_iff {x₀ : M} {u w X : ℝ → E} {t : ℝ}
    (htgt : u t ∈ (extChartAt I x₀).target)
    (hd : HasDerivAt X (-(gammaOp (cov := cov) x₀ u w t (X t))) t) :
    chartCovDeriv cov x₀ u w X t = 0 := by
  rw [chartCovDeriv_apply (I := I) htgt, hd.deriv,
    gammaOp_apply (cov := cov) (mem_source_chartCurve (I := I) htgt) (X t)]
  abel

/-- **Parallel fields along a chart curve exist and are unique.** -/
theorem exists_parallelFieldOn (htor : cov.torsion = 0)
    {x₀ : M} {u w : ℝ → E} {A₀ B₀ : ℝ}
    (hstay : ∀ t ∈ Set.Ioo A₀ B₀, u t ∈ (extChartAt I x₀).target)
    (hu : ContDiffOn ℝ ∞ u (Set.Ioo A₀ B₀)) (hw : ContDiffOn ℝ ∞ w (Set.Ioo A₀ B₀))
    {a b t₀ : ℝ} (hab : a < b) (ha₀ : A₀ < a) (hb₀ : b < B₀)
    (ht₀ : t₀ ∈ Set.Icc a b) (X₀ : E) :
    ∃ X : ℝ → E, X t₀ = X₀ ∧
      (∀ t ∈ Set.Icc a b, HasDerivAt X (-(gammaOp (cov := cov) x₀ u w t (X t))) t) ∧
      (∀ t ∈ Set.Icc a b, chartCovDeriv cov x₀ u w X t = 0) ∧
      (∀ Y : ℝ → E, Y t₀ = X₀ →
        (∀ t ∈ Set.Icc a b, HasDerivAt Y (-(gammaOp (cov := cov) x₀ u w t (Y t))) t) →
        Set.EqOn Y X (Set.Icc a b)) := by
  have hsub : Set.Icc a b ⊆ Set.Ioo A₀ B₀ := fun t ht => ⟨lt_of_lt_of_le ha₀ ht.1, lt_of_le_of_lt ht.2 hb₀⟩
  have hcont : ContinuousOn (fun t : ℝ => gammaOp (cov := cov) x₀ u w t) (Set.Icc a b) :=
    (ContDiffOn.continuousOn
      (Submission.Coeff.contDiffOn_gammaOp_along_Ioo (cov := cov) htor hstay hu hw)).mono hsub
  have hA : ContinuousOn (fun t : ℝ => -(gammaOp (cov := cov) x₀ u w t)) (Set.Icc a b) :=
    hcont.neg
  obtain ⟨X, hXt₀, hXder, hXuniq⟩ :=
    Commons.Analysis.ODE.exists_linearODE_solution_Icc (E := E) hab hA ht₀ X₀
  refine ⟨X, hXt₀, hXder, fun t ht => ?_, fun Y hYt₀ hYder => hXuniq Y hYt₀ hYder⟩
  exact chartCovDeriv_eq_zero_iff (cov := cov) (hstay t (hsub ht)) (hXder t ht)

/-- **The inner product of two parallel fields along a chart curve is constant.**

This is metric compatibility applied to the parallel (covariant-derivative-zero) fields: the
derivative of `t ↦ ⟨X t, Y t⟩` is `⟨∇X, Y⟩ + ⟨X, ∇Y⟩ = 0`. -/
theorem chartGram_parallelField_eq (hmet : IsMetricCompatible cov)
    {x₀ : M} {u w X Y : ℝ → E} {a b : ℝ}
    (hu : ∀ t ∈ Set.Ioo a b, HasDerivAt u (w t) t)
    (hstay : ∀ t ∈ Set.Ioo a b, u t ∈ (extChartAt I x₀).target)
    (hX : ∀ t ∈ Set.Ioo a b, HasDerivAt X (deriv X t) t)
    (hY : ∀ t ∈ Set.Ioo a b, HasDerivAt Y (deriv Y t) t)
    (hpX : ∀ t ∈ Set.Ioo a b, chartCovDeriv cov x₀ u w X t = 0)
    (hpY : ∀ t ∈ Set.Ioo a b, chartCovDeriv cov x₀ u w Y t = 0) :
    ∀ t₁ ∈ Set.Ioo a b, ∀ t₂ ∈ Set.Ioo a b,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₁)) (X t₁) (Y t₁)
        = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₂)) (X t₂) (Y t₂) := by
  set g : ℝ → ℝ := fun t => chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (X t) (Y t)
    with hgdef
  have hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt g 0 t := by
    intro t ht
    have h := hasDerivAt_chartGram_chartCovDeriv (cov := cov) hmet x₀ (hu t ht)
      (hstay t ht) (Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) (fun s hs => hstay s hs))
      (hX t ht) (hY t ht)
    have hval : chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t))
        (chartCovDeriv cov x₀ u w X t) (Y t)
      + chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t)) (X t)
        (chartCovDeriv cov x₀ u w Y t) = 0 := by
      rw [hpX t ht, hpY t ht]
      simp only [chartGram_zero_fst, chartGram_zero_snd, add_zero]
    rw [← hval]
    exact h
  have hdiff : DifferentiableOn ℝ g (Set.Ioo a b) := fun t ht => (hderiv t ht).differentiableAt.differentiableWithinAt
  have hzero : ∀ t ∈ Set.Ioo a b, deriv g t = 0 := fun t ht => (hderiv t ht).deriv
  intro t₁ ht₁ t₂ ht₂
  obtain ⟨c, hc⟩ := isOpen_Ioo.exists_is_const_of_deriv_eq_zero (convex_Ioo a b).isPreconnected
    hdiff hzero
  change g t₁ = g t₂
  rw [hc t₁ ht₁, hc t₂ ht₂]


/-- **A parallel field has constant (chart-)norm.**  The special case `Y = X` of
`chartGram_parallelField_eq`. -/
theorem chartGram_self_parallelField_eq (hmet : IsMetricCompatible cov)
    {x₀ : M} {u w X : ℝ → E} {a b : ℝ}
    (hu : ∀ t ∈ Set.Ioo a b, HasDerivAt u (w t) t)
    (hstay : ∀ t ∈ Set.Ioo a b, u t ∈ (extChartAt I x₀).target)
    (hX : ∀ t ∈ Set.Ioo a b, HasDerivAt X (deriv X t) t)
    (hpX : ∀ t ∈ Set.Ioo a b, chartCovDeriv cov x₀ u w X t = 0) :
    ∀ t₁ ∈ Set.Ioo a b, ∀ t₂ ∈ Set.Ioo a b,
      chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₁)) (X t₁) (X t₁)
        = chartGram (I := I) x₀ ((extChartAt I x₀).symm (u t₂)) (X t₂) (X t₂) :=
  chartGram_parallelField_eq (cov := cov) hmet hu hstay hX hX hpX hpX

end

end Submission.ParallelField
