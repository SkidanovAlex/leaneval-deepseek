import ChallengeDeps
import Submission.MChartGlobal
import Submission.ModelMinimality
import Mathlib

/-!
# Speed of a chart curve in the manifold equals its coordinate speed

For a point `p : M` with `φ := extChartAt I p`, take the global coordinate metric `ge` from
`Submission.chart_metric_global` (C³ symmetric positive definite, agreeing with the fibre inner
products on `ball (φ p) ρ`).  Let `γ : ℝ → M` be a curve with `γ s = φ.symm (c s)` for all `s`
(so that `γ` is the chart-parametrised curve with coordinate representation `c`).  Where `c` is
differentiable at `t` (`HasDerivAt c u t`) and `c t` lies in the agreement ball, we prove that the
**manifold speed** of `γ` equals the **coordinate speed** measured by `ge`:

    ‖mfderiv% γ t 1‖ₑ = ENNReal.ofReal (Real.sqrt ((ge (c t)) u u))

The proof has three parts, all proved below:

1. `chart_mfderiv_comp`: the chain rule in charts gives
   `(mfderiv% γ t) 1 = (mfderiv[range I] φ.symm (c t)) u`
   (the manifold derivative of the curve equals the derivative of the inverse chart applied to
   the coordinate velocity; this uses `HasMFDerivAt.comp`, the differentiability of the inverse
   chart `mdifferentiableWithinAt_extChartAt_symm`, and `[I.Boundaryless]` so that the
   within-`range I` differentiability is a genuine differentiability at the point).

2. `enorm_sqrt_inner`: in any real inner-product space, the extended norm satisfies
   `‖v‖ₑ = ENNReal.ofReal (Real.sqrt (inner ℝ v v))` (the norm induced by the inner product).

3. `chart_speed_core`: the above two facts plus the agreement clause of `chart_metric_global`
   (which says that on the ball `(ge y) u v` equals the fibre inner product of the pushed
   tangent vectors) give the final speed equality.
-/

open scoped Manifold ENNReal ContDiff Bundle Topology InnerProductSpace
open Set Bundle Metric Filter

namespace Submission

open LeanEval.Geometry

noncomputable section

set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
variable (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
variable [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
variable [IsRiemannianManifold I M]

/-- In a real inner product space the extended norm equals `ENNReal.ofReal` of the square root
of the inner product of a vector with itself. -/
lemma enorm_sqrt_inner {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (v : V) : ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (inner ℝ v v)) := by
  rw [← norm_eq_sqrt_real_inner]
  rw [enorm_eq_nnnorm]
  congr 1
  symm
  exact Real.toNNReal_of_nonneg (norm_nonneg v)

/-- The manifold derivative of the chart curve `γ = φ.symm ∘ c` at `t`, applied to the tangent
vector `1`, equals the derivative of the inverse chart at `c t` applied to the coordinate
velocity `u`. -/
lemma chart_mfderiv_comp (p : M) {γ : ℝ → M} {c : ℝ → E} {t : ℝ} {u : E}
    (hγeq : γ = (extChartAt I p).symm ∘ c)
    (hct : c t ∈ (extChartAt I p).target)
    (hc : HasDerivAt c u t) :
    (mfderiv% γ t) 1 = (mfderiv[range I] (extChartAt I p).symm (c t)) u := by
  let φ := extChartAt I p
  have h_range : range I = Set.univ := ModelWithCorners.Boundaryless.range_eq_univ
  -- `φ.symm` is differentiable within `range I` at `c t` (it is the inverse of a chart)
  have hgmd : MDiffAt[range I] φ.symm (c t) :=
    mdifferentiableWithinAt_extChartAt_symm (I := I) (x := p) hct
  -- boundaryless model: the within-`range I` differentiability is differentiability at the point
  have hgfull : HasMFDerivAt% φ.symm (c t) (mfderiv[range I] φ.symm (c t)) := by
    apply HasMFDerivWithinAt.hasMFDerivAt (s := range I)
    · exact hgmd.hasMFDerivWithinAt
    · rw [h_range]
      exact univ_mem
  -- the curve `c` is differentiable at `t` as a manifold map, with derivative `toSpanSingleton u`
  have hcF : HasFDerivAt c (ContinuousLinearMap.toSpanSingleton ℝ u) t :=
    (hasDerivAt_iff_hasFDerivAt (𝕜 := ℝ)).1 hc
  have hcM : HasMFDerivAt% c t (ContinuousLinearMap.toSpanSingleton ℝ u) := hcF.hasMFDerivAt
  -- chain rule
  have hcomp : HasMFDerivAt% (φ.symm ∘ c) t
      ((mfderiv[range I] φ.symm (c t)).comp (ContinuousLinearMap.toSpanSingleton ℝ u)) := by
    exact HasMFDerivAt.comp t hgfull hcM
  have hγ : HasMFDerivAt% γ t ((mfderiv[range I] φ.symm (c t)).comp (ContinuousLinearMap.toSpanSingleton ℝ u)) := by
    rw [hγeq]
    exact hcomp
  have hγm : mfderiv% γ t = (mfderiv[range I] φ.symm (c t)).comp (ContinuousLinearMap.toSpanSingleton ℝ u) :=
    hγ.mfderiv
  rw [hγm]
  change (mfderiv[range I] (extChartAt I p).symm (c t))
      ((ContinuousLinearMap.toSpanSingleton ℝ u) 1) =
    (mfderiv[range I] (extChartAt I p).symm (c t)) u
  rw [ContinuousLinearMap.toSpanSingleton_apply, one_smul]

/-- The core speed identity: whenever the coordinate metric `ge` agrees with the fibre inner
products on the ball `ball (φ p) ρ` (contained in the chart target), the manifold speed of the
chart curve equals its coordinate speed `Real.sqrt ((ge (c t)) u u)`. -/
lemma chart_speed_core (p : M) {ρ : ℝ} {ge : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hagree : ∀ y ∈ ball (extChartAt I p p) ρ, ∀ u v : E,
      (ge y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
        ((extChartAt I p).symm y)
        ((mfderiv[range I] (extChartAt I p).symm y) u)
        ((mfderiv[range I] (extChartAt I p).symm y) v))
    (hball : ball (extChartAt I p p) ρ ⊆ (extChartAt I p).target)
    {γ : ℝ → M} {c : ℝ → E} {t : ℝ} {u : E}
    (hγeq : ∀ s : ℝ, γ s = (extChartAt I p).symm (c s))
    (hcball : c t ∈ ball (extChartAt I p p) ρ)
    (hu : HasDerivAt c u t) :
    ‖mfderiv% γ t 1‖ₑ = ENNReal.ofReal (Real.sqrt ((ge (c t)) u u)) := by
  have hγeq' : γ = (extChartAt I p).symm ∘ c := by
    funext s
    exact hγeq s
  have hct_target : c t ∈ (extChartAt I p).target := hball hcball
  -- the chain rule gives the equality of the tangent vectors
  have hder : (mfderiv% γ t) 1 = (mfderiv[range I] (extChartAt I p).symm (c t)) u :=
    chart_mfderiv_comp (I := I) (M := M) p hγeq' hct_target hu
  -- rewrite the extended norm of the velocity into a square root of the fibre inner product
  have hnorm : ‖mfderiv% γ t 1‖ₑ =
      ENNReal.ofReal (Real.sqrt (inner ℝ (mfderiv% γ t 1) (mfderiv% γ t 1))) := by
    exact enorm_sqrt_inner (mfderiv% γ t 1)
  rw [hnorm]
  -- expose the base point of the fibre inner product (it is the typeclass inner on the fibre
  -- over `γ t`, which is definitionally the bundle metric at `γ t`)
  have hfib1 : inner ℝ (mfderiv% γ t 1) (mfderiv% γ t 1) =
      (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner (γ t)
        (mfderiv% γ t 1) (mfderiv% γ t 1) := by
    rfl
  rw [hfib1]
  -- replace the tangent vector by the chart derivative applied to `u`, and the base point
  -- `γ t` by `φ.symm (c t)`, then use the agreement of `ge` with the fibre inner product
  rw [hder]
  rw [hγeq t]
  rw [hagree (c t) hcball u u]

/-- The manifold speed of a chart curve equals the coordinate speed given by the model metric. -/
theorem chart_speed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    (M : Type*) [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [Bundle.RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M => TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] (p : M) :
    ∃ ρ > 0, ∃ ge : E → E →L[ℝ] E →L[ℝ] ℝ,
      ContDiff ℝ 3 ge ∧
      (∀ y u v : E, (ge y) u v = (ge y) v u) ∧
      (∀ y : E, ∀ v : E, v ≠ 0 → 0 < (ge y) v v) ∧
      (∀ y ∈ ball (extChartAt I p p) ρ, ∀ u v : E,
         (ge y) u v = (Bundle.RiemannianBundle.g (E := fun x : M => TangentSpace I x)).inner
                       ((extChartAt I p).symm y)
                       ((mfderiv[range I] (extChartAt I p).symm y) u)
                       ((mfderiv[range I] (extChartAt I p).symm y) v)) ∧
      (∀ {γ : ℝ → M} {c : ℝ → E} {t : ℝ} {u : E},
        (∀ s, γ s = (extChartAt I p).symm (c s)) →
        c t ∈ ball (extChartAt I p p) ρ →
        HasDerivAt c u t →
        ‖mfderiv% γ t 1‖ₑ = ENNReal.ofReal (Real.sqrt ((ge (c t)) u u))) := by
  -- take the global coordinate metric `ge` from `chart_metric_global`
  rcases chart_metric_global (I := I) (M := M) p with ⟨ρ₀, hρ₀pos, ge, hgeC, hgeSymm, hgePos, hgeAgree⟩
  -- choose an additional small radius so that the ball around the chart centre stays inside the
  -- chart target (where the inverse chart is differentiable)
  have hopenT : IsOpen (extChartAt I p).target := isOpen_extChartAt_target (I := I) p
  have hmemT : (extChartAt I p).target ∈ 𝓝 (extChartAt I p p) :=
    hopenT.mem_nhds (mem_extChartAt_target p)
  rcases Metric.nhds_basis_ball.mem_iff.mp hmemT with ⟨ρ₁, hρ₁pos, hρ₁sub⟩
  let ρ : ℝ := min ρ₀ ρ₁
  have hρpos : 0 < ρ := lt_min hρ₀pos hρ₁pos
  have hρle₀ : ρ ≤ ρ₀ := min_le_left ρ₀ ρ₁
  have hρle₁ : ρ ≤ ρ₁ := min_le_right ρ₀ ρ₁
  have hball₀ : ball (extChartAt I p p) ρ ⊆ ball (extChartAt I p p) ρ₀ := ball_subset_ball hρle₀
  have hball₁ : ball (extChartAt I p p) ρ ⊆ ball (extChartAt I p p) ρ₁ := ball_subset_ball hρle₁
  refine ⟨ρ, hρpos, ge, hgeC, hgeSymm, hgePos, ?_, ?_⟩
  · -- agreement of `ge` with the fibre inner products on the (smaller) ball `ball (φ p) ρ`
    intro y hy u v
    exact hgeAgree y (hball₀ hy) u v
  · -- the speed identity for chart curves
    intro γ c t u hγeq hcball hu
    refine chart_speed_core (I := I) (M := M) p (ρ := ρ) (ge := ge) ?_ ?_ hγeq hcball hu
    · intro y hy u' v'
      exact hgeAgree y (hball₀ hy) u' v'
    · intro y hy
      exact hρ₁sub (hball₁ hy)

end

end Submission
