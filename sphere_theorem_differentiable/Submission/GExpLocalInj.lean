import Submission.GExpSmooth
import Submission.CutStep2
import Submission.Commons.Geometry.Manifold.locally_injective_of_injective_mfderiv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Local injectivity of the exponential map from the injectivity of its differential

`Submission.GExpSmooth.exists_contMDiffAt_GExp` proves that the global exponential map is `C^∞` at
*every* tangent vector.  This file draws the two consequences that the cut-point analysis needs:

* **`locallyInjectiveAtGExp_of_injective_mfderiv`** — the inverse-function-theorem direction: an
  *injective* differential at `w` makes `GExp p` locally injective at `w`
  (`LocallyInjectiveAtGExp`, the hypothesis of the cut-point step);
* **`not_injective_mfderiv_of_not_locallyInjective`** — its contrapositive, i.e. the *merging*
  branch of the cut-point dichotomy forces a non-injective differential;
* **`locallyInjectiveAtGExp_of_lt_pi_div_sqrt`** — the resulting *reduction*: the merging branch
  cannot occur below the conjugate radius, so that `LocallyInjectiveAtGExp hmet p w` holds for
  `‖w‖ < π/√K` **as soon as** one knows the classical fact

  > `¬ (d GExp_p)_v` invertible  ⟹  `π/√K ≤ ‖v‖`  (a singular differential is a conjugate vector),

  which is the remaining (and only) gap for `hloc_sphere`; see `Submission/Roadmap.lean` §83.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Submission.Geodesic
open Submission.GlobalExp
open Submission.GExpSmooth
open Submission.GExpRay2
open Submission.ChartBounds
open Submission.ChartConnection
open Submission.CutStep2

namespace Submission.GExpLocalInj

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

/-- The manifold derivative of the exponential map at a tangent vector, written with the tangent
space `T_pM` (definitionally `E`) as the model of the source. -/
theorem contMDiffAt_GExp_one (hmet : IsMetricCompatible cov) (p : M) (v : TangentSpace I p) :
    ContMDiffAt 𝓘(ℝ, E) I 1 (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w))
      (show E from v) :=
  (exists_contMDiffAt_GExp (cov := cov) hmet p v).of_le
    (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from WithTop.coe_le_coe.mpr le_top)

/-- **An injective differential gives local injectivity** (inverse function theorem, via
`Commons.Geometry.Manifold.locally_injective_of_injective_mfderiv`). -/
theorem locallyInjectiveAtGExp_of_injective_mfderiv (hmet : IsMetricCompatible cov) {p : M}
    {v : TangentSpace I p}
    (hinj : Function.Injective (mfderiv 𝓘(ℝ, E) I
      (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w)) (show E from v))) :
    LocallyInjectiveAtGExp (I := I) hmet p v := by
  obtain ⟨ε, hε, hloc⟩ :=
    Commons.Geometry.Manifold.locally_injective_of_injective_mfderiv
      (I := I) (contMDiffAt_GExp_one (cov := cov) hmet p v) hinj
  obtain ⟨lam, hlam, hbnd⟩ := exists_model_norm_le_fibre_div (I := I) p
  have hsq : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  refine ⟨Metric.ball v (ε * Real.sqrt lam), Metric.isOpen_ball.mem_nhds ?_, ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm, sub_self, norm_zero]
    exact mul_pos hε hsq
  · intro y hy z hz hyz
    rw [Metric.mem_ball, dist_eq_norm] at hy hz
    have hy' : (fun z : E => ‖z‖) (show E from (y - v)) < ε := by
      have h0 := hbnd (y - v)
      have h1 : ‖y - v‖ / Real.sqrt lam < ε := by
        rw [div_lt_iff₀ hsq]
        calc ‖y - v‖ < ε * Real.sqrt lam := hy
          _ = ε * Real.sqrt lam := rfl
      exact lt_of_le_of_lt (by simpa using h0) h1
    have hz' : (fun z : E => ‖z‖) (show E from (z - v)) < ε := by
      have h0 := hbnd (z - v)
      have h1 : ‖z - v‖ / Real.sqrt lam < ε := by
        rw [div_lt_iff₀ hsq]
        calc ‖z - v‖ < ε * Real.sqrt lam := hz
          _ = ε * Real.sqrt lam := rfl
      exact lt_of_le_of_lt (by simpa using h0) h1
    exact hloc (show E from y) (show E from z) hy' hz' hyz

/-- **The merging branch of the cut-point dichotomy forces a non-injective differential.**  If
`GExp p` is not locally injective at `v` then the differential of `GExp p` at `v` is not
injective. -/
theorem not_injective_mfderiv_of_not_locallyInjective (hmet : IsMetricCompatible cov) {p : M}
    {v : TangentSpace I p} (h : ¬ LocallyInjectiveAtGExp (I := I) hmet p v) :
    ¬ Function.Injective (mfderiv 𝓘(ℝ, E) I
      (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w)) (show E from v)) :=
  fun hinj => h (locallyInjectiveAtGExp_of_injective_mfderiv (cov := cov) hmet hinj)

/-- **A non-injective differential is not invertible.** -/
theorem not_isInvertible_of_not_injective (hmet : IsMetricCompatible cov) {p : M}
    {v : TangentSpace I p}
    (h : ¬ Function.Injective (mfderiv 𝓘(ℝ, E) I
      (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w)) (show E from v))) :
    ¬ (mfderiv 𝓘(ℝ, E) I
      (fun w : E => GExp (cov := cov) hmet p (show TangentSpace I p from w)) (show E from v)).IsInvertible :=
  fun hinv => h hinv.injective

/-- **The reduction.**  If every singular differential of the exponential map is a conjugate vector
(`π/√K ≤ ‖v‖`, the classical statement that is still missing), then `GExp p` is locally injective at
every vector of length `< π/√K`.  This is exactly the hypothesis `hloc_sphere` of the cut-point
step, in the case `m < π/√K`. -/
theorem locallyInjectiveAtGExp_of_lt_pi_div_sqrt (hmet : IsMetricCompatible cov) {p : M}
    {v : TangentSpace I p}
    {K : ℝ}
    (hconj : ∀ (q : M) (w : TangentSpace I q), w ≠ 0 →
      ¬ (mfderiv 𝓘(ℝ, E) I
        (fun u : E => GExp (cov := cov) hmet q (show TangentSpace I q from u)) (show E from w)).IsInvertible →
      Real.pi / Real.sqrt K ≤ ‖w‖)
    (hv0 : v ≠ 0) (hv : ‖v‖ < Real.pi / Real.sqrt K) :
    LocallyInjectiveAtGExp (I := I) hmet p v := by
  by_contra hloc
  have h1 := not_injective_mfderiv_of_not_locallyInjective (cov := cov) hmet hloc
  have h2 := not_isInvertible_of_not_injective (cov := cov) hmet (p := p) h1
  exact absurd (hconj p v hv0 h2) (not_le.mpr hv)



/-- **The differential of the exponential map at the origin is the identity.**  The global form of
`d exp_0 = id`: near `0` the global exponential map agrees with the chart exponential map
(`exists_pos_GExp_eq_expMap`), whose differential at `0` is the identity
(`Geodesic.mfderiv_expMap_zero`).  The only bookkeeping is the conversion between the **fibre** norm
used by the agreement statement and the **model** norm used for the ball: the chart-Gram upper bound
`chartGram x₀ x₀ a a ≤ Λ ‖a‖²` gives `‖v‖_fibre ≤ √(max Λ 1) ‖v‖_model`. -/
theorem mfderiv_GExp_zero (hmet : IsMetricCompatible cov) (p : M) :
    mfderiv 𝓘(ℝ, E) I (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v))
      (0 : E) = ContinuousLinearMap.id ℝ E := by
  obtain ⟨ρ, hρ, hagree⟩ := exists_pos_GExp_eq_expMap (cov := cov) hmet p
  obtain ⟨_lam, _hlam, Lam, hLam, hbnd⟩ := exists_chartGram_bounds (I := I) (x₀ := p)
    (K := ({p} : Set M)) isCompact_singleton ⟨p, rfl⟩
    (by intro y hy; rw [Set.mem_singleton_iff] at hy; rw [hy]; exact mem_chart_source H p)
  have hmaxpos : 0 < max Lam 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsqpos : 0 < Real.sqrt (max Lam 1) := Real.sqrt_pos.mpr hmaxpos
  have hnorm_sq : ∀ v : TangentSpace I p,
      ‖v‖ ^ 2 = chartGram (I := I) p p (show E from v) (show E from v) := by
    intro v
    rw [Submission.Distance.chartGram_self_apply (I := I) p (show E from v) (show E from v)]
    exact (real_inner_self_eq_norm_sq v).symm
  have hfib : ∀ v : TangentSpace I p, ‖v‖ ≤ Real.sqrt (max Lam 1) * ‖(show E from v)‖ := by
    intro v
    have hb := (hbnd p (by simp) (show E from v)).2
    have hle : ‖v‖ ^ 2 ≤ (max Lam 1) * ‖(show E from v)‖ ^ 2 := by
      rw [hnorm_sq v]
      have h1 : Lam * ‖(show E from v)‖ ^ 2 ≤ max Lam 1 * ‖(show E from v)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      linarith
    calc ‖v‖ = Real.sqrt (‖v‖ ^ 2) := (Real.sqrt_sq (norm_nonneg v)).symm
      _ ≤ Real.sqrt ((max Lam 1) * ‖(show E from v)‖ ^ 2) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt (max Lam 1) * ‖(show E from v)‖ := by
          rw [Real.sqrt_mul (le_of_lt hmaxpos), Real.sqrt_sq (norm_nonneg _)]
  have hev : (fun v : E => GExp (cov := cov) hmet p (show TangentSpace I p from v))
      =ᶠ[𝓝 (0 : E)] (fun v : E => expMap cov p v) := by
    filter_upwards [Metric.ball_mem_nhds (0 : E)
      (div_pos hρ hsqpos)] with v hv
    rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hv
    refine hagree (show TangentSpace I p from v) ?_
    calc ‖(show TangentSpace I p from v)‖ ≤ Real.sqrt (max Lam 1) * ‖v‖ := hfib _
      _ < Real.sqrt (max Lam 1) * (ρ / Real.sqrt (max Lam 1)) :=
          mul_lt_mul_of_pos_left hv hsqpos
      _ = ρ := by field_simp
  rw [hev.mfderiv_eq]
  exact Submission.Geodesic.mfderiv_expMap_zero (cov := cov) p

end

end Submission.GExpLocalInj
