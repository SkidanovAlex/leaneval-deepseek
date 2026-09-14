import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false

/-!
# Derivative of the diagonal exponential integral

We prove that the map
`t ↦ ∫_{K} exp(-π ∑ᵢ exp(2 t aᵢ) xᵢ²) dx`
(for a bounded set `K`) has derivative
`-2π ∑ᵢ aᵢ ∫_{K} xᵢ² exp(-π ‖x‖²) dx`
at `t = 0`.

This is used in the reduction of the diagonal (B)-conjecture to an even Poincaré
inequality.
-/

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory
open scoped Real BigOperators

/-- The quadratic form `∑ᵢ exp(2 t aᵢ) xᵢ²` appearing in the diagonal exponential. -/
noncomputable def diagQuad {n : ℕ} (a : Fin n → ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i, Real.exp (2 * t * a i) * (x i) ^ 2

/-- The diagonal exponential `exp(-π ∑ᵢ exp(2 t aᵢ) xᵢ²)`. -/
noncomputable def diagExp {n : ℕ} (a : Fin n → ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  Real.exp (-Real.pi * diagQuad a t x)

/-- The `t`-derivative of `diagExp`. -/
noncomputable def diagExpDeriv {n : ℕ} (a : Fin n → ℝ) (t : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  -2 * Real.pi * (∑ i, a i * Real.exp (2 * t * a i) * (x i) ^ 2)
    * Real.exp (-Real.pi * diagQuad a t x)

lemma hasDerivAt_diagExp {n : ℕ} (a : Fin n → ℝ) (x : EuclideanSpace ℝ (Fin n))
    (s : ℝ) : HasDerivAt (fun t : ℝ => diagExp a t x) (diagExpDeriv a s x) s := by
  have h1 : HasDerivAt (fun t : ℝ => ∑ i, Real.exp (2 * t * a i) * (x i) ^ 2)
      (2 * ∑ i, a i * Real.exp (2 * s * a i) * (x i) ^ 2) s := by
    have key : HasDerivAt
        (fun t : ℝ => ∑ i ∈ Finset.univ, Real.exp (2 * t * a i) * (x i) ^ 2)
        (∑ i ∈ Finset.univ, 2 * (a i * Real.exp (2 * s * a i) * (x i) ^ 2)) s :=
      HasDerivAt.fun_sum (fun i _ => by
        have hbase : HasDerivAt (fun t : ℝ => 2 * t * a i) (2 * a i) s := by
          simpa using ((hasDerivAt_id s).const_mul 2).mul_const (a i)
        exact (hbase.exp.mul_const ((x i) ^ 2)).congr_deriv (by ring))
    rw [← Finset.mul_sum] at key
    simpa using key
  have h2 : HasDerivAt (fun t : ℝ => -Real.pi * ∑ i, Real.exp (2 * t * a i) * (x i) ^ 2)
      (-Real.pi * (2 * ∑ i, a i * Real.exp (2 * s * a i) * (x i) ^ 2)) s := by
    simpa using h1.const_mul (-Real.pi)
  have h3 := h2.exp
  refine h3.congr_deriv ?_
  simp only [diagQuad, diagExpDeriv]
  ring

lemma continuous_diagExpDeriv {n : ℕ} (a : Fin n → ℝ) :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin n) => diagExpDeriv a p.1 p.2) := by
  unfold diagExpDeriv diagQuad
  fun_prop

lemma continuous_diagExpDeriv_apply {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => diagExpDeriv a t x) :=
  (continuous_diagExpDeriv a).comp (continuous_const.prodMk continuous_id)

lemma continuous_diagExp {n : ℕ} (a : Fin n → ℝ) (t : ℝ) :
    Continuous (fun x : EuclideanSpace ℝ (Fin n) => diagExp a t x) := by
  unfold diagExp diagQuad
  fun_prop

theorem deriv_diagonal_exp_integral {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (hKbdd : Bornology.IsBounded K) (a : Fin n → ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x in K,
        Real.exp (-Real.pi * ∑ i, Real.exp (2 * t * a i) * (x i) ^ 2))
      (-2 * Real.pi * ∑ i, a i * ∫ x in K, (x i) ^ 2 * Real.exp (-Real.pi * ‖x‖ ^ 2)) 0 := by
  classical
  haveI hfin : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.2 hKbdd.measure_lt_top.ne
  obtain ⟨R₀, hR₀⟩ := hKbdd.exists_norm_le
  set R : ℝ := max R₀ 0 with hRdef
  have hR : ∀ x ∈ K, ‖x‖ ≤ R := fun x hx => (hR₀ x hx).trans (le_max_left _ _)
  have hR0 : 0 ≤ R := le_max_right _ _
  -- Almost every point of `K` lies in the closed ball of radius `R`
  have hae : ∀ᵐ y ∂(volume.restrict K),
      y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    rw [MeasureTheory.ae_iff]
    have hmeas : MeasurableSet (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ :=
      Metric.isClosed_closedBall.measurableSet.compl
    change (volume.restrict K) (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ = 0
    rw [Measure.restrict_apply hmeas]
    have hempty : (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)ᶜ ∩ K = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hyc, hyK⟩
      exact hyc (by rw [Metric.mem_closedBall, dist_zero_right]; exact hR y hyK)
    rw [hempty, measure_empty]
  -- Compactness yields a uniform bound on the derivative
  have hcompT : IsCompact
      (Set.Icc (-1 : ℝ) 1 ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :=
    isCompact_Icc.prod (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) R)
  have himg : IsCompact ((fun p : ℝ × EuclideanSpace ℝ (Fin n) => diagExpDeriv a p.1 p.2) ''
      (Set.Icc (-1 : ℝ) 1 ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R)) :=
    hcompT.image (continuous_diagExpDeriv a)
  obtain ⟨M, hM⟩ := himg.isBounded.exists_norm_le
  have hbound : ∀ᵐ y ∂(volume.restrict K), ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      ‖diagExpDeriv a x y‖ ≤ M := by
    filter_upwards [hae] with y hy
    intro x hx
    have hp : (x, y) ∈ Set.Icc (-1 : ℝ) 1
        ×ˢ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R :=
      ⟨Set.mem_Icc.mpr ⟨le_of_lt hx.1, le_of_lt hx.2⟩, hy⟩
    exact hM _ (Set.mem_image_of_mem _ hp)
  -- Integrability of `diagExp a 0`
  have hF_int : Integrable (fun x : EuclideanSpace ℝ (Fin n) => diagExp a 0 x)
      (volume.restrict K) := by
    refine Integrable.of_bound (continuous_diagExp a 0).aestronglyMeasurable 1 ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (by rw [diagExp]; exact Real.exp_nonneg _)]
    rw [diagExp, diagQuad]
    apply Real.exp_le_one_iff.mpr
    have hsum : 0 ≤ ∑ i, Real.exp (2 * 0 * a i) * (y i) ^ 2 := by
      apply Finset.sum_nonneg; intro i _
      positivity
    nlinarith [Real.pi_pos]
  -- The main parametric differentiation theorem
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Set.Ioo (-1 : ℝ) 1) (x₀ := (0 : ℝ))
    (F := fun t (x : EuclideanSpace ℝ (Fin n)) => diagExp a t x)
    (F' := fun t (x : EuclideanSpace ℝ (Fin n)) => diagExpDeriv a t x)
    (μ := volume.restrict K) (bound := fun _ => M)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
    (Filter.Eventually.of_forall fun t => (continuous_diagExp a t).aestronglyMeasurable)
    hF_int
    (continuous_diagExpDeriv_apply a 0).aestronglyMeasurable
    hbound
    (integrable_const M)
    (Filter.Eventually.of_forall fun y x _ => hasDerivAt_diagExp a y x)
  -- Evaluation of the integral of the derivative
  have hdiag : ∀ y : EuclideanSpace ℝ (Fin n),
      diagExpDeriv a 0 y =
        -2 * Real.pi * ∑ i, a i * ((y i) ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2)) := by
    intro y
    have hnorm : Real.exp (-Real.pi * ∑ i, (y i) ^ 2) = Real.exp (-Real.pi * ‖y‖ ^ 2) := by
      rw [EuclideanSpace.real_norm_sq_eq]
    have hbase : diagExpDeriv a 0 y =
        -2 * Real.pi * (∑ i, a i * (y i) ^ 2) * Real.exp (-Real.pi * ‖y‖ ^ 2) := by
      simp only [diagExpDeriv, diagQuad, mul_zero, zero_mul, Real.exp_zero, one_mul, mul_one]
      rw [hnorm]
    rw [hbase, mul_assoc, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hint_i : ∀ i : Fin n, Integrable
      (fun y : EuclideanSpace ℝ (Fin n) => (y i) ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2))
      (volume.restrict K) := by
    intro i
    refine Integrable.of_bound (by fun_prop) (R ^ 2) ?_
    filter_upwards [hae] with y hy
    have hyR : ‖y‖ ≤ R := by
      rw [Metric.mem_closedBall, dist_zero_right] at hy; exact hy
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : (y i) ^ 2 ≤ R ^ 2 := by
      have hle : (y i) ^ 2 ≤ ‖y‖ ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        exact Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
      nlinarith [norm_nonneg y, hyR, hR0]
    have h2 : Real.exp (-Real.pi * ‖y‖ ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      nlinarith [Real.pi_pos, sq_nonneg ‖y‖]
    nlinarith [Real.exp_nonneg (-Real.pi * ‖y‖ ^ 2)]
  have hint : ∫ y in K, diagExpDeriv a 0 y =
      -2 * Real.pi * ∑ i, a i * ∫ y in K, (y i) ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2) := by
    rw [show (∫ y in K, diagExpDeriv a 0 y) =
        ∫ y in K, -2 * Real.pi * ∑ i, a i * ((y i) ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2)) from
      integral_congr_ae (Filter.Eventually.of_forall hdiag)]
    rw [integral_const_mul]
    congr 1
    rw [show (∫ y in K, ∑ i, a i * ((y i) ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2))) =
        ∑ i, ∫ y in K, a i * ((y i) ^ 2 * Real.exp (-Real.pi * ‖y‖ ^ 2)) from
      integral_finsetSum Finset.univ (fun i _ => (hint_i i).const_mul (a i))]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
  rw [hint] at hmain
  simpa only [diagExp, diagQuad] using hmain.2

end Commons.Analysis.GaussianMeasure