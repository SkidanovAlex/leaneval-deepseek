import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

set_option linter.style.haveILetI false

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory Set Real Filter Polynomial
open scoped Real Topology Interval

noncomputable section

/-- The Gaussian-type convolution `x ↦ ∫ t, q t * κ (x - t)` of `q` with a kernel `κ`. -/
def smoothed (q κ : ℝ → ℝ) : ℝ → ℝ := fun x => ∫ t, q t * κ (x - t)

@[simp] lemma smoothed_apply (q κ : ℝ → ℝ) (x : ℝ) :
    smoothed q κ x = ∫ t, q t * κ (x - t) := rfl

/-- If `q` is measurable and bounded by `C` and `κ` is integrable, then
`t ↦ q t * κ (a - t)` is integrable. -/
lemma integrable_mul_comp_sub {q κ : ℝ → ℝ} {C : ℝ} (hC : ∀ t, |q t| ≤ C) (hq : Measurable q)
    (hκ : Integrable κ) (a : ℝ) : Integrable (fun t => q t * κ (a - t)) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (q 0)) (hC 0)
  have h1 : Integrable (fun t : ℝ => κ (a - t)) := hκ.comp_sub_left a
  have h2 : Integrable (fun t : ℝ => C * κ (a - t)) := h1.const_mul C
  refine Integrable.mono h2 ((hq.aestronglyMeasurable).mul h1.aestronglyMeasurable) ?_
  filter_upwards with t
  calc ‖q t * κ (a - t)‖ = |q t| * |κ (a - t)| := by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ C * |κ (a - t)| := by gcongr; exact hC t
    _ = |C| * |κ (a - t)| := by rw [abs_of_nonneg hC0]
    _ = ‖C * κ (a - t)‖ := by rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]

/-- Pointwise bound for the smoothed function. -/
lemma abs_smoothed_le {q κ : ℝ → ℝ} {C : ℝ} (hC : ∀ t, |q t| ≤ C) (hq : Measurable q)
    (hκ : Integrable κ) (x : ℝ) : |smoothed q κ x| ≤ C * ∫ t, |κ t| := by
  have hInt : Integrable (fun t => q t * κ (x - t)) := integrable_mul_comp_sub hC hq hκ x
  have hbound : Integrable (fun t : ℝ => C * |κ (x - t)|) :=
    (hκ.norm.comp_sub_left x).const_mul C
  have h1 : |smoothed q κ x| ≤ ∫ t, ‖q t * κ (x - t)‖ := by
    rw [smoothed_apply, ← Real.norm_eq_abs]
    exact norm_integral_le_integral_norm _
  have h2 : ∫ t, ‖q t * κ (x - t)‖ ≤ ∫ t, C * |κ (x - t)| := by
    apply integral_mono hInt.norm hbound
    intro t
    show ‖q t * κ (x - t)‖ ≤ C * |κ (x - t)|
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC t) (abs_nonneg _)
  have h3 : ∫ t, C * |κ (x - t)| = C * ∫ t, |κ t| := by
    rw [integral_const_mul, integral_sub_left_eq_self (fun t => |κ t|) volume x]
  exact h1.trans (h2.trans (le_of_eq h3))

/-- Product integrability used for the Fubini step. -/
lemma integrable_uncurry_prod {q g : ℝ → ℝ} {C x y : ℝ} (hC : ∀ t, |q t| ≤ C)
    (hq : Measurable q) (hg : Continuous g) (hgi : Integrable g) :
    Integrable (fun p : ℝ × ℝ => q p.2 * g (x + p.1 * (y - x) - p.2))
      ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume) := by
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (q 0)) (hC 0)
  set μ : Measure ℝ := volume.restrict (Set.uIoc (0 : ℝ) 1) with hμ
  haveI : IsFiniteMeasure μ := by
    rw [hμ, isFiniteMeasure_restrict, volume_uIoc]; exact ENNReal.ofReal_ne_top
  have htarget_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => q p.2 * g (x + p.1 * (y - x) - p.2)) (μ.prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => q p.2) (μ.prod volume) :=
      (hq.comp measurable_snd).aestronglyMeasurable
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => g (x + p.1 * (y - x) - p.2))
        (μ.prod volume) := (hg.comp (by fun_prop)).aestronglyMeasurable
    exact h1.mul h2
  have hdom_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => C * |g (x + p.1 * (y - x) - p.2)|) (μ.prod volume) :=
    (continuous_const.mul ((hg.comp (by fun_prop)).abs)).aestronglyMeasurable
  have hdom : Integrable (fun p : ℝ × ℝ => C * |g (x + p.1 * (y - x) - p.2)|)
      (μ.prod volume) := by
    rw [integrable_prod_iff hdom_meas]
    constructor
    · filter_upwards with θ
      exact (hgi.norm.comp_sub_left (x + θ * (y - x))).const_mul C
    · have hnorm : ∀ a : ℝ, ‖C * |a|‖ = C * |a| := fun a => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC0, abs_of_nonneg (abs_nonneg a)]
      have heq : (fun θ : ℝ =>
            ∫ t, ‖(fun p : ℝ × ℝ => C * |g (x + p.1 * (y - x) - p.2)|) (θ, t)‖)
          = fun _ : ℝ => C * ∫ t, |g t| := by
        funext θ
        simp only [hnorm]
        rw [integral_const_mul, integral_sub_left_eq_self (fun t => |g t|) volume (x + θ * (y - x))]
      rw [heq]
      exact integrable_const _
  refine Integrable.mono hdom htarget_meas ?_
  filter_upwards with p
  show ‖q p.2 * g (x + p.1 * (y - x) - p.2)‖
      ≤ ‖C * |g (x + p.1 * (y - x) - p.2)|‖
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
  rw [abs_mul, abs_of_nonneg hC0, abs_of_nonneg (abs_nonneg _)]
  exact mul_le_mul_of_nonneg_right (hC p.2) (abs_nonneg _)

/-- The fundamental identity: the increment of the smoothed function is the integral of
the smoothed derivative along the segment. -/
lemma smoothed_sub_eq {q κ γ : ℝ → ℝ} {C : ℝ} (hC : ∀ t, |q t| ≤ C) (hq : Measurable q)
    (hκint : Integrable κ) (hκ : ∀ t, HasDerivAt κ (γ t) t)
    (hγc : Continuous γ) (hγint : Integrable γ) (x y : ℝ) :
    smoothed q κ y - smoothed q κ x
      = (y - x) * ∫ θ in (0 : ℝ)..1, smoothed q γ (x + θ * (y - x)) := by
  have hy : Integrable (fun t => q t * κ (y - t)) := integrable_mul_comp_sub hC hq hκint y
  have hx : Integrable (fun t => q t * κ (x - t)) := integrable_mul_comp_sub hC hq hκint x
  rw [smoothed_apply, smoothed_apply, ← integral_sub hy hx]
  -- pointwise FTC in `θ`
  have hstep : ∀ t, (q t * κ (y - t) - q t * κ (x - t))
      = ∫ θ in (0 : ℝ)..1, q t * ((y - x) * γ (x + θ * (y - x) - t)) := by
    intro t
    have hFTC : κ (y - t) - κ (x - t)
        = ∫ θ in (0 : ℝ)..1, (y - x) * γ (x + θ * (y - x) - t) := by
      have hderiv : ∀ θ ∈ Set.uIcc (0 : ℝ) 1,
          HasDerivAt (fun s : ℝ => κ (x + s * (y - x) - t))
            ((y - x) * γ (x + θ * (y - x) - t)) θ := by
        intro θ _
        have h1 : HasDerivAt (fun s : ℝ => x + s * (y - x) - t) (y - x) θ := by
          simpa using (((hasDerivAt_id θ).mul_const (y - x)).const_add x).sub_const t
        exact ((hκ (x + θ * (y - x) - t)).comp θ h1).congr_deriv (by ring)
      have hint : IntervalIntegrable
          (fun θ : ℝ => (y - x) * γ (x + θ * (y - x) - t)) volume 0 1 :=
        (((hγc.comp (by fun_prop : Continuous fun θ : ℝ => x + θ * (y - x) - t))).const_mul
          (y - x)).intervalIntegrable 0 1
      have key := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
      rw [key]
      congr 1 <;> ring_nf
    rw [← mul_sub, hFTC]
    exact (intervalIntegral.integral_const_mul (q t)
      (fun θ => (y - x) * γ (x + θ * (y - x) - t))).symm
  trans ∫ t, ∫ θ in (0 : ℝ)..1, q t * ((y - x) * γ (x + θ * (y - x) - t))
  · apply integral_congr_ae; filter_upwards with t; exact hstep t
  · have hbase : Integrable (fun p : ℝ × ℝ => q p.2 * γ (x + p.1 * (y - x) - p.2))
        ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume) :=
      integrable_uncurry_prod hC hq hγc hγint
    have h_int : Integrable
        (Function.uncurry (fun θ t => q t * ((y - x) * γ (x + θ * (y - x) - t))))
        ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume) := by
      have hfun : Function.uncurry (fun θ t => q t * ((y - x) * γ (x + θ * (y - x) - t)))
          = fun p : ℝ × ℝ => q p.2 * ((y - x) * γ (x + p.1 * (y - x) - p.2)) := by
        funext p; rfl
      rw [hfun]
      have hA : Integrable (fun p : ℝ × ℝ => (y - x) * (q p.2 * γ (x + p.1 * (y - x) - p.2)))
          ((volume.restrict (Set.uIoc (0 : ℝ) 1)).prod volume) := hbase.const_mul (y - x)
      refine hA.congr (Filter.Eventually.of_forall fun p => ?_)
      show (y - x) * (q p.2 * γ (x + p.1 * (y - x) - p.2))
          = q p.2 * ((y - x) * γ (x + p.1 * (y - x) - p.2))
      ring
    rw [(intervalIntegral_integral_swap (μ := volume)
        (f := fun θ t => q t * ((y - x) * γ (x + θ * (y - x) - t))) h_int).symm]
    have hinner : (fun θ : ℝ => ∫ t, q t * ((y - x) * γ (x + θ * (y - x) - t)))
        = fun θ : ℝ => (y - x) * smoothed q γ (x + θ * (y - x)) := by
      funext θ
      rw [smoothed_apply]
      rw [show (fun t => q t * ((y - x) * γ (x + θ * (y - x) - t)))
          = fun t => (y - x) * (q t * γ (x + θ * (y - x) - t)) by funext t; ring]
      rw [integral_const_mul]
    rw [hinner, intervalIntegral.integral_const_mul]

/-- Lipschitz bound for the smoothed function. -/
lemma smoothed_lipschitz {q κ γ : ℝ → ℝ} {C : ℝ} (hC : ∀ t, |q t| ≤ C) (hq : Measurable q)
    (hκint : Integrable κ) (hκ : ∀ t, HasDerivAt κ (γ t) t) (hγc : Continuous γ)
    (hγint : Integrable γ) (x y : ℝ) :
    |smoothed q κ y - smoothed q κ x| ≤ C * (∫ t, |γ t|) * |y - x| := by
  rw [smoothed_sub_eq hC hq hκint hκ hγc hγint x y, abs_mul]
  have hb : |∫ θ in (0 : ℝ)..1, smoothed q γ (x + θ * (y - x))| ≤ C * (∫ t, |γ t|) := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
      (C := C * (∫ t, |γ t|)) (f := fun θ : ℝ => smoothed q γ (x + θ * (y - x)))
      (fun θ _ => by rw [Real.norm_eq_abs]; exact abs_smoothed_le hC hq hγint _)
    rw [Real.norm_eq_abs] at h
    simpa using h
  calc |y - x| * |∫ θ in (0 : ℝ)..1, smoothed q γ (x + θ * (y - x))|
        ≤ |y - x| * (C * ∫ t, |γ t|) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = C * (∫ t, |γ t|) * |y - x| := by ring

/-- Continuity of the smoothed function. -/
lemma continuous_smoothed {q κ γ : ℝ → ℝ} {C : ℝ} (hC : ∀ t, |q t| ≤ C) (hq : Measurable q)
    (hκint : Integrable κ) (hκ : ∀ t, HasDerivAt κ (γ t) t) (hγc : Continuous γ)
    (hγint : Integrable γ) : Continuous (smoothed q κ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (g := fun y : ℝ => C * (∫ t, |γ t|) * |y - x|)
    (fun y => norm_nonneg _) (fun y => ?_) ?_
  · rw [Real.norm_eq_abs]; exact smoothed_lipschitz hC hq hκint hκ hγc hγint x y
  · have h1 : Tendsto (fun y : ℝ => y - x) (𝓝 x) (𝓝 0) := by
      have := (tendsto_id : Tendsto (fun y : ℝ => y) (𝓝 x) (𝓝 x)).sub_const x
      simpa using this
    simpa using (h1.abs.const_mul (C * (∫ t, |γ t|)))

/-- Differentiability of the smoothed function, with derivative the smoothing of `γ`. -/
lemma hasDerivAt_smoothed {q κ γ γ' : ℝ → ℝ} {C : ℝ} (hC : ∀ t, |q t| ≤ C)
    (hq : Measurable q) (hκint : Integrable κ) (hκ : ∀ t, HasDerivAt κ (γ t) t)
    (hγc : Continuous γ) (hγint : Integrable γ) (hγ : ∀ t, HasDerivAt γ (γ' t) t)
    (hγ'c : Continuous γ') (hγ'int : Integrable γ') (x : ℝ) :
    HasDerivAt (smoothed q κ) (smoothed q γ x) x := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hLip : ∀ u v, |smoothed q γ v - smoothed q γ u| ≤ C * (∫ t, |γ' t|) * |v - u| :=
    fun u v => smoothed_lipschitz hC hq hγint hγ hγ'c hγ'int u v
  have hEq : ∀ y : ℝ, y ≠ x → slope (smoothed q κ) x y
      = ∫ θ in (0 : ℝ)..1, smoothed q γ (x + θ * (y - x)) := by
    intro y hyx
    have hs := smoothed_sub_eq hC hq hκint hκ hγc hγint x y
    simp only [slope, smul_eq_mul, vsub_eq_sub]
    rw [hs, ← mul_assoc, inv_mul_cancel₀ (sub_ne_zero.mpr hyx), one_mul]
  have hTend : Tendsto (fun y => ∫ θ in (0 : ℝ)..1, smoothed q γ (x + θ * (y - x)))
      (𝓝 x) (𝓝 (smoothed q γ x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (g := fun y : ℝ => C * (∫ t, |γ' t|) * |y - x|)
      (fun y => norm_nonneg _) (fun y => ?_) ?_
    · have hcont : Continuous (fun θ : ℝ => smoothed q γ (x + θ * (y - x))) :=
        (continuous_smoothed hC hq hγint hγ hγ'c hγ'int).comp (by fun_prop)
      have heq : (∫ θ in (0 : ℝ)..1, smoothed q γ (x + θ * (y - x))) - smoothed q γ x
          = ∫ θ in (0 : ℝ)..1, (smoothed q γ (x + θ * (y - x)) - smoothed q γ x) := by
        have h1 : IntervalIntegrable (fun θ : ℝ => smoothed q γ (x + θ * (y - x))) volume 0 1 :=
          hcont.intervalIntegrable 0 1
        have h2 : IntervalIntegrable (fun _ : ℝ => smoothed q γ x) volume 0 1 :=
          continuous_const.intervalIntegrable 0 1
        have hsum := intervalIntegral.integral_sub h1 h2
        have hc : (∫ θ in (0 : ℝ)..1, (fun _ : ℝ => smoothed q γ x) θ) = smoothed q γ x := by
          rw [intervalIntegral.integral_const]; simp
        rw [hsum, hc]
      rw [Real.norm_eq_abs, heq, ← Real.norm_eq_abs]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
        (C := C * (∫ t, |γ' t|) * |y - x|)
        (f := fun θ : ℝ => smoothed q γ (x + θ * (y - x)) - smoothed q γ x) ?_
      · simpa using hb
      · intro θ hθ
        rw [Real.norm_eq_abs]
        have hθ' : θ ∈ Set.Ioc (0 : ℝ) 1 := by
          rwa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hθ
        have hL0 : 0 ≤ C * (∫ t, |γ' t|) :=
          mul_nonneg (le_trans (abs_nonneg (q 0)) (hC 0))
            (integral_nonneg (f := fun t => |γ' t|) (fun t => abs_nonneg _))
        calc |smoothed q γ (x + θ * (y - x)) - smoothed q γ x|
            ≤ C * (∫ t, |γ' t|) * |(x + θ * (y - x)) - x| := hLip x (x + θ * (y - x))
          _ = C * (∫ t, |γ' t|) * (|θ| * |y - x|) := by
              rw [show (x + θ * (y - x)) - x = θ * (y - x) by ring, abs_mul]
          _ ≤ C * (∫ t, |γ' t|) * (1 * |y - x|) := by
              apply mul_le_mul_of_nonneg_left _ hL0
              rw [abs_of_pos hθ'.1]
              exact mul_le_mul_of_nonneg_right hθ'.2 (abs_nonneg _)
          _ = C * (∫ t, |γ' t|) * |y - x| := by ring
    · have h1 : Tendsto (fun y : ℝ => y - x) (𝓝 x) (𝓝 0) := by
        have := (tendsto_id : Tendsto (fun y : ℝ => y) (𝓝 x) (𝓝 x)).sub_const x
        simpa using this
      simpa using (h1.abs.const_mul (C * (∫ t, |γ' t|)))
  refine Tendsto.congr' ?_ (hTend.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact (hEq y hy).symm

/-- The smoothed function is `C^n` for every `n`, with `k`-th derivative the smoothing of
the `k`-th derivative of the kernel. -/
theorem smoothed_contDiff {q κ : ℝ → ℝ} {C : ℝ} (hC : ∀ t, |q t| ≤ C) (hq : Measurable q)
    (hκc : ∀ n : ℕ, ContDiff ℝ n κ) (hκi : ∀ n : ℕ, Integrable (iteratedDeriv n κ)) :
    (∀ n : ℕ, ContDiff ℝ n (smoothed q κ)) ∧
      (∀ n : ℕ, iteratedDeriv n (smoothed q κ) = smoothed q (iteratedDeriv n κ)) := by
  have hderiv : ∀ k : ℕ, ∀ t : ℝ,
      HasDerivAt (iteratedDeriv k κ) (iteratedDeriv (k + 1) κ t) t := by
    intro k t
    have hd : Differentiable ℝ (iteratedDeriv k κ) :=
      (hκc (k + 1)).differentiable_iteratedDeriv k (Nat.cast_lt.mpr (Nat.lt_succ_self k))
    exact ((hd t).hasDerivAt).congr_deriv (by rw [iteratedDeriv_succ])
  have hiter : ∀ k : ℕ, iteratedDeriv k (smoothed q κ) = smoothed q (iteratedDeriv k κ) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [iteratedDeriv_succ, ih]
      funext x
      exact (hasDerivAt_smoothed hC hq (hκi k) (hderiv k)
        ((hκc (k + 1)).continuous_iteratedDeriv (k + 1) le_rfl) (hκi (k + 1))
        (hderiv (k + 1)) ((hκc (k + 2)).continuous_iteratedDeriv (k + 2) le_rfl)
        (hκi (k + 2)) x).deriv
  refine ⟨fun n => ?_, hiter⟩
  apply contDiff_of_differentiable_iteratedDeriv
  intro m _
  rw [hiter m]
  exact fun x => (hasDerivAt_smoothed hC hq (hκi m) (hderiv m)
    ((hκc (m + 1)).continuous_iteratedDeriv (m + 1) le_rfl) (hκi (m + 1))
    (hderiv (m + 1)) ((hκc (m + 2)).continuous_iteratedDeriv (m + 2) le_rfl)
    (hκi (m + 2)) x).differentiableAt

/-! ### The Gaussian kernel and its iterated derivatives -/

/-- The centred Gaussian kernel with variance `s ^ 2`. -/
noncomputable def gaussKernel (s : ℝ) : ℝ → ℝ :=
  fun z => (Real.sqrt (2 * Real.pi))⁻¹ * s⁻¹ * Real.exp (-(z / s) ^ 2 / 2)

lemma contDiff_gaussKernel (s : ℝ) (n : ℕ) : ContDiff ℝ n (gaussKernel s) := by
  unfold gaussKernel; fun_prop

/-- Integrability of `z ^ i * exp (-(z ^ 2 / 2))`. -/
lemma integrable_pow_exp_neg_sq (i : ℕ) :
    Integrable (fun z : ℝ => z ^ i * Real.exp (-(z ^ 2 / 2))) := by
  have hs : (-1 : ℝ) < (i : ℝ) := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg i)
  have h1 : Integrable (fun z : ℝ => z ^ ((i : ℕ) : ℝ) * Real.exp (-(1/2 : ℝ) * z ^ 2)) :=
    integrable_rpow_mul_exp_neg_mul_sq (b := (1/2 : ℝ)) (s := ((i:ℕ):ℝ)) (by norm_num) hs
  refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
  show z ^ ((i:ℕ):ℝ) * Real.exp (-(1/2 : ℝ) * z^2) = z ^ i * Real.exp (-(z^2/2))
  rw [Real.rpow_natCast, show -(1/2 : ℝ) * z ^ 2 = -(z ^ 2 / 2) by ring]

lemma integrable_polynomial_mul_gaussian (P : ℝ[X]) :
    Integrable (fun z : ℝ => Polynomial.eval z P * Real.exp (-(z ^ 2 / 2))) := by
  have h : (fun z : ℝ => Polynomial.eval z P * Real.exp (-(z ^ 2 / 2)))
      = fun z => ∑ i ∈ Finset.range (P.natDegree + 1),
          P.coeff i * (z ^ i * Real.exp (-(z ^ 2 / 2))) := by
    funext z
    rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h]
  apply integrable_finsetSum
  intro i _
  exact (integrable_pow_exp_neg_sq i).const_mul (P.coeff i)

lemma aeval_hermite_eq_eval_map (n : ℕ) (z : ℝ) :
    Polynomial.aeval z (Polynomial.hermite n)
      = ((Polynomial.hermite n).map (algebraMap ℤ ℝ)).eval z := by
  rw [Polynomial.aeval_def, Polynomial.eval_map]

lemma iteratedDeriv_exp_neg_sq_eq (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Real.exp (-(y ^ 2 / 2)))
      = fun z => (-1 : ℝ) ^ n * (((Polynomial.hermite n).map (algebraMap ℤ ℝ)).eval z)
          * Real.exp (-(z ^ 2 / 2)) := by
  funext z
  rw [iteratedDeriv_eq_iterate, Polynomial.deriv_gaussian_eq_hermite_mul_gaussian,
    aeval_hermite_eq_eval_map]

lemma integrable_iteratedDeriv_exp_neg_sq (n : ℕ) :
    Integrable (fun y : ℝ => iteratedDeriv n (fun z : ℝ => Real.exp (-(z ^ 2 / 2))) y) := by
  have hP := integrable_polynomial_mul_gaussian ((Polynomial.hermite n).map (algebraMap ℤ ℝ))
  have h2 : Integrable (fun y : ℝ => (-1 : ℝ) ^ n *
      (((Polynomial.hermite n).map (algebraMap ℤ ℝ)).eval y) * Real.exp (-(y ^ 2 / 2))) :=
    (hP.const_mul ((-1 : ℝ) ^ n)).congr (Filter.Eventually.of_forall fun y => by ring)
  refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [iteratedDeriv_exp_neg_sq_eq]

lemma iteratedDeriv_gaussKernel (s : ℝ) (n : ℕ) :
    iteratedDeriv n (gaussKernel s)
      = fun z => (Real.sqrt (2 * Real.pi))⁻¹ * s⁻¹ * s⁻¹ ^ n *
          iteratedDeriv n (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) (s⁻¹ * z) := by
  have hG : ContDiff ℝ n (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) := by fun_prop
  have hfun : gaussKernel s = fun w => (Real.sqrt (2 * Real.pi))⁻¹ * s⁻¹ *
      (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) (s⁻¹ * w) := by
    funext w
    simp only [gaussKernel]
    congr 2
    rw [div_eq_inv_mul]
    ring
  rw [hfun]
  funext z
  rw [iteratedDeriv_const_mul_field]
  simp only [iteratedDeriv_comp_const_mul hG]
  ring

lemma integrable_iteratedDeriv_gaussKernel (s : ℝ) (hs : s ≠ 0) (n : ℕ) :
    Integrable (iteratedDeriv n (gaussKernel s)) := by
  rw [iteratedDeriv_gaussKernel s n]
  have h1 : Integrable (fun z : ℝ =>
      iteratedDeriv n (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) (s⁻¹ * z)) :=
    (integrable_comp_mul_left_iff (iteratedDeriv n (fun y : ℝ => Real.exp (-(y ^ 2 / 2))))
      (inv_ne_zero hs)).mpr (integrable_iteratedDeriv_exp_neg_sq n)
  have h2 : Integrable (fun z : ℝ => s⁻¹ ^ n *
      iteratedDeriv n (fun y : ℝ => Real.exp (-(y ^ 2 / 2))) (s⁻¹ * z)) := h1.const_mul _
  exact (h2.const_mul ((Real.sqrt (2 * Real.pi))⁻¹ * s⁻¹)).congr
    (Filter.Eventually.of_forall fun z => by ring)

/-- Change of variables: the Ornstein–Uhlenbeck semigroup integral is a Gaussian smoothing. -/
lemma ou_substitution (f : ℝ → ℝ) (t : ℝ) (ht : 0 < t) :
    (fun x : ℝ => ∫ y, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2)))
      = fun x : ℝ => smoothed f (gaussKernel (Real.sqrt (1 - Real.exp (-(2 * t)))))
          (Real.exp (-t) * x) := by
  have hs2 : 0 < 1 - Real.exp (-(2 * t)) := by
    have : Real.exp (-(2 * t)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  set c : ℝ := Real.exp (-t) with hc
  set s : ℝ := Real.sqrt (1 - Real.exp (-(2 * t))) with hs
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hs2
  have hsne : s ≠ 0 := ne_of_gt hspos
  funext x
  simp only [smoothed_apply]
  have hA : (∫ y, f (c * x + s * y) * gaussKernel s (c * x - (c * x + s * y)))
      = s⁻¹ * ∫ u, f u * gaussKernel s (c * x - u) := by
    have h1 := Measure.integral_comp_mul_left
      (fun v : ℝ => f (c * x + v) * gaussKernel s (c * x - (c * x + v))) s
    simp only [smul_eq_mul] at h1
    rw [integral_add_left_eq_self (fun u : ℝ => f u * gaussKernel s (c * x - u)) (c * x),
      abs_inv, abs_of_pos hspos] at h1
    exact h1
  have hB : ∀ y : ℝ, f (c * x + s * y) * gaussKernel s (c * x - (c * x + s * y))
      = s⁻¹ * (f (c * x + s * y) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2))) := by
    intro y
    have harg : c * x - (c * x + s * y) = -(s * y) := by ring
    simp only [gaussKernel, harg]
    rw [show (-(s * y)) / s = -y by rw [neg_div, mul_div_cancel_left₀ y hsne],
      show (-y) ^ 2 = y ^ 2 by ring]
    ring
  have hkey : s⁻¹ * (∫ y, f (c * x + s * y) *
        ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2)))
      = s⁻¹ * (∫ u, f u * gaussKernel s (c * x - u)) := by
    have e1 : (∫ y, f (c * x + s * y) * gaussKernel s (c * x - (c * x + s * y)))
        = ∫ y, s⁻¹ * (f (c * x + s * y) *
            ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2))) := by
      apply integral_congr_ae; filter_upwards with y; exact hB y
    rw [← hA, e1, integral_const_mul]
  exact mul_left_cancel₀ (inv_ne_zero hsne) hkey

/-- **The Ornstein–Uhlenbeck semigroup is smoothing**: convolving a bounded measurable function
with a centred Gaussian of positive variance yields a `C^n` function all of whose derivatives up
to `n` are bounded. -/
theorem ou_semigroup_contDiff_bounded (f : ℝ → ℝ) (C : ℝ) (hC : ∀ x : ℝ, |f x| ≤ C)
    (hf : Measurable f) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ n (fun x : ℝ => ∫ y : ℝ, f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2))) ∧
      ∀ k ≤ n, ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ, |iteratedDeriv k (fun x : ℝ => ∫ y : ℝ,
          f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
          * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2))) x| ≤ B := by
  set c : ℝ := Real.exp (-t) with hc
  set s : ℝ := Real.sqrt (1 - Real.exp (-(2 * t))) with hs
  have hs2 : 0 < 1 - Real.exp (-(2 * t)) := by
    have : Real.exp (-(2 * t)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have hspos : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr hs2
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hC0 : 0 ≤ C := le_trans (abs_nonneg (f 0)) (hC 0)
  have hsub := ou_substitution f t ht
  rw [← hc, ← hs] at hsub
  have hκcont : ∀ m : ℕ, ContDiff ℝ m (gaussKernel s) := fun m => contDiff_gaussKernel s m
  have hκint : ∀ m : ℕ, Integrable (iteratedDeriv m (gaussKernel s)) :=
    fun m => integrable_iteratedDeriv_gaussKernel s hsne m
  obtain ⟨hcont, hiter⟩ := smoothed_contDiff hC hf hκcont hκint
  constructor
  · rw [hsub]
    exact (hcont n).comp (by fun_prop : ContDiff ℝ n (fun x : ℝ => c * x))
  · intro k _
    refine ⟨|c| ^ k * (C * ∫ t, |iteratedDeriv k (gaussKernel s) t|),
      mul_nonneg (pow_nonneg (abs_nonneg c) k)
        (mul_nonneg hC0 (integral_nonneg (f := fun t => |iteratedDeriv k (gaussKernel s) t|)
          (fun t => abs_nonneg _))), ?_⟩
    intro x
    rw [hsub, iteratedDeriv_comp_const_mul (hcont k) c, abs_mul, abs_pow, hiter k]
    exact mul_le_mul_of_nonneg_left (abs_smoothed_le hC hf (hκint k) (c * x))
      (pow_nonneg (abs_nonneg c) k)

end

end Commons.Analysis.GaussianMeasure