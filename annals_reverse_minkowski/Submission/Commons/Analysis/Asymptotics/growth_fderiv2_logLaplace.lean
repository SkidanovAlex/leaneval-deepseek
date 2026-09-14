import Mathlib
import Submission.Commons.Analysis.Convex.convexOn_logLaplace
import Submission.Commons.Analysis.Convex.contDiff_logLaplace_penalty
import Submission.Commons.Analysis.Convex.fderiv2_nonneg_of_convexOn
import Submission.Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_apply_add
import Submission.Commons.Measure.Integral.integral_rpow_mul_rpow_le

namespace Commons.Analysis.Asymptotics

open MeasureTheory

noncomputable section

/-! ## Elementary helpers -/

/-- `(exp u) ^ s = exp (u * s)`: the exponential is positive, so `rpow` is ordinary exponentiation. -/
private lemma exp_rpow (u s : ℝ) : (Real.exp u) ^ s = Real.exp (u * s) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp]

/-- The second derivative of the squared norm, as a quadratic form. -/
lemma fderiv2_norm_sq_apply (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x v : E) :
    fderiv ℝ (fderiv ℝ (fun x : E => ‖x‖ ^ 2)) x v v = 2 * ‖v‖ ^ 2 := by
  rw [fderiv_norm_sq]
  have key : fderiv ℝ (2 • ⇑(innerSL ℝ)) x = (2:ℝ) • (innerSL ℝ : E →L[ℝ] (E →L[ℝ] ℝ)) := by
    rw [show (2 • ⇑(innerSL ℝ) : E → (E →L[ℝ] ℝ))
          = ⇑((2:ℝ) • (innerSL ℝ : E →L[ℝ] (E →L[ℝ] ℝ))) from by
      ext y; simp [smul_apply]]
    exact ContinuousLinearMap.fderiv _
  rw [key]
  simp only [smul_apply, smul_eq_mul]
  have hv : ((innerSL ℝ) v) v = ‖v‖ ^ 2 := by rw [innerSL_apply_apply, real_inner_self_eq_norm_sq]
  rw [hv]

/-- `fderiv ℝ (fderiv ℝ f) x v v` is the iterated second derivative at `(v, v)`. -/
lemma fderiv_fderiv_eq_iteratedFDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → ℝ) (x v : E) :
    fderiv ℝ (fderiv ℝ f) x v v = iteratedFDeriv ℝ 2 f x ![v, v] :=
  (iteratedFDeriv_two_apply f x ![v, v]).symm

/-- Second derivative of `‖x‖ ^ 2` in quadratic-form form, via `iteratedFDeriv`. -/
lemma iteratedFDeriv_two_norm_sq_apply (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x v : E) :
    iteratedFDeriv ℝ 2 (fun x : E => ‖x‖ ^ 2) x ![v, v] = 2 * ‖v‖ ^ 2 := by
  rw [← fderiv2_norm_sq_apply E x v]
  exact iteratedFDeriv_two_apply (fun x : E => ‖x‖ ^ 2) x ![v, v]

/-- Second derivative of `c * ‖x‖ ^ 2` in quadratic-form form. -/
lemma iteratedFDeriv_two_mul_norm_sq (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (c : ℝ) (x v : E) :
    iteratedFDeriv ℝ 2 (fun x : E => c * ‖x‖ ^ 2) x ![v, v] = 2 * c * ‖v‖ ^ 2 := by
  have hcd : ContDiffAt ℝ (2 : WithTop ℕ∞) (fun x : E => ‖x‖ ^ 2) x :=
    (ContDiff.norm_sq ℝ (contDiff_id (𝕜 := ℝ))).contDiffAt
  have hfun : (fun x : E => c * ‖x‖ ^ 2) = c • (fun x : E => ‖x‖ ^ 2) := by
    funext y; simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun, iteratedFDeriv_const_smul_apply (i := 2) (a := c) hcd]
  simp only [smul_apply, smul_eq_mul, iteratedFDeriv_two_norm_sq_apply]
  ring

/-- Second derivative of `‖x‖ ^ 2 / ε ^ 2` in quadratic-form form. -/
lemma iteratedFDeriv_two_div_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ε : ℝ} (x v : E) :
    iteratedFDeriv ℝ 2 (fun x : E => ‖x‖ ^ 2 / ε ^ 2) x ![v, v] = (2 / ε ^ 2) * ‖v‖ ^ 2 := by
  have hfun : (fun x : E => ‖x‖ ^ 2 / ε ^ 2) = fun x : E => (1 / ε ^ 2) * ‖x‖ ^ 2 := by
    funext y; rw [div_eq_mul_inv, one_div, mul_comm]
  rw [hfun, iteratedFDeriv_two_mul_norm_sq]
  ring

/-- Second derivative of a pointwise negation, in quadratic-form form. -/
lemma iteratedFDeriv_two_neg_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x a b : E} (hf : ContDiffAt ℝ 2 f x) :
    (iteratedFDeriv ℝ 2 (fun z : E => -f z) x) ![a, b]
      = -((iteratedFDeriv ℝ 2 f x) ![a, b]) := by
  have hfun : (fun z : E => -f z) = (-1 : ℝ) • f := by
    funext z; simp [Pi.smul_apply, smul_eq_mul]
  rw [hfun, iteratedFDeriv_const_smul_apply (i := 2) (a := (-1 : ℝ)) hf]
  simp only [smul_apply, smul_eq_mul, neg_one_mul]

/-! ## The Laplace transform weight -/

/-- The weighted Laplace transform `Λ x = ∫_A exp (2 ⟪x, y⟫ / ε²) exp (-‖y‖² / ε²) dy`,
appearing in the decomposition `∫_A exp (-‖x - y‖²/ε²) = exp (-‖x‖²/ε²) · Λ x`. -/
def gaussLaplaceWeight (n : ℕ) (A : Set (EuclideanSpace ℝ (Fin n))) (ε : ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => ∫ y in A, Real.exp (2 * inner ℝ x y / ε ^ 2) * Real.exp (-‖y‖ ^ 2 / ε ^ 2)

variable {n : ℕ} {ε : ℝ}

/-- The integrand of `gaussLaplaceWeight` is integrable (a Gaussian times an exponential of a
linear functional). -/
lemma integrable_exp_inner_gauss (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      Real.exp (2 * inner ℝ x y / ε ^ 2) * Real.exp (-‖y‖ ^ 2 / ε ^ 2)) volume := by
  have hc : (0:ℝ) < 1 / ε ^ 2 := by positivity
  have hbase : Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      Real.exp ((2 * ‖x‖ / ε ^ 2) * ‖y‖) * Real.exp (-(1 / ε ^ 2) * ‖y‖ ^ 2)) volume :=
    Commons.Analysis.Convex.integrable_exp_mul_exp_neg_sq (1 / ε ^ 2) (2 * ‖x‖ / ε ^ 2) hc
  refine hbase.mono' ?_ ?_
  · apply Continuous.aestronglyMeasurable
    fun_prop
  · filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))]
    refine mul_le_mul ?_ ?_ (Real.exp_nonneg _) (Real.exp_nonneg _)
    · apply Real.exp_le_exp.mpr
      have h1 : inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
      calc 2 * inner ℝ x y / ε ^ 2 ≤ 2 * (‖x‖ * ‖y‖) / ε ^ 2 := by gcongr
        _ = (2 * ‖x‖ / ε ^ 2) * ‖y‖ := by ring
    · apply Real.exp_le_exp.mpr
      have hee : -(1 / ε ^ 2) * ‖y‖ ^ 2 = -‖y‖ ^ 2 / ε ^ 2 := by
        rw [div_eq_mul_inv]; ring
      rw [hee]

/-- **Decomposition of the log-Laplace integral.** Completing the square,
`∫_A exp (-‖x - y‖²/ε²) = exp (-‖x‖²/ε²) · Λ x`. -/
lemma setIntegral_exp_neg_sq_eq_gaussLaplaceWeight (hε : 0 < ε)
    (A : Set (EuclideanSpace ℝ (Fin n))) (hAm : MeasurableSet A)
    (x : EuclideanSpace ℝ (Fin n)) :
    (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))
      = Real.exp (-‖x‖ ^ 2 / ε ^ 2) * gaussLaplaceWeight n A ε x := by
  have hpt : ∀ y : EuclideanSpace ℝ (Fin n),
      Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)
        = Real.exp (-‖x‖ ^ 2 / ε ^ 2)
          * (Real.exp (2 * inner ℝ x y / ε ^ 2) * Real.exp (-‖y‖ ^ 2 / ε ^ 2)) := by
    intro y
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [norm_sub_sq_real]
    field_simp
    ring
  rw [gaussLaplaceWeight]
  rw [← integral_const_mul]
  exact setIntegral_congr_fun hAm (fun y _ => hpt y)

/-- Pointwise `rpow` identity: the `(1-t, t)` weighted product of the two Laplace integrands
at `x` and `x'` is the Laplace integrand at `(1-t) • x + t • x'`. -/
lemma rpow_weight_mul_eq (x x' : EuclideanSpace ℝ (Fin n)) (t : ℝ)
    (y : EuclideanSpace ℝ (Fin n)) :
    (Real.exp (2 * inner ℝ x y / ε ^ 2) * Real.exp (-‖y‖ ^ 2 / ε ^ 2)) ^ (1 - t)
      * (Real.exp (2 * inner ℝ x' y / ε ^ 2) * Real.exp (-‖y‖ ^ 2 / ε ^ 2)) ^ t
    = Real.exp (2 * inner ℝ ((1 - t) • x + t • x') y / ε ^ 2)
        * Real.exp (-‖y‖ ^ 2 / ε ^ 2) := by
  rw [Real.mul_rpow (Real.exp_nonneg _) (Real.exp_nonneg _),
      Real.mul_rpow (Real.exp_nonneg _) (Real.exp_nonneg _)]
  rw [exp_rpow, exp_rpow, exp_rpow, exp_rpow]
  conv_rhs => rw [← Real.exp_add]
  rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, Real.exp_eq_exp]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  field_simp
  ring

/-- **Log-convexity of the Laplace transform weight**, from Hölder's inequality. -/
lemma gaussLaplaceWeight_logConvex (hε : 0 < ε) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hAm : MeasurableSet A) :
    ∀ x x' : EuclideanSpace ℝ (Fin n), ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      gaussLaplaceWeight n A ε ((1 - t) • x + t • x')
        ≤ (gaussLaplaceWeight n A ε x) ^ (1 - t) * (gaussLaplaceWeight n A ε x') ^ t := by
  intro x x' t ht0 ht1
  rcases eq_or_lt_of_le ht0 with h0 | ht0'
  · rw [← h0]; simp
  rcases eq_or_lt_of_le ht1 with h1 | ht1'
  · rw [h1]; simp
  set F : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => Real.exp (2 * inner ℝ x y / ε ^ 2) * Real.exp (-‖y‖ ^ 2 / ε ^ 2) with hFdef
  set G : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => Real.exp (2 * inner ℝ x' y / ε ^ 2) * Real.exp (-‖y‖ ^ 2 / ε ^ 2) with hGdef
  have hpt : ∀ y, (Real.exp (2 * inner ℝ x y / ε ^ 2) * Real.exp (-‖y‖ ^ 2 / ε ^ 2)) ^ (1 - t)
      * (Real.exp (2 * inner ℝ x' y / ε ^ 2) * Real.exp (-‖y‖ ^ 2 / ε ^ 2)) ^ t
      = Real.exp (2 * inner ℝ ((1 - t) • x + t • x') y / ε ^ 2)
        * Real.exp (-‖y‖ ^ 2 / ε ^ 2) := fun y => rpow_weight_mul_eq x x' t y
  have hHolder := Commons.Measure.Integral.integral_rpow_mul_rpow_le
    (μ := volume.restrict A) ht0' ht1'
    (f := fun y => Real.exp (2 * inner ℝ x y / ε ^ 2) * Real.exp (-‖y‖ ^ 2 / ε ^ 2))
    (g := fun y => Real.exp (2 * inner ℝ x' y / ε ^ 2) * Real.exp (-‖y‖ ^ 2 / ε ^ 2))
    (Filter.Eventually.of_forall (fun y => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)))
    (Filter.Eventually.of_forall (fun y => mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)))
    (Continuous.aemeasurable (by fun_prop))
    (Continuous.aemeasurable (by fun_prop))
    ((integrable_exp_inner_gauss hε A x).integrableOn)
    ((integrable_exp_inner_gauss hε A x').integrableOn)
    (((integrable_exp_inner_gauss hε A ((1 - t) • x + t • x')).integrableOn).congr
      (Filter.Eventually.of_forall (fun y => (hpt y).symm)))
  have hL : ∫ a in A, (Real.exp (2 * inner ℝ x a / ε ^ 2) * Real.exp (-‖a‖ ^ 2 / ε ^ 2)) ^ (1 - t)
        * (Real.exp (2 * inner ℝ x' a / ε ^ 2) * Real.exp (-‖a‖ ^ 2 / ε ^ 2)) ^ t
      = gaussLaplaceWeight n A ε ((1 - t) • x + t • x') := by
    rw [gaussLaplaceWeight]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  have hFx : (∫ a in A, Real.exp (2 * inner ℝ x a / ε ^ 2) * Real.exp (-‖a‖ ^ 2 / ε ^ 2))
      = gaussLaplaceWeight n A ε x := rfl
  have hFx' : (∫ a in A, Real.exp (2 * inner ℝ x' a / ε ^ 2) * Real.exp (-‖a‖ ^ 2 / ε ^ 2))
      = gaussLaplaceWeight n A ε x' := rfl
  rw [hL, hFx, hFx'] at hHolder
  exact hHolder

/-- Log-convexity of a positive function implies convexity of its logarithm. -/
lemma convexOn_log_of_logConvex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Λ : E → ℝ} (hpos : ∀ x, 0 < Λ x)
    (hlog : ∀ x y : E, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Λ ((1 - t) • x + t • y) ≤ Λ x ^ (1 - t) * Λ y ^ t) :
    ConvexOn ℝ Set.univ (fun x => Real.log (Λ x)) := by
  rw [convexOn_iff_forall_pos]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hb1 : b ≤ 1 := by linarith
  have hab' : a = 1 - b := by linarith
  have key : Real.log (Λ ((1 - b) • x + b • y))
      ≤ (1 - b) * Real.log (Λ x) + b * Real.log (Λ y) := by
    have h' : Λ ((1 - b) • x + b • y) ≤ Λ x ^ (1 - b) * Λ y ^ b := hlog x y b hb.le hb1
    calc Real.log (Λ ((1 - b) • x + b • y)) ≤ Real.log (Λ x ^ (1 - b) * Λ y ^ b) :=
          Real.log_le_log (hpos _) h'
      _ = (1 - b) * Real.log (Λ x) + b * Real.log (Λ y) := by
          rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos (hpos x) _))
                (ne_of_gt (Real.rpow_pos_of_pos (hpos y) _)),
              Real.log_rpow (hpos x), Real.log_rpow (hpos y)]
  rw [hab', smul_eq_mul, smul_eq_mul]
  exact key

/-- **Polynomial (indeed uniform) bound on the second derivative of the log-Laplace penalty.**

For a convex measurable set `A ⊆ ℝ^n` of positive measure and `ε > 0`, the second derivative of
`φ x = -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))` satisfies a quadratic-form bound:
`|(fderiv ℝ (fderiv ℝ φ) x v) v| ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2` for all `x, v`; here
`0 ≤ (fderiv ℝ (fderiv ℝ φ) x v) v ≤ (2 / ε ^ 2) * ‖v‖ ^ 2`. -/
theorem growth_fderiv2_logLaplace (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (A : Set (EuclideanSpace ℝ (Fin n))) (hAm : MeasurableSet A) (hA : Convex ℝ A)
    (hApos : 0 < volume A)
    (hpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < ∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N : ℕ, ∀ x v : EuclideanSpace ℝ (Fin n),
      |fderiv ℝ (fderiv ℝ
          (fun x => -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)))) x v v|
        ≤ C * (1 + ‖x‖) ^ N * ‖v‖ ^ 2 := by
  classical
  set φ : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) with hφdef
  set Λ : EuclideanSpace ℝ (Fin n) → ℝ := gaussLaplaceWeight n A ε with hΛdef
  -- Completing the square: `F x = exp (-‖x‖²/ε²) · Λ x`.
  have hdecomp : ∀ x : EuclideanSpace ℝ (Fin n),
      (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) = Real.exp (-‖x‖ ^ 2 / ε ^ 2) * Λ x := by
    intro x
    rw [hΛdef]
    exact setIntegral_exp_neg_sq_eq_gaussLaplaceWeight hε A hAm x
  -- Positivity of `Λ`.
  have hΛpos : ∀ x, 0 < Λ x := by
    intro x
    have h := hpos x
    rw [hdecomp x] at h
    exact (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp h
  -- `φ x = ‖x‖²/ε² - log (Λ x)`.
  have hφsplit : ∀ x, φ x = ‖x‖ ^ 2 / ε ^ 2 + -Real.log (Λ x) := by
    intro x
    rw [hφdef]
    change -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))
      = ‖x‖ ^ 2 / ε ^ 2 + -Real.log (Λ x)
    rw [hdecomp x]
    rw [Real.log_mul (ne_of_gt (Real.exp_pos _)) (ne_of_gt (hΛpos x)), Real.log_exp]
    ring
  -- Smoothness and convexity of `φ` (from the commons).
  have hφcd : ContDiff ℝ 2 φ := by
    have htop : ContDiff ℝ ⊤ φ := by
      rw [hφdef]
      exact Commons.Analysis.Convex.contDiff_logLaplace_penalty n hε A hAm hpos
    exact htop.of_le le_top
  have hφconv : ConvexOn ℝ Set.univ φ := by
    rw [hφdef]
    exact Commons.Analysis.Convex.convexOn_logLaplace n hε A hAm hA
  -- Log-convexity of `Λ`, hence convexity of `log ∘ Λ`.
  have hΛlogconv : ∀ x x' : EuclideanSpace ℝ (Fin n), ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      Λ ((1 - t) • x + t • x') ≤ (Λ x) ^ (1 - t) * (Λ x') ^ t := by
    intro x x' t h0 h1
    simpa only [hΛdef] using gaussLaplaceWeight_logConvex hε A hAm x x' t h0 h1
  have hlogΛconv : ConvexOn ℝ Set.univ (fun x => Real.log (Λ x)) :=
    convexOn_log_of_logConvex hΛpos hΛlogconv
  have hqcd : ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 / ε ^ 2) :=
    (ContDiff.norm_sq ℝ (contDiff_id (𝕜 := ℝ))).div_const (ε ^ 2)
  have hlogΛcd : ContDiff ℝ 2 (fun x => Real.log (Λ x)) := by
    have hfun : (fun x : EuclideanSpace ℝ (Fin n) => Real.log (Λ x))
        = fun x => ‖x‖ ^ 2 / ε ^ 2 - φ x := by
      funext x
      rw [hφsplit x]
      ring
    rw [hfun]
    exact hqcd.sub hφcd
  have hψcd : ContDiff ℝ 2 (fun x => -Real.log (Λ x)) := hlogΛcd.neg
  refine ⟨2 / ε ^ 2, by positivity, 0, ?_⟩
  intro x v
  rw [pow_zero, mul_one, abs_le]
  refine ⟨?_, ?_⟩
  · -- lower bound: convexity of `φ`
    have h0 : 0 ≤ fderiv ℝ (fderiv ℝ φ) x v v :=
      Commons.Analysis.Convex.fderiv2_nonneg_of_convexOn φ hφcd hφconv x v
    have hC : (0 : ℝ) ≤ 2 / ε ^ 2 := by positivity
    nlinarith [h0, sq_nonneg ‖v‖]
  · -- upper bound: `D²φ = (2/ε²) • I - D²(log ∘ Λ)`
    have hsplit : fderiv ℝ (fderiv ℝ φ) x v v
        = fderiv ℝ (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 / ε ^ 2)) x v v
          + fderiv ℝ (fderiv ℝ (fun x => -Real.log (Λ x))) x v v := by
      rw [fderiv_fderiv_eq_iteratedFDeriv, fderiv_fderiv_eq_iteratedFDeriv,
          fderiv_fderiv_eq_iteratedFDeriv]
      rw [show φ = (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 / ε ^ 2)
            + (fun x => -Real.log (Λ x)) from by
        funext x; rw [hφsplit x]; simp [Pi.add_apply]]
      exact Commons.Analysis.Calculus.FDeriv.iteratedFDeriv_two_apply_add
        hqcd.contDiffAt hψcd.contDiffAt
    have hq2 : fderiv ℝ (fderiv ℝ (fun x : EuclideanSpace ℝ (Fin n) => ‖x‖ ^ 2 / ε ^ 2)) x v v
        = (2 / ε ^ 2) * ‖v‖ ^ 2 := by
      rw [fderiv_fderiv_eq_iteratedFDeriv]
      exact iteratedFDeriv_two_div_norm_sq x v
    have hψ2 : fderiv ℝ (fderiv ℝ (fun x => -Real.log (Λ x))) x v v ≤ 0 := by
      have h1 : 0 ≤ fderiv ℝ (fderiv ℝ (fun x => Real.log (Λ x))) x v v :=
        Commons.Analysis.Convex.fderiv2_nonneg_of_convexOn _ hlogΛcd hlogΛconv x v
      rw [fderiv_fderiv_eq_iteratedFDeriv (fun x => Real.log (Λ x)) x v] at h1
      rw [fderiv_fderiv_eq_iteratedFDeriv]
      rw [iteratedFDeriv_two_neg_apply (f := fun x : EuclideanSpace ℝ (Fin n) => Real.log (Λ x))
        hlogΛcd.contDiffAt]
      linarith
    rw [hsplit, hq2]
    linarith

end

end Commons.Analysis.Asymptotics
