import Mathlib
import Submission.Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm
import Submission.Commons.Analysis.Convex.prekopa_leindler_inequality

namespace Commons.Analysis.Convex

open MeasureTheory

/-! ### Auxiliary lemmas -/

/-- The squared norm is convex along a convex combination: for `a, b ≥ 0` with `a + b = 1`,
`‖a • p + b • q‖ ^ 2 ≤ a * ‖p‖ ^ 2 + b * ‖q‖ ^ 2`. This is the "log-concavity of the
Gaussian" ingredient behind the Prékopa–Leindler argument for the log-Laplace penalty. -/
lemma norm_sq_convex_combination {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (p q : V) :
    ‖a • p + b • q‖ ^ 2 ≤ a * ‖p‖ ^ 2 + b * ‖q‖ ^ 2 := by
  have h1 : ‖a • p + b • q‖ ≤ a * ‖p‖ + b * ‖q‖ := by
    calc ‖a • p + b • q‖ ≤ ‖a • p‖ + ‖b • q‖ := norm_add_le _ _
      _ = a * ‖p‖ + b * ‖q‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have h2 : (a * ‖p‖ + b * ‖q‖) ^ 2 ≤ a * ‖p‖ ^ 2 + b * ‖q‖ ^ 2 := by
    have h3 := (Even.convexOn_pow (𝕜 := ℝ) (n := 2) (by decide)).2 (x := ‖p‖) (Set.mem_univ _)
      (y := ‖q‖) (Set.mem_univ _) ha hb hab
    simpa using h3
  calc ‖a • p + b • q‖ ^ 2 ≤ (a * ‖p‖ + b * ‖q‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ a * ‖p‖ ^ 2 + b * ‖q‖ ^ 2 := h2

/-- For a positive base, the `rpow` of an exponential is again an exponential. -/
private lemma exp_rpow (y c : ℝ) : (Real.exp y) ^ c = Real.exp (y * c) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp]

/-- **Log-concavity of the Gaussian kernel in `rpow` form.** For `a, b ≥ 0` with `a + b = 1`
and `ε > 0`,
`(exp (-‖p‖²/ε²))^a * (exp (-‖q‖²/ε²))^b ≤ exp (-‖a • p + b • q‖²/ε²)`. -/
lemma exp_neg_norm_sq_logconcave {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {ε : ℝ} (hε : 0 < ε) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (p q : V) :
    (Real.exp (-‖p‖ ^ 2 / ε ^ 2)) ^ a * (Real.exp (-‖q‖ ^ 2 / ε ^ 2)) ^ b
      ≤ Real.exp (-‖a • p + b • q‖ ^ 2 / ε ^ 2) := by
  have hε2 : (0:ℝ) < ε ^ 2 := pow_pos hε 2
  have hA : ‖a • p + b • q‖ ^ 2 ≤ a * ‖p‖ ^ 2 + b * ‖q‖ ^ 2 :=
    norm_sq_convex_combination ha hb hab p q
  have harg : (-(a * ‖p‖ ^ 2 + b * ‖q‖ ^ 2)) / ε ^ 2
      = -(a * ‖p‖ ^ 2 / ε ^ 2) + -(b * ‖q‖ ^ 2 / ε ^ 2) := by
    field_simp; ring
  calc (Real.exp (-‖p‖ ^ 2 / ε ^ 2)) ^ a * (Real.exp (-‖q‖ ^ 2 / ε ^ 2)) ^ b
      = Real.exp (-‖p‖ ^ 2 / ε ^ 2 * a) * Real.exp (-‖q‖ ^ 2 / ε ^ 2 * b) := by
          rw [exp_rpow, exp_rpow]
    _ = Real.exp (-‖p‖ ^ 2 / ε ^ 2 * a + -‖q‖ ^ 2 / ε ^ 2 * b) := (Real.exp_add _ _).symm
    _ = Real.exp ((-(a * ‖p‖ ^ 2 + b * ‖q‖ ^ 2)) / ε ^ 2) := by
          congr 1
          rw [harg]; ring
    _ ≤ Real.exp (-‖a • p + b • q‖ ^ 2 / ε ^ 2) := by
          apply Real.exp_le_exp.mpr
          rw [neg_div, neg_div]
          exact neg_le_neg (div_le_div_of_nonneg_right hA hε2.le)

/-- Integrability of the (translated) Gaussian kernel `y ↦ exp (-‖x - y‖²/ε²)` on
`EuclideanSpace ℝ (Fin n)`. -/
lemma integrable_gaussian_translate {n : ℕ} {ε : ℝ} (hε : 0 < ε)
    (x : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) => Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)) := by
  have hε2 : (0:ℝ) < 1 / ε ^ 2 := by positivity
  have hbase : Integrable (fun z : EuclideanSpace ℝ (Fin n) => Real.exp (-(1/ε^2) * ‖z‖^2)) :=
    Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm (1/ε^2) hε2
  have htrans : Integrable (fun t : EuclideanSpace ℝ (Fin n) => Real.exp (-(1/ε^2) * ‖t - x‖^2)) :=
    hbase.comp_sub_right x
  refine htrans.congr (ae_of_all _ (fun y => ?_))
  simp only []
  congr 1
  rw [norm_sub_rev]
  field_simp

/-! ### The main theorem -/

/-- **Convexity of the log-Laplace penalty.**

For a convex measurable set `A ⊆ ℝ^n` and `ε > 0`, the log-Laplace (Moreau–Yosida smoothed)
penalty
`x ↦ -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))`
is convex on `ℝ^n`.

Equivalently, `F x = ∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2)` is log-concave on `ℝ^n`.

This is the classical "the convolution of log-concave functions is log-concave" theorem: `F = 1_A ⋆ g`
with `1_A` log-concave (because `A` is convex) and `g y = Real.exp (-‖y‖ ^ 2 / ε ^ 2)` log-concave.

Proof: Prékopa–Leindler (`Commons.Analysis.Convex.prekopa_leindler_inequality`) applied to
`f u = exp (-‖x - u‖²/ε²) * 1_A u`, `g v = exp (-‖x' - v‖²/ε²) * 1_A v` and
`h w = exp (-‖z - w‖²/ε²) * 1_A w` with `z = (1 - t) • x + t • x'`.  The pointwise hypothesis is
the conjunction of the convexity of `A` (`1_A z ≥ (1_A u)^(1-t) (1_A v)^t`) and the log-concavity
of the Gaussian (`exp_neg_norm_sq_logconcave`), using that
`z - ((1 - t) • u + t • v) = (1 - t) • (x - u) + t • (x' - v)`. -/
theorem convexOn_logLaplace (n : ℕ) {ε : ℝ} (hε : 0 < ε)
    (A : Set (EuclideanSpace ℝ (Fin n))) (hAm : MeasurableSet A) (hA : Convex ℝ A) :
    ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) =>
      -Real.log (∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2))) := by
  classical
  set F : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => ∫ y in A, Real.exp (-‖x - y‖ ^ 2 / ε ^ 2) with hF
  -- Pointwise description of `F` as the integral of `exp (-‖x - ·‖²/ε²) * 1_A`.
  have hconv : ∀ x : EuclideanSpace ℝ (Fin n),
      (∫ u, Real.exp (-‖x - u‖ ^ 2 / ε ^ 2) * A.indicator (fun _ => (1:ℝ)) u) = F x := by
    intro x
    rw [hF]
    simp only []
    rw [← MeasureTheory.integral_indicator (s := A)
      (f := fun u => Real.exp (-‖x - u‖ ^ 2 / ε ^ 2)) hAm]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with u
    by_cases hu : u ∈ A
    · rw [Set.indicator_of_mem hu, Set.indicator_of_mem hu, mul_one]
    · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem hu, mul_zero]
  have hnng : ∀ x : EuclideanSpace ℝ (Fin n),
      ∀ u, 0 ≤ Real.exp (-‖x - u‖ ^ 2 / ε ^ 2) * A.indicator (fun _ => (1:ℝ)) u := by
    intro x u
    by_cases hu : u ∈ A
    · rw [Set.indicator_of_mem hu, mul_one]; exact Real.exp_nonneg _
    · rw [Set.indicator_of_notMem hu, mul_zero]
  have hint : ∀ x : EuclideanSpace ℝ (Fin n),
      Integrable (fun u => Real.exp (-‖x - u‖ ^ 2 / ε ^ 2) * A.indicator (fun _ => (1:ℝ)) u) := by
    intro x
    refine (integrable_gaussian_translate hε x).mono' ?_ (ae_of_all _ (fun u => ?_))
    · exact ((Continuous.measurable (by fun_prop)).mul
        (measurable_const.indicator hAm)).aestronglyMeasurable
    · by_cases hu : u ∈ A
      · rw [Set.indicator_of_mem hu, mul_one, Real.norm_eq_abs,
          abs_of_nonneg (Real.exp_nonneg _)]
      · rw [Set.indicator_of_notMem hu, mul_zero, norm_zero]
        exact Real.exp_nonneg _
  by_cases hnull : volume A = 0
  · -- Null `A`: the integral, hence the penalty, vanishes identically.
    have hF0 : ∀ x, F x = 0 := by
      intro x
      rw [hF]
      simp only []
      rw [Measure.restrict_eq_zero.mpr hnull]
      simp
    have hfun : (fun x : EuclideanSpace ℝ (Fin n) => -Real.log (F x)) = fun _ => (0:ℝ) := by
      funext x; rw [hF0 x, Real.log_zero, neg_zero]
    rw [hfun]
    exact convexOn_const 0 convex_univ
  · have hApos : 0 < volume A := pos_iff_ne_zero.mpr hnull
    -- Positivity of `F`: the integrand is everywhere positive on the positive-measure set `A`.
    have hpos : ∀ x : EuclideanSpace ℝ (Fin n), 0 < F x := by
      intro x
      have hsupp : Function.support
          (A.indicator (fun u => Real.exp (-‖x - u‖ ^ 2 / ε ^ 2))) = A := by
        ext u
        rw [Function.mem_support]
        by_cases hu : u ∈ A
        · rw [Set.indicator_of_mem hu]
          exact iff_of_true (Real.exp_ne_zero _) hu
        · rw [Set.indicator_of_notMem hu]
          exact iff_of_false (fun h => h rfl) hu
      have hnn : 0 ≤ᵐ[volume] (A.indicator (fun u => Real.exp (-‖x - u‖ ^ 2 / ε ^ 2))) :=
        ae_of_all _ (fun u => Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) u)
      have hint' : Integrable (A.indicator (fun u => Real.exp (-‖x - u‖ ^ 2 / ε ^ 2))) := by
        refine (integrable_gaussian_translate hε x).mono' ?_ (ae_of_all _ (fun u => ?_))
        · exact ((Continuous.measurable (by fun_prop)).indicator hAm).aestronglyMeasurable
        · rw [Real.norm_eq_abs]
          by_cases hu : u ∈ A
          · rw [Set.indicator_of_mem hu, abs_of_nonneg (Real.exp_nonneg _)]
          · rw [Set.indicator_of_notMem hu, abs_zero]; exact Real.exp_nonneg _
      have hsupppos : 0 < volume (Function.support
          (A.indicator (fun u => Real.exp (-‖x - u‖ ^ 2 / ε ^ 2)))) := by
        rw [hsupp]; exact hApos
      have hpp := (integral_pos_iff_support_of_nonneg_ae hnn hint').mpr hsupppos
      rw [hF]
      simp only []
      rw [← MeasureTheory.integral_indicator (s := A)
        (f := fun u => Real.exp (-‖x - u‖ ^ 2 / ε ^ 2)) hAm]
      exact hpp
    -- Log-concavity of `F`, from Prékopa–Leindler.
    have hlogconc : ∀ (x x' : EuclideanSpace ℝ (Fin n)) (t : ℝ), 0 ≤ t → t ≤ 1 →
        F ((1 - t) • x + t • x') ≥ F x ^ (1 - t) * F x' ^ t := by
      intro x x' t ht0 ht1
      rcases eq_or_lt_of_le ht0 with rfl | ht0p
      · simp
      rcases eq_or_lt_of_le ht1 with rfl | ht1l
      · simp
      have ht1pos : 0 < 1 - t := by linarith
      set z := (1 - t) • x + t • x' with hzdef
      have hz_eq : ∀ u v : EuclideanSpace ℝ (Fin n),
          z - ((1 - t) • u + t • v) = (1 - t) • (x - u) + t • (x' - v) := by
        intro u v
        rw [hzdef]; module
      have hhyp : ∀ u v : EuclideanSpace ℝ (Fin n),
          (fun w => Real.exp (-‖z - w‖ ^ 2 / ε ^ 2) * A.indicator (fun _ => (1:ℝ)) w)
              ((1 - t) • u + t • v)
            ≥ (fun u => Real.exp (-‖x - u‖ ^ 2 / ε ^ 2) * A.indicator (fun _ => (1:ℝ)) u) u ^ (1 - t)
              * (fun v => Real.exp (-‖x' - v‖ ^ 2 / ε ^ 2)
                  * A.indicator (fun _ => (1:ℝ)) v) v ^ t := by
        intro u v
        simp only []
        by_cases hu : u ∈ A
        · by_cases hv : v ∈ A
          · have hzmem : (1 - t) • u + t • v ∈ A :=
              hA hu hv (by linarith) ht0 (by ring)
            rw [Set.indicator_of_mem hu, Set.indicator_of_mem hv, Set.indicator_of_mem hzmem,
                mul_one, mul_one, mul_one, hz_eq u v]
            exact exp_neg_norm_sq_logconcave hε (by linarith) ht0 (by ring) (x - u) (x' - v)
          · rw [Set.indicator_of_notMem hv, mul_zero, Real.zero_rpow (ne_of_gt ht0p), mul_zero]
            exact mul_nonneg (Real.exp_nonneg _)
              (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
        · rw [Set.indicator_of_notMem hu, mul_zero, Real.zero_rpow (ne_of_gt ht1pos), zero_mul]
          exact mul_nonneg (Real.exp_nonneg _)
            (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      have hkey := prekopa_leindler_inequality
        (fun u => Real.exp (-‖x - u‖ ^ 2 / ε ^ 2) * A.indicator (fun _ => (1:ℝ)) u)
        (fun v => Real.exp (-‖x' - v‖ ^ 2 / ε ^ 2) * A.indicator (fun _ => (1:ℝ)) v)
        (fun w => Real.exp (-‖z - w‖ ^ 2 / ε ^ 2) * A.indicator (fun _ => (1:ℝ)) w)
        t ht0 ht1 (hnng x) (hnng x') (hnng z) (hint x) (hint x') (hint z) hhyp
      rw [hconv x, hconv x', hconv z] at hkey
      exact hkey
    -- From log-concavity of the positive function `F`, `-log F` is convex.
    rw [convexOn_iff_forall_pos]
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ a b ha hb hab
    have ha_eq : a = 1 - b := by linarith
    have hgoal_eq : a • x + b • y = (1 - b) • x + b • y := by rw [ha_eq]
    rw [hgoal_eq]
    have hbc : b ≤ 1 := by linarith
    have hlog := hlogconc x y b hb.le hbc
    have hFx := hpos x
    have hFy := hpos y
    have hposz : 0 < F x ^ (1 - b) * F y ^ b :=
      mul_pos (Real.rpow_pos_of_pos hFx _) (Real.rpow_pos_of_pos hFy _)
    have hkey2 : (1 - b) * Real.log (F x) + b * Real.log (F y)
        ≤ Real.log (F ((1 - b) • x + b • y)) := by
      have h1 := Real.log_le_log hposz hlog
      rwa [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hFx _))
            (ne_of_gt (Real.rpow_pos_of_pos hFy _)),
           Real.log_rpow hFx, Real.log_rpow hFy] at h1
    rw [ha_eq]
    calc -Real.log (F ((1 - b) • x + b • y))
        ≤ -((1 - b) * Real.log (F x) + b * Real.log (F y)) := neg_le_neg hkey2
      _ = (1 - b) * -Real.log (F x) + b * -Real.log (F y) := by ring

end Commons.Analysis.Convex
