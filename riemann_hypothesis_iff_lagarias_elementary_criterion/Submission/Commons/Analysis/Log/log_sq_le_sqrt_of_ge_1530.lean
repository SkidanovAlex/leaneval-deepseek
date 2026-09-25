import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Log

noncomputable section

/-- Explicit upper bound `log 1530 ≤ 7.3330307`, obtained from the factorization
`1530 = 3 · 2⁹ · (1 - 1/256)` together with Mathlib's explicit bounds on
`log 2`, `log 3` and the elementary bound `log (1 - 1/256) ≤ -1/256`. -/
private lemma log_1530_ub : Real.log 1530 ≤ 7.3330307 := by
  have hdecomp : Real.log 1530 = Real.log 3 + 9 * Real.log 2 + Real.log (1 - 1/256) := by
    have h1530 : (1530:ℝ) = 3 * 2^9 * (1 - 1/256) := by norm_num
    rw [h1530, Real.log_mul (by norm_num) (by norm_num),
        Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    ring
  have hlogsub : Real.log (1 - 1/256) ≤ -(1/256:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 - 1/256 by norm_num)
    linarith
  rw [hdecomp]
  linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, hlogsub]

/-- Lower bound `√1530 ≥ 39.1152`. -/
private lemma sqrt_1530_lb : (39.1152 : ℝ) ≤ Real.sqrt 1530 := by
  rw [Real.le_sqrt (by norm_num) (by norm_num)]
  norm_num

/-- For `x ≥ 1296`, `log x ≤ √x / 3`: with `s = √x ≥ 36` we have
`exp (s/6) ≥ (s/6)³/6 = s³/1296 ≥ s`, hence `log s ≤ s/6` and `log x = 2 log s ≤ s/3`. -/
private lemma log_le_sqrt_div_three {x : ℝ} (hx : (1296:ℝ) ≤ x) : Real.log x ≤ Real.sqrt x / 3 := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hx0
  have hs36 : (36:ℝ) ≤ Real.sqrt x := by
    rw [Real.le_sqrt (by norm_num) hx0.le]
    nlinarith [hx]
  have hs6 : Real.log (Real.sqrt x) ≤ Real.sqrt x / 6 := by
    rw [Real.log_le_iff_le_exp hs0]
    have hpow : (Real.sqrt x / 6)^3 / 6 ≤ Real.exp (Real.sqrt x / 6) := by
      have h := Real.pow_div_factorial_le_exp (Real.sqrt x / 6) (by positivity) 3
      rw [show (Nat.factorial 3 : ℝ) = 6 by norm_num] at h
      exact h
    have hge : Real.sqrt x ≤ (Real.sqrt x / 6)^3 / 6 := by
      have hsq : (36:ℝ)^2 ≤ (Real.sqrt x)^2 := by
        rw [Real.sq_sqrt hx0.le]; linarith
      nlinarith [hs0, hsq]
    linarith
  have hlogx : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx0.le]; ring
  rw [hlogx]
  linarith

/-- The auxiliary function `F x = 1.37478 · √x - (log x)²`; the target inequality is
`0 ≤ F x` for `x ≥ 1530`. -/
private def F (x : ℝ) : ℝ := 1.37478 * Real.sqrt x - (Real.log x)^2

/-- Derivative of `F` at a positive point. -/
private lemma F_hasDerivAt (x : ℝ) (hx : 0 < x) :
    HasDerivAt F (1.37478 * (1/(2*Real.sqrt x)) - 2*Real.log x * x⁻¹) x := by
  have hxne : x ≠ 0 := ne_of_gt hx
  have h1 : HasDerivAt (fun y => (1.37478:ℝ) * Real.sqrt y) (1.37478 * (1/(2*Real.sqrt x))) x :=
    (Real.hasDerivAt_sqrt hxne).const_mul 1.37478
  have h2 : HasDerivAt (Real.log ^ 2) (2 * Real.log x * x⁻¹) x :=
    ((Real.hasDerivAt_log hxne).pow 2).congr_deriv (by norm_num)
  have hsub := h1.sub h2
  have hev : F =ᶠ[nhds x] ((fun y => (1.37478:ℝ) * Real.sqrt y) - Real.log^2) := by
    filter_upwards with y
    simp [F, Pi.sub_apply, Pi.pow_apply]
  exact hsub.congr_of_eventuallyEq hev

/-- `F` has nonnegative derivative on `[1530, ∞)`: using `log x ≤ √x/3` we get
`2 log x / x ≤ 2/(3 √x) ≤ 1.37478/(2 √x)`. -/
private lemma F_deriv_nonneg {x : ℝ} (hx : (1530:ℝ) ≤ x) :
    0 ≤ 1.37478 * (1/(2*Real.sqrt x)) - 2*Real.log x * x⁻¹ := by
  have hx0 : 0 < x := by linarith
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos_of_pos hx0
  have hlog : Real.log x ≤ Real.sqrt x / 3 := log_le_sqrt_div_three (by linarith)
  have hle1 : 2 * Real.log x * x⁻¹ ≤ 2 * (Real.sqrt x / 3) * x⁻¹ := by
    have hfac : (0:ℝ) ≤ 2 * x⁻¹ := by positivity
    have hh := mul_le_mul_of_nonneg_left hlog hfac
    nlinarith [hh]
  have hle2 : 2 * (Real.sqrt x / 3) * x⁻¹ = 2 / (3 * Real.sqrt x) := by
    have hsq : (Real.sqrt x)^2 = x := Real.sq_sqrt hx0.le
    field_simp
    nlinarith [hsq]
  have heq : 1.37478 * (1 / (2 * Real.sqrt x)) - 2 * (Real.sqrt x / 3) * x⁻¹
      = (1.37478/2 - 2/3) / Real.sqrt x := by
    rw [hle2]
    field_simp
  have hnonneg : (0:ℝ) ≤ (1.37478/2 - 2/3) / Real.sqrt x := by
    apply div_nonneg _ hs0.le
    norm_num
  calc (0:ℝ) ≤ (1.37478/2 - 2/3) / Real.sqrt x := hnonneg
    _ = 1.37478 * (1/(2*Real.sqrt x)) - 2 * (Real.sqrt x/3) * x⁻¹ := heq.symm
    _ ≤ 1.37478 * (1/(2*Real.sqrt x)) - 2 * Real.log x * x⁻¹ := by linarith [hle1]

/-- `F` is nondecreasing on `[1530, ∞)`. -/
private lemma F_mono : MonotoneOn F (Set.Ici (1530:ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 1530)
  · change ContinuousOn (fun x => (1.37478:ℝ) * Real.sqrt x - (Real.log x)^2) (Set.Ici (1530:ℝ))
    apply ContinuousOn.sub
    · exact (continuous_const.mul Real.continuous_sqrt).continuousOn
    · apply ContinuousOn.pow
      apply Real.continuousOn_log.mono
      intro x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have := Set.mem_Ici.mp hx
      linarith
  · rw [interior_Ici]
    intro x hx
    have hx0 : 0 < x := by have := Set.mem_Ioi.mp hx; linarith
    exact (F_hasDerivAt x hx0).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro x hx
    have hx0 : (1530:ℝ) ≤ x := by have := Set.mem_Ioi.mp hx; linarith
    rw [(F_hasDerivAt x (by linarith : 0 < x)).deriv]
    exact F_deriv_nonneg hx0

/-- For x ≥ 1530 the elementary bound `(log x)^2 ≤ 1.37478 * sqrt x` holds.
This follows from the antitonicity of `x ↦ (log x)^2 / sqrt x` on `[1530, ∞)`
(its derivative is `(log x)(2 - (log x)/2) / (2 x^{3/2}) ≤ 0` for `log x ≥ 4`)
and the numeric evaluation at `x = 1530`. -/
theorem log_sq_le_sqrt_of_ge_1530 (x : ℝ) (hx : 1530 ≤ x) :
    (Real.log x) ^ 2 ≤ 1.37478 * Real.sqrt x := by
  have hxmem : x ∈ Set.Ici (1530:ℝ) := hx
  have h1 : F 1530 ≤ F x := F_mono (by norm_num) hxmem hx
  have hF1530 : 0 ≤ F 1530 := by
    have hub : Real.log 1530 ≤ 7.3330307 := log_1530_ub
    have hlb : (39.1152 : ℝ) ≤ Real.sqrt 1530 := sqrt_1530_lb
    have hlogpos : 0 ≤ Real.log 1530 := Real.log_nonneg (by norm_num)
    have hsq : (Real.log 1530)^2 ≤ (7.3330307:ℝ)^2 := by nlinarith [hub, hlogpos]
    have hrhs : 1.37478 * 39.1152 ≤ 1.37478 * Real.sqrt 1530 := by nlinarith [hlb]
    have key : (7.3330307:ℝ)^2 ≤ 1.37478 * 39.1152 := by norm_num
    simp only [F]
    linarith
  simp only [F] at h1 hF1530
  linarith

end

end Commons.Analysis.Log