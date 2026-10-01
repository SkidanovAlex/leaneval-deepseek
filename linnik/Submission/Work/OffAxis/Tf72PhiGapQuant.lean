/-
# OffAxis — the quantitative gap lower bound for HB Lemma 7.2 at `λ = 6/7`

`Work.ZeroFreeTables.tf72fPhi lam = ∫_0^{7/3} exp (lam t) * tf72fK t dt`, where
`tf72fK t = (1 - 2 exp (-(6/7) t)) * tf72f (6/7) t` is the signed kernel of the `F`-method
gap for Heath-Brown's test function `tf72f (6/7)` (supported on `[0, 7/3]`).

The goal is the *quantitative* lower bound

  `(104/66825) * (6/7 - lam) ≤ tf72fPhi (6/7) - tf72fPhi lam`   for `0 ≤ lam ≤ 6/7`.

The chain of ideas is short.

* Since `tf72fPhi lam = ∫ exp (lam t) * tf72fK t dt`, its derivative is
  `tf72fPhi' x = ∫ t * (exp (x t) * tf72fK t) dt` (`tf72fK_hasDerivAt`).
* The kernel changes sign exactly once, at `τ = (7/6) log 2`, so freezing the weight at `τ`
  and splitting the integral there compares the weighted `t`-moment with the unweighted one:

    `exp (x τ) * M ≤ tf72fPhi' x`,   `M = ∫_0^{7/3} t * tf72fK t`,

  for `x ≥ 0` (the same weight-freezing argument as in `tf72f_gap_mono`).
* `M ≥ 104/66825 > 0` (quartic Taylor bound for `exp` plus the moments of `tf72f (6/7)`)
  and `exp (x τ) ≥ 1`, hence `tf72fPhi' x ≥ 104/66825` on `[0, ∞)`.
* Therefore `s ↦ tf72fPhi s - (104/66825) * s` is non-decreasing on `[0, ∞)`
  (`monotoneOn_of_deriv_nonneg`), which is the assertion after rearranging.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.tf72fK_defs
import Submission.Work.ZeroFreeTables.tf72fK_hasDerivAt
import Submission.Work.ZeroFreeTables.tf72fK_t_moment_nonneg
import Submission.Work.ZeroFreeTables.tf72f_moment
import Submission.Work.ZeroFreeTables.testFn72_defs

open scoped Interval
open MeasureTheory

noncomputable section
namespace Work.OffAxis

open Work.ZeroFreeTables

/-! ## 1.  The first moment of the signed kernel is at least `104/66825` -/

/-- The signed kernel `tf72fK` has first moment `∫_0^{7/3} t · tf72fK t ≥ 104/66825`.

This is the sharp form of `Work.ZeroFreeTables.tf72fK_t_moment_nonneg`: the quartic Taylor
bound `exp (-x) ≤ 1 - x + x²/2 - x³/6 + x⁴/24` gives the pointwise bound
`poly t * tf72f (6/7) t ≤ t * tf72fK t` with the quintic
`poly t = -t + (12/7) t² - (36/49) t³ + (72/343) t⁴ - (108/2401) t⁵`, and the integral of
`poly * tf72f (6/7)` equals exactly `104/66825`. -/
lemma tf72fK_moment_ge :
    (104/66825 : ℝ) ≤ ∫ t in (0:ℝ)..(7/3), t * tf72fK t := by
  have hab : (0:ℝ) ≤ 7/3 := by norm_num
  have hcontf : ContinuousOn (fun t : ℝ => tf72f (6/7) t) (Set.uIcc (0:ℝ) (7/3)) := by
    refine (tf72f_cont (6/7) (by norm_num)).mono ?_
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ht.1
  have hcontK : ContinuousOn (fun t : ℝ => t * tf72fK t) (Set.uIcc (0:ℝ) (7/3)) := by
    have hexp : Continuous (fun t : ℝ => (1:ℝ) - 2 * Real.exp (-(6/7) * t)) := by fun_prop
    have h : ContinuousOn (fun t : ℝ => (t * ((1:ℝ) - 2 * Real.exp (-(6/7) * t)))
        * tf72f (6/7) t) (Set.uIcc (0:ℝ) (7/3)) :=
      (continuous_id.continuousOn.mul hexp.continuousOn).mul hcontf
    simpa only [tf72fK, mul_assoc] using h
  have hcontL : ContinuousOn (fun t : ℝ => (((-1:ℝ) * t^1 + (12/7) * t^2 + (-(36/49)) * t^3
      + (72/343) * t^4 + (-(108/2401)) * t^5) * tf72f (6/7) t))
      (Set.uIcc (0:ℝ) (7/3)) :=
    (by fun_prop : Continuous (fun t : ℝ => ((-1:ℝ) * t^1 + (12/7) * t^2 + (-(36/49)) * t^3
      + (72/343) * t^4 + (-(108/2401)) * t^5))).continuousOn.mul hcontf
  have hintK : IntervalIntegrable (fun t : ℝ => t * tf72fK t) volume (0:ℝ) (7/3) :=
    hcontK.intervalIntegrable
  have hintL : IntervalIntegrable (fun t : ℝ => (((-1:ℝ) * t^1 + (12/7) * t^2 + (-(36/49)) * t^3
      + (72/343) * t^4 + (-(108/2401)) * t^5) * tf72f (6/7) t))
      volume (0:ℝ) (7/3) := hcontL.intervalIntegrable
  have hle := intervalIntegral.integral_mono_on hab hintL hintK
    (fun t ht => tf72fK_t_moment_pointwise t (Set.mem_Icc.mp ht).1)
  have hval : (∫ t in (0:ℝ)..(7/3), (((-1:ℝ) * t^1 + (12/7) * t^2 + (-(36/49)) * t^3
      + (72/343) * t^4 + (-(108/2401)) * t^5) * tf72f (6/7) t)) = 104/66825 :=
    tf72fK_moment_lincomb
  linarith

/-! ## 2.  The single sign change of the kernel at `τ = (7/6) log 2` -/

/-- The point where the kernel changes sign: `exp ((6/7) t) = 2`. -/
private def tau : ℝ := (7/6) * Real.log 2

private lemma tau_nonneg : 0 ≤ tau := by
  have h : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold tau
  nlinarith

private lemma tau_le : tau ≤ 7/3 := by
  have h : Real.log 2 ≤ 1 := by
    have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  unfold tau
  linarith

private lemma exp_sixsevenths_tau : Real.exp ((6/7) * tau) = 2 := by
  have h : (6/7) * tau = Real.log 2 := by unfold tau; ring
  rw [h, Real.exp_log (by norm_num)]

/-- `tf72fK` is continuous on the interval of integration. -/
private lemma tf72fK_contOn : ContinuousOn tf72fK (Set.Icc (0:ℝ) (7/3)) := by
  unfold tf72fK
  exact ContinuousOn.mul (by fun_prop)
    ((tf72f_cont (6/7) (by norm_num)).mono Set.Icc_subset_Ici_self)

/-- On `[0, τ]` the kernel is non-positive. -/
private lemma tf72fK_nonpos_of_le_tau (t : ℝ) (ht : t ≤ tau) : tf72fK t ≤ 0 := by
  have hexp : Real.exp ((6/7) * t) ≤ 2 := by
    have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 6/7))
    rwa [exp_sixsevenths_tau] at h
  have hone : 1 ≤ 2 * Real.exp (-(6/7) * t) := by
    have hmul : Real.exp (-(6/7) * t) * Real.exp ((6/7) * t) = 1 := by
      rw [← Real.exp_add, show -(6/7) * t + (6/7) * t = 0 by ring, Real.exp_zero]
    have hle : Real.exp (-(6/7) * t) * Real.exp ((6/7) * t)
        ≤ Real.exp (-(6/7) * t) * 2 :=
      mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    linarith
  have hf : 0 ≤ tf72f (6/7) t := tf72f_nonneg (6/7) (by norm_num) t
  unfold tf72fK
  nlinarith [hone, hf]

/-- On `[τ, ∞)` the kernel is non-negative. -/
private lemma tf72fK_nonneg_of_tau_le (t : ℝ) (ht : tau ≤ t) : 0 ≤ tf72fK t := by
  have hexp : 2 ≤ Real.exp ((6/7) * t) := by
    have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (by norm_num : (0:ℝ) ≤ 6/7))
    rwa [exp_sixsevenths_tau] at h
  have hone : 2 * Real.exp (-(6/7) * t) ≤ 1 := by
    have hmul : Real.exp (-(6/7) * t) * Real.exp ((6/7) * t) = 1 := by
      rw [← Real.exp_add, show -(6/7) * t + (6/7) * t = 0 by ring, Real.exp_zero]
    have hle : Real.exp (-(6/7) * t) * 2 ≤ Real.exp (-(6/7) * t) * Real.exp ((6/7) * t) :=
      mul_le_mul_of_nonneg_left hexp (Real.exp_pos _).le
    linarith
  have hf : 0 ≤ tf72f (6/7) t := tf72f_nonneg (6/7) (by norm_num) t
  unfold tf72fK
  nlinarith [hone, hf]

/-- Weighted comparison on the negative part `[0, τ]`: since `t * tf72fK t ≤ 0` there and
`exp (x t) ≤ exp (x τ)` for `x ≥ 0`, the weight-frozen integrand is the smaller one. -/
private lemma weight_le_left (x t : ℝ) (hx : 0 ≤ x) (ht0 : 0 ≤ t) (htt : t ≤ tau) :
    t * (Real.exp (x * tau) * tf72fK t) ≤ t * (Real.exp (x * t) * tf72fK t) := by
  have hexp : Real.exp (x * t) ≤ Real.exp (x * tau) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htt hx)
  have hK : tf72fK t ≤ 0 := tf72fK_nonpos_of_le_tau t htt
  have htK : t * tf72fK t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht0 hK
  calc t * (Real.exp (x * tau) * tf72fK t)
      = Real.exp (x * tau) * (t * tf72fK t) := by ring
    _ ≤ Real.exp (x * t) * (t * tf72fK t) := mul_le_mul_of_nonpos_right hexp htK
    _ = t * (Real.exp (x * t) * tf72fK t) := by ring

/-- Weighted comparison on the positive part `[τ, 7/3]`. -/
private lemma weight_le_right (x t : ℝ) (hx : 0 ≤ x) (htt : tau ≤ t) :
    t * (Real.exp (x * tau) * tf72fK t) ≤ t * (Real.exp (x * t) * tf72fK t) := by
  have hexp : Real.exp (x * tau) ≤ Real.exp (x * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left htt hx)
  have hK : 0 ≤ tf72fK t := tf72fK_nonneg_of_tau_le t htt
  have ht0 : 0 ≤ t := le_trans tau_nonneg htt
  have htK : 0 ≤ t * tf72fK t := mul_nonneg ht0 hK
  calc t * (Real.exp (x * tau) * tf72fK t)
      = Real.exp (x * tau) * (t * tf72fK t) := by ring
    _ ≤ Real.exp (x * t) * (t * tf72fK t) := mul_le_mul_of_nonneg_right hexp htK
    _ = t * (Real.exp (x * t) * tf72fK t) := by ring

/-- A function continuous on `[0, 7/3]` is interval integrable on every subinterval. -/
private lemma icc_integrable {g : ℝ → ℝ} (hg : ContinuousOn g (Set.Icc (0:ℝ) (7/3)))
    {a b : ℝ} (h0 : 0 ≤ a) (hab : a ≤ b) (h3 : b ≤ 7/3) : IntervalIntegrable g volume a b :=
  (hg.mono (Set.Icc_subset_Icc h0 h3)).intervalIntegrable_of_Icc hab

/-- **Weight freezing at `τ`.**  For `x ≥ 0`, the weighted `t`-moment against `tf72fK` is at
least the weight-frozen integral `exp (x τ) * M`, `M = ∫_0^{7/3} t * tf72fK t`. -/
private lemma moment_frozen_le (x : ℝ) (hx : 0 ≤ x) :
    (∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * tau) * tf72fK t))
      ≤ ∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * t) * tf72fK t) := by
  have hG : ContinuousOn (fun t : ℝ => t * (Real.exp (x * t) * tf72fK t))
      (Set.Icc (0:ℝ) (7/3)) :=
    ContinuousOn.mul (by fun_prop) (ContinuousOn.mul (by fun_prop) tf72fK_contOn)
  have hH : ContinuousOn (fun t : ℝ => t * (Real.exp (x * tau) * tf72fK t))
      (Set.Icc (0:ℝ) (7/3)) :=
    ContinuousOn.mul (by fun_prop) (ContinuousOn.mul (by fun_prop) tf72fK_contOn)
  have iG1 : IntervalIntegrable
      (fun t : ℝ => t * (Real.exp (x * t) * tf72fK t)) volume (0:ℝ) tau :=
    icc_integrable hG le_rfl tau_nonneg tau_le
  have iG2 : IntervalIntegrable
      (fun t : ℝ => t * (Real.exp (x * t) * tf72fK t)) volume tau (7/3) :=
    icc_integrable hG tau_nonneg tau_le (by norm_num)
  have iH1 : IntervalIntegrable
      (fun t : ℝ => t * (Real.exp (x * tau) * tf72fK t)) volume (0:ℝ) tau :=
    icc_integrable hH le_rfl tau_nonneg tau_le
  have iH2 : IntervalIntegrable
      (fun t : ℝ => t * (Real.exp (x * tau) * tf72fK t)) volume tau (7/3) :=
    icc_integrable hH tau_nonneg tau_le (by norm_num)
  have e1 : (∫ t in (0:ℝ)..tau, t * (Real.exp (x * tau) * tf72fK t))
      ≤ ∫ t in (0:ℝ)..tau, t * (Real.exp (x * t) * tf72fK t) :=
    intervalIntegral.integral_mono_on tau_nonneg iH1 iG1
      (fun t ht => weight_le_left x t hx ht.1 ht.2)
  have e2 : (∫ t in tau..(7/3), t * (Real.exp (x * tau) * tf72fK t))
      ≤ ∫ t in tau..(7/3), t * (Real.exp (x * t) * tf72fK t) :=
    intervalIntegral.integral_mono_on tau_le iH2 iG2
      (fun t ht => weight_le_right x t hx ht.1)
  calc (∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * tau) * tf72fK t))
      = (∫ t in (0:ℝ)..tau, t * (Real.exp (x * tau) * tf72fK t))
          + ∫ t in tau..(7/3), t * (Real.exp (x * tau) * tf72fK t) :=
        (intervalIntegral.integral_add_adjacent_intervals iH1 iH2).symm
    _ ≤ (∫ t in (0:ℝ)..tau, t * (Real.exp (x * t) * tf72fK t))
          + ∫ t in tau..(7/3), t * (Real.exp (x * t) * tf72fK t) := add_le_add e1 e2
    _ = ∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * t) * tf72fK t) :=
        intervalIntegral.integral_add_adjacent_intervals iG1 iG2

/-! ## 3.  The derivative lower bound and monotonicity of the shifted gap -/

/-- **Derivative lower bound.**  For `x ≥ 0`,
`tf72fPhi' x = ∫ t * exp (x t) * tf72fK t ≥ 104/66825`. -/
private lemma deriv_lower (x : ℝ) (hx : 0 ≤ x) :
    (104/66825 : ℝ) ≤ ∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * t) * tf72fK t) := by
  have hM : (104/66825 : ℝ) ≤ ∫ t in (0:ℝ)..(7/3), t * tf72fK t := tf72fK_moment_ge
  have hM0 : (0:ℝ) ≤ ∫ t in (0:ℝ)..(7/3), t * tf72fK t :=
    le_trans (by norm_num : (0:ℝ) ≤ 104/66825) hM
  have hfrozen := moment_frozen_le x hx
  have hfrozen_eq :
      (∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * tau) * tf72fK t))
        = Real.exp (x * tau) * (∫ t in (0:ℝ)..(7/3), t * tf72fK t) := by
    rw [show (∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * tau) * tf72fK t))
        = ∫ t in (0:ℝ)..(7/3), Real.exp (x * tau) * (t * tf72fK t) from by
      apply intervalIntegral.integral_congr
      intro t _
      ring]
    rw [intervalIntegral.integral_const_mul]
  have hexp_ge_one : (1:ℝ) ≤ Real.exp (x * tau) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hx tau_nonneg)
  have hstep : (∫ t in (0:ℝ)..(7/3), t * tf72fK t)
      ≤ ∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * t) * tf72fK t) := by
    calc (∫ t in (0:ℝ)..(7/3), t * tf72fK t)
        ≤ Real.exp (x * tau) * (∫ t in (0:ℝ)..(7/3), t * tf72fK t) :=
          le_mul_of_one_le_left hM0 hexp_ge_one
      _ = ∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * tau) * tf72fK t) := hfrozen_eq.symm
      _ ≤ ∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * t) * tf72fK t) := hfrozen
  linarith

/-- **Monotonicity of the shifted gap.**  `s ↦ tf72fPhi s - (104/66825) * s` is non-decreasing
on `[0, ∞)`, because its derivative is `tf72fPhi' s - 104/66825 ≥ 0` there. -/
private lemma phi_sub_monotone :
    MonotoneOn (fun s : ℝ => tf72fPhi s - (104/66825 : ℝ) * s) (Set.Ici 0) := by
  have hdiff : ∀ x : ℝ, HasDerivAt (fun s : ℝ => tf72fPhi s - (104/66825 : ℝ) * s)
      ((∫ t in (0:ℝ)..(7/3), t * (Real.exp (x * t) * tf72fK t)) - 104/66825) x := by
    intro x
    exact (tf72fK_hasDerivAt x).sub (hasDerivAt_const_mul (x := x) (104/66825))
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0) ?_ ?_ ?_
  · intro x _
    exact (hdiff x).continuousAt.continuousWithinAt
  · intro x _
    exact ((hdiff x).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [(hdiff x).deriv]
    have hx0 : 0 ≤ x := Set.mem_Ici.mp (interior_subset hx)
    have h := deriv_lower x hx0
    linarith

/-! ## 4.  The theorem -/

theorem Tf72PhiGapQuant (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 6/7) :
    (104/66825 : ℝ) * (6/7 - lam)
      ≤ Work.ZeroFreeTables.tf72fPhi (6/7) - Work.ZeroFreeTables.tf72fPhi lam := by
  have hmono := phi_sub_monotone (Set.mem_Ici.mpr h0)
    (Set.mem_Ici.mpr (by norm_num : (0:ℝ) ≤ 6/7)) h1
  linarith

end Work.OffAxis
