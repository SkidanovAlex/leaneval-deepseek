/-
# The unit-step trapezoid comparison: `∑_{n=a}^{b} w(n) − ∫_a^b w`

This file proves the elementary single-scale comparison between the sum of a `C²` function
`w : ℝ → ℂ` over the integers of `[a, b]` and its integral:

`‖∑_{n∈[a,b]} w(n) − ∫_a^b w‖ ≤ (1/2)(‖w a‖ + ‖w b‖) + (1/8)∫_a^b ‖w''‖`.

It is used in Area A7 to compare the discrete average `N⁻¹ ∑_{N/2<n≤N} …` with an
oscillatory integral: it is the fixed-scale `k = 1`, second-derivative case of the
Euler–Maclaurin comparison, with the *sharp* kernel constant `1/8` (the Euler–Maclaurin
kernel `B̃₂ = {x}²−{x}+1/6` only gives `1/6`, which is not enough here).

The proof is the standard one:

* The unit-interval (single-trapezoid) comparison `trap_interval_bound`, with the kernel
  `trapKernel c t = (t−c)(c+1−t)/2` (whose modulus is `≤ 1/8` on `[c, c+1]`): writing
  `φ = trapKernel c` and `F t = φ t • w'(t) − φ'(t) • w(t)`, one has `F' t = φ t • w''(t) + w(t)`
  (because `φ'' = −1`), so the fundamental theorem of calculus gives
  `∫_c^{c+1} w = (w c + w(c+1))/2 − ∫_c^{c+1} φ • w''`, whence the claimed bound by
  `‖∫φ•w''‖ ≤ ∫‖φ‖‖w''‖ ≤ (1/8)∫‖w''‖`.
* The bookkeeping lemmas `sum_Icc_eq_endpoints_add_sum_Ico` (endpoint/telescoping identity for
  the sum) and `integral_Icc_eq_sum_Ico_unit` (additivity of the integral over the unit
  sub-intervals with integer endpoints) decompose both sides into the unit pieces.

They are proved in the companion files `Submission/Work/A7/sum_Icc_eq_endpoints_add_sum_Ico.lean`
and `Submission/Work/A7/integral_Icc_eq_sum_Ico_unit.lean`.
-/
import Mathlib
import Submission.Work.A7.integral_Icc_eq_sum_Ico_unit
import Submission.Work.A7.sum_Icc_eq_endpoints_add_sum_Ico

namespace Work.A7

open MeasureTheory intervalIntegral

/-- The quadratic Euler–Maclaurin (trapezoid) kernel of the unit interval `[c, c+1]`,
`trapKernel c t = (t - c) * (c + 1 - t) / 2`.  Its modulus is `≤ 1/8` on `[c, c+1]` and it is the
kernel of the exact single-trapezoid comparison
`∫_c^{c+1} w = (w c + w (c+1))/2 - ∫_c^{c+1} trapKernel c t • w'' t`. -/
noncomputable def trapKernel (c : ℝ) : ℝ → ℝ := fun t => (t - c) * (c + 1 - t) / 2

/-- Derivative of the trapezoid kernel: `(trapKernel c)' t = c + 1/2 - t` (so that the second
derivative is `-1`, which is what makes the antiderivative `F` below have the simple derivative). -/
lemma trapKernel_hasDerivAt (c t : ℝ) : HasDerivAt (trapKernel c) (c + 1/2 - t) t := by
  have hderiv : deriv (trapKernel c) t = c + 1/2 - t := by
    change deriv (fun x : ℝ => (x - c) * (c + 1 - x) / 2) t = c + 1/2 - t
    rw [deriv_div_const]
    change deriv ((fun x : ℝ => x - c) * (fun x : ℝ => c + 1 - x)) t / 2 = c + 1/2 - t
    rw [deriv_mul (by fun_prop) (by fun_prop)]
    rw [deriv_sub_const, deriv_const_sub]
    rw [show deriv (fun x : ℝ => x) t = 1 from by simp]
    ring
  rw [← hderiv]
  exact ((by unfold trapKernel; fun_prop : DifferentiableAt ℝ (trapKernel c) t)).hasDerivAt

/-- Pointwise bound for the trapezoid kernel on its interval: `|trapKernel c t| ≤ 1/8` for
`t ∈ [c, c+1]`.  (The kernel equals `u(1-u)/2` for `u = t - c ∈ [0,1]`, whose maximum is `1/8`.) -/
lemma trapKernel_abs_le {c t : ℝ} (ht : t ∈ Set.Icc c (c+1)) : |trapKernel c t| ≤ 1/8 := by
  obtain ⟨h1, h2⟩ := ht
  have h0 : 0 ≤ trapKernel c t := by
    rw [trapKernel]
    apply div_nonneg
    · exact mul_nonneg (by linarith) (by linarith)
    · norm_num
  rw [abs_of_nonneg h0, trapKernel]
  rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  nlinarith [sq_nonneg (t - c - 1/2)]

/-- **The single-trapezoid comparison on a unit interval**, with the sharp constant `1/8`:

`‖(w c + w (c+1))/2 − ∫_c^{c+1} w‖ ≤ (1/8) ∫_c^{c+1} ‖w''‖`

for `w` of class `C²`.  This is the exact statement obtained from the kernel identity
`∫_c^{c+1} w = (w c + w (c+1))/2 − ∫_c^{c+1} trapKernel c · w''` together with
`|trapKernel c| ≤ 1/8`. -/
lemma trap_interval_bound (g : ℝ → ℂ) (hg : ContDiff ℝ 2 g) (c : ℝ) :
    ‖(g c + g (c+1))/2 - ∫ t in c..(c+1), g t‖
      ≤ (1/8) * ∫ t in c..(c+1), ‖iteratedDeriv 2 g t‖ := by
  have hctrap : Continuous (trapKernel c) := by unfold trapKernel; fun_prop
  have hcg2 : Continuous (iteratedDeriv 2 g) := hg.continuous_iteratedDeriv 2 (by norm_num)
  have hi1 : IntervalIntegrable (fun t => trapKernel c t • iteratedDeriv 2 g t) volume c (c+1) :=
    (hctrap.smul hcg2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable g volume c (c+1) := hg.continuous.intervalIntegrable _ _
  -- The fundamental theorem of calculus for `F t = φ t • w'(t) - φ'(t) • w(t)`,
  -- whose derivative is `φ t • w''(t) + w(t)` because `φ'' = -1`.
  have hderiv : ∀ t ∈ Set.uIcc c (c+1),
      HasDerivAt (fun s : ℝ => trapKernel c s • deriv g s - (c + 1/2 - s) • g s)
        (trapKernel c t • iteratedDeriv 2 g t + g t) t := by
    intro t _
    have hφ := trapKernel_hasDerivAt c t
    have hg1 : HasDerivAt (deriv g) (iteratedDeriv 2 g t) t := by
      have hd : Differentiable ℝ (iteratedDeriv 1 g) :=
        hg.differentiable_iteratedDeriv 1 (by norm_num)
      have h := (hd.differentiableAt (x := t)).hasDerivAt
      rw [iteratedDeriv_one] at h
      have e : iteratedDeriv 2 g = deriv (deriv g) := by
        rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
      rw [e]; exact h
    have hg0 : HasDerivAt g (deriv g t) t :=
      ((hg.differentiable (by norm_num)).differentiableAt (x := t)).hasDerivAt
    have hψ : HasDerivAt (fun s : ℝ => c + 1/2 - s) (-1) t := by
      have hderiv' : deriv (fun s : ℝ => c + 1/2 - s) t = -1 := by
        rw [deriv_const_sub]; simp
      rw [← hderiv']
      exact ((by fun_prop : DifferentiableAt ℝ (fun s : ℝ => c + 1/2 - s) t)).hasDerivAt
    have h3 := (hφ.smul hg1).sub (hψ.smul hg0)
    have heq : trapKernel c t • iteratedDeriv 2 g t + (c + 1/2 - t) • deriv g t
        - ((c + 1/2 - t) • deriv g t + (-1 : ℝ) • g t)
        = trapKernel c t • iteratedDeriv 2 g t + g t := by
      rw [neg_one_smul]; abel
    exact h3.congr_deriv heq
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at hFTC
  -- The endpoint values of the antiderivative: `F (c+1) - F c = (w c + w (c+1))/2`.
  have hFval : ((fun s : ℝ => trapKernel c s • deriv g s - (c + 1/2 - s) • g s) (c+1))
      - ((fun s : ℝ => trapKernel c s • deriv g s - (c + 1/2 - s) • g s) c)
      = (g c + g (c+1))/2 := by
    simp only [trapKernel]
    rw [show c + 1/2 - (c + 1) = -(1/2) from by ring, show c + 1/2 - c = 1/2 from by ring]
    norm_num
    ring
  rw [hFval] at hFTC
  -- The exact kernel identity `(w c + w (c+1))/2 - ∫_c^{c+1} w = ∫_c^{c+1} φ • w''`.
  have hid : (g c + g (c+1))/2 - ∫ t in c..(c+1), g t
      = ∫ t in c..(c+1), trapKernel c t • iteratedDeriv 2 g t := by
    rw [add_comm] at hFTC
    rw [← hFTC]
    abel
  rw [hid]
  have hcontA : Continuous (fun t => |trapKernel c t| * ‖iteratedDeriv 2 g t‖) :=
    hctrap.abs.mul hcg2.norm
  have hcontB : Continuous (fun t => (1/8) * ‖iteratedDeriv 2 g t‖) :=
    continuous_const.mul hcg2.norm
  calc ‖∫ t in c..(c+1), trapKernel c t • iteratedDeriv 2 g t‖
      ≤ ∫ t in c..(c+1), ‖trapKernel c t • iteratedDeriv 2 g t‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ = ∫ t in c..(c+1), |trapKernel c t| * ‖iteratedDeriv 2 g t‖ := by
        refine intervalIntegral.integral_congr (fun t _ => ?_)
        rw [norm_smul, Real.norm_eq_abs]
    _ ≤ ∫ t in c..(c+1), (1/8) * ‖iteratedDeriv 2 g t‖ := by
        refine intervalIntegral.integral_mono_on (by linarith) ?_ ?_ ?_
        · exact hcontA.intervalIntegrable _ _
        · exact hcontB.intervalIntegrable _ _
        · intro t ht
          exact mul_le_mul_of_nonneg_right (trapKernel_abs_le ht) (norm_nonneg _)
    _ = (1/8) * ∫ t in c..(c+1), ‖iteratedDeriv 2 g t‖ := by
        rw [intervalIntegral.integral_const_mul]

/-- **The unit-step trapezoid comparison for a sum over the integers of `[a, b]`.**

For `w : ℝ → ℂ` of class `C²` and integers `a ≤ b`,

`‖∑_{n∈[a,b]} w(n) − ∫_a^b w‖ ≤ (1/2)(‖w a‖ + ‖w b‖) + (1/8)∫_a^b ‖w''‖`.

This is the Euler–Maclaurin comparison at step `1` with the sharp `1/8` constant, obtained by
splitting the sum and the integral into unit pieces and applying `trap_interval_bound` to each. -/
theorem ModelApproxCore_trapezoid (w : ℝ → ℂ) (hw : ContDiff ℝ 2 w) {a b : ℤ} (hab : a ≤ b) :
    ‖(∑ n ∈ Finset.Icc a b, w (n : ℝ)) - ∫ t in (a : ℝ)..(b : ℝ), w t‖
      ≤ (1 / 2) * (‖w (a : ℝ)‖ + ‖w (b : ℝ)‖)
        + (1 / 8) * ∫ t in (a : ℝ)..(b : ℝ), ‖iteratedDeriv 2 w t‖ := by
  classical
  have hsum := sum_Icc_eq_endpoints_add_sum_Ico w hab
  have hint := integral_Icc_eq_sum_Ico_unit w hw.continuous hab
  -- Split the sum at the endpoints and the integral over the unit sub-intervals.
  have hdecomp : (∑ n ∈ Finset.Icc a b, w (n : ℝ)) - ∫ t in (a : ℝ)..(b : ℝ), w t
      = (w (a:ℝ) + w (b:ℝ))/2
        + ∑ n ∈ Finset.Ico a b,
            ((w (n:ℝ) + w ((n:ℝ)+1))/2 - ∫ t in (n:ℝ)..((n:ℝ)+1), w t) := by
    rw [hsum, hint, Finset.sum_sub_distrib]
    ring
  rw [hdecomp]
  have hend : ‖(w (a:ℝ) + w (b:ℝ))/2‖ ≤ (1/2) * (‖w (a:ℝ)‖ + ‖w (b:ℝ)‖) := by
    rw [norm_div, show ‖(2:ℂ)‖ = 2 from by norm_num, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
    nlinarith [norm_add_le (w (a:ℝ)) (w (b:ℝ))]
  -- Additivity of the integral of `‖w''‖` over the unit sub-intervals (deduced from the
  -- complex-valued tiling identity via `intervalIntegral.integral_ofReal`).
  have hR : (∑ n ∈ Finset.Ico a b, ∫ t in (n:ℝ)..((n:ℝ)+1), ‖iteratedDeriv 2 w t‖)
      = ∫ t in (a:ℝ)..(b:ℝ), ‖iteratedDeriv 2 w t‖ := by
    have hcont : Continuous (fun t => ((‖iteratedDeriv 2 w t‖ : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((hw.continuous_iteratedDeriv 2 (by norm_num)).norm)
    have hC := integral_Icc_eq_sum_Ico_unit (fun t => ((‖iteratedDeriv 2 w t‖ : ℝ) : ℂ)) hcont hab
    simp only [intervalIntegral.integral_ofReal] at hC
    rw [← Complex.ofReal_sum] at hC
    exact (Complex.ofReal_inj).mp hC.symm
  calc ‖(w (a:ℝ) + w (b:ℝ))/2
        + ∑ n ∈ Finset.Ico a b,
            ((w (n:ℝ) + w ((n:ℝ)+1))/2 - ∫ t in (n:ℝ)..((n:ℝ)+1), w t)‖
      ≤ ‖(w (a:ℝ) + w (b:ℝ))/2‖
        + ‖∑ n ∈ Finset.Ico a b,
            ((w (n:ℝ) + w ((n:ℝ)+1))/2 - ∫ t in (n:ℝ)..((n:ℝ)+1), w t)‖ :=
        norm_add_le _ _
    _ ≤ ‖(w (a:ℝ) + w (b:ℝ))/2‖
        + ∑ n ∈ Finset.Ico a b,
            ‖((w (n:ℝ) + w ((n:ℝ)+1))/2 - ∫ t in (n:ℝ)..((n:ℝ)+1), w t)‖ :=
        add_le_add (le_refl _) (norm_sum_le _ _)
    _ ≤ (1/2) * (‖w (a:ℝ)‖ + ‖w (b:ℝ)‖)
        + ∑ n ∈ Finset.Ico a b,
            (1/8) * ∫ t in (n:ℝ)..((n:ℝ)+1), ‖iteratedDeriv 2 w t‖ :=
        add_le_add hend (Finset.sum_le_sum (fun n _ => trap_interval_bound w hw (n:ℝ)))
    _ = (1/2) * (‖w (a:ℝ)‖ + ‖w (b:ℝ)‖)
        + (1/8) * ∑ n ∈ Finset.Ico a b,
            ∫ t in (n:ℝ)..((n:ℝ)+1), ‖iteratedDeriv 2 w t‖ := by
        rw [Finset.mul_sum]
    _ = (1/2) * (‖w (a:ℝ)‖ + ‖w (b:ℝ)‖)
        + (1/8) * ∫ t in (a:ℝ)..(b:ℝ), ‖iteratedDeriv 2 w t‖ := by
        rw [hR]

end Work.A7
