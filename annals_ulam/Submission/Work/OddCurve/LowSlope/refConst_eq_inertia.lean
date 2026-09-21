import Mathlib
import Submission.Work.OddCurve.LowSlope.Defs

/-!
# `refConst n = (2n+1) * ballInertiaConst n`

Integration-by-parts identity of the low-slope chapter of the odd-dimensional case: the moment
constant of the unit ball at slope `0`,

`refConst n = ∫_{-1}^{1} (1-u²)^n √(1-u²) du`,

equals `(2n+1)` times the ball's inertia constant

`ballInertiaConst n = ∫_{-1}^{1} u² (1-u²)^{n-1} √(1-u²) du`.

The proof is the elementary one: with `F u = u * (1-u²)^n √(1-u²)` one has, on `(-1,1)`,
`F' u = (1-u²)^n √(1-u²) - (2n+1) u² (1-u²)^{n-1} √(1-u²)`, and `F (±1) = 0`; the fundamental
theorem of calculus on `[-1,1]` gives the identity. -/

namespace Work.OddCurve.LowSlope

open MeasureTheory Set Filter
open scoped Topology Interval

set_option maxHeartbeats 1600000

/-- The pointwise algebraic identity behind the integration by parts: if `s = √(1-u²)` (so
`s * s = 1 - u²`, `s ≠ 0`) then the derivative of `u ↦ u (1-u²)^n √(1-u²)` computed by the product
rule equals `(1-u²)^n √(1-u²) - (2n+1) u² (1-u²)^{n-1} √(1-u²)`. -/
private lemma key_identity (n : ℕ) (hn : 1 ≤ n) {s u : ℝ} (hs : s ≠ 0) (hss : s * s = 1 - u ^ 2) :
    (1 - u ^ 2) ^ n * s + u * (n * (1 - u ^ 2) ^ (n - 1) * (0 - 2 * u) * s
        + (1 - u ^ 2) ^ n * ((0 - 2 * u) / (2 * s)))
      = (1 - u ^ 2) ^ n * s - (2 * (n : ℝ) + 1) * (u ^ 2 * (1 - u ^ 2) ^ (n - 1) * s) := by
  have hpow : (1 - u ^ 2) ^ n = (1 - u ^ 2) ^ (n - 1) * (1 - u ^ 2) := by
    conv_lhs => rw [show n = (n - 1) + 1 by omega]
    rw [pow_succ]
  rw [hpow, ← hss]
  field_simp
  ring

theorem refConst_eq_inertia (n : ℕ) (hn : 1 ≤ n) :
    Work.OddCurve.refConst n =
      (2 * (n : ℝ) + 1) * Work.OddCurve.LowSlope.ballInertiaConst n := by
  have hn0 : n ≠ 0 := by omega
  set c : ℝ := 2 * (n : ℝ) + 1 with hc
  -- the antiderivative `F` and its derivative on the interior of `[-1,1]`
  have hderiv : ∀ u ∈ Set.Ioo (-1 : ℝ) 1,
      HasDerivAt (fun u : ℝ => u * ((1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2)))
        ((1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2)
          - c * (u ^ 2 * (1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2))) u := by
    intro u hu
    have hpos : 0 < 1 - u ^ 2 := by
      have h1 := hu.1; have h2 := hu.2; nlinarith
    set s : ℝ := Real.sqrt (1 - u ^ 2) with hsdef
    have hss : s * s = 1 - u ^ 2 := by
      rw [hsdef]
      simpa [sq] using Real.sq_sqrt (le_of_lt hpos)
    have hsne : s ≠ 0 := by
      rw [hsdef]; exact ne_of_gt (Real.sqrt_pos_of_pos hpos)
    have hbase : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (0 - 2 * u) u := by
      have h := (hasDerivAt_const (x := u) (c := (1 : ℝ))).sub ((hasDerivAt_id u).pow 2)
      have hfun : ((fun _ : ℝ => (1 : ℝ)) - id ^ 2) = fun y : ℝ => 1 - y ^ 2 := by
        funext y; simp
      rw [hfun] at h
      simpa using h
    have hA : HasDerivAt (fun y : ℝ => (1 - y ^ 2) ^ n)
        (n * (1 - u ^ 2) ^ (n - 1) * (0 - 2 * u)) u := by
      have h := hbase.pow n
      have hfun : ((fun y : ℝ => 1 - y ^ 2) ^ n) = fun y : ℝ => (1 - y ^ 2) ^ n := by
        funext y; simp
      rw [hfun] at h
      exact h
    have hB : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2)) ((0 - 2 * u) / (2 * s)) u := by
      have h0 : (fun y : ℝ => 1 - y ^ 2) u ≠ 0 := by
        show (1 : ℝ) - u ^ 2 ≠ 0
        exact ne_of_gt hpos
      have h := hbase.sqrt h0
      have hfun : (fun x : ℝ => Real.sqrt ((fun y : ℝ => 1 - y ^ 2) x))
          = fun y : ℝ => Real.sqrt (1 - y ^ 2) := by
        funext y; simp
      rw [hfun] at h
      have hv : Real.sqrt ((fun y : ℝ => 1 - y ^ 2) u) = s := by
        show Real.sqrt (1 - u ^ 2) = s
        exact hsdef.symm
      rw [hv] at h
      exact h
    have hAB := hA.mul hB
    have hF := (hasDerivAt_id u).mul hAB
    refine hF.congr_deriv ?_
    simp only [Pi.mul_apply, id_eq, one_mul]
    rw [← hsdef, hc]
    exact key_identity n hn hsne hss
  have hcont : ContinuousOn (fun u : ℝ => u * ((1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2)))
      (Set.Icc (-1) 1) := by fun_prop
  have hintG : IntervalIntegrable (fun u : ℝ => (1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hintK : IntervalIntegrable
      (fun u : ℝ => c * (u ^ 2 * (1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2)))
      volume (-1) 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  -- fundamental theorem of calculus: the integral of the derivative vanishes
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (show (-1 : ℝ) ≤ 1 by norm_num) hcont hderiv (hintG.sub hintK)
  have hz1 : (1 : ℝ) * ((1 - 1 ^ 2) ^ n * Real.sqrt (1 - 1 ^ 2)) = 0 := by
    have h1 : (1 : ℝ) - 1 ^ 2 = 0 := by norm_num
    simp only [h1, zero_pow hn0, Real.sqrt_zero, mul_zero]
  have hz2 : (-1 : ℝ) * ((1 - (-1) ^ 2) ^ n * Real.sqrt (1 - (-1) ^ 2)) = 0 := by
    have h1 : (1 : ℝ) - (-1) ^ 2 = 0 := by norm_num
    simp only [h1, zero_pow hn0, Real.sqrt_zero, mul_zero]
  -- the integral splits into the two constants
  have hsplit : ∫ u in (-1 : ℝ)..1,
        ((1 - u ^ 2) ^ n * Real.sqrt (1 - u ^ 2)
          - c * (u ^ 2 * (1 - u ^ 2) ^ (n - 1) * Real.sqrt (1 - u ^ 2)))
      = Work.OddCurve.refConst n - c * Work.OddCurve.LowSlope.ballInertiaConst n := by
    rw [intervalIntegral.integral_sub hintG hintK, intervalIntegral.integral_const_mul]
    unfold Work.OddCurve.refConst Work.OddCurve.LowSlope.ballInertiaConst
    ring
  have hmain : Work.OddCurve.refConst n - c * Work.OddCurve.LowSlope.ballInertiaConst n = 0 := by
    rw [← hsplit, hFTC, hz1, hz2]
    ring
  rw [hc] at hmain
  linarith

end Work.OddCurve.LowSlope
