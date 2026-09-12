import Mathlib

/-! RECONSTRUCTION of module `S5si_facts` (namespace `Submission.SiFacts`).

This module provides the *facts about the sine-integral partial sums* that
`Submission/S5si_bounds.lean` requires.  Read `S5si_bounds.lean` to pin down
the EXACT signatures needed; the declarations below are the expected
interface.  You may adjust statements if the actual usage demands it, but the
FILE `S5si_bounds.lean` must then still compile unchanged, and so must
`Submission.S5_sHat` and everything above it (`Submission.S5_TheoremSine`,
`Submission.S6_Flat`, `Submission`, `lake build Submission` green).

The mathematics (sinc := sin x / x, extended by 1 at 0; `Real.sinc`):

  u(j)     := ∫_{jπ}^{(j+1)π} sinc x dx
  S(k)     := u(0) + u(1) + ... + u(k)
  block(j,m):= ∫_{jπ}^{(j+2m)π} sinc x dx   (window of 2m half-periods)

Facts (all classical, proved with sin positivity/negativity on each
half-period and the monotonicity of 1/x):

  • u(2t) > 0, u(2t+1) < 0          (sin sign on each half-period)
  • 0 < u(2t) + u(2t+1)             (the paired contributions are positive)
  • |u(j+1)| < |u(j)|               (strict decay)
  • u_neg_eq: sincInt-type reflection: for j ≥ 1,
        ∫_{-jπ}^{-(j-1)π} sinc x dx = u (j-1)
  • S_bounds: for all k,  S(1) ≤ S(k) ≤ S(0)
  • block_even_bounds: for t ≥ 0, m ≥ 1:
        0 < block (2t) m ∧ block (2t) m < u (2t)
  • block_odd_bounds: for t ≥ 0, m ≥ 1:
        u (2t+1) < block (2t+1) m ∧ block (2t+1) m < 0

Numerical values of S(1) (= ∫_0^{2π} sinc), S(0) (= ∫_0^π sinc), u(1)
(≈ -0.43) etc. are in the SEPARATE existing module `Submission.S5sinc_num`
(namespace SincNum: `int_0_2pi_ge`, `int_0_pi_le`, `int_pi_2pi_ge`) — DO NOT
redefine them here; S5si_bounds imports both.  Use `intervalIntegral`,
`Real.continuous_sinc`, `Real.sinc_of_ne_zero`, `Real.sinc_zero`,
`Real.sin_pos_of_pos_of_lt_pi`, `Real.sin_neg_of_pos_of_lt_pi`-type lemmas
(search Mathlib for the sin-positivity/negativity lemmas on (0,π)/(π,2π);
for 1/x decay use `div_lt_div_of_pos_left`-type arguments; `norm_num` for
simple bounds).  Everything is real-valued; `∫ x in a..b, ...` is the
interval integral.

Keep the namespace structure: `namespace Submission`, `namespace SiFacts`.
This file must be complete (no placeholders) in the end. -/

noncomputable section
open scoped BigOperators
open MeasureTheory intervalIntegral
open Set

set_option autoImplicit false

namespace Submission
namespace SiFacts

/-- `u(j) := ∫_{jπ}^{(j+1)π} sinc x dx`. -/
def u (j : ℕ) : ℝ :=
  ∫ x in (((j : ℕ) : ℝ) * Real.pi)..((((j + 1 : ℕ) : ℝ)) * Real.pi), Real.sinc x

/-- `S(k) := u(0) + ... + u(k)`. -/
def S (k : ℕ) : ℝ := ∑ j ∈ Finset.range (k + 1), u j

/-- `block(j,m) := ∫_{jπ}^{(j+2m)π} sinc x dx`. -/
def block (j m : ℕ) : ℝ :=
  ∫ x in (((j : ℕ) : ℝ) * Real.pi)..((((j + 2 * m : ℕ) : ℝ)) * Real.pi), Real.sinc x

/-! ## Basic interval-endpoint helpers -/

lemma cast_half_even (t : ℕ) : ((2*t + 1 : ℕ) : ℝ) * Real.pi = ((2*t : ℕ) : ℝ) * Real.pi + Real.pi := by
  norm_num; ring

lemma cast_half_odd (t : ℕ) : ((2*t + 2 : ℕ) : ℝ) * Real.pi = ((2*t + 1 : ℕ) : ℝ) * Real.pi + Real.pi := by
  norm_num; ring

lemma sin_pos_half_even (t : ℕ) :
    ∀ x : ℝ, x ∈ Ioo (((2*t : ℕ) : ℝ) * Real.pi) (((2*t + 1 : ℕ) : ℝ) * Real.pi) →
      0 < Real.sin x := by
  intro x hx
  have hy0 : 0 < x - ((2*t : ℕ) : ℝ) * Real.pi := by linarith [hx.1]
  have hyπ : x - ((2*t : ℕ) : ℝ) * Real.pi < Real.pi := by linarith [hx.2, cast_half_even t]
  have hpow : (-1 : ℝ) ^ (2 * t) = 1 := by rw [pow_mul]; norm_num
  have hsin : Real.sin x = Real.sin (x - ((2*t : ℕ) : ℝ) * Real.pi) := by
    calc
      Real.sin x = Real.sin ((x - ((2*t : ℕ) : ℝ) * Real.pi) + ((2*t : ℕ) : ℝ) * Real.pi) := by ring
      _ = Real.sin (x - ((2*t : ℕ) : ℝ) * Real.pi) := by
        rw [Real.sin_add_nat_mul_pi (x - ((2*t : ℕ) : ℝ) * Real.pi) (2 * t), hpow]
        ring
  rw [hsin]
  exact Real.sin_pos_of_pos_of_lt_pi hy0 hyπ

lemma sin_neg_half_odd (t : ℕ) :
    ∀ x : ℝ, x ∈ Ioo (((2*t + 1 : ℕ) : ℝ) * Real.pi) (((2*t + 2 : ℕ) : ℝ) * Real.pi) →
      Real.sin x < 0 := by
  intro x hx
  have hyπ : Real.pi < x - ((2*t : ℕ) : ℝ) * Real.pi := by linarith [hx.1, cast_half_even t]
  have hy2π : x - ((2*t : ℕ) : ℝ) * Real.pi < 2 * Real.pi := by
    have hx2' : x < ((2*t : ℕ) : ℝ) * Real.pi + 2 * Real.pi := by
      have hx2'' := hx.2
      rw [cast_half_odd t, cast_half_even t] at hx2''
      linarith
    linarith
  have hpow : (-1 : ℝ) ^ (2 * t) = 1 := by rw [pow_mul]; norm_num
  have hsin : Real.sin x = Real.sin (x - ((2*t : ℕ) : ℝ) * Real.pi) := by
    calc
      Real.sin x = Real.sin ((x - ((2*t : ℕ) : ℝ) * Real.pi) + ((2*t : ℕ) : ℝ) * Real.pi) := by ring
      _ = Real.sin (x - ((2*t : ℕ) : ℝ) * Real.pi) := by
        rw [Real.sin_add_nat_mul_pi (x - ((2*t : ℕ) : ℝ) * Real.pi) (2 * t), hpow]
        ring
  rw [hsin]
  have hy0 : 0 < (x - ((2*t : ℕ) : ℝ) * Real.pi) - Real.pi := by linarith [hyπ]
  have hyπ2 : (x - ((2*t : ℕ) : ℝ) * Real.pi) - Real.pi < Real.pi := by linarith [hy2π]
  have hsinp : Real.sin ((x - ((2*t : ℕ) : ℝ) * Real.pi) - Real.pi)
      = - Real.sin (x - ((2*t : ℕ) : ℝ) * Real.pi) := by
    have hs := Real.sin_sub_nat_mul_pi (x - ((2*t : ℕ) : ℝ) * Real.pi) 1
    simpa using hs
  have hpos : 0 < Real.sin (((x - ((2*t : ℕ) : ℝ) * Real.pi)) - Real.pi) :=
    Real.sin_pos_of_pos_of_lt_pi hy0 hyπ2
  rw [hsinp] at hpos
  linarith

lemma x_pos_even (t : ℕ) :
    ∀ x : ℝ, x ∈ Ioo (((2*t : ℕ) : ℝ) * Real.pi) (((2*t + 1 : ℕ) : ℝ) * Real.pi) → 0 < x := by
  intro x hx
  exact lt_of_le_of_lt (by positivity : 0 ≤ ((2*t : ℕ) : ℝ) * Real.pi) hx.1

lemma x_pos_odd (t : ℕ) :
    ∀ x : ℝ, x ∈ Ioo (((2*t + 1 : ℕ) : ℝ) * Real.pi) (((2*t + 2 : ℕ) : ℝ) * Real.pi) → 0 < x := by
  intro x hx
  exact lt_of_le_of_lt (by positivity : 0 ≤ ((2*t + 1 : ℕ) : ℝ) * Real.pi) hx.1

/-- `u(0) > 0`. -/
lemma u0_pos : 0 < u 0 := by
  unfold u
  norm_num
  refine intervalIntegral_pos_of_pos_on ?hfi ?hpos (by positivity : (0:ℝ) < Real.pi)
  · simpa using Real.continuous_sinc.intervalIntegrable (0:ℝ) Real.pi
  · intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    rw [Real.sinc_of_ne_zero hx0]
    exact div_pos (Real.sin_pos_of_mem_Ioo hx) hx.1

/-- Even-index blocks are positive: `u(2t) > 0`. -/
lemma u_pos_even (t : ℕ) : 0 < u (2 * t) := by
  unfold u
  refine intervalIntegral_pos_of_pos_on ?hfi ?hpos ?hab
  · simpa using Real.continuous_sinc.intervalIntegrable (((2*t : ℕ) : ℝ) * Real.pi) ((((2*t + 1 : ℕ) : ℝ)) * Real.pi)
  · intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (x_pos_even t x hx)
    rw [Real.sinc_of_ne_zero hx0]
    exact div_pos (sin_pos_half_even t x hx) (x_pos_even t x hx)
  · rw [cast_half_even t]
    linarith [Real.pi_pos]

/-- Odd-index blocks are negative: `u(2t+1) < 0`. -/
lemma u_neg_odd (t : ℕ) : u (2 * t + 1) < 0 := by
  unfold u
  have hpos : 0 < ∫ x in (((2*t + 1 : ℕ) : ℝ) * Real.pi)..((((2*t + 2 : ℕ) : ℝ)) * Real.pi), -Real.sinc x := by
    refine intervalIntegral_pos_of_pos_on ?hfi ?hpos ?hab
    · exact (Real.continuous_sinc.neg).intervalIntegrable _ _
    · intro x hx
      have hx0 : x ≠ 0 := ne_of_gt (x_pos_odd t x hx)
      rw [Real.sinc_of_ne_zero hx0]
      have hs : Real.sin x < 0 := sin_neg_half_odd t x hx
      have hxpos : 0 < x := x_pos_odd t x hx
      rw [← neg_div]
      exact div_pos (neg_pos.2 hs) hxpos
    · rw [cast_half_odd t]
      linarith [Real.pi_pos]
  have hneg : (∫ x in (((2*t + 1 : ℕ) : ℝ) * Real.pi)..((((2*t + 2 : ℕ) : ℝ)) * Real.pi), Real.sinc x) < 0 := by
    have := hpos
    rw [intervalIntegral.integral_neg] at this
    linarith
  exact hneg

/-! ## The positive even pair sum -/

lemma u_succ_shift (j : ℕ) :
    u (j + 1) = ∫ x in (((j : ℕ) : ℝ) * Real.pi)..(((j + 1 : ℕ) : ℝ) * Real.pi), Real.sinc (x + Real.pi) := by
  unfold u
  rw [intervalIntegral.integral_comp_add_right]
  congr 1 <;> norm_num <;> ring

lemma sinc_add_shift (x : ℝ) (hx0 : x ≠ 0) (hxp : x + Real.pi ≠ 0) :
    Real.sinc x + Real.sinc (x + Real.pi) = Real.sin x * Real.pi / (x * (x + Real.pi)) := by
  rw [Real.sinc_of_ne_zero hx0, Real.sinc_of_ne_zero hxp, Real.sin_add_pi]
  field_simp [hx0, hxp]
  ring

/-- Paired blocks are positive: `0 < u(2t) + u(2t+1)`. -/
lemma u_pair_pos (t : ℕ) : 0 < u (2 * t) + u (2 * t + 1) := by
  have hsucc := u_succ_shift (2 * t)
  have huadd :
      u (2 * t) + u (2 * t + 1)
        = ∫ x in (((2*t : ℕ) : ℝ) * Real.pi)..(((2*t + 1 : ℕ) : ℝ) * Real.pi),
            (Real.sinc x + Real.sinc (x + Real.pi)) := by
    rw [hsucc]
    unfold u
    have hf : IntervalIntegrable Real.sinc volume (((2*t : ℕ) : ℝ) * Real.pi) (((2*t + 1 : ℕ) : ℝ) * Real.pi) := by
      exact Real.continuous_sinc.intervalIntegrable _ _
    have hg : IntervalIntegrable (fun x : ℝ => Real.sinc (x + Real.pi)) volume (((2*t : ℕ) : ℝ) * Real.pi) (((2*t + 1 : ℕ) : ℝ) * Real.pi) := by
      exact (Real.continuous_sinc.comp (by fun_prop : Continuous (fun x : ℝ => x + Real.pi))).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add hf hg]
  rw [huadd]
  refine intervalIntegral_pos_of_pos_on ?hfi ?hpos ?hab
  · exact (Real.continuous_sinc.add (Real.continuous_sinc.comp (by fun_prop : Continuous (fun x : ℝ => x + Real.pi)))).intervalIntegrable _ _
  · intro x hx
    have hxpos : 0 < x := by
      exact lt_of_le_of_lt (by positivity : 0 ≤ ((2*t : ℕ) : ℝ) * Real.pi) hx.1
    have hx0 : x ≠ 0 := ne_of_gt hxpos
    have hxp : x + Real.pi ≠ 0 := by
      have : 0 < x + Real.pi := by linarith [Real.pi_pos, hxpos]
      exact ne_of_gt this
    rw [sinc_add_shift x hx0 hxp]
    have hsin : 0 < Real.sin x := sin_pos_half_even t x hx
    exact div_pos (mul_pos hsin Real.pi_pos) (mul_pos hxpos (by linarith [Real.pi_pos, hxpos]))
  · rw [cast_half_even t]
    linarith [Real.pi_pos]

/-! ## Canonical half-period integrals and strict decay -/

lemma u_shift_canon (n : ℕ) :
    u n = ∫ y in (0 : ℝ)..Real.pi, Real.sinc (y + (n : ℝ) * Real.pi) := by
  unfold u
  rw [show ((n + 1 : ℕ) : ℝ) * Real.pi = Real.pi + (n : ℝ) * Real.pi by norm_num; ring]
  symm
  simpa [zero_add] using
    (intervalIntegral.integral_comp_add_right (f := Real.sinc) (a := (0:ℝ)) (b := Real.pi)
      (d := (n : ℝ) * Real.pi))

lemma u_eq_negpow_canon (n : ℕ) (hn : 1 ≤ n) :
    u n = (-1 : ℝ) ^ n * ∫ y in (0 : ℝ)..Real.pi, Real.sin y / (y + (n : ℝ) * Real.pi) := by
  rw [u_shift_canon n]
  have hint_eq : ∫ y in (0:ℝ)..Real.pi, Real.sinc (y + (n : ℝ) * Real.pi)
      = ∫ y in (0:ℝ)..Real.pi, (-1 : ℝ) ^ n * (Real.sin y / (y + (n : ℝ) * Real.pi)) := by
    refine intervalIntegral.integral_congr ?_
    intro y hy
    change Real.sinc (y + (n : ℝ) * Real.pi) = (-1 : ℝ) ^ n * (Real.sin y / (y + (n : ℝ) * Real.pi))
    have hy0 : 0 ≤ y := by
      have hy' : y ∈ Icc (0:ℝ) Real.pi := by
        simpa [uIcc_of_le (by positivity : (0:ℝ) ≤ Real.pi)] using hy
      exact hy'.1
    have hden : y + (n : ℝ) * Real.pi ≠ 0 := by
      have hpos : 0 < y + (n : ℝ) * Real.pi := by
        have hnp : 0 < (n : ℝ) * Real.pi := mul_pos (by exact_mod_cast (Nat.succ_le_iff.mp hn)) Real.pi_pos
        nlinarith
      exact ne_of_gt hpos
    rw [Real.sinc_of_ne_zero hden, Real.sin_add_nat_mul_pi y n]
    ring
  rw [hint_eq]
  simp

lemma B_nonneg (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ ∫ y in (0 : ℝ)..Real.pi, Real.sin y / (y + (n : ℝ) * Real.pi) := by
  refine intervalIntegral.integral_nonneg (by positivity : (0:ℝ) ≤ Real.pi) ?_
  intro y hy
  have hden : 0 < y + (n : ℝ) * Real.pi := by
    have hnp : 0 < (n : ℝ) * Real.pi := mul_pos (by exact_mod_cast (Nat.succ_le_iff.mp hn)) Real.pi_pos
    nlinarith [hy.1]
  exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hy.1 hy.2) (le_of_lt hden)

lemma u_abs_eq_canon (n : ℕ) (hn : 1 ≤ n) :
    |u n| = ∫ y in (0 : ℝ)..Real.pi, Real.sin y / (y + (n : ℝ) * Real.pi) := by
  rw [u_eq_negpow_canon n hn]
  have hB : 0 ≤ ∫ y in (0:ℝ)..Real.pi, Real.sin y / (y + (n : ℝ) * Real.pi) := B_nonneg n hn
  rw [abs_mul]
  have h1 : |(-1 : ℝ) ^ n| = 1 := by
    rw [abs_pow]
    norm_num
  rw [h1, abs_of_nonneg hB]
  norm_num

lemma canon_strict_dec (k : ℕ) (hk : 1 ≤ k) :
    (∫ y in (0:ℝ)..Real.pi, Real.sin y / (y + ((k + 1 : ℕ) : ℝ) * Real.pi))
      < ∫ y in (0:ℝ)..Real.pi, Real.sin y / (y + ((k : ℕ) : ℝ) * Real.pi) := by
  refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by positivity : (0:ℝ) < Real.pi) ?hfc ?hgc ?hle ?hlt
  · apply ContinuousOn.div
    · exact Continuous.continuousOn Real.continuous_sin
    · exact Continuous.continuousOn (by fun_prop : Continuous (fun y : ℝ => y + ((k + 1 : ℕ) : ℝ) * Real.pi))
    · intro y hy
      have hpos : 0 < y + ((k + 1 : ℕ) : ℝ) * Real.pi := by
        have hnp : 0 < ((k + 1 : ℕ) : ℝ) * Real.pi := by positivity
        nlinarith [hy.1]
      exact ne_of_gt hpos
  · apply ContinuousOn.div
    · exact Continuous.continuousOn Real.continuous_sin
    · exact Continuous.continuousOn (by fun_prop : Continuous (fun y : ℝ => y + ((k : ℕ) : ℝ) * Real.pi))
    · intro y hy
      have hpos : 0 < y + ((k : ℕ) : ℝ) * Real.pi := by
        have hnp : 0 < ((k : ℕ) : ℝ) * Real.pi := mul_pos (by positivity : 0 < (k : ℝ)) Real.pi_pos
        nlinarith [hy.1]
      exact ne_of_gt hpos
  · intro y hy
    have hsin : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hy.1) hy.2
    have hpos1 : 0 < y + ((k : ℕ) : ℝ) * Real.pi := by
      have hnp : 0 < ((k : ℕ) : ℝ) * Real.pi := mul_pos (by positivity : 0 < (k : ℝ)) Real.pi_pos
      nlinarith [hy.1]
    have hle_d : y + ((k : ℕ) : ℝ) * Real.pi ≤ y + ((k + 1 : ℕ) : ℝ) * Real.pi := by
      push_cast
      nlinarith [Real.pi_pos]
    exact div_le_div_of_nonneg_left hsin hpos1 hle_d
  · refine ⟨Real.pi / 2, by constructor <;> linarith [Real.pi_pos], ?_⟩
    have hsin : 0 < Real.sin (Real.pi / 2) := by rw [Real.sin_pi_div_two]; norm_num
    have hpos1 : 0 < Real.pi / 2 + ((k : ℕ) : ℝ) * Real.pi := by positivity
    have hpos2 : 0 < Real.pi / 2 + ((k + 1 : ℕ) : ℝ) * Real.pi := by positivity
    have hlt_d : Real.pi / 2 + ((k + 1 : ℕ) : ℝ) * Real.pi > Real.pi / 2 + ((k : ℕ) : ℝ) * Real.pi := by
      push_cast
      nlinarith [Real.pi_pos]
    exact div_lt_div_of_pos_left hsin hpos1 hlt_d

lemma B1_lt_u0 :
    (∫ y in (0:ℝ)..Real.pi, Real.sin y / (y + Real.pi))
      < ∫ y in (0:ℝ)..Real.pi, Real.sinc y := by
  refine intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by positivity : (0:ℝ) < Real.pi) ?hfc ?hgc ?hle ?hlt
  · apply ContinuousOn.div
    · exact Continuous.continuousOn Real.continuous_sin
    · exact Continuous.continuousOn (by fun_prop : Continuous (fun y : ℝ => y + Real.pi))
    · intro y hy
      have hpos : 0 < y + Real.pi := by nlinarith [Real.pi_pos, hy.1]
      exact ne_of_gt hpos
  · exact Real.continuous_sinc.continuousOn
  · intro y hy
    have hy0 : y ≠ 0 := ne_of_gt hy.1
    have hsin : 0 ≤ Real.sin y := Real.sin_nonneg_of_nonneg_of_le_pi (le_of_lt hy.1) hy.2
    rw [Real.sinc_of_ne_zero hy0]
    exact div_le_div_of_nonneg_left hsin hy.1 (by linarith [Real.pi_pos])
  · refine ⟨Real.pi / 2, by constructor <;> linarith [Real.pi_pos], ?_⟩
    have hsin : 0 < Real.sin (Real.pi / 2) := by rw [Real.sin_pi_div_two]; norm_num
    have hy0 : Real.pi / 2 ≠ 0 := by positivity
    rw [Real.sinc_of_ne_zero hy0]
    exact div_lt_div_of_pos_left hsin (by positivity) (by linarith [Real.pi_pos])

lemma abs_u1_lt_abs_u0 : |u 1| < |u 0| := by
  have hB1 : |u 1| = ∫ y in (0:ℝ)..Real.pi, Real.sin y / (y + Real.pi) := by
    have h := u_abs_eq_canon 1 (by norm_num : 1 ≤ 1)
    simpa using h
  rw [hB1, abs_of_pos u0_pos]
  unfold u
  norm_num
  exact B1_lt_u0

/-- Strict decay of the block magnitudes: `|u(k+1)| < |u(k)|`. -/
lemma u_abs_decreasing (k : ℕ) : |u (k + 1)| < |u k| := by
  by_cases hk : 1 ≤ k
  · have h1 : |u (k + 1)| = ∫ y in (0:ℝ)..Real.pi, Real.sin y / (y + ((k + 1 : ℕ) : ℝ) * Real.pi) := by
      exact u_abs_eq_canon (k + 1) (by omega)
    have h2 : |u k| = ∫ y in (0:ℝ)..Real.pi, Real.sin y / (y + ((k : ℕ) : ℝ) * Real.pi) := by
      exact u_abs_eq_canon k hk
    rw [h1, h2]
    exact canon_strict_dec k hk
  · have hk0 : k = 0 := by omega
    subst k
    exact abs_u1_lt_abs_u0

/-- Reflection: for `j ≥ 1`, `∫_{-jπ}^{-(j-1)π} sinc = u(j-1)`. -/
lemma u_neg_eq (j : ℕ) (hj : 1 ≤ j) :
    (∫ x in (-(((j : ℕ) : ℝ) * Real.pi))..(-((((j - 1 : ℕ) : ℝ)) * Real.pi)), Real.sinc x) =
      u (j - 1) := by
  have hconv : (∫ x in (-(((j : ℕ) : ℝ) * Real.pi))..(-((((j - 1 : ℕ) : ℝ)) * Real.pi)), Real.sinc x)
      = ∫ x in (-(((j : ℕ) : ℝ) * Real.pi))..(-((((j - 1 : ℕ) : ℝ)) * Real.pi)), Real.sinc (-x) := by
    refine intervalIntegral.integral_congr ?_
    intro x hx
    change Real.sinc x = Real.sinc (-x)
    rw [Real.sinc_neg]
  rw [hconv]
  rw [intervalIntegral.integral_comp_neg]
  unfold u
  congr 1
  · have h1 : -(-((((j - 1 : ℕ) : ℝ)) * Real.pi)) = ((j - 1 : ℕ) : ℝ) * Real.pi := by ring
    rw [h1]
  · have h2 : -(-(((j : ℕ) : ℝ) * Real.pi)) = ((j : ℕ) : ℝ) * Real.pi := by ring
    rw [h2]
    have hn : ((j - 1 + 1 : ℕ) : ℝ) = (j : ℝ) := by
      have hnat : j - 1 + 1 = j := by omega
      rw [hnat]
    rw [hn]

/-! ## Odd pairs are negative (needs decay + signs) -/

lemma odd_pair_neg (i : ℕ) : u (2 * i + 1) + u (2 * i + 2) < 0 := by
  have hdec := u_abs_decreasing (2 * i + 1)
  have hodd : u (2 * i + 1) < 0 := u_neg_odd i
  have heven : 0 < u (2 * i + 2) := by
    have h := u_pos_even (i + 1)
    rwa [show 2 * (i + 1) = 2 * i + 2 by omega] at h
  have h1 : |u (2 * i + 1)| = -(u (2 * i + 1)) := abs_of_neg hodd
  have h2 : |u (2 * i + 2)| = u (2 * i + 2) := abs_of_pos heven
  linarith

/-! ## Finset-sum helpers -/

lemma sum_range_two_mul (m : ℕ) (g : ℕ → ℝ) :
    (∑ i ∈ Finset.range m, (g (2 * i) + g (2 * i + 1))) = ∑ s ∈ Finset.range (2 * m), g s := by
  induction m with
  | zero => simp
  | succ m ih =>
      have h2 : 2 * (m + 1) = 2 * m + 2 := by omega
      rw [h2]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [← ih]
      ring

lemma sum_range_succ0 (n : ℕ) (g : ℕ → ℝ) :
    (∑ s ∈ Finset.range (n + 1), g s) = g 0 + ∑ s ∈ Finset.range n, g (s + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [← Finset.sum_range_succ]
      rw [ih]
      rw [Finset.sum_range_succ]
      ring

lemma sum_range_succ_shift (n : ℕ) (g : ℕ → ℝ) :
    (∑ s ∈ Finset.range n, g (s + 1)) = (∑ s ∈ Finset.range n, g s) - g 0 + g n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [ih]
      ring

lemma block_step (j m : ℕ) :
    block j (m + 1) = block j m + u (j + 2 * m) + u (j + 2 * m + 1) := by
  unfold block u
  have hnat : (j + 2 * (m + 1) : ℕ) = j + 2 * m + 2 := by omega
  rw [hnat]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (((j : ℕ) : ℝ) * Real.pi)) (b := (((j + 2 * m : ℕ) : ℝ) * Real.pi))
    (c := (((j + 2 * m + 2 : ℕ) : ℝ) * Real.pi)) (f := Real.sinc)
    (by simpa using Real.continuous_sinc.intervalIntegrable _ _)
    (by simpa using Real.continuous_sinc.intervalIntegrable _ _)]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (a := (((j + 2 * m : ℕ) : ℝ) * Real.pi)) (b := (((j + 2 * m + 1 : ℕ) : ℝ) * Real.pi))
    (c := (((j + 2 * m + 2 : ℕ) : ℝ) * Real.pi)) (f := Real.sinc)
    (by simpa using Real.continuous_sinc.intervalIntegrable _ _)
    (by simpa using Real.continuous_sinc.intervalIntegrable _ _)]
  have hn2 : (j + 2 * m + 1 + 1 : ℕ) = j + 2 * m + 2 := by omega
  rw [hn2]
  ac_rfl

lemma block_eq_sum (j m : ℕ) : block j m = ∑ s ∈ Finset.range (2 * m), u (j + s) := by
  induction m with
  | zero => simp [block]
  | succ m ih =>
      have h2 : 2 * (m + 1) = 2 * m + 2 := by omega
      rw [h2]
      rw [Finset.sum_range_succ]
      rw [Finset.sum_range_succ]
      rw [← ih]
      have hn : (j + (2 * m + 1) : ℕ) = j + 2 * m + 1 := by omega
      rw [hn]
      rw [← block_step]

lemma S_succ (k : ℕ) : S (k + 1) = S k + u (k + 1) := by
  unfold S
  rw [Finset.sum_range_succ]

/-! ## Identities expressing `S` by alternating pair sums -/

lemma S_even_odd (m : ℕ) :
    S (2 * m) = u 0 + ∑ i ∈ Finset.range m, (u (2 * i + 1) + u (2 * i + 2)) := by
  unfold S
  rw [show (2 * m) + 1 = 2 * m + 1 by omega]
  rw [sum_range_succ0 (2 * m) u]
  rw [← sum_range_two_mul m (fun s => u (s + 1))]

lemma S_odd_odd (m : ℕ) :
    S (2 * m + 1) = u 0 + (∑ i ∈ Finset.range m, (u (2 * i + 1) + u (2 * i + 2))) + u (2 * m + 1) := by
  have h := S_succ (2 * m)
  rw [h]
  rw [S_even_odd]

lemma S_even_even (m : ℕ) :
    S (2 * m) = (∑ i ∈ Finset.range m, (u (2 * i) + u (2 * i + 1))) + u (2 * m) := by
  unfold S
  rw [show (2 * m) + 1 = 2 * m + 1 by omega]
  rw [Finset.sum_range_succ]
  rw [← sum_range_two_mul m u]

lemma S_odd_even (m : ℕ) :
    S (2 * m + 1) = ∑ i ∈ Finset.range (m + 1), (u (2 * i) + u (2 * i + 1)) := by
  unfold S
  rw [show (2 * m + 1) + 1 = 2 * (m + 1) by omega]
  rw [← sum_range_two_mul (m + 1) u]

/-- Partial sums lie between `S 1` and `S 0`: `S 1 ≤ S k ∧ S k ≤ S 0`. -/
lemma S_bounds (k : ℕ) : S 1 ≤ S k ∧ S k ≤ S 0 := by
  -- values at 0,1
  have hS0 : S 0 = u 0 := by unfold S; simp
  have hS1 : S 1 = u 0 + u 1 := by
    unfold S
    rw [Finset.sum_range_succ]
    rw [Finset.sum_range_succ]
    simp
  have hu1neg : u 1 < 0 := by
    simpa [one_mul, zero_add] using (u_neg_odd 0)
  rcases Nat.even_or_odd k with ⟨m, hk⟩ | ⟨m, hk⟩
  · -- k even: k = m + m = 2m
    have hk2 : k = 2 * m := by omega
    rw [hk2]
    by_cases hm : 1 ≤ m
    · -- m ≥ 1
      constructor
      · -- S1 ≤ S(2m)
        have hpos : 0 < S (2 * m) - S 1 := by
          -- S(2m) - S1 = Σ_{i<m} evenPair(i) - evenPair(0) + u(2m) ≥ u(2m) > 0
          rw [S_even_even m]
          rw [hS1]
          have hsum_pos : u 0 + u 1 ≤ ∑ i ∈ Finset.range m, (u (2 * i) + u (2 * i + 1)) := by
            have h := Finset.single_le_sum (s := Finset.range m) (a := 0)
              (f := fun i => u (2 * i) + u (2 * i + 1))
              (fun i hi => le_of_lt (u_pair_pos i))
              (Finset.mem_range.mpr (by omega : 0 < m))
            simpa using h
          have hu2m : 0 < u (2 * m) := u_pos_even m
          linarith
        have : S 1 ≤ S (2 * m) := by linarith
        exact this
      · -- S(2m) ≤ S0
        rw [S_even_odd m]
        have htail : (∑ i ∈ Finset.range m, (u (2 * i + 1) + u (2 * i + 2))) ≤ 0 := by
          apply Finset.sum_nonpos
          intro i hi
          exact le_of_lt (odd_pair_neg i)
        linarith
    · -- m = 0: k = 0
      have hm0 : m = 0 := by omega
      subst m
      constructor
      · rw [hS1, hS0]
        linarith
      · rw [hS0]
  · -- k odd: k = 2m+1
    rw [show k = 2 * m + 1 by omega]
    constructor
    · -- S1 ≤ S(2m+1)
      rw [S_odd_even m]
      rw [hS1]
      have h := Finset.single_le_sum (s := Finset.range (m + 1)) (a := 0)
        (f := fun i => u (2 * i) + u (2 * i + 1))
        (fun i hi => le_of_lt (u_pair_pos i))
        (Finset.mem_range.mpr (by omega : 0 < m + 1))
      simpa using h
    · -- S(2m+1) ≤ S0
      rw [S_odd_odd m]
      have htail : (∑ i ∈ Finset.range m, (u (2 * i + 1) + u (2 * i + 2))) + u (2 * m + 1) ≤ 0 := by
        have hs : (∑ i ∈ Finset.range m, (u (2 * i + 1) + u (2 * i + 2))) ≤ 0 := by
          apply Finset.sum_nonpos
          intro i hi
          exact le_of_lt (odd_pair_neg i)
        have hu : u (2 * m + 1) ≤ 0 := le_of_lt (u_neg_odd m)
        linarith
      rw [hS0]
      linarith

/-! ## Block pair-sum identities -/

lemma block_even_pair (t m : ℕ) :
    block (2*t) m = ∑ i ∈ Finset.range m, (u (2 * (t + i)) + u (2 * (t + i) + 1)) := by
  rw [block_eq_sum]
  rw [← sum_range_two_mul m (fun s => u (2*t + s))]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  · congr 1
    omega
  · congr 1
    omega

lemma block_odd_pair (t m : ℕ) :
    block (2*t + 1) m = ∑ i ∈ Finset.range m, (u (2 * (t + i) + 1) + u (2 * (t + i) + 2)) := by
  rw [block_eq_sum]
  rw [← sum_range_two_mul m (fun s => u (2*t + 1 + s))]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  · congr 1
    omega
  · congr 1
    omega

lemma block_even_minus (t m : ℕ) :
    block (2*t) m - u (2*t)
      = (∑ i ∈ Finset.range m, (u (2 * (t + i) + 1) + u (2 * (t + i) + 2)))
          - u (2*(t + m)) := by
  rw [block_eq_sum]
  calc
    (∑ s ∈ Finset.range (2 * m), u (2*t + s)) - u (2*t)
        = (∑ s ∈ Finset.range (2 * m), u (2*t + (s + 1))) - u (2*t + 2*m) := by
          have hs := sum_range_succ_shift (2 * m) (fun s => u (2*t + s))
          have hz : u (2*t + 0) = u (2*t) := by rfl
          nlinarith [hs, hz]
    _ = (∑ i ∈ Finset.range m, (u (2 * (t + i) + 1) + u (2 * (t + i) + 2)))
          - u (2*t + 2*m) := by
          have hpair : (∑ i ∈ Finset.range m, (u (2 * (t + i) + 1) + u (2 * (t + i) + 2)))
              = ∑ s ∈ Finset.range (2 * m), u (2*t + (s + 1)) := by
            rw [← sum_range_two_mul m (fun s => u (2*t + (s + 1)))]
            apply Finset.sum_congr rfl
            intro i hi
            congr 1
            · congr 1
              omega
            · congr 1
              omega
          rw [← hpair]
    _ = (∑ i ∈ Finset.range m, (u (2 * (t + i) + 1) + u (2 * (t + i) + 2)))
          - u (2*(t + m)) := by
          congr 1
          congr 1
          omega

lemma block_odd_minus (t m : ℕ) :
    block (2*t + 1) m - u (2*t + 1)
      = (∑ i ∈ Finset.range m, (u (2 * (t + 1 + i)) + u (2 * (t + 1 + i) + 1)))
          - u (2*(t + m) + 1) := by
  rw [block_eq_sum]
  calc
    (∑ s ∈ Finset.range (2 * m), u (2*t + 1 + s)) - u (2*t + 1)
        = (∑ s ∈ Finset.range (2 * m), u (2*t + 1 + (s + 1))) - u (2*t + 1 + 2*m) := by
          have hs := sum_range_succ_shift (2 * m) (fun s => u (2*t + 1 + s))
          have hz : u (2*t + 1 + 0) = u (2*t + 1) := by rfl
          nlinarith [hs, hz]
    _ = (∑ i ∈ Finset.range m, (u (2 * (t + 1 + i)) + u (2 * (t + 1 + i) + 1)))
          - u (2*t + 1 + 2*m) := by
          have hpair : (∑ i ∈ Finset.range m, (u (2 * (t + 1 + i)) + u (2 * (t + 1 + i) + 1)))
              = ∑ s ∈ Finset.range (2 * m), u (2*t + 1 + (s + 1)) := by
            rw [← sum_range_two_mul m (fun s => u (2*t + 1 + (s + 1)))]
            apply Finset.sum_congr rfl
            intro i hi
            congr 1
            · congr 1
              omega
            · congr 1
              omega
          rw [← hpair]
    _ = (∑ i ∈ Finset.range m, (u (2 * (t + 1 + i)) + u (2 * (t + 1 + i) + 1)))
          - u (2*(t + m) + 1) := by
          congr 1
          congr 1
          omega

/-- Even-starting windows: `0 < block(2t,m) ∧ block(2t,m) < u(2t)` (m ≥ 1). -/
lemma block_even_bounds (t m : ℕ) (hm : 1 ≤ m) :
    0 < block (2 * t) m ∧ block (2 * t) m < u (2 * t) := by
  constructor
  · rw [block_even_pair]
    apply Finset.sum_pos
    · intro i hi
      exact u_pair_pos (t + i)
    · exact ⟨0, Finset.mem_range.mpr (by omega : 0 < m)⟩
  · have hneg : block (2*t) m - u (2*t) < 0 := by
      rw [block_even_minus]
      have hsum : (∑ i ∈ Finset.range m, (u (2 * (t + i) + 1) + u (2 * (t + i) + 2))) < 0 := by
        apply Finset.sum_neg
        · intro i hi
          exact odd_pair_neg (t + i)
        · exact ⟨0, Finset.mem_range.mpr (by omega : 0 < m)⟩
      have hpos : 0 < u (2 * (t + m)) := u_pos_even (t + m)
      linarith
    linarith

/-- Odd-starting windows: `u(2t+1) < block(2t+1,m) ∧ block(2t+1,m) < 0` (m ≥ 1). -/
lemma block_odd_bounds (t m : ℕ) (hm : 1 ≤ m) :
    u (2 * t + 1) < block (2 * t + 1) m ∧ block (2 * t + 1) m < 0 := by
  constructor
  · have hpos : 0 < block (2*t + 1) m - u (2*t + 1) := by
      rw [block_odd_minus]
      have hsum : 0 < (∑ i ∈ Finset.range m, (u (2 * (t + 1 + i)) + u (2 * (t + 1 + i) + 1))) := by
        apply Finset.sum_pos
        · intro i hi
          exact u_pair_pos (t + 1 + i)
        · exact ⟨0, Finset.mem_range.mpr (by omega : 0 < m)⟩
      have hneg : u (2 * (t + m) + 1) < 0 := u_neg_odd (t + m)
      linarith
    linarith
  · rw [block_odd_pair]
    apply Finset.sum_neg
    · intro i hi
      exact odd_pair_neg (t + i)
    · exact ⟨0, Finset.mem_range.mpr (by omega : 0 < m)⟩

end SiFacts
end Submission
