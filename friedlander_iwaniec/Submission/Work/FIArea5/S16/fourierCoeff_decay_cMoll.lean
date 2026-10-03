import Mathlib
import Submission.Work.FIArea6.fourier_coeff_decay

namespace Work.FIArea5.S16

open MeasureTheory intervalIntegral
open scoped Topology

/-- Support bound for the integral of `|q''|` with an arbitrary constant `M`:
because `q` (and hence `q''`) is supported in `[0, 2πθ]`, this integral is at most
the length `2πθ` of the support times `M`. -/
lemma integral_abs_dd_le_gen (q : ℝ → ℝ) (θ M : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hqC : ContDiff ℝ 2 q) (hM : ∀ α, |deriv (deriv q) α| ≤ M)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ) :
    ∫ α in (0 : ℝ)..(2 * Real.pi), |deriv (deriv q) α| ≤ 2 * Real.pi * θ * M := by
  have hle : 2 * Real.pi * θ ≤ 2 * Real.pi := by
    have : (0 : ℝ) < 2 * Real.pi := by positivity
    nlinarith
  have hqθ : 0 ≤ 2 * Real.pi * θ := by positivity
  have hd0 : ∀ x, 2 * Real.pi * θ ≤ x → deriv (deriv q) x = 0 :=
    (Work.FIArea6.q_vanish_support q θ hqC hqsupp).2.2.2.2.2
  have hcont : Continuous (fun α : ℝ => |deriv (deriv q) α|) := by
    have h : Continuous (deriv (deriv q)) :=
      (Work.FIArea6.iteratedDeriv_two_eq q) ▸ hqC.continuous_iteratedDeriv' 2
    exact h.abs
  have hsplit : (∫ x in (0 : ℝ)..(2 * Real.pi * θ), |deriv (deriv q) x|)
        + (∫ x in (2 * Real.pi * θ)..(2 * Real.pi), |deriv (deriv q) x|)
      = ∫ x in (0 : ℝ)..(2 * Real.pi), |deriv (deriv q) x| :=
    intervalIntegral.integral_add_adjacent_intervals
      (hcont.intervalIntegrable (0 : ℝ) (2 * Real.pi * θ))
      (hcont.intervalIntegrable (2 * Real.pi * θ) (2 * Real.pi))
  rw [← hsplit]
  have hz : ∫ x in (2 * Real.pi * θ)..(2 * Real.pi), |deriv (deriv q) x| = 0 := by
    have h : ∫ x in (2 * Real.pi * θ)..(2 * Real.pi), |deriv (deriv q) x|
        = ∫ x in (2 * Real.pi * θ)..(2 * Real.pi), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hle] at hx
      show |deriv (deriv q) x| = (0 : ℝ)
      rw [hd0 x hx.1, abs_zero]
    rw [h, intervalIntegral.integral_zero]
  rw [hz, add_zero]
  have hmono : ∫ x in (0 : ℝ)..(2 * Real.pi * θ), |deriv (deriv q) x|
      ≤ ∫ x in (0 : ℝ)..(2 * Real.pi * θ), M :=
    intervalIntegral.integral_mono_on hqθ (hcont.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _) (fun x _ => hM x)
  have hone : ∫ x in (0 : ℝ)..(2 * Real.pi * θ), M = 2 * Real.pi * θ * M := by
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  linarith [hmono, hone]

/-- Numeric comparison, small regime (`(θℓ)² ≤ 8`): the trivial bound `2πθ` already
beats `10⁷ θ (1 + θ²ℓ²)⁻¹`. -/
lemma decay_small_num (θ l : ℝ) (hθ : 0 < θ) (hl : (θ * l) ^ 2 ≤ 8) :
    2 * Real.pi * θ ≤ 10000000 * θ * (1 + (θ * l) ^ 2)⁻¹ := by
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have ht0 : (0 : ℝ) < 1 + (θ * l) ^ 2 := by positivity
  have hle : 1 + (θ * l) ^ 2 ≤ 9 := by nlinarith [hl]
  have hinv : (1 : ℝ) / 9 ≤ (1 + (θ * l) ^ 2)⁻¹ := by
    rw [one_div]
    exact (inv_le_inv₀ (show (0 : ℝ) < 9 by norm_num) ht0).mpr hle
  calc 2 * Real.pi * θ ≤ 8 * θ := by nlinarith [hpi, hθ]
    _ ≤ 10000000 * θ * (1 / 9) := by nlinarith [hθ]
    _ ≤ 10000000 * θ * (1 + (θ * l) ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left hinv (by positivity)

/-- Numeric comparison, large regime (`8 < (θℓ)²`): the two-fold integration-by-parts bound
`(ℓ²)⁻¹ · (2πθ · (2²⁰θ⁻²))` is at most `10⁷ θ (1 + θ²ℓ²)⁻¹`. -/
lemma decay_large_num (θ l : ℝ) (hθ : 0 < θ) (hl : 8 < (θ * l) ^ 2) :
    (l ^ 2)⁻¹ * (2 * Real.pi * θ * (1048576 / θ ^ 2))
      ≤ 10000000 * θ * (1 + (θ * l) ^ 2)⁻¹ := by
  set t : ℝ := (θ * l) ^ 2 with ht
  have ht8 : 8 < t := by rw [ht]; exact hl
  have ht0 : 0 < t := by linarith
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hl2 : l ^ 2 = t / θ ^ 2 := by
    rw [ht, eq_div_iff (pow_ne_zero 2 (ne_of_gt hθ))]; ring
  have hkey : 2 * Real.pi * 1048576 * (1 + t) ≤ 10000000 * t := by
    have hP : 2 * Real.pi * 1048576 < 8388608 := by nlinarith [hpi]
    have h1 : 1 + t ≤ (9 / 8) * t := by nlinarith [ht8]
    have hmul : 2 * Real.pi * 1048576 * (1 + t) ≤ 8388608 * ((9 / 8) * t) :=
      mul_le_mul hP.le h1 (by linarith) (by norm_num)
    have hconst : 8388608 * ((9 / 8) * t) ≤ 10000000 * t := by nlinarith [ht0]
    linarith [hmul, hconst]
  have hstep : (θ ^ 2 / t) * (2 * Real.pi * θ * (1048576 / θ ^ 2))
      = 2 * Real.pi * 1048576 * θ / t := by
    field_simp
  rw [hl2, inv_div, hstep]
  have hgoal : 2 * Real.pi * 1048576 * θ / t ≤ (10000000 * θ) / (1 + t) := by
    rw [div_le_div_iff₀ ht0 h1t]
    nlinarith [hkey, hθ]
  exact hgoal

/-- **(16.26), round-4 constants.**  For a `C²` angular mollifier `q` with `0 ≤ q ≤ 1`,
support in `[0, 2πθ]` and `|q''| ≤ 2²⁰ θ⁻²`, the Fourier coefficients satisfy
`‖q̂(ℓ)‖ ≤ 10⁷ θ (1 + θ²ℓ²)⁻¹`. -/
theorem fourierCoeff_decay_cMoll (q : ℝ → ℝ) (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hqC : ContDiff ℝ 2 q) (hq0 : ∀ α, 0 ≤ q α) (hq1 : ∀ α, q α ≤ 1)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ)
    (hd2 : ∀ α, |iteratedDeriv 2 q α| ≤ 1048576 / θ ^ 2) (ℓ : ℤ) :
    ‖∫ α in (0 : ℝ)..(2 * Real.pi), (q α : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖
      ≤ 10000000 * θ * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹ := by
  have h2πpos : (0 : ℝ) < 2 * Real.pi := by positivity
  have h2πθ_le : 2 * Real.pi * θ ≤ 2 * Real.pi := by
    nlinarith [hθ, hθ1, Real.pi_pos]
  have hnormint : ∀ α : ℝ,
      ‖(q α : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖ = q α := by
    intro α
    rw [norm_mul, Work.FIArea6.norm_exp_int ℓ α, mul_one,
      show ‖(q α : ℂ)‖ = |q α| from by simp, abs_of_nonneg (hq0 α)]
  have htriv : ‖∫ α in (0 : ℝ)..(2 * Real.pi),
        (q α : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖ ≤ 2 * Real.pi * θ := by
    calc ‖∫ α in (0 : ℝ)..(2 * Real.pi),
            (q α : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖
        ≤ ∫ α in (0 : ℝ)..(2 * Real.pi),
            ‖(q α : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖ :=
          intervalIntegral.norm_integral_le_integral_norm (le_of_lt h2πpos)
      _ = ∫ α in (0 : ℝ)..(2 * Real.pi), q α := by
          apply intervalIntegral.integral_congr
          intro α _
          exact hnormint α
      _ ≤ 2 * Real.pi * θ := Work.FIArea6.integral_q_le_decay q θ hθ hθ1 hqC hq1 hqsupp
  by_cases hsmall : ((θ * (ℓ : ℝ)) ^ 2) ≤ 8
  · exact le_trans htriv (decay_small_num θ (ℓ : ℝ) hθ hsmall)
  · rw [not_le] at hsmall
    have hl_ne : (ℓ : ℝ) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hsmall
      norm_num at hsmall
    obtain ⟨hv1, hv2, hv3, hv4, hv5, hv6⟩ :=
      Work.FIArea6.q_vanish_support q θ hqC hqsupp
    have hq0' : q 0 = 0 := hv1 0 le_rfl
    have hq2π : q (2 * Real.pi) = 0 := hv2 (2 * Real.pi) h2πθ_le
    have hdq0 : deriv q 0 = 0 := hv3 0 le_rfl
    have hdq2π : deriv q (2 * Real.pi) = 0 := hv4 (2 * Real.pi) h2πθ_le
    have hibp := Work.FIArea6.ibp_twice q ℓ hqC hq0' hq2π hdq0 hdq2π
    have hd2' : ∀ α, |deriv (deriv q) α| ≤ 1048576 / θ ^ 2 := by
      intro α; rw [← Work.FIArea6.iteratedDeriv_two_eq q]; exact hd2 α
    have hC : (-(ℓ : ℂ) * Complex.I) ≠ 0 := by
      intro h
      have h2 : (ℓ : ℂ) = 0 := by
        rcases mul_eq_zero.mp h with h3 | h3
        · exact neg_eq_zero.mp h3
        · exact absurd h3 Complex.I_ne_zero
      exact hl_ne (by simpa using congrArg Complex.re h2)
    have hC2 : (-(ℓ : ℂ) * Complex.I) ^ 2 ≠ 0 := pow_ne_zero 2 hC
    have hJeq : (∫ α in (0 : ℝ)..(2 * Real.pi),
          (q α : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α))
        = ((-(ℓ : ℂ) * Complex.I) ^ 2)⁻¹
          * ∫ α in (0 : ℝ)..(2 * Real.pi),
              ((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α) := by
      rw [eq_inv_mul_iff_mul_eq₀ hC2, mul_comm]
      exact hibp
    have hnormC : ‖((- (ℓ : ℂ) * Complex.I) ^ 2)⁻¹‖ = ((ℓ : ℝ) ^ 2)⁻¹ := by
      rw [norm_inv, norm_pow]
      have hc : ‖(-(ℓ : ℂ) * Complex.I)‖ = |(ℓ : ℝ)| := by
        rw [norm_mul, norm_neg, Complex.norm_intCast, Complex.norm_I, mul_one]
      rw [hc, sq_abs]
    have hL : ‖∫ α in (0 : ℝ)..(2 * Real.pi),
          ((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖
        ≤ 2 * Real.pi * θ * (1048576 / θ ^ 2) := by
      calc ‖∫ α in (0 : ℝ)..(2 * Real.pi),
              ((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖
          ≤ ∫ α in (0 : ℝ)..(2 * Real.pi),
              ‖((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖ :=
            intervalIntegral.norm_integral_le_integral_norm (le_of_lt h2πpos)
        _ = ∫ α in (0 : ℝ)..(2 * Real.pi), |deriv (deriv q) α| := by
            apply intervalIntegral.integral_congr
            intro α _
            show ‖((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖
                = |deriv (deriv q) α|
            rw [norm_mul, Work.FIArea6.norm_exp_int ℓ α, mul_one]
            simp
        _ ≤ 2 * Real.pi * θ * (1048576 / θ ^ 2) :=
            integral_abs_dd_le_gen q θ (1048576 / θ ^ 2) hθ hθ1 hqC hd2' hqsupp
    calc ‖∫ α in (0 : ℝ)..(2 * Real.pi),
            (q α : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖
        = ‖((- (ℓ : ℂ) * Complex.I) ^ 2)⁻¹
            * ∫ α in (0 : ℝ)..(2 * Real.pi),
                ((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖ := by
          rw [hJeq]
      _ ≤ ‖((- (ℓ : ℂ) * Complex.I) ^ 2)⁻¹‖
            * ‖∫ α in (0 : ℝ)..(2 * Real.pi),
                ((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖ :=
          norm_mul_le _ _
      _ = ((ℓ : ℝ) ^ 2)⁻¹
            * ‖∫ α in (0 : ℝ)..(2 * Real.pi),
                ((deriv (deriv q) α : ℝ) : ℂ) * Complex.exp (-(ℓ : ℂ) * Complex.I * α)‖ := by
          rw [hnormC]
      _ ≤ ((ℓ : ℝ) ^ 2)⁻¹ * (2 * Real.pi * θ * (1048576 / θ ^ 2)) :=
          mul_le_mul_of_nonneg_left hL (inv_nonneg.mpr (sq_nonneg _))
      _ ≤ 10000000 * θ * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹ :=
          decay_large_num θ (ℓ : ℝ) hθ hsmall

end Work.FIArea5.S16
