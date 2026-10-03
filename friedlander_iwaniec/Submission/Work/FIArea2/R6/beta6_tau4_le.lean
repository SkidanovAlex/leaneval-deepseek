import Mathlib
import Submission.Work.FIArea2.R6.beta6_gnorm_divisors_card_le
import Submission.Work.FIArea3.CrudeBracketReduce
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea2.R6.BetaFacts6

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea2.R6

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-!
## The `τ(|z|²)^4 ≤ N^{1/16}` bound on the support of a round-6 coefficient
-/

/-- **`hu` forces `log x` to be large.**  From `1/10 ≤ θ√N`, `θ = (log x)^{-A'}` with
`A' ≥ 2^{20}` and `N ≤ √x` we get `(log x)^{A'} ≤ 10 x^{1/4}`; the contrary assumption
`log x < 22027` then gives `log log x < 0.006`, contradicting `log log x ≥ 9/109`. -/
theorem log_x_ge_22027 {Pa : Work.FITop.Params}
    (hu : (1 : ℝ) / 10 ≤ Pa.θ * Real.sqrt Pa.N) :
    22027 ≤ Real.log (Pa.x : ℝ) := by
  by_contra hcon
  simp only [not_le] at hcon
  have hA20 : (1048576 : ℝ) ≤ Pa.A' := by
    have h : (2 : ℝ) ^ (20 : ℕ) ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
    have h2 : (2 : ℝ) ^ (20 : ℕ) = 1048576 := by norm_num
    linarith [h, h2.le, h2.ge]
  have hxpos : 0 < (Pa.x : ℝ) := by
    have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    linarith
  have hLpos : 0 < Real.log (Pa.x : ℝ) := by
    have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    have h3 : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) hx3
    linarith [Real.log_three_gt_d9]
  have hL109 : (109 : ℝ) / 100 ≤ Real.log (Pa.x : ℝ) := by
    have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    have h3 : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) hx3
    linarith [Real.log_three_gt_d9]
  have hNn : 0 ≤ Pa.N := by linarith [Pa.hN1]
  have hs : Pa.N ^ 2 ≤ (Pa.x : ℝ) := by
    have h1 : Pa.N * Pa.N ≤ Pa.M * Pa.N := mul_le_mul_of_nonneg_right Pa.hMge hNn
    have h2 : Pa.M * Pa.N ≤ (Pa.x : ℝ) := Pa.hMNx
    nlinarith [h1, h2]
  have hNle : Pa.N ≤ Real.sqrt (Pa.x : ℝ) := Real.le_sqrt_of_sq_le hs
  have hsqrtN : Real.sqrt Pa.N ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := by
    have h2 : Real.sqrt Pa.N ≤ Real.sqrt (Real.sqrt (Pa.x : ℝ)) := Real.sqrt_le_sqrt hNle
    have h3 : Real.sqrt (Real.sqrt (Pa.x : ℝ)) = (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := by
      rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hxpos.le]
      norm_num
    rwa [h3] at h2
  have hlow : (1 : ℝ) / 10 * (Real.log (Pa.x : ℝ)) ^ Pa.A' ≤ Real.sqrt Pa.N := by
    have hLp : 0 < (Real.log (Pa.x : ℝ)) ^ Pa.A' := Real.rpow_pos_of_pos hLpos _
    have h1 : (1 : ℝ) / 10 ≤ (Real.log (Pa.x : ℝ)) ^ (-Pa.A') * Real.sqrt Pa.N := by
      simpa [Pa.hθ] using hu
    have h2 := mul_le_mul_of_nonneg_right h1 hLp.le
    have h3 : ((Real.log (Pa.x : ℝ)) ^ (-Pa.A') * Real.sqrt Pa.N)
        * (Real.log (Pa.x : ℝ)) ^ Pa.A' = Real.sqrt Pa.N := by
      have e : ((Real.log (Pa.x : ℝ)) ^ (-Pa.A') * Real.sqrt Pa.N)
          * (Real.log (Pa.x : ℝ)) ^ Pa.A'
          = ((Real.log (Pa.x : ℝ)) ^ (-Pa.A') * (Real.log (Pa.x : ℝ)) ^ Pa.A')
              * Real.sqrt Pa.N := by ring
      rw [e, ← Real.rpow_add hLpos]
      simp
    linarith [h2, h3.le, h3.ge]
  have hkey : (1 : ℝ) / 10 * (Real.log (Pa.x : ℝ)) ^ Pa.A'
      ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) := le_trans hlow hsqrtN
  have hlog : Pa.A' * Real.log (Real.log (Pa.x : ℝ))
      ≤ Real.log 10 + Real.log (Pa.x : ℝ) / 4 := by
    have hLp : 0 < (Real.log (Pa.x : ℝ)) ^ Pa.A' := Real.rpow_pos_of_pos hLpos _
    have h := Real.log_le_log
      (by positivity : 0 < (1 : ℝ) / 10 * (Real.log (Pa.x : ℝ)) ^ Pa.A') hkey
    rw [Real.log_mul (by norm_num) (ne_of_gt hLp), Real.log_rpow hxpos,
      Real.log_rpow hLpos] at h
    rw [show Real.log ((1 : ℝ) / 10) = -Real.log 10 by
      rw [show ((1 : ℝ) / 10) = (10 : ℝ)⁻¹ by norm_num, Real.log_inv]] at h
    linarith
  have hloglog_upper : Real.log (Real.log (Pa.x : ℝ)) < (9 + 22027 / 4) / 1048576 := by
    have hlog10 : Real.log 10 ≤ 9 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10); linarith
    have h1 : Pa.A' * Real.log (Real.log (Pa.x : ℝ)) < 9 + 22027 / 4 := by
      have h2 : Real.log (Pa.x : ℝ) / 4 < 22027 / 4 := by linarith [hcon]
      linarith [hlog, hlog10, h2]
    have hloglogpos : 0 ≤ Real.log (Real.log (Pa.x : ℝ)) := by
      apply Real.log_nonneg; linarith
    have h3 : (1048576 : ℝ) * Real.log (Real.log (Pa.x : ℝ))
        ≤ Pa.A' * Real.log (Real.log (Pa.x : ℝ)) :=
      mul_le_mul_of_nonneg_right hA20 hloglogpos
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 1048576)]
    linarith [h1, h3]
  have hloglog_lower : (9 : ℝ) / 109 ≤ Real.log (Real.log (Pa.x : ℝ)) := by
    have h1 : Real.log ((109 : ℝ) / 100) ≤ Real.log (Real.log (Pa.x : ℝ)) :=
      Real.log_le_log (by norm_num) hL109
    have h2 : 1 - ((109 : ℝ) / 100)⁻¹ ≤ Real.log ((109 : ℝ) / 100) :=
      Real.one_sub_inv_le_log_of_pos (by norm_num)
    have h3 : 1 - ((109 : ℝ) / 100)⁻¹ = (9 : ℝ) / 109 := by norm_num
    linarith [h1, h2, h3.le, h3.ge]
  have : (9 + 22027 / 4) / 1048576 < (9 : ℝ) / 109 := by norm_num
  linarith [hloglog_upper, hloglog_lower, this]

/-- **`(log log x)² ≥ 81`**: from `log x ≥ 22027 > 3^9 ≥ e^9` we get `log log x > 9`. -/
theorem sq_loglog_ge_81 {Pa : Work.FITop.Params}
    (hL : 22027 ≤ Real.log (Pa.x : ℝ)) :
    81 ≤ (Real.log (Real.log (Pa.x : ℝ))) ^ (2 : ℕ) := by
  have h9 : (9 : ℝ) < Real.log (Real.log (Pa.x : ℝ)) := by
    have h1 : (9 : ℝ) < Real.log 22027 := by
      rw [← Real.log_exp 9]
      apply Real.log_lt_log (Real.exp_pos 9)
      calc Real.exp 9 = Real.exp ((9 : ℕ) * (1 : ℝ)) := by norm_num
        _ = (Real.exp 1) ^ 9 := Real.exp_nat_mul 1 9
        _ < (3 : ℝ) ^ 9 :=
            pow_lt_pow_left₀ Real.exp_one_lt_three (le_of_lt (Real.exp_pos 1)) (by norm_num)
        _ < 22027 := by norm_num
    exact lt_of_lt_of_le h1 (Real.log_le_log (by norm_num) hL)
  nlinarith [h9]

/-- **`log N ≥ 10`**: from `(1/10)(log x)^{A'} ≤ √N`, `log x ≥ 1.09`, `A' ≥ 2^{20}`. -/
theorem ten_le_log_N {Pa : Work.FITop.Params}
    (hu : (1 : ℝ) / 10 ≤ Pa.θ * Real.sqrt Pa.N) :
    10 ≤ Real.log Pa.N := by
  have hA20 : (1048576 : ℝ) ≤ Pa.A' := by
    have h : (2 : ℝ) ^ (20 : ℕ) ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
    have h2 : (2 : ℝ) ^ (20 : ℕ) = 1048576 := by norm_num
    linarith [h, h2.le, h2.ge]
  have hA200 : (200 : ℝ) ≤ Pa.A' := by linarith
  have hLpos : 0 < Real.log (Pa.x : ℝ) := by
    have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    have h3 : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) hx3
    linarith [Real.log_three_gt_d9]
  have hL109 : (109 : ℝ) / 100 ≤ Real.log (Pa.x : ℝ) := by
    have hx3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
    have h3 : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) hx3
    linarith [Real.log_three_gt_d9]
  have hlow : (1 : ℝ) / 10 * (Real.log (Pa.x : ℝ)) ^ Pa.A' ≤ Real.sqrt Pa.N := by
    have hLp : 0 < (Real.log (Pa.x : ℝ)) ^ Pa.A' := Real.rpow_pos_of_pos hLpos _
    have h1 : (1 : ℝ) / 10 ≤ (Real.log (Pa.x : ℝ)) ^ (-Pa.A') * Real.sqrt Pa.N := by
      simpa [Pa.hθ] using hu
    have h2 := mul_le_mul_of_nonneg_right h1 hLp.le
    have h3 : ((Real.log (Pa.x : ℝ)) ^ (-Pa.A') * Real.sqrt Pa.N)
        * (Real.log (Pa.x : ℝ)) ^ Pa.A' = Real.sqrt Pa.N := by
      have e : ((Real.log (Pa.x : ℝ)) ^ (-Pa.A') * Real.sqrt Pa.N)
          * (Real.log (Pa.x : ℝ)) ^ Pa.A'
          = ((Real.log (Pa.x : ℝ)) ^ (-Pa.A') * (Real.log (Pa.x : ℝ)) ^ Pa.A')
              * Real.sqrt Pa.N := by ring
      rw [e, ← Real.rpow_add hLpos]
      simp
    linarith [h2, h3.le, h3.ge]
  have hpow_ge : ((109 : ℝ) / 100) ^ (200 : ℝ)
      ≤ (Real.log (Pa.x : ℝ)) ^ Pa.A' := by
    have h1 : ((109 : ℝ) / 100) ^ (200 : ℝ) ≤ ((109 : ℝ) / 100) ^ Pa.A' :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hA200
    have h2 : ((109 : ℝ) / 100) ^ Pa.A' ≤ (Real.log (Pa.x : ℝ)) ^ Pa.A' :=
      Real.rpow_le_rpow (by norm_num) hL109 (by linarith)
    linarith [h1, h2]
  have hsqrt_low : (1 : ℝ) / 10 * ((109 : ℝ) / 100) ^ (200 : ℝ) ≤ Real.sqrt Pa.N :=
    le_trans (mul_le_mul_of_nonneg_left hpow_ge (by norm_num)) hlow
  have hNn : 0 ≤ Pa.N := by linarith [Pa.hN1]
  have hN_low : ((1 : ℝ) / 10 * ((109 : ℝ) / 100) ^ (200 : ℝ)) ^ 2 ≤ Pa.N := by
    have hpos : 0 ≤ (1 : ℝ) / 10 * ((109 : ℝ) / 100) ^ (200 : ℝ) := by positivity
    nlinarith [hsqrt_low, Real.sq_sqrt hNn]
  have hlogN : Real.log (((1 : ℝ) / 10 * ((109 : ℝ) / 100) ^ (200 : ℝ)) ^ 2)
      ≤ Real.log Pa.N := Real.log_le_log (by positivity) hN_low
  rw [Real.log_pow] at hlogN
  rw [Real.log_mul (by norm_num)
    (ne_of_gt (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < (109 : ℝ) / 100) _))] at hlogN
  rw [show Real.log ((1 : ℝ) / 10) = -Real.log 10 by
    rw [show ((1 : ℝ) / 10) = (10 : ℝ)⁻¹ by norm_num, Real.log_inv]] at hlogN
  rw [Real.log_rpow (by norm_num : (0 : ℝ) < (109 : ℝ) / 100)] at hlogN
  have hlog109 : (9 : ℝ) / 109 ≤ Real.log ((109 : ℝ) / 100) := by
    have h2 := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < (109 : ℝ) / 100)
    have h3 : (1 : ℝ) - ((109 : ℝ) / 100)⁻¹ = (9 : ℝ) / 109 := by norm_num
    linarith [h2, h3.le, h3.ge]
  have hlog10 : Real.log 10 ≤ 9 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10); linarith
  linarith [hlogN, hlog109, hlog10]

/-- **Numeric absorption.**  If `τ ≤ 2^{log(2N)/L2}` with `L2 ≥ 81` and `log N ≥ 10`, then
`τ^4 ≤ N^{1/16}`. -/
theorem pow4_card_divisors_le {n : ℕ} {N L2 : ℝ}
    (hNpos : 0 < N) (hN10 : 10 ≤ Real.log N) (hL2 : 81 ≤ L2)
    (hτ : ((n.divisors.card : ℕ) : ℝ) ≤ (2 : ℝ) ^ (Real.log (2 * N) / L2)) :
    (((n.divisors.card : ℕ) : ℝ)) ^ 4 ≤ N ^ ((1 : ℝ) / 16) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hN1 : 1 ≤ N := by
    have h : 0 < Real.log N := by linarith
    exact le_of_lt ((Real.log_pos_iff hNpos.le).mp h)
  have hK0 : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hdiv : 4 * Real.log (2 * N) / L2 ≤ 4 * Real.log (2 * N) / 81 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) hL2
  have hKle : Real.log (2 * N) ≤ 1.1 * Real.log N := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hNpos)]
    nlinarith [Real.log_two_lt_d9, hN10]
  have hlogNnn : 0 ≤ Real.log N := le_trans (by norm_num) hN10
  have hcoef : 4.4 * Real.log 2 / 81 ≤ (1 : ℝ) / 16 := by
    nlinarith [Real.log_two_lt_d9]
  have hstep1 : (4 * Real.log (2 * N) / L2) * Real.log 2
      ≤ (4 * Real.log (2 * N) / 81) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hdiv hlog2pos.le
  have hstep2 : (4 * Real.log (2 * N) / 81) * Real.log 2
      ≤ (4.4 * Real.log 2 / 81) * Real.log N := by
    have h1 : 4 * Real.log (2 * N) / 81 ≤ 4 * (1.1 * Real.log N) / 81 :=
      div_le_div_of_nonneg_right (by linarith) (by norm_num)
    have h2 := mul_le_mul_of_nonneg_right h1 hlog2pos.le
    have heq : (4 * (1.1 * Real.log N) / 81) * Real.log 2
        = (4.4 * Real.log 2 / 81) * Real.log N := by ring
    linarith [h2, heq.le, heq.ge]
  have hstep3 : (4.4 * Real.log 2 / 81) * Real.log N ≤ ((1 : ℝ) / 16) * Real.log N :=
    mul_le_mul_of_nonneg_right hcoef hlogNnn
  have hlogineq : (4 * Real.log (2 * N) / L2) * Real.log 2
      ≤ ((1 : ℝ) / 16) * Real.log N := le_trans (le_trans hstep1 hstep2) hstep3
  have h2pow : (2 : ℝ) ^ (4 * Real.log (2 * N) / L2) ≤ N ^ ((1 : ℝ) / 16) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.rpow_def_of_pos hNpos]
    apply Real.exp_le_exp.mpr
    linarith [hlogineq]
  have hτ4 : (((n.divisors.card : ℕ) : ℝ)) ^ 4
      ≤ ((2 : ℝ) ^ (Real.log (2 * N) / L2)) ^ 4 :=
    pow_le_pow_left₀ (by positivity) hτ 4
  have heq2 : ((2 : ℝ) ^ (Real.log (2 * N) / L2)) ^ 4
      = (2 : ℝ) ^ (4 * Real.log (2 * N) / L2) := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (Real.log (2 * N) / L2)) 4,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [heq2] at hτ4
  exact le_trans hτ4 h2pow

/-- **The target.**  On the support of a round-6 coefficient, `τ(|z|²)^4 ≤ N^{1/16}`, under the
lower-range hypothesis `1/10 ≤ θ√N`. -/
theorem beta6_tau4_le {Pa : Work.FITop.Params} {φ : ℝ} {z0 : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β)
    (hu : (1 : ℝ) / 10 ≤ Pa.θ * Real.sqrt Pa.N) {z : GaussianInt} (hz : β z ≠ 0) :
    ((((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)) ^ (4 : ℕ)
      ≤ (Pa.N : ℝ) ^ ((1 : ℝ) / 16) := by
  have hτ := beta6_gnorm_divisors_card_le hβ hz
  have hL := log_x_ge_22027 hu
  have hL2 := sq_loglog_ge_81 hL
  have hlogN := ten_le_log_N hu
  exact pow4_card_divisors_le (by linarith [Pa.hN1]) hlogN hL2 hτ

end

end Work.FIArea2.R6
