/-
# `FIArea2/R6/WPropNormAux` — the (9.6) pointwise bound `‖β z‖ ≤ τ(|z|²)` on the round-6 support
-/
import Mathlib
import Submission.Work.FITop4.Defs6
import Submission.Work.FIArea2.R6.BetaFacts6
import Submission.Work.FIArea3.CrudeBracketReduce

set_option maxHeartbeats 1000000

namespace Work.FIArea2.R6

open scoped BigOperators

/-- **`‖β z‖ ≤ τ(|z|²)`** for a round-6 coefficient: on the support `β z = q·p·μ·γ` with
`|q|,|p|,|μ| ≤ 1` and `|γ(n;C)| ≤ τ(n)` (the (9.6) bound). -/
theorem beta6_norm_le_tau {Pa : Work.FITop.Params} {φ : ℝ} {z0 z : GaussianInt}
    {β : GaussianInt → ℂ} (hβ : Work.FITop4.IsBetaCoeff6 Pa φ z0 β) :
    ‖β z‖ ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
  obtain ⟨q, p, -, -, hq0, hq1, -, -, hp0, hp1, -, -, hform⟩ := hβ
  rw [hform z]
  split_ifs with hz
  · have hqp : ‖((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq0 _) (hp0 _))]
      calc q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) ≤ 1 * 1 :=
            mul_le_mul (hq1 _) (hp1 _) (hp0 _) (by norm_num)
        _ = 1 := by ring
    have hmu : ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖ ≤ 1 := by
      have h1 := ArithmeticFunction.abs_moebius_le_one (n := Work.FIPlan.gnorm z)
      have h1' : ‖((ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, ← Int.cast_abs]
        exact_mod_cast h1
      rwa [Complex.ofReal_intCast] at h1'
    have hg : ‖(Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)‖
        ≤ (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact Work.FITop3.abs_gammaTrunc_le Pa.C (Work.FIPlan.gnorm z)
    calc ‖((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)
            * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
            * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)‖
        = ‖((q (Complex.arg z.toComplex - φ) * p (Work.FIPlan.gnorm z) : ℝ) : ℂ)‖
            * ‖(ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)‖
            * ‖(Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ 1 * 1 * (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) :=
          mul_le_mul (mul_le_mul hqp hmu (norm_nonneg _) (by norm_num)) hg (norm_nonneg _)
            (by positivity)
      _ = (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ) := by ring
  · simp


/-- `1 < log x` for `x ≥ 3`. -/
theorem one_lt_log_x (Pa : Work.FITop.Params) : (1 : ℝ) < Real.log (Pa.x : ℝ) := by
  have h3 : (3 : ℝ) ≤ (Pa.x : ℝ) := by exact_mod_cast Pa.hx
  have hA : (1 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
  have hB : Real.log 3 ≤ Real.log (Pa.x : ℝ) := Real.log_le_log (by norm_num) h3
  linarith

/-- `θ ≤ (log x)^{-2^20}`. -/
theorem theta_le_log_pow (Pa : Work.FITop.Params) :
    Pa.θ ≤ (Real.log (Pa.x : ℝ)) ^ (-((2 : ℝ) ^ (20 : ℕ))) := by
  rw [Pa.hθ]
  refine Real.rpow_le_rpow_of_exponent_le (le_of_lt (one_lt_log_x Pa)) ?_
  have hA' : (2 : ℝ) ^ (20 : ℕ) ≤ Pa.A' := by linarith [Pa.hA', Pa.hA]
  linarith

/-- If `1/10 ≤ u = θ√N` then `1 ≤ log N`. -/
theorem one_le_log_N_of_u_ge {Pa : Work.FITop.Params}
    (hu : (1 : ℝ) / 10 ≤ Pa.θ * Real.sqrt Pa.N) :
    (1 : ℝ) ≤ Real.log (Pa.N : ℝ) := by
  have hlogx1 : (1 : ℝ) < Real.log (Pa.x : ℝ) := one_lt_log_x Pa
  have hθle : Pa.θ ≤ (Real.log (Pa.x : ℝ)) ^ (-((2 : ℝ) ^ (20 : ℕ))) := theta_le_log_pow Pa
  have hN1 : (1 : ℝ) ≤ (Pa.N : ℝ) := by exact_mod_cast Pa.hN1
  have hNpos : (0 : ℝ) < (Pa.N : ℝ) := by linarith
  have hxpos : (0 : ℝ) < Real.log (Pa.x : ℝ) := lt_trans zero_lt_one hlogx1
  have hpos : 0 < (Real.log (Pa.x : ℝ)) ^ ((2 : ℝ) ^ (20 : ℕ)) := Real.rpow_pos_of_pos hxpos _
  -- `(log x)^{2^20} ≤ θ⁻¹`
  have hinv : (Real.log (Pa.x : ℝ)) ^ ((2 : ℝ) ^ (20 : ℕ)) ≤ Pa.θ⁻¹ := by
    have h2 : Pa.θ ≤ (((Real.log (Pa.x : ℝ)) ^ ((2 : ℝ) ^ (20 : ℕ)))⁻¹) := by
      rw [← Real.rpow_neg hxpos.le]; exact hθle
    have h1 : Pa.θ * (Real.log (Pa.x : ℝ)) ^ ((2 : ℝ) ^ (20 : ℕ)) ≤ 1 := by
      calc Pa.θ * (Real.log (Pa.x : ℝ)) ^ ((2 : ℝ) ^ (20 : ℕ))
          ≤ (((Real.log (Pa.x : ℝ)) ^ ((2 : ℝ) ^ (20 : ℕ)))⁻¹)
              * (Real.log (Pa.x : ℝ)) ^ ((2 : ℝ) ^ (20 : ℕ)) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = 1 := by field_simp
    have h3 : (Real.log (Pa.x : ℝ)) ^ ((2 : ℝ) ^ (20 : ℕ)) * Pa.θ ≤ 1 := by linarith [h1]
    have h4 := (le_div_iff₀ Pa.hθ0).mpr h3
    rwa [one_div] at h4
  have hu' : (1 : ℝ) / 10 ≤ Real.sqrt (Pa.N : ℝ) * Pa.θ := by
    rw [mul_comm]; exact hu
  have hsqrt : (1 : ℝ) / 10 * (Real.log (Pa.x : ℝ)) ^ ((2 : ℝ) ^ (20 : ℕ))
      ≤ Real.sqrt (Pa.N : ℝ) := by
    have h2 : (1 : ℝ) / 10 / Pa.θ ≤ Real.sqrt (Pa.N : ℝ) := by
      rw [div_le_iff₀ Pa.hθ0]; exact hu'
    have h3 : (1 : ℝ) / 10 * (Real.log (Pa.x : ℝ)) ^ ((2 : ℝ) ^ (20 : ℕ)) ≤ (1 : ℝ) / 10 / Pa.θ := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv (by norm_num)
    linarith [h2, h3]
  have hlogsqrt : Real.log ((1 : ℝ) / 10 * (Real.log (Pa.x : ℝ)) ^ ((2 : ℝ) ^ (20 : ℕ)))
      ≤ Real.log (Real.sqrt (Pa.N : ℝ)) :=
    Real.log_le_log (by positivity) hsqrt
  rw [Real.log_mul (by norm_num) (ne_of_gt hpos), Real.log_rpow hxpos,
    Real.log_sqrt hNpos.le] at hlogsqrt
  have hlog10 : Real.log ((10 : ℝ)⁻¹) = - Real.log 10 := Real.log_inv 10
  rw [one_div, hlog10] at hlogsqrt
  have hlog10' : Real.log (10 : ℝ) ≤ 9 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 10); linarith
  have hℓ : (1 : ℝ) / 16 ≤ Real.log (Real.log (Pa.x : ℝ)) := Work.FIArea3.pj_loglog_ge Pa
  have hbig : (2 : ℝ) ^ (21 : ℕ) * (1 / 16 : ℝ) ≤ (2 : ℝ) ^ (21 : ℕ) * Real.log (Real.log (Pa.x : ℝ)) := by
    rw [show (2 : ℝ) ^ (21 : ℕ) = (2 : ℝ) ^ (20 : ℕ) * 2 from by norm_num]
    exact mul_le_mul_of_nonneg_left hℓ (by positivity)
  have hnum : (2 : ℝ) ^ (21 : ℕ) * (1 / 16 : ℝ) = 131072 := by norm_num
  rw [hnum] at hbig
  have hpow : (2 : ℝ) ^ (21 : ℕ) = 2 * (2 : ℝ) ^ (20 : ℕ) := by norm_num
  have hA : (2 : ℝ) ^ (21 : ℕ) * Real.log (Real.log (Pa.x : ℝ)) - 18
      ≤ 2 * Real.log (Real.sqrt (Pa.N : ℝ)) := by
    rw [hpow, Real.log_sqrt hNpos.le]; linarith [hlogsqrt, hlog10']
  have hA' : (2 : ℝ) ^ (21 : ℕ) * Real.log (Real.log (Pa.x : ℝ)) - 18
      ≤ Real.log (Pa.N : ℝ) := by
    rw [Real.log_sqrt hNpos.le] at hA
    have h2 : 2 * (Real.log (Pa.N : ℝ) / 2) = Real.log (Pa.N : ℝ) := by ring
    linarith [hA, h2]
  linarith [hA', hbig]

end Work.FIArea2.R6
