import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.Tactic.NormNum.RealSqrt
import Submission.Commons.NumberTheory.DirichletCharacter.L_lower_re_two_explicit
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_mid_strip_le
import Submission.Commons.NumberTheory.DirichletCharacter.completedLogDeriv_two_le
import Submission.Port.LogDerivCompat
import Submission.Commons.Analysis.Series.summable_log_div_sq_and_tsum_le_one

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Complex DirichletCharacter ArithmeticFunction
open scoped Real LSeries.notation
set_option autoImplicit false
noncomputable section

namespace Commons.NumberTheory.DirichletCharacter

/-! ### The logarithmic derivative of `L(χ, ·)` on the line `Re s = 2`

For `Re s > 1` the logarithmic derivative of a Dirichlet L-function is the negative of the
L-series of the von Mangoldt function twisted by `χ`
(`DirichletCharacter.LSeries_twist_vonMangoldt_eq`), so on the line `Re s = 2` it is bounded
by `∑' n, log n / n^2 ≤ 1`. -/

/-- On the line `Re s = 2`, the twisted von Mangoldt L-series of `χ` is bounded by `1`. -/
lemma norm_LSeries_twist_vonMangoldt_two_le {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (T : ℝ) :
    ‖L (↗χ * ↗Λ) ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤ 1 := by
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  have hs : 1 < s.re := by simp [s]
  have hsum : LSeriesSummable (↗χ * ↗Λ) s :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  have hsum' : Summable (fun n : ℕ => ‖LSeries.term (↗χ * ↗Λ) s n‖) :=
    summable_norm_iff.mpr hsum
  have hle : ‖L (↗χ * ↗Λ) s‖ ≤ ∑' n : ℕ, ‖LSeries.term (↗χ * ↗Λ) s n‖ :=
    norm_tsum_le_tsum_norm hsum'
  have hbound : ∀ n : ℕ, ‖LSeries.term (↗χ * ↗Λ) s n‖ ≤ Real.log (n : ℝ) / (n : ℝ) ^ 2 := by
    intro n
    rcases eq_or_ne n 0 with hn0 | hn0
    · subst hn0
      simp [LSeries.term_zero]
    · rw [LSeries.norm_term_eq]
      simp only [hn0, if_false]
      have hsre : s.re = 2 := by simp [s]
      rw [hsre]
      have hnormχ : ‖(χ (n : ZMod N) : ℂ)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      have hΛnonneg : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
      have hΛle : Λ n ≤ Real.log (n : ℝ) := vonMangoldt_le_log
      have hmul : ‖(χ (n : ZMod N) : ℂ) * ((Λ n : ℝ) : ℂ)‖ ≤ Real.log (n : ℝ) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛnonneg]
        calc ‖(χ (n : ZMod N) : ℂ)‖ * Λ n ≤ 1 * Real.log (n : ℝ) :=
              mul_le_mul hnormχ hΛle hΛnonneg (by norm_num)
          _ = Real.log (n : ℝ) := one_mul _
      have hpow : (0 : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := by positivity
      calc ‖(χ (n : ZMod N) : ℂ) * ((Λ n : ℝ) : ℂ)‖ / (n : ℝ) ^ (2 : ℝ)
          ≤ Real.log (n : ℝ) / (n : ℝ) ^ (2 : ℝ) := div_le_div_of_nonneg_right hmul hpow
        _ = Real.log (n : ℝ) / (n : ℝ) ^ 2 := by norm_num
  calc ‖L (↗χ * ↗Λ) s‖ ≤ ∑' n : ℕ, ‖LSeries.term (↗χ * ↗Λ) s n‖ := hle
    _ ≤ ∑' n : ℕ, Real.log (n : ℝ) / (n : ℝ) ^ 2 :=
        Summable.tsum_le_tsum hbound hsum' Commons.Analysis.Series.summable_log_div_sq_and_tsum_le_one.1
    _ ≤ 1 := Commons.Analysis.Series.summable_log_div_sq_and_tsum_le_one.2

/-- The logarithmic derivative of `LFunction χ` at `s` (with `1 < Re s`) is the negative of
the L-series of `Λ · χ`. -/
lemma logDeriv_LFunction_eq_neg_twist {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    logDeriv (LFunction χ) s = - L (↗χ * ↗Λ) s := by
  have hident := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have hder := DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs
  have hval := DirichletCharacter.LFunction_eq_LSeries χ hs
  rw [logDeriv_apply, hder, hval, hident]
  ring

/-- Tight bound for the logarithmic derivative of a non-trivial Dirichlet L-function on the
line `Re s = 2`: `‖logDeriv (LFunction χ) (2+iT)‖ ≤ 1`. -/
lemma norm_logDeriv_L_two_le_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) :
    ‖logDeriv (LFunction χ) ((2 : ℂ) + Complex.I * (T : ℂ))‖ ≤ 1 := by
  let s : ℂ := (2 : ℂ) + Complex.I * (T : ℂ)
  have hs : 1 < s.re := by simp [s]
  rw [logDeriv_LFunction_eq_neg_twist χ hs, norm_neg]
  exact norm_LSeries_twist_vonMangoldt_two_le χ T

end Commons.NumberTheory.DirichletCharacter
