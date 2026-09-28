import Mathlib
import Submission.Work.HP.Defs

/-!
# Eventual dominance of `wOf B ^ (n-2)` over `(log B)^{1/2}`

`wOf B = log B / log log B` grows like `log B / log log B`, while the right-hand
side threshold `(log B)^{1/2}` is much smaller for large `B`.  We prove that for
`n ≥ 3` the power `wOf B ^ (n-2)` (exponent `n - 2 ≥ 1`) eventually dominates
`(log B)^{1/2}`.

The argument uses only the elementary comparison `log t ≤ t^{1/2}` for large `t`
(which follows from `Real.log =o[atTop] (·^{1/2})`): with `t = log B` this gives
`log log B ≤ (log B)^{1/2}`, whence `wOf B ≥ (log B)^{1/2}` for large `B`, and
then monotonicity of the power map on `[1, ∞)` yields the claim.
-/

set_option autoImplicit false

open Filter

namespace Work.HP

theorem w_arith_growth (n : ℕ) (hn : 3 ≤ n) :
    ∀ᶠ B in atTop, Real.log B ^ ((1 : ℝ) / 2) ≤ wOf B ^ (n - 2) := by
  -- `log t ≤ t^{1/2}` for all sufficiently large `t`.
  have hlog_sqrt : ∀ᶠ t : ℝ in atTop, Real.log t ≤ t ^ ((1 : ℝ) / 2) := by
    have hh := isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [Asymptotics.isLittleO_iff] at hh
    filter_upwards [hh zero_lt_one, eventually_ge_atTop (0 : ℝ)] with t ht ht0
    calc Real.log t ≤ |Real.log t| := le_abs_self _
      _ = ‖Real.log t‖ := (Real.norm_eq_abs _).symm
      _ ≤ 1 * ‖t ^ ((1 : ℝ) / 2)‖ := ht
      _ = ‖t ^ ((1 : ℝ) / 2)‖ := one_mul _
      _ = |t ^ ((1 : ℝ) / 2)| := Real.norm_eq_abs _
      _ = t ^ ((1 : ℝ) / 2) := abs_of_nonneg (Real.rpow_nonneg ht0 _)
  have hbig : ∀ᶠ B in atTop, Real.exp 2 ≤ B := eventually_ge_atTop _
  -- For large `B`, `sqrt (log B) ≤ wOf B`.
  have hkey : ∀ᶠ B in atTop, Real.sqrt (Real.log B) ≤ wOf B := by
    filter_upwards [Real.tendsto_log_atTop.eventually hlog_sqrt, hbig] with B hll hB
    have hB2 : (2 : ℝ) ≤ Real.log B := by
      have := Real.log_le_log (Real.exp_pos 2) hB
      rwa [Real.log_exp] at this
    have hlogpos : 0 < Real.log B := by linarith
    have hloglogpos : 0 < Real.log (Real.log B) := by
      have h1 : Real.log 2 ≤ Real.log (Real.log B) := Real.log_le_log (by norm_num) hB2
      have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      linarith
    have hsqrtpos : 0 ≤ Real.sqrt (Real.log B) := Real.sqrt_nonneg _
    have h2 : Real.log (Real.log B) ≤ Real.sqrt (Real.log B) := by
      rw [Real.sqrt_eq_rpow]; exact hll
    show Real.sqrt (Real.log B) ≤ wOf B
    unfold wOf
    rw [le_div_iff₀ hloglogpos]
    calc Real.sqrt (Real.log B) * Real.log (Real.log B)
        ≤ Real.sqrt (Real.log B) * Real.sqrt (Real.log B) :=
          mul_le_mul_of_nonneg_left h2 hsqrtpos
      _ = Real.log B := by rw [← sq, Real.sq_sqrt (le_of_lt hlogpos)]
  filter_upwards [hkey, hbig] with B hE hB
  have hB2 : (2 : ℝ) ≤ Real.log B := by
    have := Real.log_le_log (Real.exp_pos 2) hB
    rwa [Real.log_exp] at this
  have hlogpos : 0 < Real.log B := by linarith
  have hsqrt_ge1 : 1 ≤ Real.sqrt (Real.log B) := by
    have hs := Real.sq_sqrt (le_of_lt hlogpos)
    have hnn := Real.sqrt_nonneg (Real.log B)
    nlinarith [hs, hnn, hB2]
  have hw1 : 1 ≤ wOf B := le_trans hsqrt_ge1 hE
  have hk : 1 ≤ n - 2 := by omega
  have hE' : Real.log B ^ ((1 : ℝ) / 2) ≤ wOf B := by
    rw [Real.sqrt_eq_rpow] at hE; exact hE
  calc Real.log B ^ ((1 : ℝ) / 2) ≤ wOf B := hE'
    _ = wOf B ^ 1 := (pow_one _).symm
    _ ≤ wOf B ^ (n - 2) := pow_le_pow_right₀ hw1 hk

end Work.HP
