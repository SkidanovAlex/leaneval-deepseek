import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.InvLog
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Real Asymptotics MeasureTheory
open scoped Chebyshev Topology

namespace Commons.NumberTheory.Chebyshev

/-! Chebyshev's `θ(t) = ∑_{p ≤ t} log p` grows at least linearly: there exist
`c > 0` and `A ≥ 2` such that `c·t ≤ Chebyshev.theta t` for every `t ≥ A`.

The proof combines Mathlib's explicit Chebyshev lower bound
`Chebyshev.theta_ge'` (`(t - 1) * log 2 - log (t + 2) - 2 * √t * log t ≤ θ t`
for `t ≥ 1`) with the elementary asymptotic `log t = o(√t)` as `t → ∞`
(`isLittleO_log_rpow_atTop`), which absorbs the two error terms.  -/

namespace ThetaLinearLower

/-- Eventually, `log t ≤ ε * √t` for any fixed `ε > 0` (as `t → ∞`). -/
private lemma eventually_log_le_sqrt (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, log t ≤ ε * √t := by
  have hlog : log =o[atTop] (fun x : ℝ => x ^ (1 / 2 : ℝ)) := by
    simpa using
      (isLittleO_log_rpow_atTop (r := (1 / 2 : ℝ)) (by norm_num : 0 < (1 / 2 : ℝ)))
  have hle : ∀ᶠ t : ℝ in atTop, ‖log t‖ ≤ ε * ‖t ^ (1 / 2 : ℝ)‖ :=
    (isLittleO_iff.mp hlog) hε
  filter_upwards [hle, eventually_ge_atTop (1 : ℝ)] with t htle ht1
  have ht0 : 0 ≤ t := by linarith
  rw [Real.norm_of_nonneg (Real.log_nonneg ht1),
    Real.norm_of_nonneg (Real.rpow_nonneg ht0 (1 / 2 : ℝ))] at htle
  simpa [Real.sqrt_eq_rpow] using htle

/-- For `t ≥ 2`, `log (t + 2) ≤ 2 * log t`. -/
private lemma log_add_two_le_two_log {t : ℝ} (ht : 2 ≤ t) : log (t + 2) ≤ 2 * log t := by
  have hpos : 0 < t + 2 := by linarith
  have hsq : t + 2 ≤ t ^ 2 := by
    have hm : 0 ≤ (t - 2) * (t + 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith
  calc
    log (t + 2) ≤ log (t ^ 2) := Real.log_le_log hpos hsq
    _ = 2 * log t := by
      rw [Real.log_pow]
      norm_num

/-- For `t ≥ 1`, `√t ≤ t`. -/
private lemma sqrt_le_self {t : ℝ} (ht : 1 ≤ t) : √t ≤ t := by
  have ht0 : 0 ≤ t := by linarith
  have hsqrt1 : 1 ≤ √t := by
    simpa using (Real.sqrt_le_sqrt ht : √(1 : ℝ) ≤ √t)
  calc
    √t = √t * 1 := by ring
    _ ≤ √t * √t := mul_le_mul_of_nonneg_left hsqrt1 (Real.sqrt_nonneg t)
    _ = (√t) ^ 2 := by ring
    _ = t := Real.sq_sqrt ht0

end ThetaLinearLower

/-- Chebyshev's `θ(t) = ∑_{p ≤ t} log p` grows at least linearly: there exist
`c > 0` and `A ≥ 2` such that `c·t ≤ Chebyshev.theta t` for every `t ≥ A`.
A complete proof exists in `Submission/ThetaLower.lean`
(`Submission.BoundedMultiplicativeFunctions.theta_linear_lower`). -/
theorem theta_linear_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 2 ≤ A ∧ ∀ t : ℝ, A ≤ t →
      c * t ≤ Chebyshev.theta t := by
  let L : ℝ := log 2
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hev : ∀ᶠ t : ℝ in atTop, (L / 4) * t ≤ Chebyshev.theta t := by
    have hlog : ∀ᶠ t : ℝ in atTop, log t ≤ (L / 32) * √t :=
      ThetaLinearLower.eventually_log_le_sqrt (L / 32) (div_pos hLpos (by norm_num))
    filter_upwards [hlog, eventually_ge_atTop (2 : ℝ)] with t htlog ht2
    have ht1 : 1 ≤ t := by linarith
    have hθ := Chebyshev.theta_ge' ht1
    have hb1 : log (t + 2) ≤ (L / 16) * √t := by
      calc
        log (t + 2) ≤ 2 * log t := ThetaLinearLower.log_add_two_le_two_log ht2
        _ ≤ 2 * ((L / 32) * √t) :=
          mul_le_mul_of_nonneg_left htlog (by norm_num : (0 : ℝ) ≤ 2)
        _ = (L / 16) * √t := by ring
    have ht0 : 0 ≤ t := by linarith
    have hb2 : 2 * √t * log t ≤ (L / 16) * t := by
      calc
        2 * √t * log t ≤ 2 * √t * ((L / 32) * √t) := by
          exact mul_le_mul_of_nonneg_left htlog (by nlinarith [Real.sqrt_nonneg t])
        _ = (L / 16) * (√t ^ 2) := by ring
        _ = (L / 16) * t := by rw [Real.sq_sqrt ht0]
    have hsum : log (t + 2) + 2 * √t * log t + L ≤
        (L / 16) * √t + (L / 16) * t + L := by
      nlinarith [hb1, hb2]
    have hsle : √t ≤ t := ThetaLinearLower.sqrt_le_self ht1
    have hmult : (L / 16) * √t ≤ (L / 16) * t :=
      mul_le_mul_of_nonneg_left hsle (div_nonneg hLpos.le (by norm_num))
    have hsum2 : (L / 16) * √t + (L / 16) * t + L ≤
        (L / 16) * t + (L / 16) * t + L := by
      nlinarith [hmult]
    have hfrac : 0 ≤ (5 / 8 : ℝ) * t - 1 := by nlinarith
    have hprod : 0 ≤ L * ((5 / 8 : ℝ) * t - 1) := mul_nonneg hLpos.le hfrac
    have hpoly : (L / 16) * t + (L / 16) * t + L ≤ (3 / 4 : ℝ) * L * t := by
      nlinarith
    have hErr : log (t + 2) + 2 * √t * log t + L ≤ (3 / 4 : ℝ) * L * t := by
      exact le_trans hsum (le_trans hsum2 hpoly)
    have hlin : (L / 4) * t ≤ (t - 1) * L - log (t + 2) - 2 * √t * log t := by
      nlinarith [hErr]
    exact le_trans hlin hθ
  rcases eventually_atTop.mp hev with ⟨A0, hA0⟩
  refine ⟨L / 4, div_pos hLpos (by norm_num), max 2 A0, le_max_left 2 A0, ?_⟩
  intro t ht
  exact hA0 t (le_trans (le_max_right 2 A0) ht)

end Commons.NumberTheory.Chebyshev
