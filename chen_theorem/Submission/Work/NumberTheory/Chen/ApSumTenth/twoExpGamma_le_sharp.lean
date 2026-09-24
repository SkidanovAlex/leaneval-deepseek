/-
# The numerical bound `2 e^γ ≤ 3.59`

The sharp linear-sieve upper-bound profile carries the constant `2 e^γ`, where `γ` is the
Euler–Mascheroni constant.  This file provides the (deliberately generous, but still sharp)
numerical bound `2 e^γ ≤ 3.59` needed to evaluate the window sum of the switched AP-sum.

Mathlib only contains the crude estimates `1/2 < γ < 2/3`, and `2 e^(2/3) ≈ 3.895 > 3.59`, so the
upper bound has to be improved.  We use the strict decrease of `n ↦ harmonic n - log n` towards
`γ`: at `n = 100` this gives `γ < harmonic 100 - log 100 ≤ 0.5823`.  The exponential at the
rational point `5823/10000` is then bounded with the Taylor remainder of `Real.exp_bound'`.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.ApSumTenth.Defs

namespace Work.NumberTheory.Chen.ApSumTenth

open Real

/-- An explicit numerical upper bound for the Euler–Mascheroni constant, far better than
Mathlib's `γ < 2/3`: `γ < 5823/10000 = 0.5823`. -/
theorem eulerMascheroniConstant_lt_sharp :
    Real.eulerMascheroniConstant < (5823 : ℝ) / 10000 := by
  -- `100 ≠ 0`, so the upper approximating sequence is `harmonic 100 - log 100`.
  have hseq : Real.eulerMascheroniSeq' 100 = (harmonic 100 : ℝ) - Real.log 100 := by
    rw [Real.eulerMascheroniSeq']; norm_num
  have h1 := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' 100
  rw [hseq] at h1
  -- `harmonic 100 ≤ 5.187377518`.
  have hH : (harmonic 100 : ℝ) ≤ 5187377518 / 1000000000 := by norm_num [harmonic]
  -- `log 100 = 2 log 2 + 2 log 5 ≥ 4.6051701852`.
  have hlog : (46051701852 / 10000000000 : ℝ) ≤ Real.log 100 := by
    have h2 := Real.log_two_gt_d9
    have h5 := Real.log_five_gt_d9
    have hp : Real.log (100 : ℝ) = 2 * Real.log 2 + 2 * Real.log 5 := by
      rw [show (100 : ℝ) = 2 ^ 2 * 5 ^ 2 by norm_num,
        Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      norm_num
    rw [hp]; linarith
  linarith

/-- `exp` at the rational point `5823/10000`, bounded by `1795/1000` with the Taylor remainder
of `Real.exp_bound'` at order `5`. -/
theorem exp_5823_div_10000_le :
    Real.exp ((5823 : ℝ) / 10000) ≤ 1795 / 1000 := by
  have h := Real.exp_bound' (x := (5823 : ℝ) / 10000) (by norm_num) (by norm_num)
    (n := 5) (by norm_num)
  norm_num at h
  linarith

theorem twoExpGamma_le_sharp :
    Work.NumberTheory.Chen.ApSumTenth.twoExpGamma ≤ (359 : ℝ) / 100 := by
  unfold twoExpGamma
  have hmono : Real.exp Real.eulerMascheroniConstant < Real.exp ((5823 : ℝ) / 10000) :=
    Real.exp_lt_exp.mpr eulerMascheroniConstant_lt_sharp
  have hexp := exp_5823_div_10000_le
  linarith

end Work.NumberTheory.Chen.ApSumTenth
