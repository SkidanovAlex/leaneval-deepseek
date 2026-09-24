import Mathlib
import Submission.Work.NumberTheory.Chen.ApSumTenth.Defs

/-!
# A lower bound for `2e^γ`

`Work.NumberTheory.Chen.ApSumTenth.twoExpGamma_ge_seven_halves : 7/2 ≤ twoExpGamma`
(`twoExpGamma = 2e^γ = 3.5621…`).

This is the *lower* companion of the proved `twoExpGamma_le_sharp` (`≤ 3.59`); it is what the
small-`σ` cube-mass credit (`cubeExcessSharp_NOTES.md` §23.6) needs: on `[1,3]` one has
`riPhi σ = (3 − σ + Ctot)/σ` with `Ctot = 2e^γ − 3`, so `Ctot ≥ 1/2` — equivalently
`2e^γ ≥ 7/2` — gives the model fraction `Ctot/(2 + Ctot) ≥ 1/5` at `σ = 1`.

Route (the same one as `Commons/NumberTheory/Totient/sum_mu_sq_ge_log_alt.gamma_gt_11_20`):
Mathlib's **increasing** sequence `eulerMascheroniSeq n = H_n − log(n+1)` is `< γ`, so it suffices
to exhibit `γ > 0.56`; then `e^γ ≥ e^{0.56} ≥ 7/4` by the truncated exponential series.  All the
numerics are exact rational computations (`norm_num`) plus `Real.log_lt_iff_lt_exp` and
`Real.sum_le_exp_of_nonneg`.
-/

namespace Work.NumberTheory.Chen.ApSumTenth

open Finset

/-- `0.56 < γ`, from `eulerMascheroniSeq 100 = H_100 − log 101` (Mathlib's increasing sequence),
`log 101 < 4.62` (from the Taylor expansion of `exp`) and `H_100 > 5.18`. -/
theorem eulerMascheroni_gt_56_100 : (0.56 : ℝ) < Real.eulerMascheroniConstant := by
  have hlog : Real.log 101 < (4.62 : ℝ) := by
    rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 101)]
    have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 4.62) 30
    have hval : (101 : ℝ) < ∑ k ∈ Finset.range 30, (4.62 : ℝ) ^ k / k.factorial := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
    linarith
  have hH : (harmonic 100 : ℝ) > 0.56 + 4.62 := by
    rw [harmonic]; push_cast; norm_num
  have hseq : (0.56 : ℝ) < Real.eulerMascheroniSeq 100 := by
    rw [Real.eulerMascheroniSeq]
    linarith
  exact lt_trans hseq (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 100)

/-- The truncated exponential series at `0.56` exceeds `7/4`. -/
theorem seven_quarters_le_exp_56 : (7 / 4 : ℝ) ≤ Real.exp (0.56 : ℝ) := by
  have hsum := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.56) 6
  have hval : (7 / 4 : ℝ) ≤ ∑ k ∈ Finset.range 6, (0.56 : ℝ) ^ k / k.factorial := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  linarith

theorem twoExpGamma_ge_seven_halves : (7 : ℝ) / 2 ≤ twoExpGamma := by
  have h1 : (7 / 4 : ℝ) ≤ Real.exp (0.56 : ℝ) := seven_quarters_le_exp_56
  have h2 : Real.exp (0.56 : ℝ) ≤ Real.exp Real.eulerMascheroniConstant :=
    Real.exp_le_exp.mpr eulerMascheroni_gt_56_100.le
  rw [twoExpGamma]
  linarith

end Work.NumberTheory.Chen.ApSumTenth
