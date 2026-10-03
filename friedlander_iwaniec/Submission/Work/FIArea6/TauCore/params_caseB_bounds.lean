/-
# `Submission.Work.FIArea6.TauCore.params_caseB_bounds`

**The three parameter bounds of the "case B" arithmetic of `τCore`.**

Under the extra hypothesis `exp 8 ≤ x` (the left end of the range on which the case-B
computation is invoked), the numerical set-up `Params` of `Work.FITop.Defs` gives

* `3 ≤ N` and `1 ≤ log N`, i.e. `N` is `≥ 3` and its logarithm is `≥ 1`; this is the constant
  "`L ≥ 1`" used in `caseB_arith_core` (`L = log N`) and in every geometric-series bound below;
* `θ < 1` (in fact `θ = (log x)^{-A'} ≤ 1/8^{2^{20}}`), the hypothesis `hθ1` of
  `caseB_arith_core`.

The proofs are elementary: `exp 8 ≤ x` gives `log x ≥ 8 > 1`, and the range (4.6)
`x^{1/4+η} < N` with `η > 0` gives `N > x^{1/4} ≥ (exp 8)^{1/4} = exp 2 > 3`; finally
`θ = (log x)^{-A'}` with `A' ≥ 2A + 2^{20} > 0` and `log x > 1` is `< 1`.
-/
import Mathlib
import Submission.Work.FITop.Defs
import Submission.Work.FIArea6Road.TailLogNStep

namespace Work.FIArea6.TauCore

theorem params_caseB_bounds (Pa : Work.FITop.Params) (hx : Real.exp 8 ≤ (Pa.x : ℝ)) :
    1 ≤ Real.log Pa.N ∧ 3 ≤ Pa.N ∧ Pa.θ < 1 := by
  -- `x ≥ exp 8 > 1`, so `x > 0` and `log x ≥ 8 > 1`.
  have hx1 : (1 : ℝ) < (Pa.x : ℝ) := by
    have := Real.one_lt_exp_iff.mpr (by norm_num : (0 : ℝ) < 8)
    linarith
  have hxpos : (0 : ℝ) < (Pa.x : ℝ) := lt_trans zero_lt_one hx1
  have hlogx8 : 8 ≤ Real.log (Pa.x : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 8) hx
    rwa [Real.log_exp] at h
  -- (4.6): `N > x^{1/4+η} ≥ x^{1/4} ≥ (exp 8)^{1/4} = exp 2`.
  have hNexp2 : Real.exp 2 < Pa.N := by
    have hlt : (Pa.x : ℝ) ^ ((1 : ℝ) / 4) < (Pa.x : ℝ) ^ ((1 : ℝ) / 4 + Pa.η) :=
      Real.rpow_lt_rpow_of_exponent_lt hx1 (by linarith [Pa.hη])
    have hle : (Real.exp 8) ^ ((1 : ℝ) / 4) ≤ (Pa.x : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (le_of_lt (Real.exp_pos 8)) hx (by norm_num)
    have heq : (Real.exp 8) ^ ((1 : ℝ) / 4) = Real.exp 2 := by
      rw [← Real.exp_mul]; norm_num
    linarith [Pa.hNlo]
  -- `exp 2 = (exp 1)² > 2² > 3`.
  have h3exp : (3 : ℝ) < Real.exp 2 := by
    have h : (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
    have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    rw [h2]; nlinarith
  have hNpos : (0 : ℝ) < Pa.N := by linarith [Real.exp_pos 2]
  have hlogN1 : 1 ≤ Real.log Pa.N := by
    have h : Real.exp 1 ≤ Pa.N := by
      have h12 : Real.exp 1 < Real.exp 2 := by rw [Real.exp_lt_exp]; norm_num
      linarith
    exact (Real.le_log_iff_exp_le hNpos).mpr h
  -- `θ = (log x)^{-A'}` with `log x > 1` and `A' > 0`.
  have hA'pos : 0 < Pa.A' := by
    have : (0 : ℝ) < (2 : ℝ) ^ (20 : ℕ) := by positivity
    linarith [Pa.hA, Pa.hA']
  refine ⟨hlogN1, by linarith, ?_⟩
  rw [Pa.hθ]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by linarith : (1 : ℝ) < Real.log (Pa.x : ℝ))
    (by linarith : -Pa.A' < 0)

end Work.FIArea6.TauCore
