import Mathlib
import Submission.Work.BMF.halasz_defs
import Submission.Work.BMF.halasz_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

/-- `Zrcp 3 = 1/2 + 1/3 = 5/6`: the primes at most `3` are `2` and `3`. -/
private lemma Zrcp_three : Work.BMF.Zrcp 3 = 5 / 6 := by
  norm_num [Work.BMF.Zrcp, Nat.primesLE, Nat.primesBelow, Finset.sum_filter,
    Finset.sum_range_succ]

/-- **`exp (Zrcp x) / log x` is bounded below by an absolute constant for `x ≥ 3`**, with the
Mertens input as a parameter.

Given `|Zrcp t − log log t| ≤ C₀` for `t ≥ 11`: for `x ≥ 11` this gives
`exp (Zrcp x) ≥ exp (−C₀) · log x`, and for `3 ≤ x ≤ 11` the ratio `exp (Zrcp x)/log x` is at
least `exp (5/6)/log 11` by monotonicity of `Zrcp` (its minimum over `[3,11]` is at `x = 3`),
since `Zrcp 3 = 1/2 + 1/3`. -/
theorem casdiv_zrcp_log (C₀ : ℝ) (hC₀ : 0 < C₀)
    (hMertens : ∀ t : ℝ, 11 ≤ t → |Work.BMF.Zrcp t - Real.log (Real.log t)| ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      1 ≤ C * Real.exp (Work.BMF.Zrcp x) / Real.log x := by
  refine ⟨max (Real.exp C₀) (Real.log 11 / Real.exp (5 / 6)), ?_, ?_⟩
  · exact lt_max_of_lt_left (Real.exp_pos C₀)
  · intro x hx
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hCnn : (0 : ℝ) ≤ max (Real.exp C₀) (Real.log 11 / Real.exp (5 / 6)) :=
      le_trans (Real.exp_pos C₀).le (le_max_left _ _)
    -- clear the denominator; it remains to show `log x ≤ C * exp (Zrcp x)`
    rw [le_div_iff₀ hlogx, one_mul]
    rcases le_or_gt 11 x with h11 | h11
    · -- large range `x ≥ 11`: use the Mertens hypothesis
      have hM : Real.log (Real.log x) - C₀ ≤ Work.BMF.Zrcp x := by
        have := (abs_le.mp (hMertens x h11)).1
        linarith
      have hE : Real.log x / Real.exp C₀ ≤ Real.exp (Work.BMF.Zrcp x) := by
        calc Real.log x / Real.exp C₀
            = Real.exp (Real.log (Real.log x) - C₀) := by
              rw [Real.exp_sub, Real.exp_log hlogx]
          _ ≤ Real.exp (Work.BMF.Zrcp x) := Real.exp_le_exp.mpr hM
      have hA : Real.exp C₀ ≤ max (Real.exp C₀) (Real.log 11 / Real.exp (5 / 6)) :=
        le_max_left _ _
      have hEpos : (0 : ℝ) ≤ Real.log x / Real.exp C₀ := by positivity
      have hprod := mul_le_mul hA hE hEpos hCnn
      have hsimp : Real.exp C₀ * (Real.log x / Real.exp C₀) = Real.log x := by
        field_simp
      linarith [hprod, hsimp]
    · -- small range `3 ≤ x ≤ 11`: monotonicity of `Zrcp` and of `log`
      have hxle : x ≤ 11 := le_of_lt h11
      have hlogxle : Real.log x ≤ Real.log 11 := Real.log_le_log (by linarith) hxle
      have hexp : Real.exp (5 / 6) ≤ Real.exp (Work.BMF.Zrcp x) := by
        apply Real.exp_le_exp.mpr
        rw [← Zrcp_three]
        exact Work.BMF.Zrcp_mono hx
      have hA : Real.log 11 / Real.exp (5 / 6)
          ≤ max (Real.exp C₀) (Real.log 11 / Real.exp (5 / 6)) := le_max_right _ _
      have hprod := mul_le_mul hA hexp (Real.exp_pos (5 / 6)).le hCnn
      have hsimp : Real.log 11 / Real.exp (5 / 6) * Real.exp (5 / 6) = Real.log 11 := by
        field_simp
      linarith [hprod, hsimp, hlogxle]

end Work.BMF.mrlas
