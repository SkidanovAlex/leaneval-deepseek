import Mathlib
import Submission.Work.BMF.ztw_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.N7

open Filter

/-- `twD L u = ztD (2 * twT L u)` is eventually uniformly (in `u`) larger than any constant: `twT L u ≥ L^2 exp(L^{1/10}) + 7`, so `2 * twT L u + 3 ≥ exp(L^{1/10})` for `L ≥ 1` and `log (2*twT+3) ≥ L^{1/10}`. -/
theorem twD_uniform_ge (M : ℝ) : ∀ᶠ L : ℝ in Filter.atTop, ∀ u : ℝ, M ≤ Work.BMF.twD L u := by
  -- Unconditional lower bound: for `L ≥ 1` and every `u`, `twD L u ≥ L^{3/35}`.
  have key : ∀ {L : ℝ}, 1 ≤ L → ∀ u : ℝ, L ^ (3 / 35 : ℝ) ≤ Work.BMF.twD L u := by
    intro L hL u
    have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
    set h := 2 * Work.BMF.twT L u with hh
    -- `h ≥ 2 * L^2 * exp(L^{1/10}) ≥ exp(L^{1/10})` for `L ≥ 1`.
    have hexp_le : Real.exp (L ^ (1 / 10 : ℝ)) ≤ h + 3 := by
      have h1 : Real.exp (L ^ (1 / 10 : ℝ)) ≤ 2 * L ^ 2 * Real.exp (L ^ (1 / 10 : ℝ)) + 3 := by
        nlinarith [Real.exp_pos (L ^ (1 / 10 : ℝ)), sq_nonneg (L - 1), sq_nonneg L]
      have h2 := Work.BMF.le_twT L u
      rw [hh]
      nlinarith [Real.exp_pos (L ^ (1 / 10 : ℝ))]
    -- hence `log (h + 3) ≥ L^{1/10}`.
    have hlog_ge : L ^ (1 / 10 : ℝ) ≤ Real.log (h + 3) := by
      have := Real.log_le_log (Real.exp_pos (L ^ (1 / 10 : ℝ))) hexp_le
      rwa [Real.log_exp] at this
    have hlog_nn : 0 ≤ Real.log (h + 3) :=
      le_trans (Real.rpow_nonneg (le_of_lt hLpos) _) hlog_ge
    -- hence `L^{3/35} = (L^{1/10})^{6/7} ≤ (log (h+3))^{6/7}`.
    have hpow : L ^ (3 / 35 : ℝ) ≤ (Real.log (h + 3)) ^ (6 / 7 : ℝ) := by
      have hnn : 0 ≤ L ^ (1 / 10 : ℝ) := Real.rpow_nonneg (le_of_lt hLpos) _
      have hres := Real.rpow_le_rpow hnn hlog_ge (by norm_num : (0 : ℝ) ≤ 6 / 7)
      have hml : (L ^ (1 / 10 : ℝ)) ^ (6 / 7 : ℝ) = L ^ (3 / 35 : ℝ) := by
        rw [← Real.rpow_mul (le_of_lt hLpos)]
        norm_num
      rwa [hml] at hres
    -- the second `ztD` factor is `≥ 1` since `log (h+3) > 1`.
    have hsecond : (1 : ℝ) ≤ Real.log 3 + Real.log (Real.log (h + 3)) := by
      have h4 : (7 : ℝ) ≤ h + 3 := by
        have := Work.BMF.seven_le_twT L u; rw [hh]; linarith
      have h1 : (1 : ℝ) < Real.log (h + 3) :=
        lt_of_lt_of_le Work.BMF.lt_one_log_seven (Real.log_le_log (by norm_num) h4)
      have h2 : 0 ≤ Real.log (Real.log (h + 3)) := Real.log_nonneg (le_of_lt h1)
      linarith [Work.BMF.one_le_log_three]
    have hfirst_nn : 0 ≤ Real.log (h + 3) ^ (6 / 7 : ℝ) := Real.rpow_nonneg hlog_nn _
    have hstep : Real.log (h + 3) ^ (6 / 7 : ℝ) ≤ Work.BMF.ztD h := by
      rw [Work.BMF.ztD]
      exact le_mul_of_one_le_right hfirst_nn hsecond
    calc L ^ (3 / 35 : ℝ) ≤ (Real.log (h + 3)) ^ (6 / 7 : ℝ) := hpow
      _ ≤ Work.BMF.ztD h := hstep
      _ = Work.BMF.twD L u := by rw [Work.BMF.twD, hh]
  -- `L^{3/35} → ∞`, so eventually it is `≥ M`, and `L ≥ 1`.
  have htend : Tendsto (fun L : ℝ => L ^ (3 / 35 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hev : ∀ᶠ L : ℝ in atTop, M ≤ L ^ (3 / 35 : ℝ) :=
    htend.eventually (eventually_ge_atTop M)
  filter_upwards [hev, eventually_ge_atTop (1 : ℝ)] with L hM hL
  intro u
  exact le_trans hM (key hL u)

end Work.BMF.N7
