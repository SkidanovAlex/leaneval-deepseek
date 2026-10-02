import Mathlib
import Submission.Work.Bottcher.Defs
import Submission.Work.Bottcher.CritBasic
import Submission.Work.Bottcher.Green.green_comm
import Submission.Work.ParamRaysCrit.GreenBound
import Submission.Work.ParamRays.Green

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Bottcher.Contraction

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Helper lemmas -/

/-- The Green function of the tricorn commutes with the iterates of `T_c` up to the
factor `2 ^ n`: `G_c (T_c^[n] z) = 2^n G_c z`. -/
theorem green_iterate_Tantibar' (c z : ℂ) (n : ℕ) :
    Work.Bottcher.green c ((Tantibar c)^[n] z) = (2 : ℝ) ^ n * Work.Bottcher.green c z := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply', Work.Bottcher.Green.green_comm, ih, pow_succ]
      ring

/-- **The critical orbit grows at most like `exp (2^m G_c(0))`, uniformly in `m`.**

Explicitly, with the constant `log (max 2 ‖c‖)`:

`‖T_c^[m] 0‖ ≤ exp (2^m * G_c(0) + log (max 2 ‖c‖))` for every `m : ℕ`.

The proof is a pointwise case split.  If `w = T_c^[m] 0` has `‖w‖ ≤ max 2 ‖c‖`, the bound is
immediate from `exp (log (max 2 ‖c‖)) = max 2 ‖c‖` and the nonnegativity of `G_c(0)`.  Otherwise
`max 2 ‖c‖ < ‖w‖`, so the two-sided bound `|G_c w - log ‖w‖| ≤ log 2`
(`Work.ParamRays.log_sub_le_greenFun`, transported to `Work.Bottcher.green` by
`green_eq_greenFun`) gives `log ‖w‖ ≤ G_c w + log 2 = 2^m G_c(0) + log 2`, and
`log 2 ≤ log (max 2 ‖c‖)`. -/
theorem orbit_zero_bound_log (c : ℂ) :
    ∀ m : ℕ, ‖(Tantibar c)^[m] 0‖ ≤
      Real.exp ((2 : ℝ) ^ m * Work.Bottcher.greenParam c + Real.log (max 2 ‖c‖)) := by
  intro m
  have hG : 0 ≤ Work.Bottcher.greenParam c := Work.Bottcher.Green.green_nonneg c 0
  have hpos : 0 < max 2 ‖c‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _)
  have hlog2 : Real.log 2 ≤ Real.log (max 2 ‖c‖) :=
    Real.log_le_log (by norm_num) (le_max_left _ _)
  cases m with
  | zero =>
      simp only [Function.iterate_zero_apply, norm_zero]
      exact le_of_lt (Real.exp_pos _)
  | succ k =>
      set w : ℂ := (Tantibar c)^[k + 1] 0 with hw
      have hGw : Work.Bottcher.green c w = (2 : ℝ) ^ (k + 1) * Work.Bottcher.greenParam c := by
        rw [hw, green_iterate_Tantibar' c 0 (k + 1), Work.Bottcher.greenParam_def]
      by_cases hle : ‖w‖ ≤ max 2 ‖c‖
      · calc ‖w‖ ≤ max 2 ‖c‖ := hle
          _ = Real.exp (Real.log (max 2 ‖c‖)) := (Real.exp_log hpos).symm
          _ ≤ Real.exp ((2 : ℝ) ^ (k + 1) * Work.Bottcher.greenParam c
                + Real.log (max 2 ‖c‖)) := by
              apply Real.exp_le_exp.mpr
              have : 0 ≤ (2 : ℝ) ^ (k + 1) * Work.Bottcher.greenParam c :=
                mul_nonneg (by positivity) hG
              linarith
      · have hgt : max 2 ‖c‖ < ‖w‖ := not_le.mp hle
        have hwpos : 0 < ‖w‖ := lt_of_lt_of_le hpos hgt.le
        have hlog := Work.ParamRays.log_sub_le_greenFun c w hgt
        have hgf : Work.ParamRays.greenFun c w = (2 : ℝ) ^ (k + 1) * Work.Bottcher.greenParam c := by
          rw [← green_eq_greenFun, hGw]
        rw [hgf] at hlog
        have hlog' : Real.log ‖w‖ ≤
            (2 : ℝ) ^ (k + 1) * Work.Bottcher.greenParam c + Real.log (max 2 ‖c‖) := by
          linarith
        calc ‖w‖ ≤ Real.exp (Real.log ‖w‖) := (Real.log_le_iff_le_exp hwpos).mp le_rfl
          _ ≤ Real.exp ((2 : ℝ) ^ (k + 1) * Work.Bottcher.greenParam c
                + Real.log (max 2 ‖c‖)) :=
              Real.exp_le_exp.mpr hlog'

/--
There is a constant `C`, depending on `c` only, with

`‖T_c^[m] 0‖ ≤ exp (2^m · G_c 0 + C)`   for every `m : ℕ`.

This is the uniform (in `m`) version of "the critical orbit of the tricorn grows like
`exp (2^m G_c 0)`"; it is what makes the critical orbit stay below the level balls
`{‖T_c^n z‖ ≤ exp (2^n G_c 0 + C)}` used for the preconnectedness of `{G_c ≤ G_c 0}`.

Proof by a pointwise case split on `m` (each case handled independently):

* `Work.Bottcher.Green.green_nonneg c 0` gives `0 ≤ greenParam c`.
* If `‖T_c^[m] 0‖ ≤ max 2 ‖c‖` then it suffices that `C ≥ log (max 2 ‖c‖)`.
* Otherwise `w := T_c^[m] 0` lies above `max 2 ‖c‖`, so
  `Work.ParamRays.log_sub_le_greenFun` (transported by `Work.Bottcher.CritBasic.green_eq`) gives
  `log ‖w‖ ≤ green c w + log 2`, and `green c (T_c^m 0) = 2^m * greenParam c`
  (`Work.Bottcher.Green.green_comm` iterated, or `Work.ParamRays.greenFun_orbit`), so
  `‖T_c^[m] 0‖ ≤ exp (2^m greenParam c + log 2)` and it suffices that `C ≥ log 2`.

So `C := Real.log (max 2 ‖c‖)` works (`≥ 0` since `max 2 ‖c‖ ≥ 2`).
-/
theorem exists_orbit_zero_bound (c : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ,
      ‖(LeanEval.ComplexAnalysis.Tantibar c)^[m] 0‖ ≤
        Real.exp ((2 : ℝ) ^ m * Work.Bottcher.greenParam c + C) := by
  refine ⟨Real.log (max 2 ‖c‖), ?_, orbit_zero_bound_log c⟩
  exact Real.log_nonneg (le_trans (by norm_num : (1 : ℝ) ≤ 2) (le_max_left _ _))

end Work.Bottcher.Contraction
