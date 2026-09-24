import Mathlib
import Submission.Work.ChenPlan.LinearSieve.JR2.Defs
import Submission.Work.ChenPlan.LinearSieve.JR2.numeric_helpers
import Submission.Work.ChenPlan.LinearSieve.Numerics.riUp_le_Utab
import Submission.Work.NumberTheory.Chen.BTermCount.riUp_eq_twoExpGamma_div

namespace Work.ChenPlan.LinearSieve.JR2

/-- **The shift `riUp σ'' ≤ riUp σ + O(δ)` folded into `Utab`.**  For `σ'' ≤ σ`, `σ'' ≥ 1`, `σ > 2`
and `σ - σ'' ≤ 1/500000`: if `σ'' ≥ 2` use `hLip` (`RiLipschitz`, constant `C ≤ 100`); if `σ'' < 2`
then `σ < 3` and the closed form `riUp u = 2e^γ/u` on `[1,3]` (`BTermCount.riUp_eq_twoExpGamma_div`)
gives a better bound.  The accumulated sharp error `ε·1000·10100·errH σ'' ≤ 1/4000`
(`JR2.numeric_helpers.sharpness_error_le`) and `riUp σ + 1/1000 ≤ Utab σ`
(`Numerics.riUp_le_Utab`) leave the result below `Utab σ`.

Suggested imports: `Submission.Work.ChenPlan.LinearSieve.JR2.Defs`,
`Submission.Work.ChenPlan.LinearSieve.JR2.numeric_helpers`,
`Submission.Work.ChenPlan.LinearSieve.Numerics.riUp_le_Utab`,
`Submission.Work.NumberTheory.Chen.BTermCount.riUp_eq_twoExpGamma_div`. -/
theorem riUp_shift_le_utab (hLip : Work.ChenPlan.LinearSieve.JR2.RiLipschitz) {σ σ'' ε η : ℝ}
    (hε0 : 0 ≤ ε) (hεη : ε ≤ min η 1 / 10 ^ 11) (hη : 0 ≤ η)
    (hσ1 : 1 ≤ σ) (hσ2 : 2 < σ) (hs1 : 1 ≤ σ'') (hsle : σ'' ≤ σ)
    (hdiff : σ - σ'' ≤ 1 / 500000) :
    Work.NumberTheory.Chen.APSwitchUpper.riUp σ''
        + ε * (1000 * 10100) * Work.NumberTheory.Chen.APSwitchUpper.errH σ''
      ≤ Submission.ChenPlan.Utab σ + η := by
  -- The accumulated sharp error is below `1/4000`.
  have herr : ε * (1000 * 10100) * Work.NumberTheory.Chen.APSwitchUpper.errH σ'' ≤ 1 / 4000 :=
    sharpness_error_le ε η hε0 hεη σ''
  -- `riUp σ + 1/1000 ≤ Utab σ` at the unshifted point.
  have hriU : Work.NumberTheory.Chen.APSwitchUpper.riUp σ + 1 / 1000
      ≤ Submission.ChenPlan.Utab σ := by
    have h := Work.ChenPlan.LinearSieve.Numerics.riUp_le_Utab σ hσ1
    simpa [Work.NumberTheory.Chen.APSwitchUpper.riUp] using h
  -- The shift costs at most `1/5000`, uniformly in the two regimes.
  have hshift : Work.NumberTheory.Chen.APSwitchUpper.riUp σ''
      ≤ Work.NumberTheory.Chen.APSwitchUpper.riUp σ + 1 / 5000 := by
    by_cases h2 : 2 ≤ σ''
    · -- `σ'' ≥ 2`: Lipschitz with constant `C ≤ 100`.
      obtain ⟨C, hC0, hC100, hlipUp, -⟩ := hLip
      have h := hlipUp σ σ'' h2 hsle
      have h1 : Work.NumberTheory.Chen.APSwitchUpper.riUp σ''
            - Work.NumberTheory.Chen.APSwitchUpper.riUp σ ≤ C * (σ - σ'') :=
        le_trans (le_abs_self _) h
      have h2' : C * (σ - σ'') ≤ 100 * (1 / 500000) :=
        mul_le_mul hC100 hdiff (by linarith) (by norm_num)
      linarith
    · -- `σ'' < 2`: then `σ < 3` and both closed forms `riUp u = 2e^γ/u` apply.
      rw [not_le] at h2
      have hσ3 : σ ≤ 3 := by linarith
      have hs3 : σ'' ≤ 3 := by linarith
      have hσ'' : Work.NumberTheory.Chen.APSwitchUpper.riUp σ'' =
          2 * Real.exp Real.eulerMascheroniConstant / σ'' :=
        Work.NumberTheory.Chen.BTermCount.riUp_eq_twoExpGamma_div σ'' hs1 hs3
      have hσ : Work.NumberTheory.Chen.APSwitchUpper.riUp σ =
          2 * Real.exp Real.eulerMascheroniConstant / σ :=
        Work.NumberTheory.Chen.BTermCount.riUp_eq_twoExpGamma_div σ hσ1 hσ3
      have hσpos : 0 < σ := by linarith
      have hσ''pos : 0 < σ'' := by linarith
      have hpos : 0 < σ * σ'' := mul_pos hσpos hσ''pos
      have hle : (σ - σ'') / (σ * σ'') ≤ 1 / 500000 := by
        rw [div_le_iff₀ hpos]
        nlinarith
      have hnonneg : 0 ≤ (σ - σ'') / (σ * σ'') := by positivity
      have hkey : 2 * Real.exp Real.eulerMascheroniConstant * ((σ - σ'') / (σ * σ''))
          ≤ 1 / 5000 := by
        have h4 : 2 * Real.exp Real.eulerMascheroniConstant ≤ 4 :=
          le_of_lt two_exp_gamma_lt_four
        have h5 := mul_le_mul h4 hle hnonneg (by norm_num : (0 : ℝ) ≤ 4)
        linarith
      have hsub : Work.NumberTheory.Chen.APSwitchUpper.riUp σ''
            - Work.NumberTheory.Chen.APSwitchUpper.riUp σ
          = 2 * Real.exp Real.eulerMascheroniConstant * ((σ - σ'') / (σ * σ'')) := by
        rw [hσ'', hσ]
        field_simp
      linarith
  -- `1/5000 + 1/4000 ≤ 1/1000`, and `η ≥ 0`.
  linarith

end Work.ChenPlan.LinearSieve.JR2
