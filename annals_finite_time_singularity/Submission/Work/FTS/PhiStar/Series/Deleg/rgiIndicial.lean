import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt
import Submission.Work.FTS.PhiStar.Radial.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Series.Deleg

theorem rgiIndicial (α : ℝ) (hα : 0 < α) (m : ℕ) :
    (-α ^ 2 * Work.FTS.PhiStar.Series.rgiSn α m * (Work.FTS.PhiStar.Series.rgiSn α m - 1)
        - α * (5 + α) * Work.FTS.PhiStar.Series.rgiSn α m
        + Work.FTS.PhiStar.Radial.lamR m = 0) ∧
    (-α ^ 2 * Work.FTS.PhiStar.Series.rgiSp α m * (Work.FTS.PhiStar.Series.rgiSp α m - 1)
        - α * (5 + α) * Work.FTS.PhiStar.Series.rgiSp α m
        + Work.FTS.PhiStar.Radial.lamR m = 0) ∧
    (α ^ 2 * Work.FTS.PhiStar.Series.rgiK α m
        * (Work.FTS.PhiStar.Series.rgiSp α m - Work.FTS.PhiStar.Series.rgiSn α m) = 1) := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have h4m : (4 * (m : ℝ) + 5) ≠ 0 := by positivity
  -- the indicial exponents satisfy `s⁺ - s⁻ = (4m+5)/α`
  have hsp_sub : Work.FTS.PhiStar.Series.rgiSp α m - Work.FTS.PhiStar.Series.rgiSn α m
      = (4 * (m : ℝ) + 5) / α := by
    simp only [Work.FTS.PhiStar.Series.rgiSp, Work.FTS.PhiStar.Series.rgiSn]
    field_simp
    ring
  refine ⟨?_, ?_, ?_⟩
  · -- `s⁻` solves the indicial equation `-α²s(s-1) - α(5+α)s + λ_m = 0`
    simp only [Work.FTS.PhiStar.Series.rgiSn, Work.FTS.PhiStar.Radial.lamR]
    field_simp
    ring
  · simp only [Work.FTS.PhiStar.Series.rgiSp, Work.FTS.PhiStar.Radial.lamR]
    field_simp
    ring
  · -- the Wronskian normalisation: `α²·K·(s⁺-s⁻) = 1`
    rw [hsp_sub]
    simp only [Work.FTS.PhiStar.Series.rgiK]
    field_simp

end Work.FTS.PhiStar.Series.Deleg
