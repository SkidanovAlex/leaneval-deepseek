import Mathlib
import Submission.Work.TMContract.Defs

namespace Work.TMComp.IDSPrufer

/-- In the exceptional cell `t - ⌊t + 1/2⌋ = -1/2` the Prüfer step is the floor itself
(`pruferStep a t = ⌊t + 1/2⌋`), and the direction `(a cos πt - sin πt, cos πt)` equals
`(cos π·pruferStep, sin π·pruferStep)` because `π t = π⌊t+1/2⌋ - π/2` and `sin` of an
integer multiple of `π` vanishes. -/
theorem pruferStep_dir_half (a t : ℝ) (hcase : t - (⌊t + 1 / 2⌋ : ℝ) = -1 / 2) :
    ∃ r : ℝ, 0 < r ∧
      (a * Real.cos (Real.pi * t) - Real.sin (Real.pi * t), Real.cos (Real.pi * t)) =
        (r * Real.cos (Real.pi * Work.TMContract.pruferStep a t),
         r * Real.sin (Real.pi * Work.TMContract.pruferStep a t)) := by
  refine ⟨1, by norm_num, ?_⟩
  -- In the exceptional cell the definition of `pruferStep` returns the floor.
  have hF : Work.TMContract.pruferStep a t = (⌊t + 1 / 2⌋ : ℝ) := by
    unfold Work.TMContract.pruferStep
    rw [if_pos hcase]
  rw [hF]
  have ht : t = (⌊t + 1 / 2⌋ : ℝ) - 1 / 2 := by linarith
  have harg : Real.pi * t = Real.pi * (⌊t + 1 / 2⌋ : ℝ) - Real.pi / 2 := by
    conv_lhs => rw [ht]
    ring
  have hcos : Real.cos (Real.pi * t) = Real.sin (Real.pi * (⌊t + 1 / 2⌋ : ℝ)) := by
    rw [harg, Real.cos_sub_pi_div_two]
  have hsin : Real.sin (Real.pi * t) = -Real.cos (Real.pi * (⌊t + 1 / 2⌋ : ℝ)) := by
    rw [harg, Real.sin_sub_pi_div_two]
  have hsinn : Real.sin (Real.pi * (⌊t + 1 / 2⌋ : ℝ)) = 0 := by
    rw [mul_comm]; exact Real.sin_int_mul_pi ⌊t + 1 / 2⌋
  refine Prod.ext ?_ ?_
  · rw [hcos, hsin, hsinn]; ring
  · rw [hcos, hsinn]; ring

end Work.TMComp.IDSPrufer
