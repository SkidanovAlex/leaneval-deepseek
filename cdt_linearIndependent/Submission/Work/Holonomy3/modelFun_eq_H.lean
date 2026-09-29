import Mathlib
import Submission.Work.Holonomy3.model_deps

namespace Work.Holonomy3

/-- The floor identity underlying Lemma `lcm-2`: for `t ≥ 1`,
`⌊(t + max 0 (w-1))/max 1 w⌋ = ⌊(t-1)/max 1 w⌋ + 1`.  Indeed
`t + max 0 (w-1) = (t-1) + max 1 w` and `max 1 w ≠ 0`. -/
lemma floor_div_max_eq (w t : ℝ) (ht : 1 ≤ t) :
    ⌊(t + max 0 (w - 1)) / max 1 w⌋₊ = ⌊(t - 1) / max 1 w⌋₊ + 1 := by
  have hB : max 1 w ≠ 0 := by positivity
  have hsum : t + max 0 (w - 1) = (t - 1) + max 1 w := by
    rcases le_total w 1 with h | h
    · rw [max_eq_left h, max_eq_left (by linarith : w - 1 ≤ (0:ℝ))]; ring
    · rw [max_eq_right h, max_eq_right (by linarith : (0:ℝ) ≤ w - 1)]; ring
  have key : ((t - 1) + max 1 w) / max 1 w = (t - 1) / max 1 w + 1 := by
    rw [add_div, div_self hB]
  rw [hsum, key, Nat.floor_add_one (by positivity)]

/-- For `0 ≤ w` and `t ≥ 1` the model function of Lemma `lcm-2` equals
`H ⌊(t-1)/max 1 w⌋ + (t/(⌊(t-1)/max 1 w⌋+1) - w)⁺`.

Indeed `⌊(t + max 0 (w-1))/max 1 w⌋ = ⌊(t-1)/max 1 w⌋ + 1` for `t ≥ 1`: for `w ≤ 1`
both sides read `⌊t⌋` and `⌊t-1⌋+1`, and for `w ≥ 1` the argument is `(t-1)/w + 1`.
Use `Submission.CDT.IntegratedLcm.modelFun_of_le_one`, `modelFun_of_lt`,
`Submission.CDT.Lcm2Bound.H_eq`, `Nat.floor_add_one`, `Nat.floor_sub_one`. -/
theorem modelFun_eq_H (w : ℝ) (hw : 0 ≤ w) (t : ℝ) (ht : 1 ≤ t) :
    Submission.CDT.IntegratedLcm.modelFun w t
      = Submission.CDT.Lcm2Bound.H ⌊(t - 1) / max 1 w⌋₊
        + max (t / (((⌊(t - 1) / max 1 w⌋₊ + 1 : ℕ)) : ℝ) - w) 0 := by
  rcases lt_or_eq_of_le ht with hlt | heq
  · -- `t > 1`: unfold the model function as harmonic + correction
    have h1 : Submission.CDT.IntegratedLcm.harmonicFun w t
        = Submission.CDT.Lcm2Bound.H ⌊(t - 1) / max 1 w⌋₊ := by
      rw [Submission.CDT.IntegratedLcm.harmonicFun, Submission.CDT.Lcm2Bound.H_eq]
    have h2 : Submission.CDT.IntegratedLcm.correctionFun w t
        = max (t / (((⌊(t - 1) / max 1 w⌋₊ + 1 : ℕ)) : ℝ) - w) 0 := by
      rw [Submission.CDT.IntegratedLcm.correctionFun, floor_div_max_eq w t ht]
    rw [Submission.CDT.IntegratedLcm.modelFun_of_lt w t hlt, h1, h2]
  · -- `t = 1`: both sides are `max (1 - w) 0`
    subst heq
    rw [Submission.CDT.IntegratedLcm.modelFun_of_le_one w 1 le_rfl]
    simp [Submission.CDT.Lcm2Bound.H]

end Work.Holonomy3
