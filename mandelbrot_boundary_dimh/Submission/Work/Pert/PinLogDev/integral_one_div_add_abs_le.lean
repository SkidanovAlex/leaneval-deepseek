import Mathlib
import Submission.Work.Pert.PinLogDev.Prim
import Submission.Work.Pert.PinLogDev.G_left_le
import Submission.Work.Pert.PinLogDev.G_center_le
import Submission.Work.Pert.PinLogDev.G_right_le

/-!
# The integral bound `∫ (C + |s - M|)⁻¹ ≤ 2 log (1 + (b - a)/(2C))`

For `C > 0` and `a ≤ b` we bound the interval integral of `s ↦ (C + |s - M|)⁻¹` by its value in
the extreme case: the substitution `s ↦ s - M` makes the integral an increment of the primitive
`G C x = ∫ t in 0..x, (C + |t|)⁻¹` over the window `[a - M, b - M]`, and the maximum of that
increment over windows of a fixed length `L = b - a` is attained when `M` is the midpoint of
`[a, b]` (the window is centred at `0`), where it equals `2 log (1 + L/(2C))`.

The three position cases (`M` left of `[a, b]`, `M` inside, `M` right of `[a, b]`) are the lemmas
`G_left_le`, `G_center_le`, `G_right_le`; they rest on the evaluations of `G` in
`Submission/Work/Pert/PinLogDev/Prim.lean`.
-/

namespace Work.Pert.PinLogDev

open MeasureTheory

/-- The substitution `s ↦ s - M` writes the target integral as the increment of the primitive
`G C` over the window `[a - M, b - M]`. -/
lemma integral_eq_G (C M a b : ℝ) (hC : 0 < C) :
    (∫ s in a..b, (1 : ℝ) / (C + |s - M|)) = G C (b - M) - G C (a - M) := by
  have hcont : Continuous fun v : ℝ => (C + |v|)⁻¹ :=
    (by fun_prop : Continuous fun v : ℝ => C + |v|).inv₀ (fun v => by positivity)
  have hsub : (∫ s in a..b, (C + |s - M|)⁻¹) = ∫ v in a - M..b - M, (C + |v|)⁻¹ := by
    have h := intervalIntegral.integral_comp_add_right (f := fun v : ℝ => (C + |v|)⁻¹)
      (a := a) (b := b) (d := -M)
    simpa only [sub_eq_add_neg] using h
  have hadj : (∫ v in a - M..b - M, (C + |v|)⁻¹) = G C (b - M) - G C (a - M) := by
    have h := intervalIntegral.integral_add_adjacent_intervals
      (f := fun v : ℝ => (C + |v|)⁻¹) (a := (0 : ℝ)) (b := a - M) (c := b - M) (μ := volume)
      (hcont.intervalIntegrable 0 (a - M)) (hcont.intervalIntegrable (a - M) (b - M))
    simp only [G] at h ⊢
    linarith
  rw [show (∫ s in a..b, (1 : ℝ) / (C + |s - M|)) = ∫ s in a..b, (C + |s - M|)⁻¹ by
        simp only [one_div]]
  rw [hsub, hadj]

theorem integral_one_div_add_abs_le (C M a b : ℝ) (hC : 0 < C) (hab : a ≤ b) :
    (∫ s in a..b, (1 : ℝ) / (C + |s - M|)) ≤ 2 * Real.log (1 + (b - a) / (2 * C)) := by
  have hL0 : 0 ≤ b - a := by linarith
  rw [integral_eq_G C M a b hC]
  have hq : b - M = (a - M) + (b - a) := by ring
  rw [hq]
  rcases lt_or_ge (a - M) (-(b - a)) with hcase | hcase
  · exact G_left_le C (b - a) (a - M) hC hL0 (le_of_lt hcase)
  · rcases lt_or_ge 0 (a - M) with hcase2 | hcase2
    · exact G_right_le C (b - a) (a - M) hC hL0 (le_of_lt hcase2)
    · exact G_center_le C (b - a) (a - M) hC hL0 hcase hcase2

end Work.Pert.PinLogDev
