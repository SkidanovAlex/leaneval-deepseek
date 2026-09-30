import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedVariables false

namespace Work.BMF

/-- The partial sums `x ↦ ∑_{n ∈ ℕ ∩ [x, x+h]} a n` are Borel measurable:
they are the composition of the (countably valued) map
`x ↦ (⌈x⌉₊, ⌊x+h⌋₊)` with a function on the countable type `ℕ × ℕ`. -/
theorem measurable_window_sum (a : ℕ → ℂ) (h : ℝ) :
    Measurable fun x : ℝ => ∑ n ∈ natIcc x (x + h), a n := by
  show Measurable fun x : ℝ => ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊, a n
  have hmk : Measurable fun x : ℝ => (⌈x⌉₊, ⌊x + h⌋₊) :=
    Measurable.prodMk Nat.measurable_ceil
      (Nat.measurable_floor.comp (measurable_id.add measurable_const))
  have hG : Measurable fun p : ℕ × ℕ => ∑ n ∈ Finset.Icc p.1 p.2, a n :=
    measurable_of_countable _
  exact hG.comp hmk

theorem aemeasurable_window_avg (a : ℕ → ℂ) (X h₁ h₂ : ℝ) (hX : 1 ≤ X) (hh₂ : h₂ ≤ 2 * X) :
    AEMeasurable (fun x : ℝ => (1 / h₁) * (∑ n ∈ Work.BMF.natIcc x (x + h₁), a n)
        - (1 / h₂) * (∑ n ∈ Work.BMF.natIcc x (x + h₂), a n))
      (MeasureTheory.volume.restrict (Set.Ioc X (2 * X))) := by
  have hsub : Measurable (fun x : ℝ =>
      (1 / h₁) * (∑ n ∈ natIcc x (x + h₁), a n)
        - (1 / h₂) * (∑ n ∈ natIcc x (x + h₂), a n)) :=
    ((measurable_window_sum a h₁).const_mul (1 / h₁)).sub
      ((measurable_window_sum a h₂).const_mul (1 / h₂))
  exact hsub.aemeasurable

end Work.BMF
