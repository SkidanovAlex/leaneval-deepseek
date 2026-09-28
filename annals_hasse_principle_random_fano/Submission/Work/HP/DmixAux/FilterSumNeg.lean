import Mathlib

namespace Work.HP.DmixAux

/-- Removing an antipodal pair `{x, -x}` (`x ≠ -x`) from a sum of an even function `g`
subtracts `2 * g x` from the total. -/
theorem FilterSumNeg {β : Type*} [DecidableEq β] [Neg β] (Y : Finset β) (x : β) (g : β → ℝ)
    (hx : x ∈ Y) (hx' : -x ∈ Y) (hne : x ≠ -x) (heven : g (-x) = g x) :
    ∑ y ∈ Y.filter (fun y => y ≠ x ∧ y ≠ -x), g y = ∑ y ∈ Y, g y - 2 * g x := by
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not Y (fun y => y ≠ x ∧ y ≠ -x) g
  have hcomp : Y.filter (fun y => ¬ (y ≠ x ∧ y ≠ -x)) = {x, -x} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨_, h⟩
      rcases Classical.em (y = x) with hyx | hyx
      · exact Or.inl hyx
      · refine Or.inr ?_
        by_contra hc
        exact h ⟨hyx, hc⟩
    · rintro (rfl | rfl)
      · exact ⟨hx, fun h => h.1 rfl⟩
      · exact ⟨hx', fun h => h.2 rfl⟩
  rw [hcomp, Finset.sum_pair hne, heven] at hsplit
  linarith

end Work.HP.DmixAux
