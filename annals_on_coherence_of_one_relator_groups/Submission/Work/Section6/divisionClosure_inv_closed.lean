import Mathlib
import Submission.Work.ORHughesFree.DivisionClosure.inverse_mem_divisionClosure

namespace Work.Section6

theorem divisionClosure_inv_closed {S : Type} [Ring S] (R : Set S) :
    ∀ x ∈ Work.ORHughesFree.divisionClosure R, IsUnit x →
      ∃ y ∈ Work.ORHughesFree.divisionClosure R, x * y = 1 := by
  intro x hx hu
  -- A unit in `S` is `↑u` for some `u : Sˣ`; its two-sided inverse is `↑u⁻¹`.
  obtain ⟨u, rfl⟩ := hu
  refine ⟨↑u⁻¹, Work.ORHughesFree.DivisionClosure.inverse_mem_divisionClosure hx ?_ ?_, ?_⟩
  · simp
  · simp
  · simp

end Work.Section6
