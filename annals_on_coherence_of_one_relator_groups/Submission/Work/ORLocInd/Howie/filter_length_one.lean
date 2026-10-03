import Mathlib

namespace Work.ORLocInd.Howie

theorem filter_length_one {α : Type*} {l : List α} {p : α → Prop} [DecidablePred p]
    (h : (l.filter p).length = 1) :
    ∃ x : α, l.filter p = [x] ∧ x ∈ l ∧ p x ∧ ∀ y ∈ l, p y → y = x := by
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp h
  have hxmem : x ∈ l.filter p := by rw [hx]; simp
  simp only [List.mem_filter, decide_eq_true_eq] at hxmem
  refine ⟨x, hx, hxmem.1, hxmem.2, ?_⟩
  intro y hy hpy
  have : y ∈ l.filter p := by simp [List.mem_filter, hy, hpy]
  rw [hx] at this
  simpa using this

end Work.ORLocInd.Howie
