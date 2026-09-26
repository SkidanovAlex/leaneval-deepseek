import Mathlib
import Submission.Work.SG.SGprelude

namespace Work.SG

/-- If `a` is the unique element of `l` satisfying `p`, then `find?` returns it. -/
theorem find_some_of_unique {α : Type*} {l : List α} {p : α → Bool} {a : α} (ha : a ∈ l)
    (hpa : p a = true) (huniq : ∀ b ∈ l, p b = true → b = a) : l.find? p = some a := by
  revert ha hpa huniq
  induction l with
  | nil =>
    intro ha _ _
    exact absurd ha (List.not_mem_nil)
  | cons b t ih =>
    intro ha hpa huniq
    rcases List.mem_cons.mp ha with h | ha
    · subst h
      exact List.find?_cons_of_pos hpa
    · by_cases hpb : p b = true
      · rw [List.find?_cons_of_pos hpb]
        have hba : b = a := huniq b (by simp) hpb
        rw [hba]
      · rw [List.find?_cons_of_neg hpb]
        exact ih ha hpa (fun c hc hpc => huniq c (by simp [hc]) hpc)

end Work.SG
