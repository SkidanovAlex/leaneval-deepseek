import Mathlib
import Submission.Work.Peluse.SwapC.cprocNodup

namespace Work.Peluse.SwapC

theorem prefixOfFind {s : ℕ} {Λ : List (Work.Peluse.SwapC.CLeaf s)} {l : Work.Peluse.SwapC.CLeaf s}
    (h : Work.Peluse.SwapC.cnextLeaf Λ = some l) :
    ∃ (P : List (Work.Peluse.SwapC.CLeaf s)) (Q : List (Work.Peluse.SwapC.CLeaf s)),
      Λ = P ++ l :: Q ∧ ∀ a ∈ P, ¬ a.dep < s := by
  induction Λ with
  | nil => simp [cnextLeaf] at h
  | cons b t ih =>
    simp only [cnextLeaf] at h
    by_cases hb : b.dep < s
    · rw [List.find?_cons_of_pos (p := fun l : CLeaf s => decide (l.dep < s)) (by simp [hb])] at h
      injection h with h'
      subst h'
      exact ⟨[], t, rfl, by simp⟩
    · rw [List.find?_cons_of_neg (p := fun l : CLeaf s => decide (l.dep < s)) (by simp [hb])] at h
      obtain ⟨P, Q, ht, hP⟩ := ih h
      exact ⟨b :: P, Q, by simp [ht], by
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hb
        · exact hP x hx⟩

end Work.Peluse.SwapC
