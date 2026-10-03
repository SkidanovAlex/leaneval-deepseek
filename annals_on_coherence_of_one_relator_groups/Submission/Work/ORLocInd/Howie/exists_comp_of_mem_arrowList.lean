import Mathlib
import Submission.Work.ORLocInd.Howie.Relator

namespace Work.ORLocInd.Howie

theorem exists_comp_of_mem_arrowList {V : Type*} [Quiver V] {a b x y : V}
    {p : Quiver.Path a b} {f : x ⟶ y}
    (h : Quiver.Total.mk x y f ∈ p.arrowList) :
    ∃ (q : Quiver.Path a x) (s : Quiver.Path y b), p = q.comp (f.toPath.comp s) := by
  induction p with
  | nil => simp at h
  | cons p e ih =>
    rw [Quiver.Path.arrowList_cons] at h
    rcases List.mem_append.1 h with h | h
    · -- the arrow occurs in the initial segment `p`
      obtain ⟨q, s, hs⟩ := ih h
      exact ⟨q, s.cons e, by rw [hs, Quiver.Path.comp_cons, Quiver.Path.comp_cons]⟩
    · -- the arrow is the last arrow of the path
      simp only [List.mem_singleton] at h
      cases h
      exact ⟨p, Quiver.Path.nil, by simp⟩

end Work.ORLocInd.Howie
