import Mathlib
import Submission.Work.A7REC.Char.a7TableDefs

namespace Work.A7REC.Char

theorem fTuples_complete {F : List ℕ} {l : List ℕ} (h : ∀ x ∈ l, x ∈ F) :
    l ∈ fTuples F l.length := by
  induction l with
  | nil => simp [fTuples]
  | cons a t ih =>
    rw [List.length_cons, fTuples, List.mem_flatMap]
    refine ⟨a, h a (by simp), ?_⟩
    rw [List.mem_map]
    exact ⟨t, ih (fun x hx => h x (by simp [hx])), rfl⟩

end Work.A7REC.Char
