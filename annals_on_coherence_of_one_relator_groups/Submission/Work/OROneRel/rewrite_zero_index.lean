import Mathlib
import Submission.Work.OROneRel.FreiheitssatzDefs

namespace Work.OROneRel

universe u

/-- The first letter of a word that is not `t` is rewritten at index `0`: if `L` starts with
the letter `(x, b)` and `x ≠ t`, then the pair `((⟨x, hxt⟩, 0), b)` occurs in `rewrite t L`. -/
theorem rewrite_zero_index {α : Type u} (t x : α) (hxt : x ≠ t) {L : List (α × Bool)} (b : Bool)
    (h : L.head? = some (x, b)) :
    ∃ p : ({a : α // a ≠ t} × ℤ) × Bool,
      p.1.1 = (⟨x, hxt⟩ : {a : α // a ≠ t}) ∧ p.1.2 = 0 ∧
        p ∈ Work.OROneRel.rewrite t L := by
  obtain ⟨L', rfl⟩ := List.head?_eq_some_iff.mp h
  refine ⟨((⟨x, hxt⟩, 0), b), rfl, rfl, ?_⟩
  simp [rewrite, rewriteAux, hxt]

end Work.OROneRel
