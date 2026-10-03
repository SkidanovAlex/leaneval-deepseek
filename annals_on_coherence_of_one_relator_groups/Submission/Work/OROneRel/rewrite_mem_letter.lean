import Mathlib
import Submission.Work.OROneRel.FreiheitssatzDefs

namespace Work.OROneRel

universe u

/-- Every non-`t` letter of `L` survives the Magnus rewriting, at any running index `i`. -/
lemma mem_rewriteAux_of_mem {α : Type u} (t x : α) (hxt : x ≠ t) (i : ℤ) :
    ∀ {L : List (α × Bool)} (b : Bool), (x, b) ∈ L →
    ∃ p : ({a : α // a ≠ t} × ℤ) × Bool,
      p.1.1 = (⟨x, hxt⟩ : {a : α // a ≠ t}) ∧ p ∈ rewriteAux t i L := by
  intro L
  induction L generalizing i with
  | nil => intro b h; simp at h
  | cons q L' ih =>
    intro b h
    simp only [List.mem_cons] at h
    rcases h with h | h
    · have hqt : q.1 ≠ t := by
        intro hh
        have : x = q.1 := congrArg Prod.fst h
        exact hxt (this.trans hh)
      refine ⟨((⟨q.1, hqt⟩, i), q.2), ?_, ?_⟩
      · apply Subtype.ext
        exact (congrArg Prod.fst h).symm
      · classical
        rw [rewriteAux]
        simp [dif_neg hqt]
    · by_cases hq : q.1 = t
      · obtain ⟨p, hp1, hp2⟩ := ih (i + (if q.2 then 1 else -1)) b h
        refine ⟨p, hp1, ?_⟩
        classical
        rw [rewriteAux]
        simp [dif_pos hq, hp2]
      · obtain ⟨p, hp1, hp2⟩ := ih i b h
        refine ⟨p, hp1, ?_⟩
        classical
        rw [rewriteAux]
        simp [dif_neg hq, hp2]

theorem rewrite_mem_letter {α : Type u} (t x : α) (hxt : x ≠ t) {L : List (α × Bool)} (b : Bool)
    (h : (x, b) ∈ L) :
    ∃ p : ({a : α // a ≠ t} × ℤ) × Bool,
      p.1.1 = (⟨x, hxt⟩ : {a : α // a ≠ t}) ∧ p ∈ Work.OROneRel.rewrite t L := by
  exact mem_rewriteAux_of_mem t x hxt 0 b h

end Work.OROneRel
