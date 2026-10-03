import Mathlib
import Submission.Work.OROneRel.Basic

namespace Work.ORLocInd.CohenLyndon

universe u

theorem relatorNorm_le_one {α : Type u} {r : FreeGroup α} (h : Work.OROneRel.relatorNorm r ≤ 1) :
    r = 1 ∨ ∃ a : α, r = FreeGroup.of a ∨ r = (FreeGroup.of a)⁻¹ := by
  classical
  have hlen : r.toWord.length ≤ 1 := h
  have hmem : r.toWord = [] ∨ ∃ s : α × Bool, r.toWord = [s] := by
    rcases (Nat.le_one_iff_eq_zero_or_eq_one.1 hlen) with h0 | h1
    · exact Or.inl (List.length_eq_zero_iff.1 h0)
    · exact Or.inr (List.length_eq_one_iff.1 h1)
  rcases hmem with h0 | ⟨s, hs⟩
  · left
    exact FreeGroup.toWord_eq_nil_iff.mp h0
  · right
    obtain ⟨a, b⟩ := s
    cases b
    · refine ⟨a, Or.inr ?_⟩
      rw [← FreeGroup.mk_toWord (x := r), hs]
      rfl
    · refine ⟨a, Or.inl ?_⟩
      rw [← FreeGroup.mk_toWord (x := r), hs]
      rfl

end Work.ORLocInd.CohenLyndon
