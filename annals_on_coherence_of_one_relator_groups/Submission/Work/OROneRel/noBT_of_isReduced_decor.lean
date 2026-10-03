import Mathlib
import Submission.Work.OROneRel.delWordWalkDefs

namespace Work.OROneRel

universe u

/-- Consecutive elements of a `List.IsChain` are related: if `L₁ ++ p :: q :: L₂` is a chain, then
so is the pair `(p, q)`.  (Obtained by dropping the prefix, using `List.drop_left`.) -/
theorem isChain_append_rel {γ : Type*} {R : γ → γ → Prop} {L₁ L₂ : List γ} {p q : γ}
    (h : List.IsChain R (L₁ ++ p :: q :: L₂)) : R p q := by
  have hd := h.drop L₁.length
  rw [List.drop_left] at hd
  exact hd.rel

/-- **Reduced decorated words have no immediate backtrack.**  `FreeGroup.IsReduced` on a word over
`α × Bool` says exactly that whenever two consecutive letters carry the same generator, their signs
agree; for the decorated word this is precisely the no-backtrack condition `NoBT` on the underlying
walk, since the first component of a decorated letter *is* its edge. -/
theorem noBT_of_isReduced_decor {α : Type u} (c : α → ℤ) (a : ℤ) {L : List (α × Bool)}
    (h : FreeGroup.IsReduced (Work.OROneRel.decor c a L)) : Work.OROneRel.NoBT c a L := by
  intro L₁ L₂ p q hdec
  rcases Classical.em (coverEdge p = coverEdge q) with he | hne
  · right
    have hchain : List.IsChain (fun a b : (α × ℤ) × Bool => a.1 = b.1 → a.2 = b.2)
        (L₁ ++ p :: q :: L₂) := by
      rw [← hdec]
      exact h
    exact isChain_append_rel hchain he
  · exact Or.inl hne

end Work.OROneRel
