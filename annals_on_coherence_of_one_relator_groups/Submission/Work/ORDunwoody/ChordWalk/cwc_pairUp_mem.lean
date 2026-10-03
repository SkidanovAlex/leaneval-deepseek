import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.Chord

namespace Work.ORDunwoody.ChordWalk

open Work.ORDunwoody.Dunwoody

/-- The two entries of a pair produced by `pairUp` are entries of the original list.

This is the helper recursion: the equation compiler matches `pairUp`'s two-step
recursion (`a :: b :: rest ↦ (a,b) :: pairUp rest`) so that the recursive call on
`rest` is a structural subterm. -/
private theorem pairUp_mem_aux : ∀ (L : List ℕ) (p q : ℕ),
    (p, q) ∈ pairUp L → p ∈ L ∧ q ∈ L
  | [], _, _, h => by simp at h
  | [x], _, _, h => by simp at h
  | x :: y :: rest, p, q, h => by
      rw [pairUp_cons_cons] at h
      rcases List.mem_cons.mp h with h | h
      · rw [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp, by simp⟩
      · obtain ⟨hp, hq⟩ := pairUp_mem_aux rest p q h
        exact ⟨by simp [hp], by simp [hq]⟩

theorem cwc_pairUp_mem (L : List ℕ) (p q : ℕ) (h : (p, q) ∈ Work.ORDunwoody.Dunwoody.pairUp L) : p ∈ L ∧ q ∈ L :=
  pairUp_mem_aux L p q h

end Work.ORDunwoody.ChordWalk
