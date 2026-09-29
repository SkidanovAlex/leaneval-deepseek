import Mathlib
import Submission.Work.IntLib.evDefs
import Submission.Work.IntLib.Shift.Base

namespace Work.IntLib

/-- `k` avoids the nine stacks carrying data in `evStk`, expanded as the conjunction of the nine
non-equalities. -/
theorem not_mem_evStk_set {k : HvdH.Stk}
    (hk : k ∉ ({aC, aW, aO, aCW, aCB, aA, aB, a2, aL} : Finset HvdH.Stk)) :
    k ≠ aC ∧ k ≠ aW ∧ k ≠ aO ∧ k ≠ aCW ∧ k ≠ aCB ∧ k ≠ aA ∧ k ≠ aB ∧ k ≠ a2 ∧ k ≠ aL := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk
  push_neg at hk
  exact hk

/-- Componentwise characterisation of a stack function that agrees with `evStk`. -/
theorem evMainEvStkEq {X : HvdH.Stk → List HvdH.Glyph} {hs : List ℕ} {b j : ℕ}
    {W LO : List Bool} {Y : HvdH.Stk → List HvdH.Glyph} :
    X = evStk hs b j W LO Y ↔
      X aC = HvdH.Val.enc (HvdH.intList (hs.drop j)) ++ Y aC ∧
      X aW = W.map HvdH.Glyph.bit ++ Work.IntLib.Shift.gmk aW :: Y aW ∧
      X aO = LO.reverse.map HvdH.Glyph.bit ++ [HvdH.Glyph.pos] ++ Work.IntLib.Shift.gmk aO :: Y aO ∧
      X aCW = Unary 0 (Work.IntLib.Shift.gmk aCW :: Y aCW) ∧
      X aCB = Unary b (Work.IntLib.Shift.gmk aCB :: Y aCB) ∧
      X aA = Work.IntLib.Shift.gmk aA :: Y aA ∧
      X aB = Work.IntLib.Shift.gmk aB :: Y aB ∧
      X a2 = Work.IntLib.Shift.gmk a2 :: Y a2 ∧
      X aL = Work.IntLib.Shift.gmk aL :: Y aL ∧
      (∀ k : HvdH.Stk, k ∉ ({aC, aW, aO, aCW, aCB, aA, aB, a2, aL} : Finset HvdH.Stk) →
        X k = Y k) := by
  constructor
  · intro h
    subst h
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · simp
    · intro k hk
      obtain ⟨hk1,hk2,hk3,hk4,hk5,hk6,hk7,hk8,hk9⟩ := not_mem_evStk_set hk
      exact evStk_other hs b j W LO Y hk1 hk2 hk3 hk4 hk5 hk6 hk7 hk8 hk9
  · rintro ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,hrest⟩
    funext k
    by_cases hk : k ∈ ({aC, aW, aO, aCW, aCB, aA, aB, a2, aL} : Finset HvdH.Stk)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [h1, evStk_aC]
      · rw [h2, evStk_aW]
      · rw [h3, evStk_aO]
      · rw [h4, evStk_aCW]
      · rw [h5, evStk_aCB]
      · rw [h6, evStk_aA]
      · rw [h7, evStk_aB]
      · rw [h8, evStk_a2]
      · rw [h9, evStk_aL]
    · obtain ⟨hk1,hk2,hk3,hk4,hk5,hk6,hk7,hk8,hk9⟩ := not_mem_evStk_set hk
      rw [hrest k hk, evStk_other hs b j W LO Y hk1 hk2 hk3 hk4 hk5 hk6 hk7 hk8 hk9]

end Work.IntLib
