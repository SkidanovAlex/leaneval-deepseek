import Mathlib
import Submission.Work.Resample.pbDefs

namespace Work.Resample

/-- Elementary facts about the element run `ELEM.drop p ++ [m2]` of the streaming-window loop:
its head and tail reconstruct the list, the head is bounded by `B`, the element that enters the
window is `ELEM.getD p .nil` (the two differ only when the run is exhausted, in which case the
window is only ever extended by `g = 0` and the appended entry is truncated by `take L`), and the
tail of the run is the run one step on. -/
theorem auLoopAux :
    (∀ (ELEM : List HvdH.Val) (m2 : HvdH.Val) (p : ℕ),
      (ELEM.drop p ++ [m2]).headD HvdH.Val.nil :: (ELEM.drop p ++ [m2]).tail = ELEM.drop p ++ [m2]) ∧
    (∀ (ELEM : List HvdH.Val) (m2 : HvdH.Val) (p B : ℕ), (∀ v ∈ ELEM, HvdH.vsz v ≤ B) →
      HvdH.vsz m2 ≤ B → HvdH.vsz ((ELEM.drop p ++ [m2]).headD HvdH.Val.nil) ≤ B) ∧
    (∀ (ELEM : List HvdH.Val) (m2 : HvdH.Val) (p g L : ℕ) (W : List HvdH.Val),
      g ≤ 1 → W.length = L → p + g ≤ ELEM.length →
      ((W.drop g) ++ [(ELEM.drop p ++ [m2]).headD HvdH.Val.nil]).take L =
      ((W.drop g) ++ [ELEM.getD p HvdH.Val.nil]).take L) ∧
    (∀ (ELEM : List HvdH.Val) (m2 : HvdH.Val) (p : ℕ),
      ELEM.drop p ≠ [] → (ELEM.drop p ++ [m2]).tail = ELEM.drop (p+1) ++ [m2]) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- head and tail reconstruct the run (the run is never empty)
    intro ELEM m2 p
    cases hd : ELEM.drop p <;> simp
  · -- the head of the run is bounded by `B`
    intro ELEM m2 p B hE hm
    cases hd : ELEM.drop p with
    | nil => simpa using hm
    | cons a t =>
      have ha : a ∈ ELEM := List.mem_of_mem_drop (by rw [hd]; exact List.mem_cons_self)
      simpa using hE a ha
  · -- the element entering the window agrees with `ELEM.getD p .nil`, unless the truncation
    -- `take L` discards it (which happens only for `g = 0`)
    intro ELEM m2 p g L W hg hW hp
    rcases lt_or_ge p ELEM.length with hlt | hge
    · -- the run is not exhausted: head of the run is `ELEM[p] = ELEM.getD p .nil`
      have heq : (ELEM.drop p ++ [m2]).headD HvdH.Val.nil = ELEM.getD p HvdH.Val.nil := by
        cases hd : ELEM.drop p with
        | nil =>
          exfalso
          have h0 : (ELEM.drop p).length = 0 := by rw [hd]; rfl
          rw [List.length_drop] at h0
          omega
        | cons a t =>
          have hsome : ELEM[p]? = some a := by rw [← List.head?_drop, hd]; rfl
          rw [List.getElem?_eq_getElem hlt] at hsome
          have ha : a = ELEM[p] := (Option.some.inj hsome).symm
          simp [ha, List.getElem?_eq_getElem hlt]
      rw [heq]
    · -- the run is exhausted: then `p + g ≤ ELEM.length` forces `g = 0` and `take L` discards
      -- the appended slot
      have hg0 : g = 0 := by omega
      subst hg0
      simp only [List.drop_zero]
      rw [← hW]
      simp
  · -- the tail of the run is the run one step on
    intro ELEM m2 p h
    rw [List.tail_append_of_ne_nil h, List.tail_drop]

end Work.Resample
