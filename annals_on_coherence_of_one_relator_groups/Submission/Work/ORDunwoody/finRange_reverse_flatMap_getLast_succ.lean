import Mathlib

namespace Work.ORDunwoody

/-- `List.finRange (n+1)` starts with `0`, and `f 0` is nonempty, so `f 0`'s last
element is found by `List.findSome?` on `fun k => (f k).getLast?`.  Reversing the
enumeration puts `0` at the end of the `flatMap`, which is the case relevant for
`getLast?`. -/
theorem finRange_reverse_flatMap_getLast_succ {β : Type*} (n : ℕ) (f : (k : Fin (n + 1)) → List β) (hf : ∀ k, f k ≠ []) : (((List.finRange (n + 1)).reverse).flatMap f).getLast? = (f ⟨0, Nat.succ_pos n⟩).getLast? := by
  have h : (f (0 : Fin (n + 1))).getLast? = some ((f (0 : Fin (n + 1))).getLast (hf 0)) :=
    List.getLast?_eq_some_getLast (hf 0)
  rw [List.getLast?_flatMap, List.reverse_reverse, List.finRange_succ, List.findSome?_cons, h]
  rw [List.getLast?_eq_some_getLast (hf ⟨0, Nat.succ_pos n⟩)]
  rfl

end Work.ORDunwoody
