import Mathlib

namespace Work.ORDunwoody

/-- `List.finRange (n+1)` splits off its last element `Fin.last n`:
`finRange (n+1) = (finRange n).map Fin.castSucc ++ [Fin.last n]`. -/
theorem finRange_succ_last (n : ℕ) :
    List.finRange (n + 1) = (List.finRange n).map Fin.castSucc ++ [Fin.last n] := by
  rw [show List.finRange (n + 1) = List.ofFn (fun i : Fin (n + 1) => i) from rfl,
    List.ofFn_succ', List.concat_eq_append, List.ofFn_eq_map]

/-- The last entry of the flat map of `finRange (n+1)` over a family `f` of nonempty lists
is the last entry of `f` at the final index `n`. -/
theorem finRange_flatMap_getLast_succ {β : Type*} (n : ℕ) (f : (k : Fin (n + 1)) → List β) (hf : ∀ k, f k ≠ []) : ((List.finRange (n + 1)).flatMap f).getLast? = (f ⟨n, Nat.lt_succ_self n⟩).getLast? := by
  rw [finRange_succ_last, List.flatMap_append, List.flatMap_singleton,
    List.getLast?_append_of_ne_nil _ (hf (Fin.last n))]
  rfl

end Work.ORDunwoody
