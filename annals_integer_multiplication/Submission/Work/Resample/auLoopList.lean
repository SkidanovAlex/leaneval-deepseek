import Mathlib
import Submission.Work.Resample.pbDefs

namespace Work.Resample

/-- The list bookkeeping of the streaming-window loop: the prefix sums
`Σ_{j<i} g j` step by `g i` and are monotone, the chunk list reverses one element at a time, and
the elementary `drop`/`getD`/`headD`/`take` identities. -/
theorem auLoopList :
    (∀ {α : Type} (xs : List α) (n : ℕ) (d : α), n < xs.length →
      xs.drop n = xs.getD n d :: xs.drop (n+1)) ∧
    (∀ {α : Type} (xs : List α) (n : ℕ) (d : α), (xs.drop n).headD d = xs.getD n d) ∧
    (∀ {α : Type} (xs : List α) (y : α), (xs ++ [y]).take xs.length = xs) ∧
    (∀ (g : ℕ → ℕ) (i : ℕ), ((List.range (i+1)).map g).sum = ((List.range i).map g).sum + g i) ∧
    (∀ (g : ℕ → ℕ) (i t : ℕ), i ≤ t → ((List.range i).map g).sum ≤ ((List.range t).map g).sum) ∧
    (∀ (f : ℕ → HvdH.Val) (i : ℕ),
      ((List.range (i+1)).map f).reverse = f i :: ((List.range i).map f).reverse) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α xs n d hn
    rw [List.getD_eq_getElem _ _ hn]
    exact List.drop_eq_getElem_cons hn
  · intro α xs n d
    by_cases hn : n < xs.length
    · rw [List.drop_eq_getElem_cons hn, List.headD_cons, List.getD_eq_getElem _ _ hn]
    · have hle : xs.length ≤ n := Nat.le_of_not_lt hn
      rw [List.drop_eq_nil_of_le hle, List.getD_eq_default _ _ hle]
      rfl
  · intro α xs y
    rw [List.take_append_of_le_length (le_refl _), List.take_length]
  · intro g i
    rw [List.range_succ, List.map_append, List.map_singleton, List.sum_append, List.sum_singleton]
  · intro g i t hit
    exact List.Sublist.sum_le_sum (List.Sublist.map g (List.range_sublist.mpr hit))
      (fun a _ => Nat.zero_le a)
  · intro f i
    rw [List.range_succ, List.map_append, List.map_singleton, List.reverse_append,
      List.reverse_singleton, List.singleton_append]

end Work.Resample
