import Mathlib
import Submission.Work.Layout.Take.Basic

namespace Work.Layout.Take

open HvdH

/-- One `cons` glyph plus the two encodings. -/
theorem vsz_cons (a b : Val) : vsz (Val.cons a b) = vsz a + vsz b + 1 := by
  simp [vsz, Val.enc, Nat.add_comm]

/-- `ofList` unfolds one step. -/
theorem ofList_cons (x : Val) (xs : List Val) : ofList (x :: xs) = Val.cons x (ofList xs) := rfl

/-- Every value occupies at least one glyph. -/
theorem one_le_vsz (v : Val) : 1 ≤ vsz v := by
  cases v with
  | int z => simp [vsz, Val.enc]
  | nil => simp [vsz, Val.enc]
  | cons a b => simp [vsz, Val.enc]

/-- Elementary size bookkeeping for the take/drop assembly: the size of `ofList xs`, sums of `vsz`
over sublists and over the reversed list, the length of `encs ys`, and `length ≤ sum vsz`. -/
theorem takeListFacts :
    (∀ xs : List HvdH.Val, HvdH.vsz (HvdH.ofList xs) = xs.length + (xs.map HvdH.vsz).sum + 1) ∧
    (∀ xs : List HvdH.Val, ((xs.reverse).map HvdH.vsz).sum = (xs.map HvdH.vsz).sum) ∧
    (∀ (xs : List HvdH.Val) (n : ℕ), ((xs.take n).map HvdH.vsz).sum ≤ (xs.map HvdH.vsz).sum) ∧
    (∀ (xs : List HvdH.Val) (n : ℕ), ((xs.drop n).map HvdH.vsz).sum ≤ (xs.map HvdH.vsz).sum) ∧
    (∀ ys : List HvdH.Val, (HvdH.encs ys).length = (ys.map HvdH.vsz).sum) ∧
    (∀ ys : List HvdH.Val, ys.length ≤ (ys.map HvdH.vsz).sum) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro xs
    induction xs with
    | nil => simp [ofList, vsz, Val.enc]
    | cons x xs ih =>
        rw [ofList_cons, vsz_cons, ih]
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        omega
  · intro xs
    rw [List.map_reverse, List.sum_reverse]
  · intro xs n
    induction xs generalizing n with
    | nil => simp
    | cons x xs ih =>
        cases n with
        | zero => simp
        | succ k =>
            simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
            have := ih k
            omega
  · intro xs n
    induction xs generalizing n with
    | nil => simp
    | cons x xs ih =>
        cases n with
        | zero => simp
        | succ k =>
            simp only [List.drop_succ_cons, List.map_cons, List.sum_cons]
            have := ih k
            omega
  · intro ys
    rw [encs, List.length_flatten, List.map_map]
    congr 1
  · intro ys
    have h := List.length_le_sum_of_one_le (ys.map vsz)
      (fun i hi => by
        obtain ⟨v, _, rfl⟩ := List.mem_map.mp hi
        exact one_le_vsz v)
    rwa [List.length_map] at h

end Work.Layout.Take
