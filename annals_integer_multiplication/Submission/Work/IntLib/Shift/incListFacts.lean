import Mathlib
import Submission.Work.IntLib.Defs
import Submission.Work.IntLib.Shift.Defs
import Submission.Work.IntLib.Basic
import Submission.Work.IntLib.ofBits_bits
import Submission.Work.IntLib.bits_ofBits_of_isBits

/-!
# Facts about `incList`

`Work.IntLib.Shift.incList` is the carry propagation of "add one" on a bit list written least
significant bit first:

* `incList [] = [true]`,
* `incList (false :: xs) = true :: xs`,
* `incList (true :: xs) = false :: incList xs`.

We record that it computes the successor `n ↦ n + 1` on values (`ofBits`), that it is the exact
list-level counterpart of `Nat.bits` of the successor, that it never returns `[]`, and that it
preserves canonical bit strings (`IsBits`).
-/

set_option autoImplicit false

namespace Work.IntLib.Shift

open Work.IntLib

/-! ## `ofBits` -/

/-- `incList` adds one to the value of a bit list. -/
theorem ofBits_incList (xs : List Bool) : ofBits (incList xs) = ofBits xs + 1 := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | false =>
      simp only [incList_false, ofBits_cons, Bool.toNat_true, Bool.toNat_false]
      omega
    | true =>
      simp only [incList_true, ofBits_cons, Bool.toNat_true, Bool.toNat_false]
      omega

/-- `incList` never returns the empty list. -/
theorem incList_ne_nil (xs : List Bool) : incList xs ≠ [] := by
  cases xs with
  | nil => simp [incList]
  | cons b xs => cases b <;> simp [incList]

/-! ## Canonical forms -/

/-- Dropping the lowest bit of a canonical list keeps it canonical. -/
theorem isBits_tail {b : Bool} {xs : List Bool} (h : IsBits (b :: xs)) : IsBits xs := by
  cases xs with
  | nil => exact isBits_nil
  | cons y ys =>
    rcases h with hnil | hlast
    · exact absurd hnil (by simp)
    · exact Or.inr (by rwa [List.getLast?_cons_cons] at hlast)

/-- If `false :: xs` is canonical then `xs` is non-empty (a canonical list does not end in
`false`). -/
theorem ne_nil_of_isBits_false_cons {xs : List Bool} (h : IsBits (false :: xs)) : xs ≠ [] := by
  rintro rfl
  rcases h with hnil | hlast
  · exact absurd hnil (by simp)
  · rw [List.getLast?_cons] at hlast
    exact absurd hlast (by decide)

/-- `incList` preserves canonical bit strings. -/
theorem isBits_incList (xs : List Bool) (h : IsBits xs) : IsBits (incList xs) := by
  induction xs with
  | nil => exact Or.inr rfl
  | cons b xs ih =>
    cases b with
    | false =>
      show IsBits (true :: xs)
      exact isBits_cons (isBits_tail h) (ne_nil_of_isBits_false_cons h)
    | true =>
      show IsBits (false :: incList xs)
      exact isBits_cons (ih (isBits_tail h)) (incList_ne_nil xs)

/-! ## `Nat.bits` of a successor -/

/-- `incList` is exactly the list-level "add one": it turns `m.bits` into `(m + 1).bits`. -/
theorem bits_succ_incList (m : ℕ) : (m + 1).bits = incList m.bits := by
  have h1 : ofBits (incList m.bits) = m + 1 := by
    rw [ofBits_incList, ofBits_bits]
  have h2 : IsBits (incList m.bits) := isBits_incList m.bits (isBits_bits m)
  rw [← h1]
  exact bits_ofBits_of_isBits _ h2

/-! ## The assembled statement -/

theorem incListFacts : (∀ xs : List Bool, Work.IntLib.ofBits (Work.IntLib.Shift.incList xs) = Work.IntLib.ofBits xs + 1) ∧ (∀ (m : ℕ), (m + 1).bits = Work.IntLib.Shift.incList m.bits) ∧ (∀ (xs : List Bool), Work.IntLib.Shift.incList xs ≠ []) ∧ (∀ (xs : List Bool), Work.IntLib.IsBits xs → Work.IntLib.IsBits (Work.IntLib.Shift.incList xs)) := by
  exact ⟨ofBits_incList, bits_succ_incList, incList_ne_nil, isBits_incList⟩

end Work.IntLib.Shift
