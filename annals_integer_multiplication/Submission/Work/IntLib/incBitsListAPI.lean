import Mathlib
import Submission.Work.IntLib.divRaw
import Submission.Work.IntLib.Basic

/-!
# The list-level API for `incBitsList`

`incBitsList` (defined in `Submission/Work/IntLib/divRaw.lean`) performs the carry propagation of
"add one" on a bit list written least significant first:

* `incBitsList [] = [true]`,
* `incBitsList (false :: xs) = true :: xs`,
* `incBitsList (true :: xs) = false :: incBitsList xs`.

The lemmas below record that it computes `n ↦ n + 1` on values (`ofBits`), preserves canonical
forms (`IsBits`), grows the length by at most one and never produces the empty list.
-/

set_option autoImplicit false

namespace Work.IntLib

/-- `incBitsList` adds one to the value of a bit list. -/
theorem ofBits_incBitsList (l : List Bool) : ofBits (incBitsList l) = ofBits l + 1 := by
  induction l with
  | nil => rfl
  | cons b xs ih =>
    cases b with
    | false =>
      simp only [incBitsList, ofBits, List.foldr_cons, Bool.toNat_true, Bool.toNat_false,
        Nat.zero_add]
      omega
    | true =>
      simp only [incBitsList, ofBits, List.foldr_cons, Bool.toNat_true, Bool.toNat_false,
        Nat.zero_add] at ih ⊢
      omega

/-- `incBitsList` never returns the empty list. -/
theorem incBitsList_ne_nil (l : List Bool) : incBitsList l ≠ [] := by
  cases l with
  | nil => simp [incBitsList]
  | cons b xs => cases b <;> simp [incBitsList]

/-- The tail of a canonical bit list (dropping the low bit) is canonical. -/
theorem isBits_of_cons {b : Bool} {xs : List Bool} (h : IsBits (b :: xs)) : IsBits xs := by
  cases xs with
  | nil => exact isBits_nil
  | cons y ys =>
    rcases h with hnil | hlast
    · exact absurd hnil (by simp)
    · refine Or.inr ?_
      rwa [List.getLast?_cons_cons] at hlast

/-- If `false :: xs` is canonical then `xs` is non-empty (a canonical list cannot end in `false`). -/
theorem ne_nil_of_isBits_false_cons {xs : List Bool} (h : IsBits (false :: xs)) : xs ≠ [] := by
  rintro rfl
  rcases h with hnil | hlast
  · exact absurd hnil (by simp)
  · rw [List.getLast?_cons] at hlast
    exact absurd hlast (by decide)

/-- `incBitsList` preserves canonical forms. -/
theorem isBits_incBitsList (l : List Bool) (h : IsBits l) : IsBits (incBitsList l) := by
  induction l with
  | nil => exact Or.inr rfl
  | cons b xs ih =>
    cases b with
    | false =>
      show IsBits (true :: xs)
      exact isBits_cons (isBits_of_cons h) (ne_nil_of_isBits_false_cons h)
    | true =>
      show IsBits (false :: incBitsList xs)
      exact isBits_cons (ih (isBits_of_cons h)) (incBitsList_ne_nil xs)

/-- `incBitsList` grows the length by at most one. -/
theorem length_incBitsList (l : List Bool) : (incBitsList l).length ≤ l.length + 1 := by
  induction l with
  | nil => simp [incBitsList]
  | cons b xs ih =>
    cases b with
    | false => simp [incBitsList]
    | true =>
      show (false :: incBitsList xs).length ≤ (true :: xs).length + 1
      simp only [List.length_cons]
      omega

theorem incBitsListAPI :
    (∀ l : List Bool, Work.IntLib.ofBits (Work.IntLib.incBitsList l) = Work.IntLib.ofBits l + 1) ∧
    (∀ l : List Bool, Work.IntLib.IsBits l → Work.IntLib.IsBits (Work.IntLib.incBitsList l)) ∧
    (∀ l : List Bool, (Work.IntLib.incBitsList l).length ≤ l.length + 1) ∧
    (∀ l : List Bool, l ≠ [] → Work.IntLib.incBitsList l ≠ []) :=
  ⟨ofBits_incBitsList, isBits_incBitsList, length_incBitsList, fun l _ => incBitsList_ne_nil l⟩

end Work.IntLib
