import Mathlib
import Submission.HvdH.Interfaces

/-! Shared definitions for the IntLib development (area IntLib).

Bit strings are represented at the Lean level as `List Bool`, least significant bit first,
matching `Nat.bits` / `Computability.encodeNat`. -/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

/-- `ofBits xs = Σ_{i < xs.length} xs[i] · 2^i`, for `xs` least significant bit first. -/
def ofBits (xs : List Bool) : ℕ := xs.foldr (fun b r => b.toNat + 2 * r) 0

/-- A bit list is in canonical form if it has no leading zeros (`[]` or last element `true`).
`n.bits` is canonical for every `n`, and this is the set of lists on which `ofBits` is injective. -/
def IsBits (xs : List Bool) : Prop := xs = [] ∨ xs.getLast? = some true

theorem isBits_nil : IsBits [] := Or.inl rfl

theorem isBits_iff {xs : List Bool} : IsBits xs ↔ xs = [] ∨ xs.getLast? = some true := Iff.rfl

theorem bits_ne_nil_iff {n : ℕ} : n.bits ≠ [] ↔ n ≠ 0 := by
  rw [ne_eq, ne_eq, ← List.length_eq_zero_iff, Nat.size_eq_bits_len, Nat.size_eq_zero]

theorem bits_getLast?_of_ne_zero {n : ℕ} (hn : n ≠ 0) : n.bits.getLast? = some true := by
  induction n using Nat.binaryRec' with
  | zero => exact absurd rfl hn
  | bit b m hm ih =>
    rw [Nat.bits_append_bit m b hm, List.getLast?_cons]
    cases b with
    | true =>
      by_cases hm0 : m = 0
      · subst hm0; rfl
      · simp only [ih hm0, Option.getD_some]
    | false =>
      have hm0 : m ≠ 0 := by intro h; exact absurd (hm h) (by decide)
      simp only [ih hm0, Option.getD_some]

theorem isBits_bits (n : ℕ) : IsBits n.bits := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inl rfl
  · exact Or.inr (bits_getLast?_of_ne_zero (Nat.pos_iff_ne_zero.mp hn))

end Work.IntLib
