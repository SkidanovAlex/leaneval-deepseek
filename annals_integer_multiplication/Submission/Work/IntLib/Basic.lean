import Mathlib
import Submission.Work.IntLib.Defs

/-!
# Elementary API for `ofBits` / `IsBits`

`ofBits xs` is the natural number whose binary expansion, least significant bit first,
is `xs`; equivalently `Nat.ofDigits 2 (xs.map Bool.toNat)`.  This file collects the
elementary transfer lemmas that the main `ofBitsAPI` statement is assembled from.
-/

set_option autoImplicit false

namespace Work.IntLib

open HvdH

theorem ofBits_eq_ofDigits (xs : List Bool) :
    ofBits xs = Nat.ofDigits 2 (xs.map Bool.toNat) := by
  rw [ofBits, Nat.ofDigits_eq_foldr, List.foldr_map]
  congr 1

theorem ofBits_cons (b : Bool) (xs : List Bool) :
    ofBits (b :: xs) = b.toNat + 2 * ofBits xs := rfl

theorem ofBits_append (xs ys : List Bool) :
    ofBits (xs ++ ys) = ofBits xs + 2 ^ xs.length * ofBits ys := by
  simp only [ofBits_eq_ofDigits, List.map_append, Nat.ofDigits_append, List.length_map]

theorem ofBits_lt_two_pow (xs : List Bool) : ofBits xs < 2 ^ xs.length := by
  rw [ofBits_eq_ofDigits, ← List.length_map (f := Bool.toNat)]
  exact Nat.ofDigits_lt_base_pow_length (by norm_num) (fun x hx => by
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    cases b <;> decide)

theorem ofBits_take_drop (xs : List Bool) (k : ℕ) :
    ofBits xs = ofBits (xs.take k) + 2 ^ k * ofBits (xs.drop k) := by
  by_cases hk : k ≤ xs.length
  · conv_lhs => rw [← List.take_append_drop k xs]
    rw [ofBits_append, List.length_take, Nat.min_eq_left hk]
  · rw [List.take_of_length_le (le_of_lt (not_le.mp hk)),
        List.drop_eq_nil_of_le (le_of_lt (not_le.mp hk))]
    simp [ofBits]

theorem bits_map_toNat (n : ℕ) : n.bits.map Bool.toNat = Nat.digits 2 n := by
  rw [Nat.digits_two_eq_bits]
  exact List.map_congr_left (fun b _ => by cases b <;> rfl)

theorem isBits_append {xs ys : List Bool} (hx : IsBits xs) (hy : IsBits ys) :
    IsBits (xs ++ ys) := by
  rcases hx with rfl | hx
  · simpa using hy
  rcases hy with rfl | hy
  · rw [List.append_nil]; exact Or.inr hx
  · exact Or.inr (by
      rw [List.getLast?_append_of_ne_nil xs (by rintro rfl; simp at hy), hy])

theorem isBits_cons {b : Bool} {xs : List Bool} (h : IsBits xs) (hne : xs ≠ []) :
    IsBits (b :: xs) := by
  rcases h with h | h
  · exact absurd h hne
  · exact Or.inr (by simp [List.getLast?_cons, h])

end Work.IntLib
