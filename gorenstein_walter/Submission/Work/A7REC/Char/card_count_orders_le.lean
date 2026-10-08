import Mathlib

/-!
# Counting elements of prescribed order

For a finite group `H`, the trivial element together with the elements of order
`2`, `3`, `4` and `6` are pairwise distinct (no element has two different
orders), hence their total number is at most `|H|`:

`1 + #{x | orderOf x = 2} + #{x | orderOf x = 3} + #{x | orderOf x = 4}
   + #{x | orderOf x = 6} ≤ |H|`.

The proof exhibits an injection from the disjoint union of these sets of
elements (encoded as a nested sum type) into `H`: an element of the union
remembers its order, so two different summands can never collide.
-/

namespace Work.A7REC.Char

section CountHelpers

variable {H : Type*} [Group H]

/-- The order tag attached to an element of the disjoint union
`Unit ⊕ A₂ ⊕ A₃ ⊕ A₄ ⊕ A₆` (the `Unit` summand carries the identity, of order `1`). -/
def countTag :
    (Unit ⊕ ({x : H // orderOf x = 2} ⊕ ({x : H // orderOf x = 3} ⊕
      ({x : H // orderOf x = 4} ⊕ {x : H // orderOf x = 6})))) → ℕ
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl _) => 2
  | Sum.inr (Sum.inr (Sum.inl _)) => 3
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl _))) => 4
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr _))) => 6

/-- The underlying group element of an element of the disjoint union
`Unit ⊕ A₂ ⊕ A₃ ⊕ A₄ ⊕ A₆`. -/
def countVal :
    (Unit ⊕ ({x : H // orderOf x = 2} ⊕ ({x : H // orderOf x = 3} ⊕
      ({x : H // orderOf x = 4} ⊕ {x : H // orderOf x = 6})))) → H
  | Sum.inl _ => 1
  | Sum.inr (Sum.inl x) => x.1
  | Sum.inr (Sum.inr (Sum.inl x)) => x.1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl x))) => x.1
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr x))) => x.1

/-- The value of `countVal` has order `countTag`. -/
lemma orderOf_countVal
    (t : Unit ⊕ ({x : H // orderOf x = 2} ⊕ ({x : H // orderOf x = 3} ⊕
      ({x : H // orderOf x = 4} ⊕ {x : H // orderOf x = 6})))) :
    orderOf (countVal t) = countTag t := by
  rcases t with _ | (⟨x, hx⟩ | (⟨x, hx⟩ | (⟨x, hx⟩ | ⟨x, hx⟩))) <;>
    simp_all [countVal, countTag]

/-- `countVal` is injective: distinct summands carry distinct orders. -/
lemma countVal_injective : Function.Injective (countVal (H := H)) := by
  intro a b hab
  have h1 : countTag a = countTag b := by
    rw [← orderOf_countVal a, ← orderOf_countVal b, hab]
  rcases a with _ | (⟨x, hx⟩ | (⟨x, hx⟩ | (⟨x, hx⟩ | ⟨x, hx⟩))) <;>
    rcases b with _ | (⟨y, hy⟩ | (⟨y, hy⟩ | (⟨y, hy⟩ | ⟨y, hy⟩))) <;>
    simp_all [countTag, countVal]

end CountHelpers

theorem card_count_orders_le {H : Type*} [Group H] [Finite H] :
    1 + Nat.card {x : H // orderOf x = 2} + Nat.card {x : H // orderOf x = 3}
      + Nat.card {x : H // orderOf x = 4} + Nat.card {x : H // orderOf x = 6} ≤ Nat.card H := by
  have hT : Nat.card (Unit ⊕ ({x : H // orderOf x = 2} ⊕ ({x : H // orderOf x = 3} ⊕
      ({x : H // orderOf x = 4} ⊕ {x : H // orderOf x = 6})))) =
      1 + Nat.card {x : H // orderOf x = 2} + Nat.card {x : H // orderOf x = 3}
        + Nat.card {x : H // orderOf x = 4} + Nat.card {x : H // orderOf x = 6} := by
    simp only [Nat.card_sum, Nat.card_unique]
    omega
  have hle : Nat.card (Unit ⊕ ({x : H // orderOf x = 2} ⊕ ({x : H // orderOf x = 3} ⊕
      ({x : H // orderOf x = 4} ⊕ {x : H // orderOf x = 6})))) ≤ Nat.card H :=
    Nat.card_le_card_of_injective _ countVal_injective
  omega

end Work.A7REC.Char
