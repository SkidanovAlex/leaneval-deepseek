import Mathlib

namespace Work.ZASS2

theorem eqOfNeOneOfCardLeTwo {Q : Type} [Group Q] [Finite Q] (h : Nat.card Q ≤ 2) {x y : Q}
    (hx : x ≠ 1) (hy : y ≠ 1) : x = y := by
  by_contra hne
  -- If `x ≠ y` then `1`, `x`, `y` are three distinct elements of `Q`, so `3 ≤ Nat.card Q`.
  have hf : Function.Injective (![1, x, y] : Fin 3 → Q) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h3 : 3 ≤ Nat.card Q := by
    have := Nat.card_le_card_of_injective (![1, x, y] : Fin 3 → Q) hf
    simpa using this
  omega

end Work.ZASS2
