import Mathlib

namespace Work.ZASS2

/-- A finite group of cardinality at most two is commutative.  Indeed every element `x`
satisfies `x ^ 2 = 1` (its order divides `Nat.card Q ≤ 2`), and a group in which every
element is an involution is commutative. -/
private lemma isMulCommutative_of_natCard_le_two {Q : Type} [Group Q] [Finite Q]
    (h : Nat.card Q ≤ 2) : IsMulCommutative Q := by
  rw [isMulCommutative_iff]
  have key : ∀ x : Q, x ^ 2 = 1 := by
    intro x
    rw [← orderOf_dvd_iff_pow_eq_one]
    have hle : orderOf x ≤ Nat.card Q :=
      Nat.le_of_dvd (Nat.card_pos (α := Q)) (orderOf_dvd_natCard x)
    have hpos : 0 < orderOf x := orderOf_pos x
    have : orderOf x = 1 ∨ orderOf x = 2 := by omega
    rcases this with h1 | h2
    · rw [h1]; norm_num
    · rw [h2]
  intro a b
  have ha : a * a = 1 := by simpa [pow_two] using key a
  have hb : b * b = 1 := by simpa [pow_two] using key b
  have hab : (a * b) * (a * b) = 1 := by simpa [pow_two] using key (a * b)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [hai, hbi]

set_option linter.style.haveILetI false in
theorem commutatorLeOfIndexLeTwo {T : Type} [Group T] [Finite T] {H : Subgroup T}
    (hHn : H.Normal) (hidx : H.index ≤ 2) : commutator T ≤ H := by
  haveI := hHn
  have hcard : Nat.card (T ⧸ H) ≤ 2 := by
    rw [← Subgroup.index_eq_card H]; exact hidx
  exact Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
    (isMulCommutative_of_natCard_le_two hcard)

end Work.ZASS2
