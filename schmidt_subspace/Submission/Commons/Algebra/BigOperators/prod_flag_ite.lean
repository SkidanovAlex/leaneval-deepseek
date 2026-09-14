import Mathlib.Data.Fintype.BigOperators

namespace Commons.Algebra.BigOperators

open scoped BigOperators

/-- A product over `Fin N` whose term only depends on whether the index is `< i`. -/
theorem prod_flag_ite {M : Type*} [CommMonoid M] {N i : ℕ} (hi : i ≤ N) (a b : M) :
    ∏ k : Fin N, (if k.val < i then a else b) = a ^ i * b ^ (N - i) := by
  rw [Fin.prod_univ_eq_prod_range (fun k : ℕ => if k < i then a else b) N]
  conv_lhs => rw [show N = i + (N - i) from (Nat.add_sub_of_le hi).symm]
  rw [Finset.prod_range_add]
  congr 1
  · have h1 : ∀ k ∈ Finset.range i, (if k < i then a else b) = a := by
      intro k hk; rw [if_pos (Finset.mem_range.mp hk)]
    rw [Finset.prod_eq_pow_card h1, Finset.card_range]
  · have h2 : ∀ k ∈ Finset.range (N - i), (if i + k < i then a else b) = b := by
      intro k hk; rw [if_neg (by omega)]
    rw [Finset.prod_eq_pow_card h2, Finset.card_range]

end Commons.Algebra.BigOperators