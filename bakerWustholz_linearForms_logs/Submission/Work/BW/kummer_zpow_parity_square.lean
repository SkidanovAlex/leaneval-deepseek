import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If `∏ i, β i ^ (d i)` is a square in a field and every `β i` is nonzero, then the same
product with exponents reduced modulo `2` (so `0` or `1` in `ℤ`) is also a square. -/
theorem kummer_zpow_parity_square {K : Type*} [Field K] {n : ℕ} (β : Fin n → K)
    (hβnz : ∀ i, β i ≠ 0) (d : Fin n → ℤ) (hsq : IsSquare (∏ i, β i ^ d i)) :
    IsSquare (∏ i, β i ^ (d i % 2)) := by
  -- Euclidean division of each exponent: `d i = 2 * (d i / 2) + d i % 2`.
  have hdecomp : ∀ i, d i = 2 * (d i / 2) + d i % 2 := fun i => by
    have h := Int.mul_ediv_add_emod (d i) 2
    linarith
  -- Split each factor into a square times the parity-reduced factor.
  have h1 : ∀ i, β i ^ d i = (β i ^ (d i / 2)) * (β i ^ (d i / 2)) * β i ^ (d i % 2) := by
    intro i
    have h2 : β i ^ ((2 : ℤ) * (d i / 2)) = β i ^ (d i / 2) * β i ^ (d i / 2) := by
      rw [show (2 : ℤ) * (d i / 2) = (d i / 2) * 2 by ring, zpow_mul, zpow_two]
    conv_lhs => rw [hdecomp i, zpow_add₀ (hβnz i)]
    rw [h2]
  -- Hence the full product is `c^2` times the parity-reduced product, `c = ∏ β i ^ (d i / 2)`.
  have hP : ∏ i, β i ^ d i
      = (∏ i, β i ^ (d i / 2)) * (∏ i, β i ^ (d i / 2)) * ∏ i, β i ^ (d i % 2) := by
    rw [Finset.prod_congr rfl (fun i _ => h1 i)]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hc : (∏ i, β i ^ (d i / 2)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro i _
    exact zpow_ne_zero _ (hβnz i)
  have hsq2 : IsSquare ((∏ i, β i ^ (d i / 2)) * (∏ i, β i ^ (d i / 2))) :=
    IsSquare.mul_self _
  -- The parity-reduced product is the quotient of a square by the square `c^2`.
  have hd : IsSquare ((∏ i, β i ^ d i) / ((∏ i, β i ^ (d i / 2)) * (∏ i, β i ^ (d i / 2)))) :=
    IsSquare.div hsq hsq2
  have hQ : (∏ i, β i ^ d i) / ((∏ i, β i ^ (d i / 2)) * (∏ i, β i ^ (d i / 2)))
      = ∏ i, β i ^ (d i % 2) := by
    rw [hP, mul_div_cancel_left₀ _ (mul_ne_zero hc hc)]
  rwa [hQ] at hd

end Work.BW
