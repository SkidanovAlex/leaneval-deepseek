import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- For a nonzero complex number and an integer exponent, the power splits as the product of the
powers with the nonnegative part of the exponent and the inverse of the power with the
nonnegative part of the negated exponent.  Consequently the whole product over `i` splits too. -/
theorem charPoly_zpow_prod {N : ℕ} (z : Fin N → ℂ) (k : Fin N → ℤ) (hz : ∀ i, z i ≠ 0) :
    (∏ i : Fin N, z i ^ (k i)) =
      (∏ i : Fin N, z i ^ ((k i).toNat)) * (∏ i : Fin N, z i ^ ((-(k i)).toNat))⁻¹ := by
  have key : ∀ i, z i ^ (k i) = z i ^ ((k i).toNat) * (z i ^ ((-(k i)).toNat))⁻¹ := by
    intro i
    have hh : ((k i).toNat : ℤ) - ((-(k i)).toNat : ℤ) = k i := by
      have := Int.toNat_sub_toNat_neg (k i); linarith
    have h1 : z i ^ (k i) = z i ^ (((k i).toNat : ℤ) - ((-(k i)).toNat : ℤ)) := by rw [hh]
    rw [h1, zpow_sub₀ (hz i), div_eq_mul_inv]
    simp only [zpow_natCast]
  rw [Finset.prod_congr rfl (fun i _ => key i), Finset.prod_mul_distrib, Finset.prod_inv_distrib]

end Work.BW
