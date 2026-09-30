import Mathlib
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Lattice condition, split into nonnegative parts: if `y i ≠ 0` for all `i` and
`∏ i, (y i) ^ (z i) = 1` (integer exponents), then the products with the exponents replaced by
their nonnegative parts `(z i).toNat` and `(-(z i)).toNat` agree. -/
theorem prod_zpow_eq_prod_toNat {N : ℕ} (z : Fin N → ℤ) (y : Fin N → ℂ) (hy : ∀ i, y i ≠ 0)
    (h : ∏ i, (y i) ^ (z i) = 1) :
    ∏ i, (y i) ^ ((z i).toNat) = ∏ i, (y i) ^ (((-(z i))).toNat) := by
  -- `(z i).toNat = z i + ((-(z i)).toNat)` as integers, so each power splits multiplicatively.
  have hz : ∀ i, ((z i).toNat : ℤ) = z i + ((-(z i)).toNat : ℤ) := by
    intro i
    have := Int.toNat_sub_toNat_neg (z i)
    omega
  have key : ∀ i, (y i) ^ ((z i).toNat) = (y i) ^ (z i) * (y i) ^ (((-(z i))).toNat) := by
    intro i
    rw [← zpow_natCast (y i) ((z i).toNat), hz i, zpow_add₀ (hy i), zpow_natCast]
  rw [Finset.prod_congr rfl (fun i _ => key i), Finset.prod_mul_distrib, h, one_mul]

end Work.BW
