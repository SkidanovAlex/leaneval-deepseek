import Mathlib.Algebra.Order.GroupWithZero.Canonical
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.Algebra.Order

theorem pow_mul_right_injective_of_lt_one {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
    {r c : Γ₀} (hr1 : r < 1) (hr0 : r ≠ 0) (hc : c ≠ 0) :
    Function.Injective fun n : ℕ => r ^ n * c := by
  intro n m h
  have hrpos : 0 < r := zero_lt_iff.mpr hr0
  have hnm : r ^ n = r ^ m := mul_right_cancel₀ hc h
  have hanti : StrictAnti fun n : ℕ => r ^ n := pow_right_strictAnti₀ hrpos hr1
  have h1 : n ≤ m := by
    by_contra hle
    have hlt : m < n := not_le.mp hle
    exact absurd (hanti hlt) (not_lt_of_ge (le_of_eq hnm.symm))
  have h2 : m ≤ n := by
    by_contra hle
    have hlt : n < m := not_le.mp hle
    exact absurd (hanti hlt) (not_lt_of_ge (le_of_eq hnm))
  exact le_antisymm h1 h2

end Commons.Algebra.Order