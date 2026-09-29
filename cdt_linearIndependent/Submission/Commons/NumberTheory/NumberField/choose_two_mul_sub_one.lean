import Mathlib.Data.Nat.Choose.Central

namespace Commons.NumberTheory.NumberField

/-- `2 * C(2r-1, r) = C(2r, r)`, the symmetry `C(2r-1, r-1) = C(2r-1, r)`
together with Pascal's rule `C(2r, r) = C(2r-1, r-1) + C(2r-1, r)`. -/
theorem choose_two_mul_sub_one (r : ℕ) (hr : 1 ≤ r) :
    2 * ((r + r - 1).choose r) = Nat.centralBinom r := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have harg : n + 1 + (n + 1) - 1 = n + (n + 1) := by omega
  rw [harg, Nat.centralBinom_eq_two_mul_choose]
  have h2 : 2 * (n + 1) = n + (n + 1) + 1 := by ring
  rw [h2, Nat.choose_succ_succ', Nat.choose_symm_add]
  ring

end Commons.NumberTheory.NumberField