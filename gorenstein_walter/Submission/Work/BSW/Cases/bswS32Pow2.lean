import Mathlib

namespace Work.BSW.Cases

/-- Even-order part of Bender's `InvertM` (Bender 1974, §3.2): if an element `y` inverts
`m ≠ 1` (i.e. `y⁻¹ * m * y = m⁻¹`) and `m` has even order, then `u = m ^ (orderOf m / 2)` is an
involution, inverted by `y` and hence commuting with `y`. -/
theorem bswS32Pow2 {G : Type} [Group G] [Finite G] {m y : G} (hm : m ≠ 1)
    (heven : Even (orderOf m)) (hinv : y⁻¹ * m * y = m⁻¹) :
    orderOf (m ^ (orderOf m / 2)) = 2 ∧
      y * (m ^ (orderOf m / 2)) = (m ^ (orderOf m / 2)) * y := by
  -- `n = orderOf m` is even and nonzero, say `n = k + k` with `k ≥ 1`; then `n / 2 = k`.
  have hposn : 0 < orderOf m := orderOf_pos m
  obtain ⟨k, hk⟩ := heven
  -- `u = m ^ (n / 2)` is an involution: `u ^ 2 = m ^ (n / 2 * 2) = m ^ n = 1`.
  have hu2 : (m ^ (orderOf m / 2)) ^ 2 = 1 := by
    rw [← pow_mul]
    have h2 : orderOf m / 2 * 2 = orderOf m := by omega
    rw [h2, pow_orderOf_eq_one]
  -- `u ≠ 1`, since `u = 1` would force `n ∣ n / 2` with `0 < n / 2 < n`.
  have hu_ne : m ^ (orderOf m / 2) ≠ 1 := by
    intro h1
    have hdvd : orderOf m ∣ orderOf m / 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
    have hpos : 0 < orderOf m / 2 := by omega
    have hlt : orderOf m / 2 < orderOf m := by omega
    exact Nat.not_dvd_of_pos_of_lt hpos hlt hdvd
  have hord : orderOf (m ^ (orderOf m / 2)) = 2 := orderOf_eq_prime hu2 hu_ne
  -- `y` inverts `u`: conjugation of the relation `y⁻¹ m y = m⁻¹` over the power `n / 2`.
  have hconj : y⁻¹ * (m ^ (orderOf m / 2)) * y = (m ^ (orderOf m / 2))⁻¹ := by
    have h1 : (y⁻¹ * m * y) ^ (orderOf m / 2) = y⁻¹ * m ^ (orderOf m / 2) * y := by
      simpa using (conj_pow (a := y⁻¹) (b := m) (i := orderOf m / 2))
    rw [← h1, hinv, inv_pow]
  -- an involution is its own inverse, so `y` actually centralizes `u`.
  have hu_inv : (m ^ (orderOf m / 2)) = (m ^ (orderOf m / 2))⁻¹ :=
    eq_inv_iff_mul_eq_one.mpr (by rw [← pow_two]; exact hu2)
  have hcomm : y⁻¹ * (m ^ (orderOf m / 2)) * y = m ^ (orderOf m / 2) := by
    rw [hconj]; exact hu_inv.symm
  have huy : (m ^ (orderOf m / 2)) * y = y * (m ^ (orderOf m / 2)) := by
    calc (m ^ (orderOf m / 2)) * y = y * (y⁻¹ * (m ^ (orderOf m / 2)) * y) := by group
      _ = y * (m ^ (orderOf m / 2)) := by rw [hcomm]
  exact ⟨hord, huy.symm⟩

end Work.BSW.Cases
