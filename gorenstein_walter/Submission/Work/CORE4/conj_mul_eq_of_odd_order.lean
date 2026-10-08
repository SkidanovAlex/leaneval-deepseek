import Mathlib

namespace Work.CORE4

/-- If `y` conjugates `v` to `v⁻¹`, it conjugates every power of `v` to its inverse. -/
lemma conj_pow_eq_inv_pow {X : Type} [Group X] (y v : X) (hv : y * v * y⁻¹ = v⁻¹) (m : ℕ) :
    y * v ^ m * y⁻¹ = (v ^ m)⁻¹ := by
  have h1 : (MulAut.conj y) v = v⁻¹ := by rw [MulAut.conj_apply]; exact hv
  have h2 : (MulAut.conj y) (v ^ m) = ((MulAut.conj y) v) ^ m := map_pow _ v m
  rw [MulAut.conj_apply] at h2
  rw [h2, h1, inv_pow]

/-- If `y` (an involution) conjugates `u` of odd order to `u⁻¹`, then `y * u` is the
conjugate of `y` by `u ^ ((orderOf u - 1) / 2)`. -/
theorem conj_mul_eq_of_odd_order {X : Type} [Group X] (y u : X) (hy2 : y * y = 1) (hinv : y * u * y⁻¹ = u⁻¹) (hodd : Odd (orderOf u)) : y * u = u ^ ((orderOf u - 1) / 2) * y * (u ^ ((orderOf u - 1) / 2))⁻¹ := by
  have _ := hy2
  set k := (orderOf u - 1) / 2 with hk
  -- `orderOf u = 2 * k + 1`
  have hku : 2 * k + 1 = orderOf u := by
    rw [hk]
    obtain ⟨t, ht⟩ := hodd
    omega
  -- Step 1: `y * u = u⁻¹ * y`.
  have hy : y * u = u⁻¹ * y := by
    have h := congrArg (fun z => z * y) hinv
    simpa [mul_assoc] using h
  -- Step 2: conjugation by `y` inverts `u⁻¹` as well.
  have huinv : y * u⁻¹ * y⁻¹ = (u⁻¹)⁻¹ := by
    have h := congrArg (fun z => z⁻¹) hinv
    simpa [mul_assoc] using h
  -- Step 3: `y * (u ^ k)⁻¹ = u ^ k * y`.
  have hk1 : y * (u ^ k)⁻¹ = u ^ k * y := by
    have h := conj_pow_eq_inv_pow y u⁻¹ huinv k
    rw [inv_pow, inv_inv] at h
    have h2 := congrArg (fun z => z * y) h
    simpa [mul_assoc] using h2
  -- Step 4: `u ^ (2 * k) = u⁻¹`, because `u ^ (2 * k + 1) = u ^ orderOf u = 1`.
  have hpoweq : u ^ (2 * k) = u⁻¹ := by
    have h1 : u ^ (2 * k + 1) = 1 := by
      rw [hku]; exact pow_orderOf_eq_one u
    have h2 : u ^ (2 * k) * u = 1 := by rw [← pow_succ, h1]
    exact eq_inv_of_mul_eq_one_left h2
  calc y * u = u⁻¹ * y := hy
    _ = u ^ (2 * k) * y := by rw [← hpoweq]
    _ = (u ^ k * u ^ k) * y := by rw [two_mul, pow_add]
    _ = u ^ k * (u ^ k * y) := by rw [mul_assoc]
    _ = u ^ k * (y * (u ^ k)⁻¹) := by rw [← hk1]
    _ = u ^ k * y * (u ^ k)⁻¹ := by rw [mul_assoc]

end Work.CORE4
