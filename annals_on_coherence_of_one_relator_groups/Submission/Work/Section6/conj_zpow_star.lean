import Mathlib

namespace Work.Section6

theorem conj_zpow_star {U : Type} [Ring U] [StarRing U] (u : Uˣ)
    (hu : star (↑u : U) = ((u⁻¹ : Uˣ) : U)) (k : ℤ) (x : U) :
    star ((↑(u ^ k) : U) * x * (↑((u ^ k)⁻¹) : U))
      = (↑(u ^ k) : U) * star x * (↑((u ^ k)⁻¹) : U) := by
  -- `hu` says that `star u` is the inverse of `u` in the unit group.  We first
  -- record the same statement for `u⁻¹` (as an element of `U`).
  have hinv : star (↑(u⁻¹) : U) = (↑u : U) := by
    have hA : star (↑(u⁻¹) : U) * (↑(u⁻¹) : U) = 1 := by
      have h := star_mul (↑u : U) (↑(u⁻¹) : U)
      rw [Units.mul_inv, star_one, hu] at h
      exact h.symm
    have hC : (↑(u⁻¹) : U) * (↑u : U) = 1 := Units.inv_mul u
    calc star (↑(u⁻¹) : U) = star (↑(u⁻¹) : U) * 1 := (mul_one _).symm
      _ = star (↑(u⁻¹) : U) * ((↑(u⁻¹) : U) * ↑u) := by rw [hC, mul_one]
      _ = (star (↑(u⁻¹) : U) * (↑(u⁻¹) : U)) * ↑u := by rw [mul_assoc]
      _ = 1 * ↑u := by rw [hA]
      _ = ↑u := one_mul _
  -- Hence `star` sends each `u ^ k` to its inverse, by two-sided induction on `k`.
  have key : ∀ k : ℤ, star ((↑(u ^ k)) : U) = (↑((u ^ k)⁻¹) : U) := by
    refine zpow_induction_right (g := u)
      (P := fun w : Uˣ => star (↑w : U) = (↑(w⁻¹) : U)) ?h1 ?hm ?hi
    · simp
    · intro a ha
      rw [Units.val_mul, star_mul, ha, hu]
      rw [mul_inv_rev, Units.val_mul]
    · intro a ha
      rw [Units.val_mul, star_mul, ha, hinv]
      rw [mul_inv_rev, inv_inv, Units.val_mul]
  have hA : star (↑(u ^ k) : U) = (↑((u ^ k)⁻¹) : U) := key k
  have hB : star ((↑((u ^ k)⁻¹)) : U) = (↑(u ^ k) : U) := by
    rw [← hA, star_star]
  rw [star_mul, star_mul, hA, hB]
  rw [mul_assoc]

end Work.Section6
