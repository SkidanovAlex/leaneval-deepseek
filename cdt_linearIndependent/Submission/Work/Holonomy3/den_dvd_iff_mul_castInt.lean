import Mathlib

namespace Work.Holonomy3

/-- The denominator of `q : ℚ` divides `N` exactly when `N·q` is (the image of) an integer. -/
theorem den_dvd_iff_mul_castInt {q : ℚ} {N : ℕ} :
    q.den ∣ N ↔ ∃ z : ℤ, (N : ℚ) * q = (z : ℚ) := by
  constructor
  · -- If `q.den ∣ N`, write `N = q.den * k` and take `z = q.num * k`.
    rintro ⟨k, hk⟩
    refine ⟨q.num * k, ?_⟩
    have hd : (q.den : ℚ) * q = (q.num : ℚ) := by
      have h : (q.den : ℚ) * ((q.num : ℚ) / (q.den : ℚ)) = (q.num : ℚ) := by
        rw [mul_comm, div_mul_cancel₀]
        exact_mod_cast q.den_nz
      rwa [Rat.num_div_den] at h
    rw [hk, Nat.cast_mul, mul_assoc, mul_comm (k : ℚ) q, ← mul_assoc, hd]
    push_cast
    ring
  · -- If `N·q = z`, then `q = z / N`, whose denominator divides `N`.
    rintro ⟨z, hz⟩
    rcases eq_or_ne N 0 with rfl | hN
    · simp
    · have hNQ : (N : ℚ) ≠ 0 := by exact_mod_cast hN
      have hq : q = (z : ℚ) / N := by
        rw [eq_div_iff hNQ, mul_comm]
        exact hz
      have hq' : q = Rat.divInt z (N : ℤ) := by
        rw [hq, ← Int.cast_natCast (R := ℚ) N, Rat.intCast_div_eq_divInt]
      rw [hq']
      exact (Int.natCast_dvd_natCast).mp (Rat.den_dvd z (N : ℤ))

end Work.Holonomy3
