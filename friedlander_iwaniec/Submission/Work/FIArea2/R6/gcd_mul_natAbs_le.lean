import Mathlib

namespace Work.FIArea2.R6

/-- `Nat.gcd` of a product is at most the product of the `Nat.gcd`s (pointwise on prime
valuations: `min (v a + v b) (v c) ≤ min (v a) (v c) + min (v b) (v c)`). -/
theorem gcd_mul_natAbs_le (c : ℕ) (a b : ℤ) :
    Nat.gcd (a * b).natAbs c ≤ Nat.gcd a.natAbs c * Nat.gcd b.natAbs c := by
  rw [Int.natAbs_mul]
  -- `Nat.gcd` of a product divides the product of the `Nat.gcd`s (generic `GCDMonoid` fact).
  have hdvd : Nat.gcd (a.natAbs * b.natAbs) c ∣ Nat.gcd a.natAbs c * Nat.gcd b.natAbs c := by
    have hh : Nat.gcd c (a.natAbs * b.natAbs) ∣ Nat.gcd c a.natAbs * Nat.gcd c b.natAbs :=
      gcd_mul_dvd_mul_gcd c a.natAbs b.natAbs
    rw [Nat.gcd_comm c (a.natAbs * b.natAbs), Nat.gcd_comm c a.natAbs, Nat.gcd_comm c b.natAbs]
      at hh
    exact hh
  rcases Nat.eq_zero_or_pos (Nat.gcd a.natAbs c * Nat.gcd b.natAbs c) with hpos | hpos
  · -- product of the two gcds vanishes, so both `a` and `b` (and `c`) are `0`
    rcases Nat.mul_eq_zero.mp hpos with h1 | h1
    · rw [Nat.gcd_eq_zero_iff] at h1
      obtain ⟨ha, hc⟩ := h1
      rw [Int.natAbs_eq_zero] at ha
      simp [ha, hc]
    · rw [Nat.gcd_eq_zero_iff] at h1
      obtain ⟨hb, hc⟩ := h1
      rw [Int.natAbs_eq_zero] at hb
      simp [hb, hc]
  · exact Nat.le_of_dvd hpos hdvd

end Work.FIArea2.R6
