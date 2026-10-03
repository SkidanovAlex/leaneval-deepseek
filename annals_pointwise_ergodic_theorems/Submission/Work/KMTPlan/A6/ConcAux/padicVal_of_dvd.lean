import Mathlib

namespace Work.KMTPlan.A6.ConcAux

theorem padicVal_of_dvd (p k N : ℕ) (hp : p.Prime) {z : ℤ} (hz : z ≠ 0)
    (h : (p : ℤ) ^ k ∣ (p : ℤ) ^ N * z) : k ≤ N + padicValNat p z.natAbs := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hzabs : z.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hz
  have hp0 : p ≠ 0 := hp.ne_zero
  -- Push divisibility in `ℤ` down to divisibility of the absolute values in `ℕ`.
  have h' : p ^ k ∣ p ^ N * z.natAbs := by
    have h1 := Int.natAbs_dvd_natAbs.mpr h
    simpa [Int.natAbs_pow, Int.natAbs_mul, Int.natAbs_natCast] using h1
  have hw : p ^ N * z.natAbs ≠ 0 := mul_ne_zero (pow_ne_zero N hp0) hzabs
  have h2 : k ≤ padicValNat p (p ^ N * z.natAbs) := (padicValNat_dvd_iff_le hw).mp h'
  -- Compute the valuation of the product.
  have hv : padicValNat p (p ^ N * z.natAbs) = N + padicValNat p z.natAbs := by
    rw [padicValNat.mul (pow_ne_zero N hp0) hzabs, padicValNat.pow, padicValNat.self hp.one_lt]
    ring
  omega

end Work.KMTPlan.A6.ConcAux
