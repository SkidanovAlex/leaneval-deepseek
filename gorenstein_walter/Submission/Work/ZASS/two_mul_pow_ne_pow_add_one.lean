import Mathlib
import Submission.Work.ZASS.Defs

namespace Work.ZASS

/-- **Z4 arithmetic (blueprint §ZASS).** `1 + (p^k-1)/2 = (p^k+1)/2` is never a power of `p`
for `p` prime and `k ≥ 1`: `2 * p^m = p^k + 1` would give `p ∣ 2 p^m - p^k = 1` when `m ≥ 1`,
and `p^k = 1` when `m = 0`.  This is the arithmetic that rules out `|W| = h + 1` in the
counting arguments of Z4/Z5. -/
theorem two_mul_pow_ne_pow_add_one {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k) :
    ∀ m : ℕ, 2 * p ^ m ≠ p ^ k + 1 := by
  intro m h
  rcases Nat.eq_zero_or_pos m with hm | hm
  · -- `m = 0`: the equation reads `2 = p ^ k + 1`, so `p ^ k = 1`, impossible since
    -- `p ^ k ≥ p ≥ 2`.
    subst hm
    simp only [pow_zero, mul_one] at h ⊢
    have hp2 : 2 ≤ p := hp.two_le
    have hle : p ≤ p ^ k := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ k := pow_le_pow_right₀ (by omega) hk
    omega
  · -- `m ≥ 1`: `p ∣ p ^ k` and `p ∣ 2 * p ^ m = p ^ k + 1`, hence `p ∣ 1 = (p ^ k + 1) - p ^ k`.
    have hdvd : p ∣ 2 * p ^ m := dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) 2
    rw [h] at hdvd
    have hdvdk : p ∣ p ^ k := dvd_pow_self p (by omega)
    have h1 : p ∣ (p ^ k + 1) - p ^ k := Nat.dvd_sub hdvd hdvdk
    have hpe : p = 1 := by simpa using h1
    exact hp.ne_one hpe

end Work.ZASS
