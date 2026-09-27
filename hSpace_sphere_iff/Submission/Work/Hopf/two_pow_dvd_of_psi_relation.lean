import Mathlib

namespace Work.Hopf

/-- 2-adic divisibility extracted from the Adams `ψ²`/`ψ³` relation.

Writing `A = 2 ^ (2n) - 2 ^ n = 2 ^ n (2 ^ n - 1)` and
`B = 3 ^ (2n) - 3 ^ n = 3 ^ n (3 ^ n - 1)`, the hypothesis says `A μ₃ = B μ₂`.
The 2-adic valuation of the left side is `n + v₂ μ₃`; that of the right side is
`v₂ (3 ^ n - 1) + v₂ μ₂`.  Since `μ₂` is odd, `v₂ μ₂ = 0`, so
`v₂ (3 ^ n - 1) = n + v₂ μ₃ ≥ n` and hence `2 ^ n ∣ 3 ^ n - 1`.

We argue without valuations: `2 ^ n` is coprime to the odd number `3 ^ n μ₂`, and it
divides `(3 ^ n μ₂) (3 ^ n - 1)`, which equals `2 ^ n ((2 ^ n - 1) μ₃)` by the
hypothesis.  Coprimality then cancels the odd factor. -/
theorem two_pow_dvd_of_psi_relation (n : ℕ) (hn : 1 ≤ n) (μ₂ μ₃ : ℤ)
    (h : ((2 : ℤ) ^ (2 * n) - (2 : ℤ) ^ n) * μ₃ = ((3 : ℤ) ^ (2 * n) - (3 : ℤ) ^ n) * μ₂)
    (hodd : Odd μ₂) : (2 : ℤ) ^ n ∣ (3 : ℤ) ^ n - 1 := by
  -- Rewrite the squares `2 ^ (2n) = (2 ^ n) ^ 2` and `3 ^ (2n) = (3 ^ n) ^ 2`.
  have h2 : (2 : ℤ) ^ (2 * n) = ((2 : ℤ) ^ n) ^ 2 := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
  have h3 : (3 : ℤ) ^ (2 * n) = ((3 : ℤ) ^ n) ^ 2 := by
    rw [show 2 * n = n * 2 by omega, pow_mul]
  rw [h2, h3] at h
  -- Reassociate the hypothesis into the form used for cancellation.
  have key : ((3 : ℤ) ^ n * μ₂) * ((3 : ℤ) ^ n - 1)
      = (2 : ℤ) ^ n * (((2 : ℤ) ^ n - 1) * μ₃) := by
    calc ((3 : ℤ) ^ n * μ₂) * ((3 : ℤ) ^ n - 1)
        = (((3 : ℤ) ^ n) ^ 2 - (3 : ℤ) ^ n) * μ₂ := by ring
      _ = (((2 : ℤ) ^ n) ^ 2 - (2 : ℤ) ^ n) * μ₃ := h.symm
      _ = (2 : ℤ) ^ n * (((2 : ℤ) ^ n - 1) * μ₃) := by ring
  have hdiv : (2 : ℤ) ^ n ∣ ((3 : ℤ) ^ n * μ₂) * ((3 : ℤ) ^ n - 1) := by
    rw [key]
    exact dvd_mul_right ((2 : ℤ) ^ n) (((2 : ℤ) ^ n - 1) * μ₃)
  -- `2 ^ n` is coprime to the odd number `3 ^ n * μ₂`.
  have hcop : IsCoprime ((2 : ℤ) ^ n) ((3 : ℤ) ^ n * μ₂) := by
    have h1 : IsCoprime (2 : ℤ) ((3 : ℤ) ^ n) :=
      Int.isCoprime_two_left.mpr (Odd.pow (show Odd (3 : ℤ) by decide))
    have h2' : IsCoprime (2 : ℤ) μ₂ := Int.isCoprime_two_left.mpr hodd
    exact IsCoprime.pow_left (IsCoprime.mul_right h1 h2')
  exact IsCoprime.dvd_of_dvd_mul_left hcop hdiv

end Work.Hopf
