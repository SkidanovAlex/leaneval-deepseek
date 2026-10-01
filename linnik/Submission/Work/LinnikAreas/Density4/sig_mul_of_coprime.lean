import Mathlib
import Submission.Work.LinnikAreas.Density4.ShiftedDefs

namespace Work.LinnikAreas.Density4

open Finset

/-- `σ_{-1/2}(n) = Σ_{d ∣ n} d^{-1/2}` is multiplicative: for coprime `m`, `n`,
`sigR (m * n) = sigR m * sigR n`.  Indeed the divisors of `m * n` are exactly the
products `d₁ * d₂` with `d₁ ∣ m`, `d₂ ∣ n`, uniquely so by coprimality, and
`(d₁ * d₂)^{-1/2} = d₁^{-1/2} · d₂^{-1/2}`. -/
theorem sig_mul_of_coprime {m n : ℕ} (hmn : m.Coprime n) :
    sigR (m * n) = sigR m * sigR n := by
  rw [sigR, sigR, sigR]
  -- the divisors of `m * n` are the pointwise products `d₁ * d₂`
  rw [Nat.divisors_mul, Finset.mul_def]
  -- the multiplication map is injective on `divisors m ×ˢ divisors n` by coprimality
  rw [Finset.sum_image]
  · rw [Finset.sum_product, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    -- `1/√(a*b) = (1/√a) * (1/√b)`
    rw [Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg a), one_div, one_div, one_div, mul_inv]
  · intro x hx y hy hxy
    exact hmn.mul_injOn_divisors hx hy hxy

end Work.LinnikAreas.Density4
