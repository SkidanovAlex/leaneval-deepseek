import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Valuation.Basic

namespace Commons.Topology.Algebra.Valued

/-- If every coefficient of `f` has valuation at most `a` and every coefficient of `g` has
valuation at most `b`, then every coefficient of `f * g` has valuation at most `a * b`.

The `n`-th coefficient of a product is a finite sum
`∑ p ∈ antidiagonal n, coeff p.1 f * coeff p.2 g` (see `PowerSeries.coeff_mul`), each of whose
summands has valuation `v (coeff p.1 f) * v (coeff p.2 g) ≤ a * b`; a valuation turns sums into
something bounded by the max of the summands (`Valuation.map_sum_le`), whence the result. -/
theorem powerSeries_coeff_mul_le {R : Type*} [CommRing R] {Γ₀ : Type*}
    [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀) (f g : PowerSeries R) {a b : Γ₀}
    (hf : ∀ m : ℕ, v (PowerSeries.coeff m f) ≤ a) (hg : ∀ m : ℕ, v (PowerSeries.coeff m g) ≤ b)
    (n : ℕ) : v (PowerSeries.coeff n (f * g)) ≤ a * b := by
  rw [PowerSeries.coeff_mul]
  refine Valuation.map_sum_le v ?_
  intro p hp
  rw [Valuation.map_mul]
  exact mul_le_mul' (hf p.1) (hg p.2)

end Commons.Topology.Algebra.Valued