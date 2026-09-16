import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Topology.Algebra.Valued.ValuedField

open Filter
open scoped WithZero Topology

namespace Commons.Topology.Algebra.Valued

/-- The product of two power series with bounded coefficients (over a `ℤᵐ⁰`-valued field) has
bounded coefficients: `T · T ⊆ T` for the Tate algebra `T`. -/
theorem powerSeries_bounded_mul (K : Type*) [Field K] [Valued K ℤᵐ⁰]
    (f g : PowerSeries K) (Mf Mg : ℤ)
    (hf : ∀ n : ℕ, Valued.v (PowerSeries.coeff n f) ≤ WithZero.exp Mf)
    (hg : ∀ n : ℕ, Valued.v (PowerSeries.coeff n g) ≤ WithZero.exp Mg) :
    ∀ n : ℕ, Valued.v (PowerSeries.coeff n (f * g)) ≤ WithZero.exp (Mf + Mg) := by
  intro n
  rw [PowerSeries.coeff_mul]
  refine Valuation.map_sum_le (v := Valued.v) (g := WithZero.exp (Mf + Mg)) ?_
  intro p _
  rw [map_mul]
  calc Valued.v (PowerSeries.coeff p.1 f) * Valued.v (PowerSeries.coeff p.2 g)
      ≤ WithZero.exp Mf * WithZero.exp Mg := mul_le_mul' (hf p.1) (hg p.2)
    _ = WithZero.exp (Mf + Mg) := (WithZero.exp_add Mf Mg).symm

end Commons.Topology.Algebra.Valued
