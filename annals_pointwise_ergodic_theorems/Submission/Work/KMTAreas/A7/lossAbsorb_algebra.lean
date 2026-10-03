import Mathlib

namespace Work.KMTAreas.A7

/-- Pure algebra of real powers (`ℝ.rpow`) behind the absorption of the loss factor:
the exponent `A + 4` of `(1+L)` splits as `4 + A`, and the exponent `(A+4) * ρ * L`
of `2` splits as `(2 * ρ * L) * 2 + A * ρ * L`, the first piece being the doubled
exponent `2 * ρ * L` of the `ℓ²` estimate and the second the exponent `A * ρ * L`
already present in the loss factor. -/
theorem lossAbsorb_algebra (A ρ L : ℝ) (hL : 0 ≤ L) :
    (1 + L) ^ (A + 4) * (2 : ℝ) ^ ((A + 4) * ρ * L) =
      ((1 + L) ^ (4 : ℝ) * ((2 : ℝ) ^ (2 * ρ * L)) ^ 2) *
        ((1 + L) ^ A * (2 : ℝ) ^ (A * ρ * L)) := by
  have h1 : (0:ℝ) < 1 + L := by linarith
  have h2 : (0:ℝ) < 2 := by norm_num
  rw [Real.rpow_add h1]
  rw [show (A + 4) * ρ * L = A * ρ * L + (2 * ρ * L + 2 * ρ * L) by ring]
  rw [Real.rpow_add h2, Real.rpow_add h2]
  ring

end Work.KMTAreas.A7
