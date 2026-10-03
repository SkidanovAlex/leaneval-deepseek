import Mathlib

namespace Work.KMTAreas.A7

open scoped ENNReal NNReal BigOperators

/-- The sum in a finite `PiLp` space is the `WithLp.toLp` of the coordinatewise sum: the
finite-dimensional continuous linear equivalence `PiLp.continuousLinearEquiv` transports `tsum`
from `Fin J → ℂ` to `WithLp r (Fin J → ℂ)`. -/
theorem toLp_tsum_pi {ι : Type*} (r : NNReal) (J : ℕ) (v : ι → Fin J → ℂ) (hv : Summable v) :
    WithLp.toLp r (∑' j, v j) = ∑' j, WithLp.toLp r (v j) := by
  have _ := hv
  simpa using
    (PiLp.continuousLinearEquiv (r : ℝ≥0∞) ℂ (fun _ : Fin J => ℂ)).symm.map_tsum (f := v)

end Work.KMTAreas.A7
