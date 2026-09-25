import Mathlib
import Submission.Work.BourgainPlan.Maximal.discAvgC

/-!
# The symbol (`Weyl/Dirichlet kernel`) of the polynomial density average

`khat P N θ = Σ_j k_N(j) e(2πi j θ) = N⁻¹ Σ_{i<N} e(2πi P(i) θ)` is the Fourier multiplier of the
density average `discAvgC P N` on `ℓ²(ℤ)` / `ℓ²(ℤ_J)` / `ℓ²(ℕ)` (see `discAvg_eq_fourier` in the
`Oscillation` area for the corresponding Fourier representation of `discAvg`, and
`polyWeylKernel` for the same object in the circle-method normalisation).  It is the object whose
minor-arc decay is `poly_kernel_minor_arc` and whose major-arc model is `polyMajorArcModelPre`.

Defined here (as a small self-contained module) so that statements about it -- in particular the
signed/block sums of its differences, `lacunary_khat_diff_sup` -- can be stated without duplicating
the expression.
-/

namespace Work.BourgainPlan.Maximal

open Finset
open scoped BigOperators

noncomputable section

/-- The symbol of `discAvgC P N`: `Σ_j k_N(j) e(2πi j θ)` with `k_N(j) = polyKernel P N j` the
density of the values of `P` on `[0,N)`. -/
def khat (P : Polynomial ℤ) (N : ℕ) (θ : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (Submission.polySupport P N), (Submission.polyKernel P N j : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (j : ℂ) * (θ : ℂ))

end

end Work.BourgainPlan.Maximal
