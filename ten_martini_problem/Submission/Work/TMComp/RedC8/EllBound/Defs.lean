import Mathlib

/-!
# The harmonic-measure barrier for the linear-in-`ε` bound on `ℓ`

Vocabulary for `ell_le_mul_of_lyap_eq_zero`.  For `R > 0` the map

`w(z) = (R + (z - E₀)) / (R - (z - E₀))`

sends the upper half disk `{‖z - E₀‖ < R, 0 < Im z}` onto the first quadrant, its diameter
onto `(0, ∞)` and its arc onto the positive imaginary axis.  Consequently

`harc E₀ R M z = (2M/π) * Im (log w(z)) = (2M/π) * arg w(z)`

is the harmonic measure of the arc: it is harmonic on the upper half disk, equals `M` on the
arc, `0` on the diameter, lies in `[0, M]`, and at `E₀ + iε` equals `(4M/π) * arctan (ε/R)`.
-/

noncomputable section

namespace Work.TMComp.RedC8

/-- The harmonic-measure barrier of the upper half disk of radius `R` about `E₀`. -/
def harc (E₀ R M : ℝ) (z : ℂ) : ℝ :=
  (2 * M / Real.pi)
    * (Complex.log ((R + (z - (E₀ : ℂ))) / (R - (z - (E₀ : ℂ))))).im

end Work.TMComp.RedC8
