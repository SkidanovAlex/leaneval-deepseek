import Mathlib
import Submission.Work.KT.Fund.SpectralAux

/-!
# `Work.KT.Fund.SpectralQ` — the resolvent functional calculus element `Q_ζ`

For `‖ζ‖ > ρ` the element
`Q b ρ ζ = (2πi)⁻¹ ∮_{|w| = ρ} (ζ - w)⁻¹ (w - b)⁻¹ dw`
of `A` is a "partial resolvent": it satisfies
`(ζ • 1 - b) * Q b ρ ζ = Proj b ρ` and `Q b ρ ζ * (ζ • 1 - b) = Proj b ρ`
(proved in `Work.KT.Fund.spectral_unit_z_Q`).  It follows that `ζ • Proj b ρ - Proj b ρ * b * Proj b ρ`
is invertible in the corner `Proj b ρ * A * Proj b ρ` for every `‖ζ‖ > ρ`, which is the input of
`Work.KT.Fund.spectral_unit_z`.
-/

namespace Work.KT.Fund

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

/-- The "outside" contour integral of the resolvent against the weight `(ζ - w)⁻¹`,
`Q b ρ ζ = (2πi)⁻¹ ∮_{|w|=ρ} (ζ - w)⁻¹ (w - b)⁻¹ dw`, for `‖ζ‖ > ρ`. -/
def Q (b : A) (ρ : ℝ) (ζ : ℂ) : A :=
  (2 * Real.pi * Complex.I)⁻¹ • ∮ w in C(0, ρ), (ζ - w)⁻¹ • Res b w

end

end Work.KT.Fund
