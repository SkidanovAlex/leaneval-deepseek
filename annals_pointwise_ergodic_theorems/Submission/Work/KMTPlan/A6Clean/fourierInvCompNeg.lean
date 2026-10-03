import Mathlib

namespace Work.KMTPlan.A6Clean

/-- Fourier inversion intertwines the reflection of the frequency variable with the
reflection of the space variable: inverting `ξ ↦ A (-ξ)` at `x` is the same as inverting
`A` at `-x`.  This is `Real.fourierInv_comp_linearIsometry` for the isometry
`LinearIsometryEquiv.neg ℝ` (whose underlying map is `ξ ↦ -ξ`). -/
theorem fourierInvCompNeg (A : ℝ → ℂ) (x : ℝ) :
    FourierTransformInv.fourierInv (fun ξ : ℝ => A (-ξ)) x = FourierTransformInv.fourierInv A (-x) :=
  Real.fourierInv_comp_linearIsometry (LinearIsometryEquiv.neg ℝ) A x

end Work.KMTPlan.A6Clean
