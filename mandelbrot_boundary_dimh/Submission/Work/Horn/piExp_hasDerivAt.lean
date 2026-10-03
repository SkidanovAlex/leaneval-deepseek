import Mathlib
import Submission.Work.Horn.basic

/-!
# Derivative of the universal cover `π(w) = exp (2πi w)`

`MandelDim.piExp w = Complex.exp (2 * Real.pi * Complex.I * w)`, so it is the exponential of a
`ℂ`-linear map and

`(πExp)' u = 2πi · πExp u`.

This is the chain rule for `Complex.exp` composed with the linear map `w ↦ 2πi w`.
-/

namespace Work.Horn

theorem piExp_hasDerivAt (u : ℂ) :
    HasDerivAt MandelDim.piExp (2 * ↑Real.pi * Complex.I * MandelDim.piExp u) u := by
  unfold MandelDim.piExp
  have h := (hasDerivAt_const_mul (x := u) (2 * ↑Real.pi * Complex.I : ℂ)).cexp
  simpa [mul_comm] using h

end Work.Horn
