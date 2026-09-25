import Mathlib
import Submission.Work.Hormander.Weights.Rint
import Submission.Work.Hormander.Weights.Expand

namespace Work.Hormander.Weights

/-- The `(1,0)`-part `∂_j u - u ∂_j φ` of the Kohn–Morrey form is compactly supported as
soon as `u` is: `∂_j u` is a first order differential operator applied to a compactly
supported function (so it is supported in `tsupport u`, since `u` vanishes on a
neighbourhood of every point outside `tsupport u`), and `u ∂_j φ` is supported in the
support of `u`. -/
theorem hasCompactSupport_delta {n : ℕ} (j : Fin n) {u : Cn n → ℂ} {φ : Cn n → ℝ}
    (hsu : HasCompactSupport u) :
    HasCompactSupport (fun z => dCoord n j u z - u z * dPhi n j φ z) :=
  (hasCompactSupport_dCoord hsu j).sub (hsu.mul_right (f' := fun z => dPhi n j φ z))

end Work.Hormander.Weights
