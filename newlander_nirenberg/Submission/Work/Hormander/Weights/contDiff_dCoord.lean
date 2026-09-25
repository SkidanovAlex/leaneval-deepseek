import Mathlib
import Submission.Work.Hormander.Weights.Basic

namespace Work.Hormander.Weights

/-- `∂_j u = (1/2)(du(e_j) - i·du(i e_j))` is a linear combination of the
components `z ↦ du_z(e_j)` and `z ↦ du_z(i e_j)` of the derivative.  For a `C²`
function `u` the derivative `du` is `C¹`, and evaluation at a fixed vector is
`C¹` (`ContDiff.clm_apply`), whence `∂_j u` is `C¹`. -/
theorem contDiff_dCoord {n : ℕ} (j : Fin n) {u : Cn n → ℂ} (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (fun z => dCoord n j u z) := by
  have hderiv : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (by norm_num)
  have hA : ContDiff ℝ 1 (fun z => fderiv ℝ u z (evec n j)) :=
    hderiv.clm_apply contDiff_const
  have hB : ContDiff ℝ 1 (fun z => fderiv ℝ u z (ivec n j)) :=
    hderiv.clm_apply contDiff_const
  have hI : ContDiff ℝ 1 (fun z : Cn n => Complex.I * fderiv ℝ u z (ivec n j)) :=
    contDiff_const.mul hB
  have hsub : ContDiff ℝ 1
      (fun z : Cn n => fderiv ℝ u z (evec n j) - Complex.I * fderiv ℝ u z (ivec n j)) :=
    hA.sub hI
  have h2 : ContDiff ℝ 1
      (fun z : Cn n => (1 / 2 : ℂ) *
        (fderiv ℝ u z (evec n j) - Complex.I * fderiv ℝ u z (ivec n j))) :=
    contDiff_const.mul hsub
  convert h2 using 1
  ext z
  rfl

end Work.Hormander.Weights
