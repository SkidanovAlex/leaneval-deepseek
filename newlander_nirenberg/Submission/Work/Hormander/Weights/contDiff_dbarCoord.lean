import Mathlib
import Submission.Work.Hormander.Weights.Basic

namespace Work.Hormander.Weights

/-- If `u` is `C²`, then `z ↦ ∂̄_j u(z)` is `C¹`: this is the regularity statement
underlying the commutation of `∂̄` with other operators in the weighted `L²` theory.

Here `∂̄_j u(z) = (1/2)(∂_{x_j} + i ∂_{y_j})u(z) = (1/2)(du_z(e_j) + i·du_z(i e_j))`,
a fixed linear combination of the two directional derivatives `du_z(e_j)` and
`du_z(i e_j)`, which are given by the continuous linear functional `fderiv ℝ u z`
evaluated at the constant vectors `e_j`, `i e_j`.  Since `z ↦ fderiv ℝ u z` is `C¹`
for `u` of class `C²` and evaluation of a continuous linear map at a fixed vector is
linear (hence smooth), the conclusion follows. -/
theorem contDiff_dbarCoord {n : ℕ} (j : Fin n) {u : Cn n → ℂ} (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (fun z => dbarCoord n j u z) := by
  -- The bundled derivative of a `C^{m+1}` function is `C^m`.
  have h : ContDiff ℝ 1 fun p : Cn n × Cn n =>
      (fderiv ℝ u p.1 : Cn n →L[ℝ] ℂ) p.2 :=
    hu.contDiff_fderiv_apply (m := 1) (by norm_num)
  -- The two directional derivatives, as functions of `z`.
  have hA : ContDiff ℝ 1 fun z : Cn n => fderiv ℝ u z (evec n j) :=
    h.comp (contDiff_prodMk_left (evec n j))
  have hB : ContDiff ℝ 1 fun z : Cn n => fderiv ℝ u z (ivec n j) :=
    h.comp (contDiff_prodMk_left (ivec n j))
  -- Unfold `dbarCoord` and assemble the linear combination.
  rw [show (fun z => dbarCoord n j u z) =
      (fun z : Cn n => (1 / 2 : ℂ) *
        (fderiv ℝ u z (evec n j) + Complex.I * fderiv ℝ u z (ivec n j))) from by
    funext z; rw [dbarCoord]]
  exact ContDiff.mul contDiff_const (hA.add (ContDiff.mul contDiff_const hB))

end Work.Hormander.Weights
