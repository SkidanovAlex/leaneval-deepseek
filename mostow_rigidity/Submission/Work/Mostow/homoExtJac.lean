import Mathlib
import Submission.Work.Mostow.visualDefs
import Submission.Work.Mostow.homoExtAux
import Submission.Work.Mostow.homoExtDeriv
import Submission.Work.Mostow.phiFunConformal
import Submission.Work.Mostow.conformalAbsDet

/-!
# The Jacobian of the homogeneous extension of the boundary action

`homoExt g` is the degree-one homogeneous extension of the boundary action `bd g` to
`E n ∖ {0}`: on the sphere it agrees with `bd g = phiFun g`, and `homoExt g x = ‖x‖ • bd g (x/‖x‖)`.

This file computes the absolute value of its Jacobian determinant:

  `|det (fderiv ℝ (homoExt g) x)| = (dfun g (‖x‖⁻¹ • x)) ^ (1 - n)`  for `x ≠ 0`.

The proof is the composition of three independent facts.

* `homoExtFDerivAux` (`Submission.Work.Mostow.homoExtDeriv`): the differential of `homoExt g` at
  `x ≠ 0` maps the radial direction `‖x‖⁻¹ • x` to `phiFun g (‖x‖⁻¹ • x)` and agrees with
  `fderiv ℝ (phiFun g) (‖x‖⁻¹ • x)` on the hyperplane orthogonal to `x`.
* `phiFunConformal` (`Submission.Work.Mostow.phiFunConformal`): `fderiv ℝ (phiFun g) ξ` is
  conformal on `ξᗮ` with factor `1 / dfun g ξ`, and its image is orthogonal to `phiFun g ξ`.
* `conformalAbsDet` (`Submission.Work.Mostow.conformalAbsDet`): a linear endomorphism of `E n`
  that fixes (up to the unit vector `ψ`) the radial direction and scales `uᗮ` by `1/s` has
  `|det| = s ^ (1 - n)`.

The two unit vectors and the positivity of the scale are supplied by `homoExtAux`
(`phiFunUnitAux`, `dfunPosAux`).
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal Pointwise

noncomputable section

theorem homoExtJac (n : ℕ) (hn : 1 ≤ n) :
    ∀ (g : LeanEval.Geometry.MostowRigidity.PO n 1) (x : Submission.Mostow.E n), x ≠ 0 →
      |(fderiv ℝ (Work.Mostow.homoExt g) x).det|
        = (Work.Mostow.dfun g (‖x‖⁻¹ • x)) ^ (-(n : ℝ) + 1) := by
  intro g x hx
  have hxn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hu_norm : ‖‖x‖⁻¹ • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_mul_cancel₀ hxn]
  have hu_sph : ‖x‖⁻¹ • x ∈ Sph n := by
    rw [Sph, mem_sphere_zero_iff_norm]; exact hu_norm
  have hd : dfun g (‖x‖⁻¹ • x) ≠ 0 := ne_of_gt (dfunPosAux n g _ hu_sph)
  have hxv : ∀ v : E n, inner ℝ (‖x‖⁻¹ • x) v = 0 → inner ℝ x v = 0 := by
    intro v hv
    have h2 : ‖x‖⁻¹ * inner ℝ x v = 0 := by simpa [real_inner_smul_left] using hv
    exact (mul_eq_zero.mp h2).resolve_left (inv_ne_zero hxn)
  refine conformalAbsDet n hn (‖x‖⁻¹ • x) (phiFun g (‖x‖⁻¹ • x)) hu_norm
    (phiFunUnitAux n g _ hu_sph) (dfun g (‖x‖⁻¹ • x)) (dfunPosAux n g _ hu_sph)
    (fderiv ℝ (homoExt g) x) (homoExtFDerivAux n g x hx hd).1 ?_ ?_
  · intro v hv
    rw [(homoExtFDerivAux n g x hx hd).2 v (hxv v hv)]
    exact (phiFunConformal n g _ hu_sph hd v hv).1
  · intro v hv
    rw [(homoExtFDerivAux n g x hx hd).2 v (hxv v hv)]
    exact (phiFunConformal n g _ hu_sph hd v hv).2

end

end Work.Mostow
