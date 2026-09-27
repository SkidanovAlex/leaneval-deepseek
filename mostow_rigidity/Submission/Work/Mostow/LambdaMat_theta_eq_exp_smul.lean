import Mathlib
import Submission.Work.Mostow.StabLift
import Submission.Work.Mostow.StabHoroForm
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.BusemannRay
import Submission.Work.Mostow.busemannCocycle
import Submission.Work.Mostow.poAux

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

open _root_.Matrix

variable {n : ℕ}

/-- The exponential of the Busemann cocycle is `tsign (rep g) / bdt g ξ`. -/
lemma exp_bCocy_eq (n : ℕ) (hA : Submission.Mostow.POActionProp n) (g : PO n 1) (ξ : E n)
    (hξ : ξ ∈ Sph n) :
    Real.exp (bCocy g ξ) = tsign (rep g) * (bdt g ξ)⁻¹ := by
  have hbd : bd g ξ ∈ Sph n := hA.2.2.2.2.2.2.2.1 g ξ hξ
  rw [bCocy, busemann_eq_log, Real.exp_log (busemann_arg_pos (bd g ξ) hbd (g • 0)),
    arg_bd_smul g ξ 0 hξ, tpart_zero, inner_zero_left, sub_zero, one_mul]

/-- For `g` fixing the boundary point `ξ`, the lift of `g` scales the null vector `θ = (ξ,1)` by
`exp (-bCocy g ξ)`. -/
theorem LambdaMat_theta_eq_exp_smul (n : ℕ) (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n) (g : LeanEval.Geometry.MostowRigidity.PO n 1)
    (ξ : Submission.Mostow.E n) (hξ : ξ ∈ Submission.Mostow.Sph n)
    (hgξ : Submission.Mostow.bd g ξ = ξ) :
    Matrix.mulVec (Work.Mostow.LambdaMat g) (Work.Mostow.theta ξ)
      = Real.exp (-(Work.Mostow.bCocy g ξ)) • Work.Mostow.theta ξ := by
  have hbdt : bdt g ξ ≠ 0 := bdt_ne_zero g ξ hξ
  have hM : mat (rep g) *ᵥ theta ξ = bdt g ξ • theta ξ := by
    have h := theta_bd_smul g ξ hξ
    rw [hgξ] at h
    have h2 := congrArg (fun v => (bdt g ξ) • v) h
    rw [smul_smul, mul_inv_cancel₀ hbdt, one_smul] at h2
    exact h2.symm
  have hL : Matrix.mulVec (LambdaMat g) (theta ξ) = (tsign (rep g) * bdt g ξ) • theta ξ := by
    rw [show LambdaMat g = tsign (rep g) • mat (rep g) from rfl, Matrix.smul_mulVec, hM,
      smul_smul]
  have hscal : tsign (rep g) * bdt g ξ = Real.exp (-(bCocy g ξ)) := by
    have ht : (tsign (rep g))⁻¹ = tsign (rep g) := inv_eq_of_mul_eq_one_right (tsign_sq (rep g))
    rw [Real.exp_neg, exp_bCocy_eq n hA g ξ hξ, mul_inv, inv_inv, ht, mul_comm]
  rw [hL, hscal]

end Work.Mostow
