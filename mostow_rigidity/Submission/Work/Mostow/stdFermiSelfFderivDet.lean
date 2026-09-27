import Mathlib
import Submission.Work.Mostow.stdFermiDefs

namespace Work.Mostow

open Submission.Mostow

/-- The standard Fermi chart `fermiSelf` of `E 2` has derivative with determinant
`cosh (x 1)^2 * cosh (x 0)`: the hyperbolic area Jacobian in Fermi coordinates. -/
theorem stdFermiSelfFderivDet (x : Submission.Mostow.E 2) :
    (fderiv ℝ Work.Mostow.FermiTwo.fermiSelf x).det =
      Real.cosh (x 1) ^ 2 * Real.cosh (x 0) := by
  let Q : Fin 2 → Submission.Mostow.E 2 →L[ℝ] ℝ :=
    fun i => PiLp.proj (𝕜 := ℝ) (2 : ENNReal) (fun _ : Fin 2 => ℝ) i
  let L : Submission.Mostow.E 2 →L[ℝ] Submission.Mostow.E 2 :=
    ((Real.cosh (x 1) * Real.cosh (x 0)) • Q 0
        + (Real.sinh (x 1) * Real.sinh (x 0)) • Q 1).smulRight FermiTwo.axis
      + ((Real.cosh (x 1) • Q 1).smulRight FermiTwo.axisPerp)
  have hfermi : fderiv ℝ FermiTwo.fermiSelf x = L := by
    have hsin0 : HasFDerivAt (fun y : Submission.Mostow.E 2 => Real.sinh (y 0))
        (Real.cosh (x 0) • Q 0) x :=
      (PiLp.hasFDerivAt_apply (2 : ENNReal) x 0).sinh
    have hcos1 : HasFDerivAt (fun y : Submission.Mostow.E 2 => Real.cosh (y 1))
        (Real.sinh (x 1) • Q 1) x :=
      (PiLp.hasFDerivAt_apply (2 : ENNReal) x 1).cosh
    have hsin1 : HasFDerivAt (fun y : Submission.Mostow.E 2 => Real.sinh (y 1))
        (Real.cosh (x 1) • Q 1) x :=
      (PiLp.hasFDerivAt_apply (2 : ENNReal) x 1).sinh
    have hprod : HasFDerivAt (fun y : Submission.Mostow.E 2 => Real.cosh (y 1) * Real.sinh (y 0))
        ((Real.cosh (x 1) * Real.cosh (x 0)) • Q 0
          + (Real.sinh (x 1) * Real.sinh (x 0)) • Q 1) x := by
      have h := hcos1.mul hsin0
      rw [show Real.cosh (x 1) • (Real.cosh (x 0) • Q 0)
            + Real.sinh (x 0) • (Real.sinh (x 1) • Q 1)
          = (Real.cosh (x 1) * Real.cosh (x 0)) • Q 0
            + (Real.sinh (x 1) * Real.sinh (x 0)) • Q 1 from by
            rw [smul_smul, smul_smul, mul_comm (Real.sinh (x 0)) (Real.sinh (x 1))]] at h
      exact h
    have hT1 := hprod.smul_const FermiTwo.axis
    have hT2 := hsin1.smul_const FermiTwo.axisPerp
    have hsum := hT1.add hT2
    have hfun : FermiTwo.fermiSelf = fun y : Submission.Mostow.E 2 =>
        (Real.cosh (y 1) * Real.sinh (y 0)) • FermiTwo.axis
          + Real.sinh (y 1) • FermiTwo.axisPerp := by
      funext y
      simp [FermiTwo.fermiSelf, FermiTwo.lineStd, smul_smul]
    rw [hfun]
    exact hsum.fderiv
  rw [hfermi]
  let b : Module.Basis (Fin 2) ℝ (Submission.Mostow.E 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
  have hb0 : b 0 = FermiTwo.axis := by
    simp [b, FermiTwo.axis, EuclideanSpace.basisFun_apply]
  have hb1 : b 1 = FermiTwo.axisPerp := by
    simp [b, FermiTwo.axisPerp, EuclideanSpace.basisFun_apply]
  have hL0 : L FermiTwo.axis = (Real.cosh (x 1) * Real.cosh (x 0)) • FermiTwo.axis := by
    simp [L, Q, ContinuousLinearMap.smulRight_apply, FermiTwo.axis, FermiTwo.axisPerp,
      PiLp.proj_apply]
  have hL1 : L FermiTwo.axisPerp =
      (Real.sinh (x 1) * Real.sinh (x 0)) • FermiTwo.axis + Real.cosh (x 1) • FermiTwo.axisPerp := by
    simp [L, Q, ContinuousLinearMap.smulRight_apply, FermiTwo.axis, FermiTwo.axisPerp,
      PiLp.proj_apply]
  have h00 : (LinearMap.toMatrix b b L) 0 0 = Real.cosh (x 1) * Real.cosh (x 0) := by
    rw [LinearMap.toMatrix_apply, hb0]
    change (b.repr (L FermiTwo.axis)) 0 = Real.cosh (x 1) * Real.cosh (x 0)
    rw [hL0]
    simp [map_smul, ← hb0]
  have h01 : (LinearMap.toMatrix b b L) 0 1 = Real.sinh (x 1) * Real.sinh (x 0) := by
    rw [LinearMap.toMatrix_apply, hb1]
    change (b.repr (L FermiTwo.axisPerp)) 0 = Real.sinh (x 1) * Real.sinh (x 0)
    rw [hL1]
    simp [map_smul, map_add, ← hb0, ← hb1]
  have h10 : (LinearMap.toMatrix b b L) 1 0 = 0 := by
    rw [LinearMap.toMatrix_apply, hb0]
    change (b.repr (L FermiTwo.axis)) 1 = 0
    rw [hL0]
    simp [map_smul, ← hb0]
  have h11 : (LinearMap.toMatrix b b L) 1 1 = Real.cosh (x 1) := by
    rw [LinearMap.toMatrix_apply, hb1]
    change (b.repr (L FermiTwo.axisPerp)) 1 = Real.cosh (x 1)
    rw [hL1]
    simp [map_smul, map_add, ← hb0, ← hb1]
  have hmat : LinearMap.toMatrix b b L
      = !![Real.cosh (x 1) * Real.cosh (x 0), Real.sinh (x 1) * Real.sinh (x 0);
           0, Real.cosh (x 1)] := by
    ext i j
    fin_cases i <;> fin_cases j
    · exact h00
    · exact h01
    · exact h10
    · exact h11
  change LinearMap.det (L : Submission.Mostow.E 2 →ₗ[ℝ] Submission.Mostow.E 2)
      = Real.cosh (x 1) ^ 2 * Real.cosh (x 0)
  rw [← LinearMap.det_toMatrix b (L : Submission.Mostow.E 2 →ₗ[ℝ] Submission.Mostow.E 2),
    hmat, Matrix.det_fin_two_of]
  ring

end Work.Mostow
