import Mathlib
import Submission.Work.Rigidity.LambdaDerivDefs
import Submission.Work.Rigidity.lamC_add_one
import Submission.Work.Rigidity.lamC_neg_inv
import Submission.Work.Rigidity.Basic

namespace Work.Rigidity

open Work.Kernels Work.Kernels.LogLambda
open UpperHalfPlane ModularGroup

/-- `((-I z)^{1/2})^4 = -z^2`. -/
private lemma cpow_half_pow_four_C (z : ℂ) :
    ((-Complex.I * z) ^ (1 / 2 : ℂ)) ^ 4 = - z ^ 2 := by
  rw [← Complex.cpow_nat_mul]
  norm_num
  rw [mul_pow, Complex.I_sq]
  ring

/-- The `S`-law of `θ₀₀⁴`, in the form needed for `ρ`: `θ₀₀(-1/z)⁴ = -z² θ₀₀(z)⁴`. -/
private lemma thetaC00_neg_inv_pow4 (z : ℂ) (hz : 0 < z.im) :
    (thetaC00 (-1 / z)) ^ 4 = - z ^ 2 * (thetaC00 z) ^ 4 := by
  have hzU : 0 < (-z⁻¹).im := im_neg_inv_pos hz
  have hpoint : (ModularGroup.S • (⟨z, hz⟩ : ℍ) : ℍ) = ⟨-z⁻¹, hzU⟩ := by
    apply UpperHalfPlane.ext
    rw [coe_S_smul]
  have h := theta00Fun_S (⟨z, hz⟩ : ℍ)
  rw [hpoint] at h
  have h4 : (theta00Fun (⟨-z⁻¹, hzU⟩ : ℍ)) ^ 4
      = -z ^ 2 * (theta00Fun (⟨z, hz⟩ : ℍ)) ^ 4 := by
    rw [h, mul_pow, cpow_half_pow_four_C]
  have hz' : (-1 : ℂ) / z = -z⁻¹ := by rw [neg_div, one_div]
  rw [hz', thetaC00_of_mem hzU, thetaC00_of_mem hz]
  exact h4

/-- The elementary algebra behind `ρ(-1/z) = ρ(z)`, after the transformation laws
of `λ`, `λ'` and `θ₀₀⁴` have reduced the goal to it. -/
private lemma rho_alg (d l t z : ℂ) (hz : z ≠ 0) :
    (-z ^ 2 * d) / ((1 - l) * (1 - (1 - l)) * (-z ^ 2 * t)) = d / (l * (1 - l) * t) := by
  have hz2 : -z ^ 2 ≠ 0 := neg_ne_zero.mpr (pow_ne_zero 2 hz)
  have h1 : (1 - l) * (1 - (1 - l)) * (-z ^ 2 * t) = (-z ^ 2) * (l * (1 - l) * t) := by
    ring
  rw [h1, mul_div_mul_left d (l * (1 - l) * t) hz2]

/-- `ρ` is invariant under the `S`-transformation `z ↦ -1/z` of `SL(2, ℤ)`. -/
theorem rhoC_neg_inv (z : ℂ) (hz : 0 < z.im) :
    Work.Rigidity.rhoC (-1 / z) = Work.Rigidity.rhoC z := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_im] at hz
    exact lt_irrefl 0 hz
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 hz0
  have hmem : (-1 / z) ∈ U := by
    rw [neg_div, one_div]
    exact im_neg_inv_pos hz
  -- (1) the transformation law of `λ`
  have hlam : lamC (-1 / z) = 1 - lamC z := lamC_neg_inv z hz
  -- (2) the transformation law of `θ₀₀⁴`
  have htheta : (thetaC00 (-1 / z)) ^ 4 = - z ^ 2 * (thetaC00 z) ^ 4 :=
    thetaC00_neg_inv_pow4 z hz
  -- (3) the transformation law of the derivative
  have hdlam : DifferentiableAt ℂ lamC (-1 / z) :=
    (differentiableOn_lamC (-1 / z) hmem).differentiableAt (isOpen_U.mem_nhds hmem)
  have hdf : DifferentiableAt ℂ (fun y : ℂ => (-1) / y) z :=
    (differentiableAt_const (-1)).div differentiableAt_id hz0
  have hcomp := deriv_comp (x := z) (h := fun y : ℂ => (-1) / y) (h₂ := lamC) hdlam hdf
  have heq : (fun y : ℂ => lamC ((-1) / y)) =ᶠ[nhds z] (fun y : ℂ => 1 - lamC y) := by
    rw [Filter.eventuallyEq_iff_exists_mem]
    exact ⟨U, isOpen_U.mem_nhds hz, fun y hy => lamC_neg_inv y hy⟩
  have hg : deriv (fun y : ℂ => lamC ((-1) / y)) z = - deriv lamC z := by
    rw [Filter.EventuallyEq.deriv_eq heq]
    exact deriv_const_sub 1
  have hderivf : deriv (fun y : ℂ => (-1) / y) z = (z ^ 2)⁻¹ := by
    rw [deriv_const_div (d := fun y : ℂ => y) (-1) differentiableAt_id hz0]
    rw [show deriv (fun y : ℂ => y) z = 1 from deriv_id z]
    ring
  have hkey : deriv lamC (-1 / z) * (z ^ 2)⁻¹ = - deriv lamC z := by
    rw [← hderivf]
    exact hcomp.symm.trans hg
  have hderiv : deriv lamC (-1 / z) = - z ^ 2 * deriv lamC z := by
    calc deriv lamC (-1 / z) = deriv lamC (-1 / z) * (z ^ 2)⁻¹ * z ^ 2 := by
          rw [mul_assoc, inv_mul_cancel₀ hz2, mul_one]
      _ = (- deriv lamC z) * z ^ 2 := by rw [hkey]
      _ = - z ^ 2 * deriv lamC z := by ring
  rw [rhoC, rhoC, hlam, htheta, hderiv]
  exact rho_alg (deriv lamC z) (lamC z) ((thetaC00 z) ^ 4) z hz0

end Work.Rigidity
