import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic
import Submission.Work.Kernels.KernelFacts.fk_slash
import Submission.Work.Kernels.TildeFacts.E6Fun_eq_theta
import Submission.Work.Kernels.TildeFacts.theta_quartic
import Submission.Work.Kernels.KernelFacts.psi2_T2
import Submission.Work.Kernels.KernelFacts.psi4_T2
import Submission.Work.Modular.thetaSeries_E8_eq_E4
import Submission.Work.Modular.thetaSeries_E8_decomposition

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle
open Work.Kernels

namespace Work.Residues

/-!
# The cleared kernel `K_-` on the diagonal

The main lemma of this file, `Work.Residues.KMinusClear_diag`, is the statement that the
cleared kernel `K_-` vanishes when `τ = z`.  In terms of the explicit formula for `K_-`
(CKMRV Section 4.4) this unfolds to the two theta identities

  `ξ₂(z)·A₁(z) + ξ₄(z)·A₂(z) = 3456·Δ(z)`   and   `(ξ₂|₂S)(z)·A₁(z) + (ξ₄|₄S)(z)·A₂(z) = 0`,

with `A₁ = E₄²W − E₆(U²−V²)`, `A₂ = −E₆W + E₄(U²−V²)`, `U = θ₀₀⁴`, `W = θ₀₁⁴`, `V = θ₁₀⁴`,
`ξ₂ = U + W`, `ξ₄ = U² + W² − 2V²`.

Everything is reduced to the classical identities `2E₄ = U²+V²+W²`, `E₆ = (W−V)(V²+W²+5VW/2)`,
`θ₀₀⁴ = θ₀₁⁴ + θ₁₀⁴` and `1728Δ = E₄³−E₆²` together with pure ring algebra.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-! ## Classical theta/Eisenstein relations used in the reduction -/

/-- `E₄` in terms of the theta quartics. -/
lemma kmc_E4Fun_eq (z : UpperHalfPlane) :
    Work.Kernels.E4Fun z =
      (Work.Kernels.UFun z ^ 2 + Work.Kernels.VFun z ^ 2 + Work.Kernels.WFun z ^ 2) / 2 := by
  have h := congrFun Work.Modular.thetaSeries_E8_eq_E4 z
  rw [Work.Modular.thetaSeries_E8_decomposition z] at h
  rw [show Work.Kernels.E4Fun z = Work.Modular.E4 z from rfl, ← h]
  simp only [Work.Modular.theta3, Work.Modular.theta4, Work.Modular.theta2,
    Work.Kernels.theta00Fun, Work.Kernels.theta01Fun, Work.Kernels.theta10Fun,
    Work.Kernels.UFun, Work.Kernels.VFun, Work.Kernels.WFun]
  ring

/-- `1728Δ = E₄³ − E₆²` in terms of the functions of `Work.Kernels`. -/
lemma kmc_DeltaFun_eq (z : UpperHalfPlane) :
    Work.Kernels.DeltaFun z =
      (Work.Kernels.E4Fun z ^ 3 - Work.Kernels.E6Fun z ^ 2) / 1728 := by
  rw [Work.Kernels.DeltaFun, CuspForm.coe_discriminant]
  exact ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z

/-- `Δ · (c/Δ) = c`. -/
lemma kmc_Delta_mul_div (z : UpperHalfPlane) (c : ℂ) :
    Work.Kernels.DeltaFun z * (c / Work.Kernels.DeltaFun z) = c := by
  rw [mul_comm]; exact div_mul_cancel₀ c (Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z)

/-- `Δ · j = E₄³`, multiplied by an arbitrary factor on the left. -/
lemma kmc_Delta_mul_j (z : UpperHalfPlane) (c : ℂ) :
    Work.Kernels.DeltaFun z * c * Work.Kernels.jInvariantFun z =
      c * Work.Kernels.E4Fun z ^ 3 := by
  rw [mul_comm (Work.Kernels.DeltaFun z) c, mul_assoc,
    Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun z]

/-- `Δ · c · (1728 − j) = −c·E₆²`. -/
lemma kmc_Delta_mul_sub_j (z : UpperHalfPlane) (c : ℂ) :
    Work.Kernels.DeltaFun z * c * ((1728 : ℂ) - Work.Kernels.jInvariantFun z) =
      - (c * Work.Kernels.E6Fun z ^ 2) := by
  have hD := kmc_DeltaFun_eq z
  have hj := Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun z
  rw [mul_comm (Work.Kernels.DeltaFun z) c, mul_assoc, mul_sub, hj, hD]
  ring

/-- `Δ · j = E₄³` (the `c = 1` case, in the shape produced by the `d = 8` matrix). -/
lemma kmc_Delta_mul_j0 (z : UpperHalfPlane) :
    Work.Kernels.DeltaFun z * Work.Kernels.jInvariantFun z = Work.Kernels.E4Fun z ^ 3 :=
  Work.Kernels.ClassicalFacts.DeltaFun_mul_jInvariantFun z

/-- `Δ · (1728 − j) = −E₆²` (the `c = 1` case). -/
lemma kmc_Delta_mul_sub_j0 (z : UpperHalfPlane) :
    Work.Kernels.DeltaFun z * ((1728 : ℂ) - Work.Kernels.jInvariantFun z) =
      - Work.Kernels.E6Fun z ^ 2 := by
  have h := kmc_Delta_mul_sub_j z 1
  simpa using h

/-! ## The two cases of the diagonal value -/

/-- Unfolding `K_-^{(8)}` on the diagonal and reducing with the classical theta relations. -/
lemma KMinusClear_8_diag (ℓ : Work.Kernels.LogLambdaData) (z : UpperHalfPlane) :
    Work.Kernels.KMinusClear ℓ 8 z z = 0 := by
  have h4 := kmc_E4Fun_eq z
  have h6 := Work.Kernels.TildeFacts.E6Fun_eq_theta z
  have hD := kmc_DeltaFun_eq z
  have hq := Work.Kernels.TildeFacts.theta_quartic z
  have h248 : ¬((24 : ℕ) = 8) := by decide
  have h824 : ¬((8 : ℕ) = 24) := by decide
  simp only [KMinusClear, UpsilonMinusClear, PiMatDelta, PiMat, Fin.sum_univ_three,
    Fin.isValue, reduceIte, Fin.reduceEq,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const, Matrix.of_apply,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    psiVec, psitVec, Pi.one_apply, Pi.div_apply, Work.Kernels.c1728, h248, h824,
    Work.Kernels.KernelFacts.fk_neg_two, Work.Kernels.KernelFacts.fk_zero,
    Work.Kernels.KernelFacts.fk_two, Work.Kernels.KernelFacts.fk_four,
    Work.Kernels.KernelFacts.fk_six, Work.Kernels.KernelFacts.fk_eight,
    Work.Kernels.KernelFacts.fk_ten, Work.Kernels.KernelFacts.fk_twelve,
    Work.Kernels.KernelFacts.fk_fourteen]
  rw [Work.Kernels.psi2, Work.Kernels.psi4]
  rw [Work.Kernels.KernelFacts.xi2Fun_slash_S z, Work.Kernels.KernelFacts.xi4S_apply z]
  rw [show xi2Fun z = UFun z + WFun z from rfl,
      show xi4Fun z = UFun z ^ 2 + WFun z ^ 2 - 2 * VFun z ^ 2 from rfl]
  rw [show E8Fun z = E4Fun z ^ 2 from rfl, show E10Fun z = E4Fun z * E6Fun z from rfl,
      show E14Fun z = E4Fun z ^ 2 * E6Fun z from rfl]
  simp only [mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add, sub_self, sub_zero,
    neg_zero]
  simp only [kmc_Delta_mul_div, kmc_Delta_mul_j0, kmc_Delta_mul_j,
    kmc_Delta_mul_sub_j0, kmc_Delta_mul_sub_j]
  rw [hD, h6, h4, hq]
  field_simp
  ring

/-- Unfolding `K_-^{(24)}` on the diagonal and reducing with the classical theta relations. -/
lemma KMinusClear_24_diag (ℓ : Work.Kernels.LogLambdaData) (z : UpperHalfPlane) :
    Work.Kernels.KMinusClear ℓ 24 z z = 0 := by
  have h4 := kmc_E4Fun_eq z
  have h6 := Work.Kernels.TildeFacts.E6Fun_eq_theta z
  have hD := kmc_DeltaFun_eq z
  have hq := Work.Kernels.TildeFacts.theta_quartic z
  have h248 : ¬((24 : ℕ) = 8) := by decide
  have h824 : ¬((8 : ℕ) = 24) := by decide
  simp only [KMinusClear, UpsilonMinusClear, PiMatDelta, PiMat, Fin.sum_univ_three,
    Fin.isValue, reduceIte, Fin.reduceEq,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.diagonal_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Matrix.head_fin_const, Matrix.of_apply,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one,
    psiVec, psitVec, Pi.one_apply, Pi.div_apply, Work.Kernels.c1728, h248, h824,
    Work.Kernels.KernelFacts.fk_neg_two, Work.Kernels.KernelFacts.fk_zero,
    Work.Kernels.KernelFacts.fk_two, Work.Kernels.KernelFacts.fk_four,
    Work.Kernels.KernelFacts.fk_six, Work.Kernels.KernelFacts.fk_eight,
    Work.Kernels.KernelFacts.fk_ten, Work.Kernels.KernelFacts.fk_twelve,
    Work.Kernels.KernelFacts.fk_fourteen]
  rw [Work.Kernels.psi2, Work.Kernels.psi4]
  rw [Work.Kernels.KernelFacts.xi2Fun_slash_S z, Work.Kernels.KernelFacts.xi4S_apply z]
  rw [show xi2Fun z = UFun z + WFun z from rfl,
      show xi4Fun z = UFun z ^ 2 + WFun z ^ 2 - 2 * VFun z ^ 2 from rfl]
  rw [show E8Fun z = E4Fun z ^ 2 from rfl, show E10Fun z = E4Fun z * E6Fun z from rfl,
      show E14Fun z = E4Fun z ^ 2 * E6Fun z from rfl]
  simp only [mul_one, mul_zero, one_mul, zero_mul, add_zero, zero_add, sub_self, sub_zero,
    neg_zero]
  simp only [kmc_Delta_mul_div, kmc_Delta_mul_j0, kmc_Delta_mul_j,
    kmc_Delta_mul_sub_j0, kmc_Delta_mul_sub_j]
  rw [hD, h6, h4, hq]
  field_simp
  ring

/-- **The cleared kernel `K_-` vanishes on the diagonal `τ = z`** (the residue of `K_-` at
`τ = z` is `−(1/2π)φ_-(1) = 0`).  Unfolding the explicit formula this is the theta identity
`(ξ₂|₂S)(z)·A₁(z) + (ξ₄|₄S)(z)·A₂(z) = 0` with `A₁ = E₄²W − E₆(U²−V²)`,
`A₂ = −E₆W + E₄(U²−V²)`, together with `(ξ₂A₁ + ξ₄A₂)(z) = 3456Δ(z)`. -/
theorem KMinusClear_diag (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (z : UpperHalfPlane) : Work.Kernels.KMinusClear ℓ d z z = 0 := by
  rcases hd with rfl | rfl
  · exact KMinusClear_8_diag ℓ z
  · exact KMinusClear_24_diag ℓ z

end Work.Residues
