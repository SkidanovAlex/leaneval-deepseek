/-
# Scalar shifts of the difference operator `T - 1` in `ℂ[ℤ/2 ∗ ℤ/3]`

The odd-weight directness theorem (`Work.Asymptotics.idealI_direct_augIdealOdd`) reduces, after
transporting along an isomorphism between the odd part `Re₋` of `R = ℂ[SL(2,ℤ)]` and the free
product algebra `RR = ℂ[ℤ/2 ∗ ℤ/3]`, to a **shifted** form of CKMRV Proposition 3.1:

  `(T - ν)² * a + X * (T - ν)² * b = 0  →  a = 0 ∧ b = 0`   (`ν³ = -i`).

This file collects the notation for that statement.  The two elements that play the role of
`MU = 1 + Y + Y²` and `MUp = Y² - Y + 1` in the shifted theory are

* `MUv ν = Y² + νY + ν²`  (satisfies `(Y + ν) * MUv ν = (1 + ν³)`), used against `X - 1`,
* `MUpv ν = Y² - νY + ν²` (satisfies `(Y - ν) * MUpv ν = (1 - ν³)`), used against `X + 1`.
-/
import Mathlib
import Submission.Work.FreeProduct.Bridge
import Submission.Work.FreeProduct.IdealImDirect
import Submission.Work.FreeProduct.IdealIpDirect

set_option linter.unusedSimpArgs false

noncomputable section

namespace Work.FreeProduct

open scoped MonoidAlgebra

/-- The shifted difference operator `T - ν` in `RR = ℂ[ℤ/2 ∗ ℤ/3]`. -/
def Tnu (ν : ℂ) : RR := TT - ν • 1

/-- `Y² - νY + ν²`; it satisfies `(Y - ν) * MUpv ν = (1 - ν³) • 1`. -/
def MUpv (ν : ℂ) : RR := Y2 - ν • Y + (ν ^ 2) • 1

/-- `Y² + νY + ν²`; it satisfies `(Y + ν) * MUv ν = (1 + ν³) • 1`. -/
def MUv (ν : ℂ) : RR := Y2 + ν • Y + (ν ^ 2) • 1

@[simp] lemma Tnu_apply (ν : ℂ) : Tnu ν = TT - ν • 1 := rfl
@[simp] lemma MUpv_apply (ν : ℂ) : MUpv ν = Y2 - ν • Y + (ν ^ 2) • 1 := rfl
@[simp] lemma MUv_apply (ν : ℂ) : MUv ν = Y2 + ν • Y + (ν ^ 2) • 1 := rfl

/-- `X * (X * Y) = Y`. -/
lemma X_mul_X_mul_Y : (X * (X * Y) : RR) = Y := by
  rw [← mul_assoc, X_mul_X, one_mul]

/-- `X * TT = Y`. -/
lemma X_mul_TT : (X * TT : RR) = Y := by
  rw [← X_mul_Y, X_mul_X_mul_Y]

/-- `TT = X * Y`. -/
lemma TT_eq : (TT : RR) = X * Y := X_mul_Y.symm

/-- `Y * Y * Y = 1`. -/
lemma Y_cube : (Y * (Y * Y) : RR) = 1 := by
  rw [← mul_assoc, Y_mul_Y, Y2_mul_Y]

lemma one_add_mul_Tnu (ν : ℂ) : ((1 + X) * Tnu ν : RR) = (X + 1) * (Y - ν • 1) := by
  have h := X_mul_X_mul_Y
  simp only [Tnu_apply, TT_eq, mul_sub, mul_add, add_mul, one_mul, mul_one, h,
    Algebra.mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
  noncomm_ring

lemma one_sub_mul_Tnu (ν : ℂ) : ((1 - X) * Tnu ν : RR) = (X - 1) * (Y + ν • 1) := by
  have h := X_mul_X_mul_Y
  simp only [Tnu_apply, TT_eq, mul_sub, sub_mul, mul_add, add_mul, one_mul, mul_one, h,
    Algebra.mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
  noncomm_ring

lemma Y_add_mul_MUpv (ν : ℂ) : ((Y + ν • 1) * MUpv ν : RR) = (1 + ν ^ 3) • 1 := by
  simp only [MUpv_apply, mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, Y_mul_Y, Y_mul_Y2, Y2_mul_Y,
    Algebra.mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
  module

lemma Y_sub_mul_MUv (ν : ℂ) : ((Y - ν • 1) * MUv ν : RR) = (1 - ν ^ 3) • 1 := by
  simp only [MUv_apply, mul_add, add_mul, mul_sub, sub_mul, one_mul, mul_one, Y_mul_Y2, Y_mul_Y, Y2_mul_Y,
    Algebra.mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_add, smul_sub, smul_smul]
  module

end Work.FreeProduct
