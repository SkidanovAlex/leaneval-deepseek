import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelFacts.KPlusCoeff_slash_S
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Kernels.TildeFacts.KPlus_z_tildeA

namespace Work.Kernels.TildeFacts

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle
open Work.Kernels

/-- The coefficient matrix `Υ_-^{(d)}` transforms in its second variable `z` under the
generator `S ∈ SL(2,ℤ)`: entrywise,
`Υ_-^{(d)}(τ, S•z)_{ij} = z^{2 - d/2 - 2j} · Υ_-^{(d)}(τ,z)_{ij}`.

The matrix `Υ_-^{(d)}(τ,z)` is a scalar multiple of `Π_a(τ) · M(j τ, j τ - j z) · Π_b(z)`,
where `Π_a(τ)`, `Π_b(z)` are diagonal with entries the modular forms `f_k` of weight `k`,
and the scalar is `(2·1728·π·Δ(z)·(j(τ) - j(z)))⁻¹`.  Under `z ↦ S•z` we have
`Δ(S•z) = z^12 Δ(z)`, `j(S•z) = j(z)`, and `f_k(S•z) = z^k f_k(z)`, so the scalar picks up
`z^{-12}` and the right `Π_b` picks up `z^{b_j}` with `b = (10,8,6)` for `d = 8` and
`b = (2,0,-2)` for `d = 24`; since `b_j = 14 - d/2 - 2j`, the total exponent is
`b_j - 12 = 2 - d/2 - 2j`. -/
theorem UpsilonMinus_S_z (d : ℕ) (hd : d = 8 ∨ d = 24) (τ : UpperHalfPlane) (i j : Fin 3)
    (z : UpperHalfPlane) :
    Work.Kernels.UpsilonMinus d τ (ModularGroup.S • z) i j =
      (z : ℂ) ^ (2 - (d : ℤ) / 2 - 2 * ((j : ℕ) : ℤ)) * Work.Kernels.UpsilonMinus d τ z i j := by
  have hz : (z : ℂ) ≠ 0 := KernelFacts.kpc_tau_ne_zero z
  rcases hd with rfl | rfl
  · -- `d = 8`
    have hΔ := KernelFacts.kpc_smul_S_of_slash KernelFacts.kpc_Delta_slash_S z
    have hJ := KernelFacts.kpc_jInvariant_S z
    have hPi := KernelFacts.kpc_PiMat_S (![10, 8, 6] : Fin 3 → ℤ) z
    simp only [UpsilonMinus, reduceIte]
    rw [hΔ, hJ, hPi]
    simp only [Matrix.smul_apply, smul_eq_mul]
    have hb : ((![10, 8, 6] : Fin 3 → ℤ) j : ℤ) = 10 - 2 * ((j : ℕ) : ℤ) := by
      fin_cases j <;> norm_num
    have hD : Matrix.diagonal (fun k => (z : ℂ) ^ ((![10, 8, 6] : Fin 3 → ℤ) k)) *
          PiMat ![10, 8, 6] z
        = Matrix.diagonal (fun k => (z : ℂ) ^ ((![10, 8, 6] : Fin 3 → ℤ) k) *
            fk ((![10, 8, 6] : Fin 3 → ℤ) k) z) := by
      rw [show PiMat ![10, 8, 6] z
            = Matrix.diagonal (fun k => fk ((![10, 8, 6] : Fin 3 → ℤ) k) z) from rfl]
      rw [Matrix.diagonal_mul_diagonal]
    rw [hD, PiMat_mul_diagonal_entry, PiMat_mul_PiMat_entry]
    have hC : (2 * c1728 * (Real.pi : ℂ) * ((z : ℂ) ^ (12 : ℤ) * DeltaFun z) *
          (jInvariantFun τ - jInvariantFun z))⁻¹
        = (z : ℂ) ^ (-12 : ℤ) * (2 * c1728 * (Real.pi : ℂ) * DeltaFun z *
          (jInvariantFun τ - jInvariantFun z))⁻¹ := by
      rw [show (2 * c1728 * (Real.pi : ℂ) * ((z : ℂ) ^ (12 : ℤ) * DeltaFun z) *
            (jInvariantFun τ - jInvariantFun z))
          = (2 * c1728 * (Real.pi : ℂ) * DeltaFun z *
            (jInvariantFun τ - jInvariantFun z)) * (z : ℂ) ^ (12 : ℤ) from by ring]
      rw [show (z : ℂ) ^ (-12 : ℤ) = ((z : ℂ) ^ (12 : ℤ))⁻¹ from by rw [_root_.zpow_neg]]
      rw [_root_.mul_inv_rev]
    rw [hC]
    have hzpow : (z : ℂ) ^ (-12 : ℤ) * (z : ℂ) ^ ((![10, 8, 6] : Fin 3 → ℤ) j)
        = (z : ℂ) ^ (2 - ((8 : ℕ) : ℤ) / 2 - 2 * ((j : ℕ) : ℤ)) := by
      rw [← zpow_add₀ hz]; congr 1; rw [hb]; ring
    rw [← hzpow]
    ring
  · -- `d = 24`
    have hΔ := KernelFacts.kpc_smul_S_of_slash KernelFacts.kpc_Delta_slash_S z
    have hJ := KernelFacts.kpc_jInvariant_S z
    have hPi := KernelFacts.kpc_PiMat_S (![2, 0, -2] : Fin 3 → ℤ) z
    simp only [UpsilonMinus, reduceIte, if_neg (show ¬((24 : ℕ) = 8) by decide)]
    rw [hΔ]
    simp only [hJ]
    rw [hPi]
    simp only [Matrix.smul_apply, smul_eq_mul]
    have hb : ((![2, 0, -2] : Fin 3 → ℤ) j : ℤ) = 2 - 2 * ((j : ℕ) : ℤ) := by
      fin_cases j <;> norm_num
    have hD : Matrix.diagonal (fun k => (z : ℂ) ^ ((![2, 0, -2] : Fin 3 → ℤ) k)) *
          PiMat ![2, 0, -2] z
        = Matrix.diagonal (fun k => (z : ℂ) ^ ((![2, 0, -2] : Fin 3 → ℤ) k) *
            fk ((![2, 0, -2] : Fin 3 → ℤ) k) z) := by
      rw [show PiMat ![2, 0, -2] z
            = Matrix.diagonal (fun k => fk ((![2, 0, -2] : Fin 3 → ℤ) k) z) from rfl]
      rw [Matrix.diagonal_mul_diagonal]
    rw [hD, PiMat_mul_diagonal_entry, PiMat_mul_PiMat_entry]
    have hC : (2 * c1728 * (Real.pi : ℂ) * ((z : ℂ) ^ (12 : ℤ) * DeltaFun z) *
          (jInvariantFun τ - jInvariantFun z))⁻¹
        = (z : ℂ) ^ (-12 : ℤ) * (2 * c1728 * (Real.pi : ℂ) * DeltaFun z *
          (jInvariantFun τ - jInvariantFun z))⁻¹ := by
      rw [show (2 * c1728 * (Real.pi : ℂ) * ((z : ℂ) ^ (12 : ℤ) * DeltaFun z) *
            (jInvariantFun τ - jInvariantFun z))
          = (2 * c1728 * (Real.pi : ℂ) * DeltaFun z *
            (jInvariantFun τ - jInvariantFun z)) * (z : ℂ) ^ (12 : ℤ) from by ring]
      rw [show (z : ℂ) ^ (-12 : ℤ) = ((z : ℂ) ^ (12 : ℤ))⁻¹ from by rw [_root_.zpow_neg]]
      rw [_root_.mul_inv_rev]
    rw [hC]
    have hzpow : (z : ℂ) ^ (-12 : ℤ) * (z : ℂ) ^ ((![2, 0, -2] : Fin 3 → ℤ) j)
        = (z : ℂ) ^ (2 - ((24 : ℕ) : ℤ) / 2 - 2 * ((j : ℕ) : ℤ)) := by
      rw [← zpow_add₀ hz]; congr 1; rw [hb]; ring
    rw [← hzpow]
    ring

end Work.Kernels.TildeFacts
