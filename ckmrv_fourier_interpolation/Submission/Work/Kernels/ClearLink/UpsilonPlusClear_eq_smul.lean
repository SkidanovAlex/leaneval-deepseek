import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic

namespace Work.Kernels.ClearLink

open Work.Kernels Matrix

set_option maxHeartbeats 1000000

/-! ## Auxiliary lemmas for `UpsilonPlusClear_eq_smul`

The cleared matrix `Υ_+^{clear}` is obtained from `Υ_+` by
* replacing `Π_{k₁,k₂,k₃}(τ)` by `Δ(τ)·Π_{k₁,k₂,k₃}(τ)` (`PiMatDelta_eq_smul`),
* multiplying the numerator matrix `M` of Section 4.4 by `(j(τ) - j(z))`
  (`N24_eq_smul` for `d = 24`; for `d = 8` the numerator matrix already contains
  the factor `j(τ) - j(z)`),
* multiplying `Π_{k₁,k₂,k₃}(z)` by the appropriate power of `Δ(z)`.

The two scalar identities record how the *coefficients* of the resulting multiples match. -/

/-- `Π_{k₁,k₂,k₃}` with an extra factor `Δ(τ)` on each diagonal entry. -/
private lemma PiMatDelta_eq_smul (v : Fin 3 → ℤ) (τ : UpperHalfPlane) :
    PiMatDelta v τ = DeltaFun τ • PiMat v τ := by
  ext i j
  simp only [PiMatDelta, PiMat, Matrix.diagonal, Matrix.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/-- The scalar identity for `d = 8`. -/
private lemma scalar8 (c Dt Dz J : ℂ) (hc : c ≠ 0) (hDz : Dz ≠ 0) (hJ : J ≠ 0) :
    c⁻¹ * Dt = Dt * Dz * J * (c * Dz * J)⁻¹ := by
  field_simp

/-- The scalar identity for `d = 24`. -/
private lemma scalar24 (c Dt Dz J : ℂ) (hc : c ≠ 0) (hDz : Dz ≠ 0) (hJ : J ≠ 0) :
    c⁻¹ * Dt * Dz * J = Dt * Dz ^ 2 * J * (c * Dz)⁻¹ := by
  field_simp

/-- The numerator matrix of `Υ_+^{(24)}` multiplied by `j(τ) - j(z)` agrees with
`(j(τ) - j(z))` times the numerator matrix (using `J · J⁻¹ = 1`). -/
private lemma N24_eq_smul (jτ J : ℂ) (hJ : J ≠ 0) :
    (!![6 * J, 0, c1728 - 6 * J;
        -12 * jτ * J + 5 * c1728 * J, -2 * c1728, 12 * jτ * J - 7 * c1728 * J;
        c1728 + 6 * J, 0, -6 * J] : Matrix (Fin 3) (Fin 3) ℂ)
      = J • (!![6, 0, c1728 * J⁻¹ - 6;
              -12 * jτ + 5 * c1728, -2 * c1728 * J⁻¹, 12 * jτ - 7 * c1728;
              c1728 * J⁻¹ + 6, 0, -6] : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.smul_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
      smul_eq_mul] <;>
    simp [Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    try field_simp

/-- Off the diagonal `j(τ) = j(z)` the cleared matrix `Υ_+^{clear}` is the growth prefactor
`Δ(τ)Δ(z)^{e}(j(τ)-j(z))` times the matrix `Υ_+`. -/
theorem UpsilonPlusClear_eq_smul (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : UpperHalfPlane)
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.UpsilonPlusClear d τ z
      = Work.Kernels.growthPrefactor d τ z • Work.Kernels.UpsilonPlus d τ z := by
  have hJ : jInvariantFun τ - jInvariantFun z ≠ 0 := sub_ne_zero.mpr h
  have hΔz : DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  rcases hd with rfl | rfl
  · -- `d = 8`
    have hc : (36 : ℂ) * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I ≠ 0 := by
      simp [Complex.I_ne_zero]
    simp only [UpsilonPlusClear, UpsilonPlus, growthPrefactor, if_true, pow_one]
    rw [PiMatDelta_eq_smul]
    rw [Matrix.smul_mul, Matrix.smul_mul, smul_smul, smul_smul]
    congr 1
    exact scalar8 _ _ _ _ hc hΔz hJ
  · -- `d = 24`
    have hc : (36 : ℂ) * c1728 * (Real.pi : ℂ) ^ (-2 : ℤ) * Complex.I ≠ 0 := by
      simp [Complex.I_ne_zero, c1728]
    simp only [UpsilonPlusClear, UpsilonPlus, growthPrefactor, if_true, if_false,
      show (24 : ℕ) ≠ 8 by norm_num]
    rw [PiMatDelta_eq_smul]
    rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul]
    rw [N24_eq_smul _ _ hJ]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    rw [smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    exact scalar24 _ _ _ _ hc hΔz hJ

end Work.Kernels.ClearLink
