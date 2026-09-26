import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.ClassicalFacts.DeltaFun_basic

namespace Work.Kernels.ClearLink

/-- `Π^Δ_{k₁,k₂,k₃} = Δ · Π_{k₁,k₂,k₃}`: the `Δ`-twisted diagonal matrix is the scalar
multiple `Δ(τ) • Π(τ)` of the plain diagonal matrix. -/
lemma PiMatDelta_eq_smul (v : Fin 3 → ℤ) (τ : UpperHalfPlane) :
    Work.Kernels.PiMatDelta v τ = Work.Kernels.DeltaFun τ • Work.Kernels.PiMat v τ := by
  ext i j
  by_cases hij : i = j
  · subst hij; simp [Work.Kernels.PiMatDelta, Work.Kernels.PiMat]
  · simp [Work.Kernels.PiMatDelta, Work.Kernels.PiMat, hij]

/-- The elementary scalar identity behind the `d = 8` case:
`a⁻¹ c = c · b · d · (a b d)⁻¹` for `a, b, d ≠ 0`. -/
lemma upsi_scalar_8 {K : Type*} [Field K] (a b c d : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hd : d ≠ 0) : a⁻¹ * c = c * b * d * (a * b * d)⁻¹ := by
  rw [mul_inv, mul_inv]
  field_simp

/-- The elementary scalar identity behind the `d = 24` case:
`a⁻¹ (b c) = c · b² · d · (a b d)⁻¹` for `a, b, d ≠ 0`. -/
lemma upsi_scalar_24 {K : Type*} [Field K] (a b c d : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hd : d ≠ 0) : a⁻¹ * (b * c) = c * b ^ 2 * d * (a * b * d)⁻¹ := by
  rw [mul_inv, mul_inv]
  field_simp

theorem UpsilonMinusClear_eq_smul (d : ℕ) (hd : d = 8 ∨ d = 24) (τ z : UpperHalfPlane)
    (h : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z) :
    Work.Kernels.UpsilonMinusClear d τ z
      = Work.Kernels.growthPrefactor d τ z • Work.Kernels.UpsilonMinus d τ z := by
  have hΔz : Work.Kernels.DeltaFun z ≠ 0 := Work.Kernels.ClassicalFacts.DeltaFun_ne_zero z
  have hJ : Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z ≠ 0 :=
    sub_ne_zero.mpr h
  have ha : (2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne_zero ?_) ?_
    · norm_num [Work.Kernels.c1728]
    · exact_mod_cast Real.pi_ne_zero
  rcases hd with rfl | rfl
  · -- `d = 8`
    simp only [Work.Kernels.UpsilonMinusClear, Work.Kernels.UpsilonMinus,
      Work.Kernels.growthPrefactor, if_true, pow_one]
    simp only [PiMatDelta_eq_smul, Matrix.smul_mul, smul_smul]
    rw [upsi_scalar_8 ((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))
      (Work.Kernels.DeltaFun z) (Work.Kernels.DeltaFun τ)
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ha hΔz hJ]
  · -- `d = 24`
    have h248 : ¬ ((24 : ℕ) = 8) := by decide
    simp only [Work.Kernels.UpsilonMinusClear, Work.Kernels.UpsilonMinus,
      Work.Kernels.growthPrefactor, h248, if_true, if_false]
    simp only [PiMatDelta_eq_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [upsi_scalar_24 ((2 : ℂ) * Work.Kernels.c1728 * (Real.pi : ℂ))
      (Work.Kernels.DeltaFun z) (Work.Kernels.DeltaFun τ)
      (Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z) ha hΔz hJ]

end Work.Kernels.ClearLink
