import Mathlib
import Submission.Work.KT.Idx.PenDefs

namespace Work.Idx

/-- **Splitting the pencil integrand at the level of an arbitrary noncommutative ring.**  If
`σ a₁ = a₂ - b₂ ρ`, `σ b₁ = b₂`, `a₂ ρ = 0`, `ρ ρ = 0`, `σ σ = 1` in a complex normed algebra `R`,
then for every `z` at which the pencil `z ↦ z • a₂ + b₂` is a unit, the pencils satisfy
`z • a₁ + b₁ = σ (z • a₂ + b₂) (1 - z • ρ)`, `(1 - z • ρ)⁻¹ = 1 + z • ρ`, and consequently
`(z • a₁ + b₁)⁻¹ a₁ = (z • a₂ + b₂)⁻¹ a₂ - ρ + z • (ρ * (z • a₂ + b₂)⁻¹ a₂)`. -/
theorem pResA_split_gen {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]
    (σ ρ a₁ b₁ a₂ b₂ : R)
    (hσa : σ * a₁ = a₂ - b₂ * ρ) (hσb : σ * b₁ = b₂)
    (haρ : a₂ * ρ = 0) (hρρ : ρ * ρ = 0) (hσσ : σ * σ = 1)
    (z : ℂ) (hz : IsUnit (z • a₂ + b₂)) :
    Work.KT.Idx.pResA a₁ b₁ z
      = Work.KT.Idx.pResA a₂ b₂ z - ρ + z • (ρ * Work.KT.Idx.pResA a₂ b₂ z) := by
  -- Unfold the pencil integrand `(z • A + B)⁻¹ A` and name the two pencils.
  simp only [Work.KT.Idx.pResA, Work.KT.Idx.pRes]
  set A : R := z • a₂ + b₂ with hA
  set B : R := z • a₁ + b₁ with hB
  have hzA : IsUnit A := by rwa [hA] at hz
  have hσ_unit : IsUnit σ := isUnit_iff_exists.mpr ⟨σ, hσσ, hσσ⟩
  -- `σ B = A (1 - z ρ)`: multiply `σ a₁ = a₂ - b₂ρ`, `σ b₁ = b₂` by `z` and add; the cross
  -- term `(z • a₂)(z • ρ) = z² • (a₂ρ)` vanishes.
  have hkey : σ * B = A * (1 - z • ρ) := by
    rw [hB, hA, mul_add, mul_smul_comm, hσa, hσb, smul_sub, mul_sub, mul_one,
      add_mul, smul_mul_assoc, mul_smul_comm, mul_smul_comm, smul_smul, haρ, smul_zero,
      zero_add]
    abel
  -- Since `σ σ = 1`, the relation `σ B = A (1 - zρ)` upgrades to `B = σ (A (1 - zρ))`.
  have hB_eq : B = σ * (A * (1 - z • ρ)) := by
    calc B = 1 * B := (one_mul B).symm
      _ = (σ * σ) * B := by rw [hσσ]
      _ = σ * (σ * B) := by rw [mul_assoc]
      _ = σ * (A * (1 - z • ρ)) := by rw [hkey]
  -- `(zρ)(zρ) = z² • (ρρ) = 0`, so `(1 - zρ)(1 + zρ) = 1 = (1 + zρ)(1 - zρ)`.
  have hrr : (z • ρ) * (z • ρ) = 0 := by
    rw [smul_mul_assoc, mul_smul_comm, smul_smul, hρρ, smul_zero]
  have hρ1 : (1 - z • ρ) * (1 + z • ρ) = 1 := by
    rw [mul_add, mul_one, sub_mul, one_mul, hrr]
    abel
  have hρ2 : (1 + z • ρ) * (1 - z • ρ) = 1 := by
    rw [add_mul, one_mul, mul_sub, mul_one, hrr]
    abel
  have hunit1 : IsUnit (1 - z • ρ) := isUnit_iff_exists.mpr ⟨1 + z • ρ, hρ1, hρ2⟩
  -- `(z • a₂ + b₂)⁻¹ b₂ = 1 - z • ((z • a₂ + b₂)⁻¹ a₂)` because `b₂ = A - z • a₂`.
  have hb₂ : b₂ = A - z • a₂ := by rw [hA]; abel
  have hAinvb₂ : Ring.inverse A * b₂ = 1 - z • (Ring.inverse A * a₂) := by
    rw [hb₂, mul_sub, mul_smul_comm, Ring.inverse_mul_cancel A hzA]
  -- `(A⁻¹ a₂) ρ = A⁻¹ (a₂ ρ) = 0`.
  have hAaρ : (Ring.inverse A * a₂) * ρ = 0 := by rw [mul_assoc, haρ, mul_zero]
  have hB_unit : IsUnit B := hB_eq ▸ IsUnit.mul hσ_unit (IsUnit.mul hzA hunit1)
  -- The claimed inverse of `B`: `(1 + zρ) A⁻¹ σ`.
  set X : R := (1 + z • ρ) * Ring.inverse A * σ with hX
  have hXB : X * B = 1 := by
    rw [hX, hB_eq]
    simp only [mul_assoc]
    rw [← mul_assoc σ σ (A * (1 - z • ρ)), hσσ, one_mul,
      ← mul_assoc (Ring.inverse A) A (1 - z • ρ), Ring.inverse_mul_cancel A hzA, one_mul,
      hρ2]
  have hXeq : X = Ring.inverse B := by
    calc X = X * 1 := (mul_one X).symm
      _ = X * (B * Ring.inverse B) := by rw [Ring.mul_inverse_cancel B hB_unit]
      _ = (X * B) * Ring.inverse B := (mul_assoc X B (Ring.inverse B)).symm
      _ = 1 * Ring.inverse B := by rw [hXB]
      _ = Ring.inverse B := one_mul _
  -- `B⁻¹ a₁ = (1 + zρ) A⁻¹ (σ a₁) = (1 + zρ) A⁻¹ (a₂ - b₂ ρ)`.
  have hXa : X * a₁ = (1 + z • ρ) * (Ring.inverse A * (a₂ - b₂ * ρ)) := by
    rw [hX]
    simp only [mul_assoc, hσa]
  have hYa : Ring.inverse A * (a₂ - b₂ * ρ) = Ring.inverse A * a₂ - ρ := by
    rw [mul_sub, ← mul_assoc, hAinvb₂, sub_mul, one_mul, smul_mul_assoc, hAaρ, smul_zero,
      sub_zero]
  have hfin : (1 + z • ρ) * (Ring.inverse A * a₂ - ρ)
      = Ring.inverse A * a₂ - ρ + z • (ρ * (Ring.inverse A * a₂)) := by
    rw [add_mul, one_mul, smul_mul_assoc, mul_sub, smul_sub, hρρ, smul_zero, sub_zero]
  rw [← hXeq, hXa, hYa, hfin]

end Work.Idx
