import Mathlib
import Submission.Work.KT.FP.PencilDefs

namespace Work.KT.FP

/-- **Product of two "resolvent-shaped" elements of an idempotent `E`.**

For an idempotent `E` and scalars `a b : ℂ`, one has
`((1 - E) + a • E) * ((1 - E) + b • E) = (1 - E) + (a * b) • E`.

Indeed `(1 - E)` and `E` are orthogonal idempotents summing to `1`, so the product of
`1 - E + aE` and `1 - E + bE` reduces to `1 - E + ab E`. -/
lemma idem_smul_mul {R : Type*} [Ring R] [Algebra ℂ R] (E : R) (hE : E * E = E) (a b : ℂ) :
    ((1 - E) + a • E) * ((1 - E) + b • E) = (1 - E) + (a * b) • E := by
  have hPP : (1 - E) * (1 - E) = 1 - E := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hE, sub_self, sub_zero]
  have hPE : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have hEP : E * (1 - E) = 0 := by rw [mul_sub, mul_one, hE, sub_self]
  have hsm : (a • E) * (b • E) = (a * b) • E := by
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul, hE]
  rw [add_mul, mul_add, mul_add, hPP, Algebra.mul_smul_comm, hPE, smul_zero,
      Algebra.smul_mul_assoc, hEP, smul_zero, hsm]
  abel

theorem pResA_idem {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (E : R) (hE : E * E = E) (z : ℂ) (hz : z ≠ 0) :
    pResA E (1 - E) z = z⁻¹ • E := by
  -- `(1 - E) * E = 0`, so the block `E` survives the multiplication by `E` at the end.
  have hPE : (1 - E) * E = 0 := by rw [sub_mul, one_mul, hE, sub_self]
  have hz1 : z * z⁻¹ = 1 := mul_inv_cancel₀ hz
  have h1z : z⁻¹ * z = 1 := inv_mul_cancel₀ hz
  -- `(1 - E) + z E` and `(1 - E) + z⁻¹ E` are mutually inverse.
  have hxy : ((1 - E) + z • E) * ((1 - E) + z⁻¹ • E) = 1 := by
    rw [idem_smul_mul E hE z z⁻¹, hz1, one_smul]; abel
  have hyx : ((1 - E) + z⁻¹ • E) * ((1 - E) + z • E) = 1 := by
    rw [idem_smul_mul E hE z⁻¹ z, h1z, one_smul]; abel
  have hunit : IsUnit ((1 - E) + z • E) := by
    rw [isUnit_iff_exists]
    exact ⟨_, hxy, hyx⟩
  -- hence `Ring.inverse` of the pencil is the explicit inverse.
  have hinv : Ring.inverse ((1 - E) + z • E) = (1 - E) + z⁻¹ • E := by
    have h := Ring.mul_inverse_cancel ((1 - E) + z • E) hunit
    calc Ring.inverse ((1 - E) + z • E)
        = (((1 - E) + z⁻¹ • E) * ((1 - E) + z • E)) * Ring.inverse ((1 - E) + z • E) := by
            rw [hyx, one_mul]
      _ = ((1 - E) + z⁻¹ • E) * (((1 - E) + z • E) * Ring.inverse ((1 - E) + z • E)) := by
            rw [mul_assoc]
      _ = (1 - E) + z⁻¹ • E := by rw [h, mul_one]
  have hpencil : z • E + (1 - E) = (1 - E) + z • E := add_comm _ _
  simp only [pResA, pRes]
  rw [hpencil, hinv, add_mul, hPE, zero_add, Algebra.smul_mul_assoc, hE]

end Work.KT.FP
