import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

/-- `ValEq` is multiplicative: the product of two elements of the same Archimedean class stays in
the same Archimedean class.  The witnesses multiply. -/
theorem valEq_mul {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] {x x' y y' : M}
    (h1 : ValEq x x') (h2 : ValEq y y') : ValEq (x * y) (x' * y') := by
  obtain ⟨N1, hN1, h1a, h1b⟩ := h1
  obtain ⟨N2, hN2, h2a, h2b⟩ := h2
  refine ⟨N1 * N2, Nat.mul_pos hN1 hN2, ?_, ?_⟩
  · rw [abs_mul, abs_mul, Nat.cast_mul, mul_inv]
    have hpos2 : (0 : M) ≤ (N2 : M)⁻¹ * |y'| :=
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (abs_nonneg y')
    calc (N1 : M)⁻¹ * (N2 : M)⁻¹ * (|x'| * |y'|)
        = ((N1 : M)⁻¹ * |x'|) * ((N2 : M)⁻¹ * |y'|) := by ring
      _ ≤ |x| * |y| := mul_le_mul h1a h2a hpos2 (abs_nonneg x)
  · rw [abs_mul, abs_mul, Nat.cast_mul]
    have hpos2 : (0 : M) ≤ (N1 : M) * |x'| :=
      mul_nonneg (Nat.cast_nonneg _) (abs_nonneg x')
    calc |x| * |y| ≤ ((N1 : M) * |x'|) * ((N2 : M) * |y'|) :=
          mul_le_mul h1b h2b (abs_nonneg y) hpos2
      _ = (N1 : M) * (N2 : M) * (|x'| * |y'|) := by ring

end Work.WilC4
