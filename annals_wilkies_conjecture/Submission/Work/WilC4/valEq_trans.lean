import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

/-- `ValEq` is transitive: "same Archimedean class" is an equivalence relation on the
`ValEq`-classes of a strictly ordered field. -/
theorem valEq_trans {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] {x y z : M} (h1 : ValEq x y) (h2 : ValEq y z) : ValEq x z := by
  obtain ⟨N1, hN1, h1a, h1b⟩ := h1
  obtain ⟨N2, hN2, h2a, h2b⟩ := h2
  refine ⟨N1 * N2, Nat.mul_pos hN1 hN2, ?_, ?_⟩
  · have hN1n : (0 : M) ≤ (N1 : M) := Nat.cast_nonneg _
    have hInv : (0 : M) ≤ (N1 : M)⁻¹ := inv_nonneg.mpr hN1n
    have h : (N1 : M)⁻¹ * ((N2 : M)⁻¹ * |z|) ≤ (N1 : M)⁻¹ * |y| :=
      mul_le_mul_of_nonneg_left h2a hInv
    rw [Nat.cast_mul, mul_inv]
    calc (N1 : M)⁻¹ * (N2 : M)⁻¹ * |z|
        = (N1 : M)⁻¹ * ((N2 : M)⁻¹ * |z|) := by ring
      _ ≤ (N1 : M)⁻¹ * |y| := h
      _ ≤ |x| := h1a
  · have hN1n : (0 : M) ≤ (N1 : M) := Nat.cast_nonneg _
    have h : (N1 : M) * |y| ≤ (N1 : M) * ((N2 : M) * |z|) :=
      mul_le_mul_of_nonneg_left h2b hN1n
    rw [Nat.cast_mul]
    calc |x| ≤ (N1 : M) * |y| := h1b
      _ ≤ (N1 : M) * ((N2 : M) * |z|) := h
      _ = (N1 : M) * (N2 : M) * |z| := by ring

end Work.WilC4
