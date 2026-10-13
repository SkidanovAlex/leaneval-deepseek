import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

/-- `ValEq` is symmetric: "same Archimedean class" is a symmetric relation.  The two
inequalities in the definition of `ValEq x y` simply swap roles. -/
theorem valEq_symm {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] {x y : M}
    (h : ValEq x y) : ValEq y x := by
  obtain ⟨N, hN, hle, hge⟩ := h
  have hNpos : (0 : M) < (N : M) := Nat.cast_pos.mpr hN
  have hNne : (N : M) ≠ 0 := ne_of_gt hNpos
  have hNinpos : (0 : M) ≤ (N : M) := le_of_lt hNpos
  have hNinvpos : (0 : M) ≤ (N : M)⁻¹ := inv_nonneg.mpr hNinpos
  refine ⟨N, hN, ?_, ?_⟩
  · -- `(N : M)⁻¹ * |x| ≤ |y|` : from `|x| ≤ N |y|`
    have h1 : (N : M)⁻¹ * |x| ≤ (N : M)⁻¹ * ((N : M) * |y|) :=
      mul_le_mul_of_nonneg_left hge hNinvpos
    calc (N : M)⁻¹ * |x| ≤ (N : M)⁻¹ * ((N : M) * |y|) := h1
      _ = |y| := by rw [← mul_assoc, inv_mul_cancel₀ hNne, one_mul]
  · -- `|y| ≤ N |x|` : from `(N : M)⁻¹ * |y| ≤ |x|`
    have h2 : (N : M) * ((N : M)⁻¹ * |y|) ≤ (N : M) * |x| :=
      mul_le_mul_of_nonneg_left hle hNinpos
    calc |y| = (N : M) * ((N : M)⁻¹ * |y|) := by
          rw [← mul_assoc, mul_inv_cancel₀ hNne, one_mul]
      _ ≤ (N : M) * |x| := h2

end Work.WilC4
