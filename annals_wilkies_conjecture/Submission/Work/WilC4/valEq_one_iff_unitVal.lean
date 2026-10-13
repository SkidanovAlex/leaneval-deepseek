import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

/-- The elements of the Archimedean class of `1`, i.e. those with value `0`: `ValEq 1 x` holds
exactly for the *units* `IsUnitVal x` (frozen notion: `(N+1)⁻¹ ≤ |x| ≤ N+1`). -/
theorem valEq_one_iff_unitVal {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] {x : M} : ValEq 1 x ↔ WilkiesDesign.CG.IsUnitVal x := by
  simp only [ValEq, WilkiesDesign.CG.IsUnitVal]
  constructor
  · rintro ⟨N, hN, hlow, hhigh⟩
    rw [abs_one] at hlow hhigh
    refine ⟨N, ?_, ?_⟩
    · rw [inv_le_iff_one_le_mul₀ (by positivity)]
      nlinarith [abs_nonneg x, hhigh]
    · have hNpos : (0 : M) < (N : M) := Nat.cast_pos.mpr hN
      have h := mul_le_mul_of_nonneg_left hlow (le_of_lt hNpos)
      rw [mul_one, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hNpos), one_mul] at h
      linarith
  · rintro ⟨N, hlow, hhigh⟩
    refine ⟨N + 1, Nat.succ_pos N, ?_, ?_⟩
    · rw [abs_one, Nat.cast_add, Nat.cast_one]
      have hc : (0 : M) < (N : M) + 1 := by positivity
      have h : |x| / ((N : M) + 1) ≤ 1 := by
        rw [div_le_iff₀ hc]
        simpa using hhigh
      rwa [div_eq_inv_mul] at h
    · rw [abs_one, Nat.cast_add, Nat.cast_one]
      have hc : (0 : M) < (N : M) + 1 := by positivity
      have h := mul_le_mul_of_nonneg_left hlow (le_of_lt hc)
      rw [mul_inv_cancel₀ (ne_of_gt hc)] at h
      linarith [h]

end Work.WilC4
