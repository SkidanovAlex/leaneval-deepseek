import Mathlib
import Submission.Work.WilC4.Defs

namespace Work.WilC4

/-- Dividing by a nonzero element turns comparability into being a unit: `ValEq x y` holds
exactly when the quotient `x / y` lies in the Archimedean class of `1` (`IsUnitVal`).  The
witness bounds agree, since `|x / y| * |y| = |x|` and `|y| > 0` lets one multiply inequalities
by `|y|` or divide by it at will. -/
theorem valEq_iff_unitVal_div {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] {x y : M} (hy : y ≠ 0) : (ValEq x y ↔ WilkiesDesign.CG.IsUnitVal (x / y)) := by
  have hyabs : (0 : M) < |y| := abs_pos.mpr hy
  have hkey : |x / y| * |y| = |x| := by
    rw [abs_div]
    exact div_mul_cancel₀ _ (ne_of_gt hyabs)
  constructor
  · rintro ⟨N, hN, h1, h2⟩
    refine ⟨N, ?_, ?_⟩
    · have hNpos : (0 : M) < (N : M) := by exact_mod_cast hN
      have hinv : ((N : M) + 1)⁻¹ ≤ (N : M)⁻¹ := by
        rw [← one_div, ← one_div]
        exact one_div_le_one_div_of_le hNpos (le_add_of_nonneg_right zero_le_one)
      rw [abs_div, le_div_iff₀ hyabs]
      calc ((N : M) + 1)⁻¹ * |y| ≤ (N : M)⁻¹ * |y| :=
            mul_le_mul_of_nonneg_right hinv (le_of_lt hyabs)
        _ ≤ |x| := h1
    · rw [abs_div, div_le_iff₀ hyabs]
      calc |x| ≤ (N : M) * |y| := h2
        _ ≤ ((N : M) + 1) * |y| :=
            mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (le_of_lt hyabs)
  · rintro ⟨K, h1, h2⟩
    refine ⟨K + 1, Nat.succ_pos K, ?_, ?_⟩
    · have hK1 : ((K + 1 : ℕ) : M) = (K : M) + 1 := by rw [Nat.cast_add, Nat.cast_one]
      rw [hK1]
      have := mul_le_mul_of_nonneg_right h1 (le_of_lt hyabs)
      rw [hkey] at this
      exact this
    · have hK1 : ((K + 1 : ℕ) : M) = (K : M) + 1 := by rw [Nat.cast_add, Nat.cast_one]
      rw [hK1]
      have := mul_le_mul_of_nonneg_right h2 (le_of_lt hyabs)
      rw [hkey] at this
      exact this

end Work.WilC4
