import Mathlib
import Submission.Work.WilC4.Defs

open Classical
open WilkiesDesign WilkiesDesign.CG
namespace Work.WilC4

/-- If `x` and `y` have the same value and `y ≠ 0`, then `x / y` is a unit
(`ν (x/y) = 0`). -/
lemma isUnitVal_div_of_valEq {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {x y : M} (hy : y ≠ 0) (h : ValEq x y) : IsUnitVal (x / y) := by
  obtain ⟨N, hN, h1, h2⟩ := h
  have hN' : (0 : M) < (N : M) := by exact_mod_cast hN
  have hyabs : 0 < |y| := abs_pos.mpr hy
  refine ⟨N, ?_, ?_⟩
  · rw [abs_div, le_div_iff₀ hyabs]
    calc ((N : M) + 1)⁻¹ * |y| ≤ (N : M)⁻¹ * |y| := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hyabs)
          rw [inv_le_inv₀ (by positivity) hN']
          exact le_add_of_nonneg_right zero_le_one
      _ ≤ |x| := h1
  · rw [abs_div, div_le_iff₀ hyabs]
    calc |x| ≤ (N : M) * |y| := h2
      _ ≤ ((N : M) + 1) * |y| := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hyabs)
          exact le_add_of_nonneg_right zero_le_one

theorem valSpans_self_zero {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] {T : Set M} (hT : IsValBase T) : ValSpans T T 0 := by
  refine ⟨Fin.elim0, ?_⟩
  intro y hy hY
  obtain ⟨c', hc'T, hc'ne, hEq⟩ := hY
  refine ⟨1, one_ne_zero, (fun i : Fin 0 => 0), c'⁻¹, hT.2.1 c' hc'T hc'ne, inv_ne_zero hc'ne, ?_⟩
  have : c'⁻¹ * y ^ 1 / zmono (fun i : Fin 0 => i.elim0) (fun i : Fin 0 => 0) = y / c' := by
    simp [zmono, div_eq_mul_inv, mul_comm]
  rw [this]
  exact isUnitVal_div_of_valEq hc'ne hEq

end Work.WilC4
