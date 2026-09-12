import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.CrossProduct

namespace Commons.LinearAlgebra.CrossProduct

open Matrix

/-- If `U, V` are orthonormal in `ℝ³` and `D` is orthogonal to `U ⨯₃ V`, then `D`
lies in the span of `U` and `V`, with the expected coefficients. -/
theorem cross_dot_eq_zero_mem_span {U V D : Fin 3 → ℝ}
    (hU : U ⬝ᵥ U = 1) (hV : V ⬝ᵥ V = 1) (hUV : U ⬝ᵥ V = 0)
    (h : D ⬝ᵥ (U ⨯₃ V) = 0) :
    D = (D ⬝ᵥ U) • U + (D ⬝ᵥ V) • V := by
  set W := U ⨯₃ V with hW
  have hDW : D ⬝ᵥ W = 0 := by rw [hW]; exact h
  have hWW : W ⬝ᵥ W = 1 := by
    rw [hW, cross_dot_cross, hU, hV, dotProduct_comm V U, hUV]
    ring
  have hWU : W ⨯₃ U = V := by
    rw [hW, cross_cross_eq_smul_sub_smul, hU, dotProduct_comm V U, hUV]
    simp
  have hWV : W ⨯₃ V = -U := by
    rw [hW, cross_cross_eq_smul_sub_smul, hV, hUV]
    simp
  have hWD : W ⨯₃ D = (D ⬝ᵥ U) • V - (D ⬝ᵥ V) • U := by
    rw [hW, cross_cross_eq_smul_sub_smul, dotProduct_comm U D, dotProduct_comm V D]
  have hDW' : D ⨯₃ W = (D ⬝ᵥ V) • U - (D ⬝ᵥ U) • V := by
    rw [← cross_anticomm W D, hWD]
    simp only [neg_sub]
  have hexp : W ⨯₃ (D ⨯₃ W) = (D ⬝ᵥ U) • U + (D ⬝ᵥ V) • V := by
    rw [hDW', map_sub, map_smul, map_smul, hWU, hWV, smul_neg, sub_neg_eq_add, add_comm]
  have hmain : W ⨯₃ (D ⨯₃ W) = D := by
    rw [cross_cross_eq_smul_sub_smul', hWW, hDW]
    simp
  exact hmain.symm.trans hexp

end Commons.LinearAlgebra.CrossProduct