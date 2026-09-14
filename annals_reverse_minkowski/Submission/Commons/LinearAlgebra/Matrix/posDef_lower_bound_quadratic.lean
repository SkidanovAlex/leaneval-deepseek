import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.posDef_dotProduct_le_trace_mul_inv_dot

open scoped Matrix

namespace Commons.LinearAlgebra.Matrix

theorem posDef_lower_bound_quadratic {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G.PosDef) : ∃ c : ℝ, 0 < c ∧ ∀ x : Fin n → ℝ,
      c * (∑ i, (x i) ^ 2) ≤ dotProduct x (G.mulVec x) := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨1, zero_lt_one, ?_⟩
    intro x
    simp
  · let t : ℝ := (G⁻¹).trace
    have hE : (G⁻¹ : Matrix (Fin n) (Fin n) ℝ).PosDef := hG.inv
    have ht : 0 < t := by
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      let i0 : Fin n := ⟨0, hnpos⟩
      dsimp [t]
      simpa [Matrix.trace, Matrix.diag] using
        (Finset.sum_pos (s := Finset.univ) (f := fun i : Fin n => (G⁻¹) i i)
          (fun i hi => hE.diag_pos)
          (show (Finset.univ : Finset (Fin n)).Nonempty from ⟨i0, Finset.mem_univ i0⟩))
    refine ⟨t⁻¹, inv_pos.mpr ht, ?_⟩
    intro x
    have hle := Commons.LinearAlgebra.Matrix.posDef_dotProduct_le_trace_mul_inv_dot
      (E := (G⁻¹ : Matrix (Fin n) (Fin n) ℝ)) hE x
    have hGinv_inv : ((G⁻¹)⁻¹ : Matrix (Fin n) (Fin n) ℝ) = G := by
      let _inst : Invertible G := Classical.choice hG.isUnit.nonempty_invertible
      exact Matrix.inv_inv_of_invertible G
    have hmain : x ⬝ᵥ x ≤ t * (x ⬝ᵥ G *ᵥ x) := by
      simpa [t, hGinv_inv] using hle
    have hxnorm : (∑ i, (x i) ^ 2) = x ⬝ᵥ x := by
      simp [dotProduct, sq]
    rw [hxnorm]
    exact (inv_mul_le_iff₀ (a := (x ⬝ᵥ G *ᵥ x)) (b := x ⬝ᵥ x) (c := t) ht).mpr hmain

end Commons.LinearAlgebra.Matrix
