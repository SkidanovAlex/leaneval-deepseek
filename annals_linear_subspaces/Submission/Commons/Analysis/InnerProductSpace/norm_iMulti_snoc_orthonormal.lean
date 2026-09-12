import Mathlib.Analysis.InnerProductSpace.ExteriorPower
import Mathlib.Logic.Equiv.Fin.Rotate
import Submission.Commons.Analysis.InnerProductSpace.exteriorPower_norm_wedge_le_prod
import Submission.Commons.Analysis.InnerProductSpace.norm_iMulti_comp_perm

set_option autoImplicit false

namespace Commons.Analysis.InnerProductSpace

open Matrix exteriorPower
open scoped BigOperators

/-- Norm of an exterior product of an orthonormal family `a` wedged with a vector `c`
orthogonal to all members of the family, with `c` put in front: `‖c ∧ a₀ ∧ ⋯ ∧ aₙ₋₁‖ = ‖c‖`. -/
lemma norm_iMulti_cons_orthonormal {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (c : E) (a : Fin n → E)
    (ha : Orthonormal ℝ a) (hc : ∀ i : Fin n, inner ℝ (a i) c = 0) :
    ‖exteriorPower.ιMulti ℝ (n + 1) (Fin.cons c a)‖ = ‖c‖ := by
  classical
  let w : Fin (n + 1) → E := Fin.cons c a
  have hsq : ‖exteriorPower.ιMulti ℝ (n + 1) w‖ ^ 2 = ‖c‖ ^ 2 := by
    calc
      ‖exteriorPower.ιMulti ℝ (n + 1) w‖ ^ 2 =
          inner ℝ (exteriorPower.ιMulti ℝ (n + 1) w) (exteriorPower.ιMulti ℝ (n + 1) w) := by
            exact (inner_self_eq_norm_sq_to_K (𝕜 := ℝ)
              (exteriorPower.ιMulti ℝ (n + 1) w)).symm
      _ = (Matrix.gram ℝ w).det := by
            rw [exteriorPower.inner_ιMulti_self]
      _ = (Matrix.gram ℝ (fun _ : PUnit.{1} => c)).det := by
            -- reindex the gram matrix to the block form with `c` in the top-left block
            have hreindex :
                Matrix.reindex (Hadamard.finSuccSumPUnit.{0} n) (Hadamard.finSuccSumPUnit.{0} n)
                    (Matrix.gram ℝ w) =
                  Matrix.fromBlocks (Matrix.gram ℝ (fun _ : PUnit.{1} => c)) 0 0 (Matrix.gram ℝ a) := by
              ext x y
              cases x with
              | inl u =>
                cases y with
                | inl v => simp [w, Matrix.gram_apply]
                | inr j =>
                  simp [w, Matrix.gram_apply]
                  simpa [real_inner_comm] using hc j
              | inr i =>
                cases y with
                | inl v =>
                  simp [w, Matrix.gram_apply]
                  exact hc i
                | inr j => simp [w, Matrix.gram_apply]
            calc
              (Matrix.gram ℝ w).det
                  = (Matrix.reindex (Hadamard.finSuccSumPUnit.{0} n) (Hadamard.finSuccSumPUnit.{0} n)
                        (Matrix.gram ℝ w)).det := by
                      rw [Matrix.det_reindex_self]
              _ = (Matrix.fromBlocks (Matrix.gram ℝ (fun _ : PUnit.{1} => c)) 0 0
                    (Matrix.gram ℝ a)).det := by rw [hreindex]
              _ = (Matrix.gram ℝ (fun _ : PUnit.{1} => c)).det * (Matrix.gram ℝ a).det := by
                    simp
              _ = (Matrix.gram ℝ (fun _ : PUnit.{1} => c)).det := by
                    simp [Matrix.gram_eq_one_iff_orthonormal.mpr ha]
      _ = ‖c‖ ^ 2 := by
            calc
              (Matrix.gram ℝ (fun _ : PUnit.{1} => c)).det = inner ℝ c c := by
                    simp [Matrix.gram_apply, Matrix.det_unique]
              _ = ‖c‖ ^ 2 := by
                    exact (inner_self_eq_norm_sq_to_K (𝕜 := ℝ) c)
  have hx : 0 ≤ ‖exteriorPower.ιMulti ℝ (n + 1) w‖ := norm_nonneg _
  have hy : 0 ≤ ‖c‖ := norm_nonneg _
  rcases (sq_eq_sq_iff_eq_or_eq_neg.mp hsq) with h | h
  · exact h
  · linarith

lemma norm_iMulti_snoc_orthonormal {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (a : Fin n → E) (ha : Orthonormal ℝ a)
    (c : E) (hc : ∀ i : Fin n, inner ℝ (a i) c = 0) :
    ‖exteriorPower.ιMulti ℝ (n + 1) (Fin.snoc (α := fun _ : Fin (n + 1) => E) a c)‖ = ‖c‖ := by
  classical
  calc
    ‖exteriorPower.ιMulti ℝ (n + 1) (Fin.snoc (α := fun _ : Fin (n + 1) => E) a c)‖
        = ‖exteriorPower.ιMulti ℝ (n + 1) (Fin.cons c a ∘ finRotate (n + 1))‖ := by
            congr 1
            rw [Fin.snoc_eq_cons_rotate a c]
            rfl
    _ = ‖exteriorPower.ιMulti ℝ (n + 1) (Fin.cons c a)‖ := by
            rw [norm_iMulti_comp_perm]
    _ = ‖c‖ := by
            exact norm_iMulti_cons_orthonormal c a ha hc

end Commons.Analysis.InnerProductSpace
