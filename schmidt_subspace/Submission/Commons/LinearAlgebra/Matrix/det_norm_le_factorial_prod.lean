import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Commons.LinearAlgebra.Matrix

open Finset

theorem det_norm_le_factorial_prod {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) (b : Fin r → ℝ)
    (hb : ∀ i, 0 ≤ b i) (h : ∀ i j, ‖A i j‖ ≤ b i) :
    ‖A.det‖ ≤ (Nat.factorial r : ℝ) * ∏ i, b i := by
  rw [Matrix.det_apply']
  calc ‖∑ σ : Equiv.Perm (Fin r), (↑↑(Equiv.Perm.sign σ) : ℂ) * ∏ i, A (σ i) i‖
      ≤ ∑ σ : Equiv.Perm (Fin r), ‖(↑↑(Equiv.Perm.sign σ) : ℂ) * ∏ i, A (σ i) i‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin r), (∏ i, b i) := by
        apply Finset.sum_le_sum
        intro σ _
        rw [norm_mul]
        have hsign : ‖(↑↑(Equiv.Perm.sign σ) : ℂ)‖ = 1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> rw [hs] <;> norm_num
        rw [hsign, one_mul]
        have h1 : ‖∏ i, A (σ i) i‖ ≤ ∏ i, b (σ i) := by
          calc ‖∏ i, A (σ i) i‖
              = ‖∏ i ∈ Finset.univ, A (σ i) i‖ := by simp
            _ ≤ ∏ i ∈ Finset.univ, ‖A (σ i) i‖ := Finset.norm_prod_le _ _
            _ ≤ ∏ i ∈ Finset.univ, b (σ i) :=
                Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => h (σ i) i)
            _ = ∏ i, b (σ i) := by simp
        rwa [Equiv.prod_comp σ b] at h1
    _ = (Nat.factorial r : ℝ) * ∏ i, b i := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
        simp

end Commons.LinearAlgebra.Matrix