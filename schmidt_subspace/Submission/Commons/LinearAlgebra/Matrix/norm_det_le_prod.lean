import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open Equiv Finset Matrix

namespace Commons.LinearAlgebra.Matrix

/-- The norm of the determinant of a complex `n × n` matrix is bounded by
`n!` times the product of the row-wise bounds. -/
theorem norm_det_le_prod {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (ρ : Fin n → ℝ)
    (hρ : ∀ i j, ‖M i j‖ ≤ ρ i) :
    ‖M.det‖ ≤ (n.factorial : ℝ) * ∏ i, ρ i := by
  -- The sign of a permutation, viewed in `ℂ`, is a unit of norm one.
  have hsign : ∀ σ : Equiv.Perm (Fin n),
      ‖((((Equiv.Perm.sign σ) : ℤˣ) : ℤ) : ℂ)‖ = 1 := by
    intro σ
    rw [Complex.norm_intCast]
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
    · rw [h]; simp
    · rw [h]; simp
  calc ‖M.det‖
      = ‖∑ σ : Equiv.Perm (Fin n), (↑↑(Equiv.Perm.sign σ) : ℂ) * ∏ i, M (σ i) i‖ := by
          rw [Matrix.det_apply']
    _ ≤ ∑ σ : Equiv.Perm (Fin n), ‖(↑↑(Equiv.Perm.sign σ) : ℂ) * ∏ i, M (σ i) i‖ :=
          norm_sum_le _ _
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, ‖M (σ i) i‖ := by
          refine Finset.sum_congr rfl (fun σ _ => ?_)
          rw [norm_mul, norm_prod, hsign σ, one_mul]
    _ ≤ ∑ σ : Equiv.Perm (Fin n), ∏ i, ρ (σ i) := by
          refine Finset.sum_le_sum (fun σ _ => ?_)
          exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hρ (σ i) i)
    _ = ∑ σ : Equiv.Perm (Fin n), ∏ i, ρ i := by
          refine Finset.sum_congr rfl (fun σ _ => ?_)
          exact Equiv.Perm.prod_comp σ Finset.univ ρ (by simp)
    _ = (n.factorial : ℝ) * ∏ i, ρ i := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
          rw [nsmul_eq_mul]

end Commons.LinearAlgebra.Matrix