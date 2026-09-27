import Mathlib
import Submission.Work.EKLC8Core.Vol

namespace Work.EKLC8Core

/-- The sum of the flow exponents vanishes: `(-1) + 1 + 0 = 0`. -/
theorem sum_flowExp : (∑ j : Fin 3, flowExp j) = 0 := by
  simp [flowExp, Fin.sum_univ_three]

/-- The scaled flow exponents still sum to zero. -/
theorem sum_smul_flowExp (τ : ℝ) : (∑ j : Fin 3, (τ • flowExp) j) = 0 := by
  simp [Pi.smul_apply, smul_eq_mul, flowExp, Fin.sum_univ_three]

/-- The normalising factor in `aDiag t` is trivial for `t = τ • flowExp`, so that
`φ_τ = aDiag (τ • flowExp)` is the honest diagonal matrix `diag(e^{-τ}, e^{τ}, 1)`. -/
theorem phi_coe (τ : ℝ) :
    (phi τ : Matrix (Fin 3) (Fin 3) ℝ) =
      Matrix.diagonal (fun i => Real.exp (flowExp i * τ)) := by
  have hsum : (∑ x : Fin 3, (τ • flowExp) x) = 0 := sum_smul_flowExp τ
  ext i j
  simp only [phi, aDiag, Subtype.coe_mk, Matrix.diagonal_apply]
  split_ifs with h
  · rw [hsum]
    congr 1
    simp [Pi.smul_apply, smul_eq_mul, mul_comm]
  · rfl

theorem phi_entries (τ : ℝ) :
    (∀ i j : Fin 3, (phi τ) i j = if i = j then Real.exp (flowExp i * τ) else 0) ∧
    (∀ i j : Fin 3, i ≠ j → (phi τ) i j = 0) ∧
    (phi τ) 0 0 = Real.exp (-τ) ∧ (phi τ) 1 1 = Real.exp τ ∧ (phi τ) 2 2 = 1 := by
  have hmat := phi_coe τ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [hmat, Matrix.diagonal_apply]
  · intro i j hij
    rw [hmat, Matrix.diagonal_apply, if_neg hij]
  · rw [hmat, Matrix.diagonal_apply_eq]; simp [flowExp]
  · rw [hmat, Matrix.diagonal_apply_eq]; simp [flowExp]
  · rw [hmat, Matrix.diagonal_apply_eq]; simp [flowExp]

end Work.EKLC8Core
