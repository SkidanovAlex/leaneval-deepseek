import Mathlib
import Submission.Work.Rigidity.SigmaEntryBound.Defs

namespace Work.Rigidity.SigmaEntryBound

open Matrix Finset

/-- `frob2C` is the squared Frobenius norm.  For each entry of `A * B` we have
`‖(A * B) i j‖ ≤ ∑ k ‖A i k‖ * ‖B k j‖`, and Cauchy–Schwarz bounds the square of that
sum by the product of the row-energy of `A` and the column-energy of `B`; summing over
`i, j` gives submultiplicativity. -/
theorem frob2C_mul (A B : Matrix (Fin 6) (Fin 6) ℂ) :
    frob2C (A * B) ≤ frob2C A * frob2C B := by
  have key : ∀ i j : Fin 6,
      ‖(A * B) i j‖ ^ 2 ≤ (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) := by
    intro i j
    have h1 : ‖(A * B) i j‖ ≤ ∑ k, ‖A i k‖ * ‖B k j‖ := by
      rw [Matrix.mul_apply]
      refine (norm_sum_le Finset.univ _).trans (le_of_eq ?_)
      apply Finset.sum_congr rfl
      intro k _
      rw [norm_mul]
    have h2 : (∑ k, ‖A i k‖ * ‖B k j‖) ^ 2 ≤ (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) :=
      sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖A i k‖) (fun k => ‖B k j‖)
    calc ‖(A * B) i j‖ ^ 2 ≤ (∑ k, ‖A i k‖ * ‖B k j‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
  have hA : (∑ i : Fin 6, ∑ k : Fin 6, ‖A i k‖ ^ 2) = frob2C A := rfl
  have hB : (∑ j : Fin 6, ∑ k : Fin 6, ‖B k j‖ ^ 2) = frob2C B := by
    rw [Finset.sum_comm]; rfl
  calc
    frob2C (A * B) = ∑ i, ∑ j, ‖(A * B) i j‖ ^ 2 := rfl
    _ ≤ ∑ i, ∑ j, (∑ k, ‖A i k‖ ^ 2) * (∑ k, ‖B k j‖ ^ 2) :=
        Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => key i j))
    _ = ∑ i, (∑ k, ‖A i k‖ ^ 2) * (∑ j, ∑ k, ‖B k j‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
    _ = (∑ i, ∑ k, ‖A i k‖ ^ 2) * (∑ j, ∑ k, ‖B k j‖ ^ 2) := by
        rw [Finset.sum_mul]
    _ = frob2C A * frob2C B := by rw [hA, hB]

end Work.Rigidity.SigmaEntryBound
