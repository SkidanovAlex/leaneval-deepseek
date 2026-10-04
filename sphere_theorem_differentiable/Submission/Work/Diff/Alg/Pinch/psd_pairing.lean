import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Alg.Pinch

open Matrix

/-- The Frobenius pairing of two positive semidefinite symmetric bilinear forms is nonnegative:
if `A` and `N` are symmetric and their quadratic forms are nonnegative, then `∑ᵢⱼ Aᵢⱼ Nᵢⱼ ≥ 0`.

This is the Hadamard/Schur-product form of "tr(A N) ≥ 0 for PSD A, N": the entrywise product
`A ⊙ N` is positive semidefinite by the Schur product theorem, and the sum of its entries is
`1 ⬝ᵥ (A ⊙ N) *ᵥ 1 ≥ 0`. -/
theorem psd_pairing {n : ℕ} {A N : Fin n → Fin n → ℝ}
    (hAsym : ∀ i j, A i j = A j i) (hNsym : ∀ i j, N i j = N j i)
    (hA : ∀ w : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, A i j * w i * w j)
    (hN : ∀ z : Fin n → ℝ, 0 ≤ ∑ i, ∑ j, N i j * z i * z j) :
    0 ≤ ∑ i, ∑ j, A i j * N i j := by
  have hAs : Matrix.PosSemidef (A : Matrix (Fin n) (Fin n) ℝ) := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact Matrix.IsHermitian.ext (fun i j => by simp only [star_trivial]; exact hAsym j i)
    · intro w
      have hw := hA w
      simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        using hw
  have hNs : Matrix.PosSemidef (N : Matrix (Fin n) (Fin n) ℝ) := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · exact Matrix.IsHermitian.ext (fun i j => by simp only [star_trivial]; exact hNsym j i)
    · intro z
      have hz := hN z
      simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]
        using hz
  have hM :
      Matrix.PosSemidef ((A : Matrix (Fin n) (Fin n) ℝ) ⊙ (N : Matrix (Fin n) (Fin n) ℝ)) :=
    hAs.hadamard hNs
  have h := hM.dotProduct_mulVec_nonneg (fun _ : Fin n => (1 : ℝ))
  simpa [dotProduct, Matrix.mulVec, Matrix.hadamard, Finset.mul_sum,
    mul_assoc, mul_left_comm, mul_comm] using h

end Work.Diff.Alg.Pinch
