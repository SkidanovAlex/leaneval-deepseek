import Mathlib

open Matrix

namespace Work.NN.Final

/-- For every `k` there are positive numbers `ε i` (`i = 0, …, k`) and weights `lam i`
such that the moments `∑ i, lam i * (-(ε i))^j` equal `1` for all `j ≤ k`.

Concretely we take `ε i = (i : ℝ) + 1` and `f i = -(ε i)`; the matrix
`(vandermonde f)ᵀ` has entry `f i ^ j` in row `j`, column `i`, so the system
`∑ i, lam i * f i ^ j = 1` is exactly `(vandermonde f)ᵀ *ᵥ lam = 1`.  Since `f` is
injective the Vandermonde determinant is nonzero, so the matrix is invertible and
its `mulVec` is surjective, furnishing `lam`. -/
theorem existsFiniteMomentData (k : ℕ) :
    ∃ (ε : Fin (k + 1) → ℝ) (lam : Fin (k + 1) → ℝ),
      (∀ i, 0 < ε i) ∧
      ∀ j : ℕ, j ≤ k → ∑ i : Fin (k + 1), lam i * (-(ε i)) ^ j = 1 := by
  let ε : Fin (k + 1) → ℝ := fun i => (i : ℝ) + 1
  let f : Fin (k + 1) → ℝ := fun i => -((i : ℝ) + 1)
  have hf : Function.Injective f := by
    intro i j hij
    simp only [f] at hij
    have h : (i : ℝ) = (j : ℝ) := by linarith
    exact Fin.ext (by exact_mod_cast h)
  have hdet : ((Matrix.vandermonde f)ᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hf
  have hunit : IsUnit ((Matrix.vandermonde f)ᵀ) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hsurj : Function.Surjective (Matrix.mulVec ((Matrix.vandermonde f)ᵀ)) :=
    (Matrix.mulVec_surjective_iff_isUnit).mpr hunit
  obtain ⟨lam, hlam⟩ := hsurj (fun _ => (1 : ℝ))
  refine ⟨ε, lam, ?_, ?_⟩
  · intro i; simp only [ε]; positivity
  · intro j hj
    have h := congrFun hlam ⟨j, Nat.lt_succ_of_le hj⟩
    change (Matrix.mulVec ((Matrix.vandermonde f)ᵀ) lam) ⟨j, Nat.lt_succ_of_le hj⟩ = 1 at h
    rw [← h]
    simp only [Matrix.mulVec_apply_eq_sum, Matrix.transpose_apply, Matrix.vandermonde_apply,
      ε, f]
    refine Finset.sum_congr rfl ?_
    intro i _
    ring

end Work.NN.Final
