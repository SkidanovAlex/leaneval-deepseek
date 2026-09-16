import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace Commons.LinearAlgebra.Matrix

/-- If `M : Matrix n n R` has the property that every nonvanishing off-diagonal entry strictly
decreases a given rank function `r : n → ℕ` (more precisely: `M i j ≠ 0 → r j ≤ r i`, with
equality only on the diagonal), then the only permutation contributing to the Leibniz formula is
the identity, so `M.det = ∏ i, M i i`. -/
theorem det_eq_prod_diag_of_rank {n : Type*} [Fintype n] [DecidableEq n]
    {R : Type*} [CommRing R] (M : Matrix n n R) (r : n → ℕ)
    (h : ∀ i j, M i j ≠ 0 → r j ≤ r i)
    (h2 : ∀ i j, M i j ≠ 0 → r j = r i → i = j) :
    M.det = ∏ i, M i i := by
  rw [Matrix.det_apply']
  refine (Finset.sum_eq_single (1 : Equiv.Perm n) ?_ ?_).trans ?_
  · intro σ _ hσ
    have hfind : ∃ i, M (σ i) i = 0 := by
      by_contra hc
      push Not at hc
      have hle : ∀ i, r i ≤ r (σ i) := fun i => h (σ i) i (hc i)
      have hsum : ∑ i, r i = ∑ i, r (σ i) := (Equiv.sum_comp σ r).symm
      have heq : ∀ i, r i = r (σ i) := fun i =>
        (Finset.sum_eq_sum_iff_of_le (fun i _ => hle i)).mp hsum i (Finset.mem_univ i)
      exact hσ (Equiv.ext (fun i => by simpa using h2 (σ i) i (hc i) (heq i)))
    obtain ⟨i, hi⟩ := hfind
    have hz : ∏ j, M (σ j) j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
    rw [hz, mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ (1 : Equiv.Perm n)) hmem
  · simp

end Commons.LinearAlgebra.Matrix