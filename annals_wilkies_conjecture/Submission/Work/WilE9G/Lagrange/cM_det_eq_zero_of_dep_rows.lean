import Mathlib
import Submission.Work.WilE9G.Lagrange.LagBlocks

namespace Work.WilE9G.Lagrange

/-- A square matrix over `ℝ` whose rows admit a nontrivial linear relation has determinant `0`.
This is the generic linear-algebra fact underlying `cM_det_eq_zero_of_dep_rows`. -/
theorem det_eq_zero_of_rows_sum_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (c : ι → ℝ)
    (hdep : ∑ i, c i • M i = 0) (hne : ∃ i, c i ≠ 0) : M.det = 0 := by
  apply Matrix.det_eq_zero_of_not_linearIndependent_rows
  rw [Fintype.not_linearIndependent_iff]
  exact ⟨c, hdep, hne⟩

/-- If the multiplier vector `mu` is non-trivial and `∑_a mu a • W_·a = 0` (i.e. the rows `h_a` of
the abstract Lagrange block matrix are linearly dependent), then — in the case `mu0 = 0` — both
`cM A W g mu 0` and `cM Aᵀ W g mu 0` have determinant `0`. -/
theorem cM_det_eq_zero_of_dep_rows {r j : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (W : Matrix (Fin r) (Fin j) ℝ) (g : Fin r → ℝ) (mu : Fin j → ℝ)
    (hdep : ∀ l : Fin r, ∑ a, mu a * W l a = 0) (hne : ∃ a : Fin j, mu a ≠ 0) :
    (Work.WilE9G.Lagrange.cM A W g mu 0).det = 0 ∧
      (Work.WilE9G.Lagrange.cM A.transpose W g mu 0).det = 0 := by
  -- The `h`-rows (indices `Sum.inl (Sum.inr b)`) of `cM B W g mu 0` do not involve `B`, `g` or
  -- `mu0`; the relation `∑_a mu a • W_·a = 0` makes them linearly dependent.  Hence the
  -- determinant vanishes for both `A` and `Aᵀ`.
  have key : ∀ B : Matrix (Fin r) (Fin r) ℝ,
      (Work.WilE9G.Lagrange.cM B W g mu 0).det = 0 := by
    intro B
    refine det_eq_zero_of_rows_sum_eq_zero
      (M := Work.WilE9G.Lagrange.cM B W g mu 0)
      (c := Sum.elim (Sum.elim (fun _ : Fin r => (0 : ℝ)) mu) (fun _ : Fin 1 => (0 : ℝ))) ?_ ?_
    · -- the combination `∑_b mu b • row_b` collapses to zero
      funext y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, add_zero]
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zero_mul, Finset.sum_const_zero, zero_add]
      rcases y with ((k | b') | u)
      · simp only [Work.WilE9G.Lagrange.cM_apply_inl_inr_inl_inl]
        exact hdep k
      · simp only [Work.WilE9G.Lagrange.cM_apply_inl_inr_inl_inr, mul_zero,
          Finset.sum_const_zero]
      · simp only [Work.WilE9G.Lagrange.cM_apply_inl_inr_inr, mul_zero, Finset.sum_const_zero]
    · obtain ⟨a, ha⟩ := hne
      exact ⟨Sum.inl (Sum.inr a), by simp [Sum.elim_inl, Sum.elim_inr, ha]⟩
  exact ⟨key A, key A.transpose⟩

end Work.WilE9G.Lagrange
