import Mathlib

/-!
# The determinant `det ((1 - t) • 1 + t • M)` expanded over subsets

For a matrix `M` over `ℝ` and a real number `t`, the determinant of the matrix
`(1 - t) • 1 + t • M` expands as a sum over all subsets `s` of the index set:
the rows indexed by `s` are taken from `M` and the remaining rows from the identity,
each subset contributing the scalar factor `t ^ #s * (1 - t) ^ (n - #s)`.

This is the standard multilinearity expansion of the determinant in its rows.
-/

namespace Work.Mostow

open Matrix Finset

/-- Multilinearity of `det` in its rows, expanded along all rows simultaneously:
the determinant of `c • A + d • B` is the sum over subsets `s` of the rows of `c • A + d • B`
where the rows in `s` come from `A` and the others from `B`, together with the scalar factor
`c ^ #s * d ^ (Fintype.card n - #s)`. -/
theorem det_smul_add_smul {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℝ) (c d : ℝ) :
    Matrix.det (c • A + d • B)
      = ∑ s : Finset n,
          c ^ s.card * d ^ (Fintype.card n - s.card) * Matrix.det (s.piecewise A B) := by
  have hprod : ∀ s : Finset n, (∏ i : n, (if i ∈ s then c else d))
      = c ^ s.card * d ^ (Fintype.card n - s.card) := by
    intro s
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have h : (Finset.univ.filter (fun x => ¬ x ∈ s)) = sᶜ := by
      ext x; simp [Finset.mem_compl]
    rw [h, Finset.card_compl]
  let D : ((n → ℝ) [⋀^n]→ₗ[ℝ] ℝ) := Matrix.detRowAlternating
  change D (c • A + d • B) = ∑ s : Finset n,
    c ^ s.card * d ^ (Fintype.card n - s.card) * Matrix.det (s.piecewise A B)
  rw [show (c • A + d • B : Matrix n n ℝ)
      = (fun i => c • (A i)) + (fun i => d • (B i)) from rfl]
  rw [D.map_add_univ]
  apply Finset.sum_congr rfl
  intro s _
  rw [show (s.piecewise (fun i => c • A i) (fun i => d • B i))
      = (fun i => (if i ∈ s then c else d) • (s.piecewise A B) i) from by
        ext i j
        simp only [Finset.piecewise, Pi.smul_apply, smul_eq_mul]
        split_ifs <;> rfl]
  rw [D.map_smul_univ, smul_eq_mul, hprod s]
  rfl

/-- The matrix whose rows outside `s` are the identity rows equals the diagonal scaling of `M`
by the indicator of `s`, plus the complementary diagonal matrix. -/
theorem piecewise_one_eq {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (s : Finset n) :
    (s.piecewise M (1 : Matrix n n ℝ)) =
      Matrix.diagonal (fun i => if i ∈ s then (1 : ℝ) else 0) * M
        + ((1 : Matrix n n ℝ) - Matrix.diagonal (fun i => if i ∈ s then (1 : ℝ) else 0)) := by
  ext i j
  rw [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.diagonal_apply]
  by_cases hi : i ∈ s
  · simp [Finset.piecewise, hi, Matrix.one_apply]
  · simp [Finset.piecewise, hi, Matrix.one_apply]

theorem detInterpExpansion (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (t : ℝ) :
    Matrix.det ((1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ) + t • M)
      = ∑ s ∈ (Finset.univ : Finset (Fin n)).powerset,
          t ^ s.card * (1 - t) ^ (n - s.card) *
            Matrix.det (Matrix.diagonal (fun i => if i ∈ s then (1 : ℝ) else 0) * M
              + (1 - Matrix.diagonal (fun i => if i ∈ s then (1 : ℝ) else 0))) := by
  have h := det_smul_add_smul (A := M) (B := (1 : Matrix (Fin n) (Fin n) ℝ))
    (c := t) (d := 1 - t)
  rw [show (1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ) + t • M
      = t • M + (1 - t) • (1 : Matrix (Fin n) (Fin n) ℝ) from add_comm _ _]
  rw [h, Finset.powerset_univ]
  apply Finset.sum_congr rfl
  intro s _
  rw [piecewise_one_eq]
  simp [Fintype.card_fin]

end Work.Mostow
