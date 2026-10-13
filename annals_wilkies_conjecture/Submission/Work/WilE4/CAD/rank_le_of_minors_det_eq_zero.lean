import Mathlib

set_option linter.style.haveILetI false

/-!
# Rank bound from vanishing maximal minors

If every `(k+1) × (k+1)` minor of an `N × N` real matrix `A` vanishes, then `A.rank ≤ k`.

The proof is the contrapositive: a matrix of rank `≥ k+1` has a nonvanishing `(k+1) × (k+1)`
minor.  Writing `rank A` as the dimension of the span of the rows, `rank A ≥ k+1` yields `k+1`
linearly independent rows; the resulting `(k+1) × N` matrix `B` has rank `k+1`, so its columns
span a `(k+1)`-dimensional space and hence `k+1` of them are linearly independent.  The
corresponding square submatrix then has linearly independent columns, so its determinant is
nonzero — contradicting the hypothesis.

The only ingredient not in Mathlib is the elementary extraction lemma
`exists_linearIndependent_comp_of_le_finrank`.
-/

namespace Work.WilE4.CAD

open Matrix

/-- **Extraction lemma.** If a finite family `v : ι → W` spans a space of dimension at least `n`,
then some `n` members of the family are linearly independent.  Concretely, there is an injection
`a : Fin n → ι` such that `v ∘ a` is linearly independent. -/
theorem exists_linearIndependent_comp_of_le_finrank {K ι W : Type*} [Field K] [AddCommGroup W]
    [Module K W] [Module.Finite K W] [Fintype ι] (v : ι → W) {n : ℕ}
    (hn : n ≤ Module.finrank K (Submodule.span K (Set.range v))) :
    ∃ a : Fin n → ι, LinearIndependent K (v ∘ a) := by
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' K v
  have hfin : Finite κ := hli.finite
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Module.finrank K (Submodule.span K (Set.range v)) := by
    rw [linearIndependent_iff_card_eq_finrank_span.mp hli]
    unfold Set.finrank
    rw [hspan]
  have hle : n ≤ Fintype.card κ := hcard ▸ hn
  let e : Fin n ↪ κ := (Fin.castLEEmb hle).trans (Fintype.equivFin κ).symm.toEmbedding
  exact ⟨a ∘ e, hli.comp e e.injective⟩

theorem rank_le_of_minors_det_eq_zero {N k : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (h : ∀ r c : Fin (k+1) → Fin N, (A.submatrix r c).det = 0) : A.rank ≤ k := by
  by_contra hcon
  rw [not_le] at hcon
  have hk : k + 1 ≤ A.rank := hcon
  -- extract `k+1` linearly independent rows
  obtain ⟨r, hr⟩ := exists_linearIndependent_comp_of_le_finrank (A.row) (n := k+1)
    (hk.trans (le_of_eq (Matrix.rank_eq_finrank_span_row A)))
  set B : Matrix (Fin (k+1)) (Fin N) ℝ := A.submatrix r id with hB
  have hBrow : LinearIndependent ℝ B.row := by
    rw [hB]
    have hrow : (A.submatrix r id).row = A.row ∘ r := by ext j i; rfl
    rw [hrow]; exact hr
  have hBrank : B.rank = k + 1 := by
    rw [LinearIndependent.rank_matrix hBrow]; simp
  -- extract `k+1` linearly independent columns of `B`
  obtain ⟨c, hc⟩ := exists_linearIndependent_comp_of_le_finrank (B.col) (n := k+1)
    (by rw [← Matrix.rank_eq_finrank_span_cols B]; omega)
  have hcol : (A.submatrix r c).col = B.col ∘ c := by
    rw [hB]
    funext j
    simpa only [Function.comp_apply] using Matrix.col_submatrix A r c j
  have hScol : LinearIndependent ℝ (A.submatrix r c).col := by rw [hcol]; exact hc
  have hdet : (A.submatrix r c).det ≠ 0 :=
    Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_col hScol)
  exact absurd (h r c) hdet

end Work.WilE4.CAD
