/-
  The rank of a matrix is determined by the pattern of vanishing of its minors.

  The main result of this file is `rank_eq_of_minors_det_eq_zero_iff`: if two `N × N` matrices
  over `ℝ` have the same set of vanishing `l × l` minors for every `l`, then they have the same
  rank.  The proof rests on the classical characterisation

  `rank A ≤ k ↔ every (k+1) × (k+1) minor of A vanishes`,

  which is established in `rank_le_iff_forall_det_submatrix_eq_zero`.
-/
import Mathlib

set_option linter.style.haveILetI false

namespace Work.WilE4.CAD

/-- **A matrix of full row rank has a nonvanishing maximal minor.**
If the rows of `M : Matrix (Fin l) (Fin n) ℝ` are linearly independent, then some `l` of its
columns form an invertible `l × l` matrix. -/
theorem exists_det_submatrix_ne_zero_of_linearIndependent {l n : ℕ}
    (M : Matrix (Fin l) (Fin n) ℝ) (h : LinearIndependent ℝ M.row) :
    ∃ c : Fin l → Fin n, (M.submatrix id c).det ≠ 0 := by
  have hrank : M.rank = l := by
    rw [LinearIndependent.rank_matrix (M := M) h, Fintype.card_fin]
  obtain ⟨κ, a, _hainj, hspan, hli⟩ := exists_linearIndependent' ℝ M.col
  haveI hfin : Finite κ := hli.finite
  haveI hfintype : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = l := by
    rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_cols (A := M), hrank]
  let ee : Fin l ≃ κ := (Fintype.equivFinOfCardEq hcard).symm
  have hcol : LinearIndependent ℝ ((M.submatrix id (a ∘ ee)).col) := by
    have h2 : (M.submatrix id (a ∘ ee)).col = M.col ∘ (a ∘ ee) := by
      ext j i; rfl
    rw [h2]
    exact hli.comp ee ee.injective
  have hns : (M.submatrix id (a ∘ ee)).Nonsingular :=
    (Matrix.linearIndependent_col_iff (A := M.submatrix id (a ∘ ee))).mp hcol
  exact ⟨a ∘ ee, (Matrix.nonsingular_iff_det_ne_zero (A := M.submatrix id (a ∘ ee))).mp hns⟩

/-- **A matrix of rank `≥ l` has `l` linearly independent rows, realised by an injection
`Fin l → Fin N`.** -/
theorem exists_linearIndependent_rows_of_le_rank {N l : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (h : l ≤ A.rank) :
    ∃ r : Fin l → Fin N, Function.Injective r ∧ LinearIndependent ℝ (fun i => A (r i)) := by
  obtain ⟨κ, a, hainj, hspan, hli⟩ := exists_linearIndependent' ℝ (A.row)
  haveI hfin : Finite κ := hli.finite
  haveI hfintype : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = A.rank := by
    rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_row (A := A)]
  have hle : l ≤ Fintype.card κ := by rw [hcard]; exact h
  let ee : Fin l ↪ κ := (Fin.castLEEmb hle).trans
    ((Fintype.equivFinOfCardEq (rfl : Fintype.card κ = Fintype.card κ)).symm.toEmbedding)
  exact ⟨a ∘ ee, hainj.comp ee.injective, hli.comp ee ee.injective⟩

/-- **Rank `≥ l` is witnessed by a nonvanishing `l × l` minor.** -/
theorem exists_det_submatrix_ne_zero_of_rank_le {N l : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (h : l ≤ A.rank) : ∃ r c : Fin l → Fin N, (A.submatrix r c).det ≠ 0 := by
  obtain ⟨r, _hr, hli⟩ := exists_linearIndependent_rows_of_le_rank A h
  obtain ⟨c, hc⟩ := exists_det_submatrix_ne_zero_of_linearIndependent (A.submatrix r id) hli
  refine ⟨r, c, ?_⟩
  have hsub : (A.submatrix r id).submatrix id c = A.submatrix r c := by
    ext i j; rfl
  rwa [hsub] at hc

/-- **The easy direction: rank `≤ k` forces every `(k+1) × (k+1)` minor to vanish.** -/
theorem det_submatrix_eq_zero_of_rank_le {N k : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (h : A.rank ≤ k) (r c : Fin (k + 1) → Fin N) : (A.submatrix r c).det = 0 := by
  refine Matrix.det_eq_zero_of_not_linearIndependent_rows (fun hli => ?_)
  have h1 : (A.submatrix r c).rank ≤ k := (Matrix.rank_submatrix_le A r c).trans h
  have h2 : (A.submatrix r c).rank = k + 1 := by
    rw [LinearIndependent.rank_matrix (M := A.submatrix r c) hli, Fintype.card_fin]
  omega

/-- **The rank is the largest size of a nonvanishing minor:**
`A.rank ≤ k` if and only if every `(k+1) × (k+1)` minor of `A` vanishes. -/
theorem rank_le_iff_forall_det_submatrix_eq_zero {N k : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) :
    A.rank ≤ k ↔ ∀ r c : Fin (k + 1) → Fin N, (A.submatrix r c).det = 0 := by
  refine ⟨fun h r c => det_submatrix_eq_zero_of_rank_le A h r c, fun h => ?_⟩
  by_contra hcon
  rw [not_le] at hcon
  have hle : k + 1 ≤ A.rank := by omega
  obtain ⟨r, c, hrc⟩ := exists_det_submatrix_ne_zero_of_rank_le A hle
  exact hrc (h r c)

theorem rank_eq_of_minors_det_eq_zero_iff {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℝ}
    (h : ∀ (l : ℕ) (r c : Fin l → Fin N), (A.submatrix r c).det = 0 ↔ (B.submatrix r c).det = 0) :
    A.rank = B.rank := by
  have hAB : ∀ k : ℕ, A.rank ≤ k ↔ B.rank ≤ k := by
    intro k
    constructor
    · intro hA
      rw [rank_le_iff_forall_det_submatrix_eq_zero B]
      intro r c
      rw [← (h (k + 1) r c)]
      exact (rank_le_iff_forall_det_submatrix_eq_zero A).mp hA r c
    · intro hB
      rw [rank_le_iff_forall_det_submatrix_eq_zero A]
      intro r c
      rw [(h (k + 1) r c)]
      exact (rank_le_iff_forall_det_submatrix_eq_zero B).mp hB r c
  exact le_antisymm ((hAB B.rank).mpr le_rfl) ((hAB A.rank).mp le_rfl)

end Work.WilE4.CAD
