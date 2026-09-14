import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.Matrix

/-- If `V` has dimension `N` over `K` and `v : Fin (N+1) → V` spans `V`, then deleting one
vector (indexed by `Fin.succAbove i`) still leaves a spanning family. -/
private lemma exists_succAbove_span_eq_top {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {N : ℕ} (hfin : Module.finrank K V = N) (v : Fin (N+1) → V)
    (hspan : Submodule.span K (Set.range v) = ⊤) :
    ∃ i : Fin (N+1), Submodule.span K (Set.range (v ∘ Fin.succAbove i)) = ⊤ := by
  have hdep : ¬ LinearIndependent K v := by
    intro hli
    have h := finrank_span_eq_card hli
    rw [hspan, finrank_top, hfin, Fintype.card_fin] at h
    omega
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg0, i0, hi0⟩ := hdep
  refine ⟨i0, ?_⟩
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin (N+1))).erase i0,
      v i ∈ Submodule.span K (Set.range (v ∘ Fin.succAbove i0)) := by
    intro i hi
    have hne : i ≠ i0 := (Finset.mem_erase.mp hi).1
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hne
    exact Submodule.subset_span ⟨a, by rw [Function.comp_apply, ha]⟩
  have hsum : (∑ i ∈ (Finset.univ : Finset (Fin (N+1))).erase i0, g i • v i) ∈
      Submodule.span K (Set.range (v ∘ Fin.succAbove i0)) :=
    Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _ (hmem i hi))
  have hvi0 : v i0 ∈ Submodule.span K (Set.range (v ∘ Fin.succAbove i0)) := by
    have hsplit : g i0 • v i0 =
        -∑ i ∈ (Finset.univ : Finset (Fin (N+1))).erase i0, g i • v i := by
      have h := Finset.add_sum_erase (Finset.univ : Finset (Fin (N+1)))
        (fun i => g i • v i) (Finset.mem_univ i0)
      rw [hg0] at h
      exact eq_neg_of_add_eq_zero_left h
    rw [← inv_smul_smul₀ hi0 (v i0), hsplit]
    exact Submodule.smul_mem _ _ (Submodule.neg_mem _ hsum)
  rw [eq_top_iff, ← hspan, Submodule.span_le]
  rintro x ⟨j, rfl⟩
  by_cases hj : j = i0
  · rw [hj]; exact hvi0
  · obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hj
    exact Submodule.subset_span ⟨a, by rw [Function.comp_apply, ha]⟩

/-- The vector of signed maximal minors of `G` is nonzero iff some maximal minor is nonzero. -/
private lemma starVec_ne_zero_iff_exists {K : Type*} [Field K] {N : ℕ}
    (G : Matrix (Fin (N+1)) (Fin N) K) :
    (fun i : Fin (N+1) => (-1 : K) ^ (i : ℕ) * (G.submatrix (Fin.succAbove i) id).det) ≠ 0 ↔
      ∃ i : Fin (N+1), (G.submatrix (Fin.succAbove i) id).det ≠ 0 := by
  have hneg : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rw [Function.ne_iff]
  simp only [Pi.zero_apply]
  exact exists_congr (fun i => by
    rw [mul_ne_zero_iff, and_iff_right (pow_ne_zero _ hneg)])

/-- A `(N+1) × N` matrix has linearly independent columns iff some `N × N` minor
(obtained by deleting a row) is nonzero. -/
private lemma exists_det_submatrix_ne_zero_iff_linearIndependent {K : Type*} [Field K] {N : ℕ}
    (G : Matrix (Fin (N+1)) (Fin N) K) :
    (∃ i : Fin (N+1), (G.submatrix (Fin.succAbove i) id).det ≠ 0) ↔
      LinearIndependent K G.col := by
  constructor
  · rintro ⟨i, hi⟩
    have hLI : LinearIndependent K (G.submatrix (Fin.succAbove i) id).col :=
      Matrix.linearIndependent_cols_of_det_ne_zero hi
    have hLI' := (Fintype.linearIndependent_iff).mp hLI
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hcol : ∀ j : Fin N, (LinearMap.funLeft K K (Fin.succAbove i)) (G.col j) =
        (G.submatrix (Fin.succAbove i) id).col j := fun j => rfl
    have hsum0 : (∑ j : Fin N, g j • (G.submatrix (Fin.succAbove i) id).col j) = 0 := by
      have h := congrArg (LinearMap.funLeft K K (Fin.succAbove i)) hg
      simpa only [map_sum, map_smul, map_zero, hcol] using h
    exact hLI' g hsum0
  · intro hLI
    have hfin_cols : Module.finrank K (Submodule.span K (Set.range G.col)) = N := by
      have h := finrank_span_eq_card hLI
      rwa [Fintype.card_fin] at h
    have hrank : G.rank = N := by
      rw [Matrix.rank_eq_finrank_span_cols, hfin_cols]
    have hfin_rows : Module.finrank K (Submodule.span K (Set.range G.row)) = N := by
      rw [← Matrix.rank_eq_finrank_span_row G, hrank]
    have hspan_rows : Submodule.span K (Set.range G.row) = ⊤ :=
      Submodule.eq_top_of_finrank_eq
        (by rw [hfin_rows, Module.finrank_fintype_fun_eq_card]; simp)
    obtain ⟨i, hi⟩ := exists_succAbove_span_eq_top (V := Fin N → K)
      (by rw [Module.finrank_fintype_fun_eq_card]; simp) G.row hspan_rows
    refine ⟨i, ?_⟩
    have hLIrow : LinearIndependent K (G.row ∘ Fin.succAbove i) :=
      linearIndependent_of_top_le_span_of_card_eq_finrank (b := G.row ∘ Fin.succAbove i)
        hi.ge (by simp [Module.finrank_fintype_fun_eq_card])
    have hf : (G.submatrix (Fin.succAbove i) id).row = G.row ∘ Fin.succAbove i := by
      ext a j; rfl
    have hLIrow' : LinearIndependent K (G.submatrix (Fin.succAbove i) id).row := by
      rw [hf]; exact hLIrow
    exact (Matrix.nonsingular_iff_det_ne_zero).mp
      ((Matrix.linearIndependent_row_iff).mp hLIrow')

theorem starVec_ne_zero_iff {K : Type*} [Field K] {N : ℕ} (G : Matrix (Fin (N+1)) (Fin N) K) :
    (fun i : Fin (N+1) => (-1 : K) ^ (i : ℕ) * (G.submatrix (Fin.succAbove i) id).det) ≠ 0 ↔
      LinearIndependent K G.col :=
  (starVec_ne_zero_iff_exists G).trans (exists_det_submatrix_ne_zero_iff_linearIndependent G)

end Commons.LinearAlgebra.Matrix