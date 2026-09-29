import Mathlib

namespace Work.ZeroEst

open Matrix

/-- Linear-algebra input for Lang's Lemma 2.4 (`lang24`).

If the rows of the square matrix `M` over a field `K` are linearly dependent, then the column
space of `M` has dimension `r < m`, it is spanned by `r` of the columns of `M` (indexed by an
injective `V : Fin r → Fin m`), and — for a suitable injective choice `k0 : Fin r → Fin m` of
rows — the corresponding `r × r` minor of `M` has nonzero determinant. -/
theorem lang24_rank {K : Type*} [Field K] {m : ℕ} (M : Matrix (Fin m) (Fin m) K)
    (hdep : ¬ LinearIndependent K M.row) :
    ∃ (r : ℕ) (_ : r < m) (V k0 : Fin r → Fin m),
      Function.Injective V ∧ Function.Injective k0 ∧ (M.submatrix k0 V).det ≠ 0 ∧
      ∀ j : Fin m, M.col j ∈ Submodule.span K (Set.range fun b : Fin r => M.col (V b)) := by
  classical
  -- `r` is the dimension of the column space of `M`, i.e. the rank of `M`.
  set r : ℕ := Module.finrank K (Submodule.span K (Set.range M.col)) with hr_def
  have hMr : M.rank = r := Matrix.rank_eq_finrank_span_cols M
  -- ### Step 1: row dependence forces `r < m`.
  have hr_lt : r < m := by
    rw [← hMr]
    have h1 : ¬ (m ≤ Set.finrank K (Set.range M.row)) := fun h ↦
      hdep (linearIndependent_iff_card_le_finrank_span.mpr (by simpa using h))
    have h2 : Set.finrank K (Set.range M.row) = M.rank :=
      (Matrix.rank_eq_finrank_span_row M).symm
    omega
  -- ### Step 2: extract `r` linearly independent columns spanning the column space.
  obtain ⟨f, hfmem, hfspan, hfli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range M.col)
  choose V hV using hfmem
  have hV_inj : Function.Injective V := by
    intro a b hab
    exact hfli.injective (by rw [← hV a, ← hV b, hab])
  have hrange : Set.range (fun b : Fin r => M.col (V b)) = Set.range f := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      exact ⟨b, (hV b).symm⟩
    · rintro ⟨b, rfl⟩
      exact ⟨b, hV b⟩
  have hsp : Submodule.span K (Set.range fun b : Fin r => M.col (V b))
      = Submodule.span K (Set.range M.col) := by
    rw [hrange, hfspan]
  have hspanM : ∀ j : Fin m,
      M.col j ∈ Submodule.span K (Set.range fun b : Fin r => M.col (V b)) := by
    intro j
    have hj : M.col j ∈ Submodule.span K (Set.range M.col) := Submodule.subset_span ⟨j, rfl⟩
    rwa [← hsp] at hj
  -- ### Step 3: the selected columns as a matrix `N`.
  let N : Matrix (Fin m) (Fin r) K := M.submatrix id V
  have hNcol : N.col = f := by
    funext b
    rw [← hV b]
    ext i
    simp [N, Matrix.col, Matrix.submatrix_apply]
  have hNli : LinearIndependent K N.col := by
    rw [hNcol]
    exact hfli
  have hNrank : N.rank = r := by
    rw [Matrix.rank_eq_finrank_span_cols, hNcol, hfspan]
  have hrowm : Module.finrank K (Submodule.span K (Set.range N.row)) = r := by
    rw [← Matrix.rank_eq_finrank_span_row N, hNrank]
  -- ### Step 4: extract `r` linearly independent rows of `N`.
  obtain ⟨g, hgmem, _hgspan, hgli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range N.row)
  set e2 : Fin (Module.finrank K (Submodule.span K (Set.range N.row))) ≃ Fin r :=
    finCongr hrowm with he2
  let g' : Fin r → (Fin r → K) := g ∘ e2.symm
  have hg'mem : ∀ i, g' i ∈ Set.range N.row := fun i => hgmem (e2.symm i)
  have hg'li : LinearIndependent K g' := hgli.comp e2.symm e2.symm.injective
  choose k0 hk0 using hg'mem
  have hk0_inj : Function.Injective k0 := by
    intro a b hab
    exact hg'li.injective (by rw [← hk0 a, ← hk0 b, hab])
  -- The chosen `r × r` minor is invertible because its rows are linearly independent.
  have hdetN : (N.submatrix k0 id).det ≠ 0 := by
    have hrow_li : LinearIndependent K (N.submatrix k0 id).row := by
      have hh : (N.submatrix k0 id).row = g' := by
        funext a
        rw [← hk0 a]
        ext b
        simp [Matrix.row, Matrix.submatrix_apply]
      rw [hh]
      exact hg'li
    rw [← Matrix.nonsingular_iff_det_ne_zero, ← Matrix.linearIndependent_row_iff]
    exact hrow_li
  have hsub : M.submatrix k0 V = N.submatrix k0 id := by
    ext a b
    simp [N, Matrix.submatrix_apply]
  have hdet : (M.submatrix k0 V).det ≠ 0 := by
    rw [hsub]
    exact hdetN
  exact ⟨r, hr_lt, V, k0, hV_inj, hk0_inj, hdet, hspanM⟩

end Work.ZeroEst
