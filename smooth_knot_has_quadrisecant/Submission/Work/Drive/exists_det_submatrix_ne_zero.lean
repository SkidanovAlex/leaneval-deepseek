import Mathlib

namespace Work.Drive

/-- **A nonzero minor for an independent family.**  If `v : Fin m → (Fin n → ℝ)` is linearly
independent (so in particular `m ≤ n`), then some selection of `m` distinct coordinates makes the
corresponding `m × m` matrix invertible. -/
theorem exists_det_submatrix_ne_zero {m n : ℕ} {v : Fin m → (Fin n → ℝ)}
    (hv : LinearIndependent ℝ v) :
    ∃ J : Fin m → Fin n, Function.Injective J ∧
      (Matrix.of (fun i j : Fin m => v i (J j))).det ≠ 0 := by
  classical
  -- Read `v` as the rows of an `m × n` matrix.
  set A : Matrix (Fin m) (Fin n) ℝ := Matrix.of (fun i j => v i j) with hA
  have hrow : LinearIndependent ℝ A.row := by
    have hr : A.row = v := by
      funext i j
      simp [hA, Matrix.row]
    rw [hr]; exact hv
  -- The rank of `A` is `m`, so its columns span an `m`-dimensional space, i.e. the whole of `ℝ^m`.
  have hrank : A.rank = m := by
    have := hrow.rank_matrix
    simpa using this
  have htop : ⊤ ≤ Submodule.span ℝ (Set.range A.col) := by
    have htop_eq : Submodule.span ℝ (Set.range A.col) = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← Matrix.rank_eq_finrank_span_cols A, hrank]
      simp [Module.finrank_fintype_fun_eq_card]
    exact htop_eq.ge
  -- Extract a basis of `ℝ^m` from the spanning set of columns.
  have hext : ∃ J : Fin m → Fin n,
      Function.Injective J ∧ LinearIndependent ℝ (fun j => A.col (J j)) := by
    let ι := Set.Elem ((linearIndepOn_empty ℝ id).extend (Set.empty_subset (Set.range A.col)))
    let b : Module.Basis ι ℝ (Fin m → ℝ) :=
      Module.Basis.ofSpan (K := ℝ) (V := Fin m → ℝ) (s := Set.range A.col) htop
    have hcard : Fintype.card ι = m := by
      rw [← Module.finrank_eq_card_basis b]
      simp [Module.finrank_fintype_fun_eq_card]
    let e : ι ≃ Fin m := Fintype.equivFinOfCardEq hcard
    have hmem : ∀ x : ι, b x ∈ Set.range A.col := fun x =>
      Module.Basis.ofSpan_subset (K := ℝ) (V := Fin m → ℝ) (s := Set.range A.col) htop ⟨x, rfl⟩
    choose J0 hJ0 using hmem
    refine ⟨fun j => J0 (e.symm j), ?_, ?_⟩
    · intro j j' hjj
      have : e.symm j = e.symm j' := by
        apply b.injective
        rw [← hJ0 (e.symm j), ← hJ0 (e.symm j')]
        exact congrArg (fun k => A.col k) hjj
      simpa using this
    · have hb := b.linearIndependent
      have := hb.comp (ι' := Fin m) e.symm e.symm.injective
      simpa [Function.comp_def, hJ0] using this
  obtain ⟨J, hJinj, hJind⟩ := hext
  refine ⟨J, hJinj, ?_⟩
  -- The selected `m` columns are linearly independent, so the corresponding square matrix is
  -- nonsingular, hence has nonzero determinant.
  have hcol : LinearIndependent ℝ (Matrix.of (fun i j : Fin m => v i (J j))).col := by
    have heq : (Matrix.of (fun i j : Fin m => v i (J j))).col = (fun j => A.col (J j)) := by
      funext j i
      simp [hA, Matrix.col]
    rw [heq]; exact hJind
  exact Matrix.nonsingular_iff_det_ne_zero.mp
    (Matrix.Nonsingular.of_linearIndependent_col hcol)

end Work.Drive
