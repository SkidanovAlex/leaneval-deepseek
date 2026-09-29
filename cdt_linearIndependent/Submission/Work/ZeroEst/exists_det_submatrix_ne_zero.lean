import Mathlib

/-!
# Existence of a nonvanishing maximal minor of a full-row-rank matrix

If `Y` is an `r × m` matrix over a field with `Y.rank = r`, then some choice of `r` columns
of `Y` yields an invertible `r × r` submatrix. Equivalently: the columns of a full-row-rank
matrix span the whole space, hence contain a basis among them.

The proof extracts a linearly independent subfamily of the columns of size `r` from the
spanning family `Y.col` using `Submodule.exists_fun_fin_finrank_span_eq`, and concludes
that the corresponding `r × r` submatrix has linearly independent columns, hence nonzero
determinant.
-/

namespace Work.ZeroEst

open Matrix Module

theorem exists_det_submatrix_ne_zero {K : Type*} [Field K] {r m : ℕ}
    (Y : Matrix (Fin r) (Fin m) K) (hrank : Y.rank = r) :
    ∃ J : Fin r → Fin m, Function.Injective J ∧ (Y.submatrix id J).det ≠ 0 := by
  classical
  -- The columns of `Y` span a space of dimension `r`, the number of rows.
  have hfin : Module.finrank K (Submodule.span K (Set.range Y.col)) = r := by
    rw [← Matrix.rank_eq_finrank_span_cols]; exact hrank
  -- Extract a linearly independent subfamily of the columns of size `r`.
  obtain ⟨f, hf_mem, -, hf_li⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range Y.col)
  -- Reindex along `hfin` so that the extracted family is indexed by `Fin r`.
  let e : Fin (Module.finrank K (Submodule.span K (Set.range Y.col))) ≃ Fin r := finCongr hfin
  let f' : Fin r → (Fin r → K) := f ∘ e.symm
  have hf'_mem : ∀ i, f' i ∈ Set.range Y.col := fun i => hf_mem _
  have hf'_li : LinearIndependent K f' := hf_li.comp _ e.symm.injective
  -- Each selected column is a specific column of `Y`; record the indices.
  choose J hJ using hf'_mem
  refine ⟨J, ?_, ?_⟩
  · -- The indices are distinct, since the columns they select are linearly independent.
    intro i j hij
    have h : f' i = f' j := by rw [← hJ i, ← hJ j, hij]
    exact hf'_li.injective h
  · -- The selected `r × r` submatrix has columns `f'`, which are linearly independent.
    have hcol : (Y.submatrix id J).col = f' := by
      funext i k
      simpa using congrFun (hJ i) k
    have hli : LinearIndependent K (Y.submatrix id J).col := hcol ▸ hf'_li
    exact Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_col hli)

end Work.ZeroEst
