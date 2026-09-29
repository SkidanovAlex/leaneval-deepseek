import Mathlib

set_option linter.style.haveILetI false

/-!
# Extracting an invertible square minor from linearly independent vectors

Given `r` linearly independent vectors `v a : Fin m → K` (`a : Fin r`), we must produce an
injective choice `I : Fin r → Fin m` of `r` coordinates such that the `r × r` matrix
`(v a (I b))` is invertible.

Equivalently, the coordinate projections of the `r`-dimensional space spanned by the `v a` span
its dual; a subfamily of `r` of them is a basis, and the corresponding square minor is invertible.

The argument here reduces to the concrete statement

  * a family `w : Fin m → (Fin r → K)` with `Submodule.span K (Set.range w) = ⊤` contains `r`
    linearly independent vectors.

This is obtained from `Module.exists_linearIndependent'`, which extracts an independent
sub-family `w ∘ a` (`a : κ → Fin m` injective) spanning the same space; since the space has
dimension `r`, the index type `κ` is finite of cardinality `r`, giving a bijection `κ ≃ Fin r`
and hence the index map `I`.
-/

namespace Work.ZeroEst2

/-- The coordinate functionals `j ↦ (a ↦ v a j)` of a linearly independent family
`v : Fin r → Fin m → K` span the whole space `Fin r → K`. -/
lemma span_range_coord_eq_top {K : Type*} [Field K] {r m : ℕ} (v : Fin r → Fin m → K)
    (hli : LinearIndependent K v) :
    Submodule.span K (Set.range (fun j : Fin m => fun a : Fin r => v a j)) = ⊤ := by
  classical
  -- `B` is the `m × r` matrix whose columns are the vectors `v a`.
  set B : Matrix (Fin m) (Fin r) K := Matrix.of (fun j a => v a j) with hB
  have hBcol : B.col = v := by
    funext a j
    simp [hB, Matrix.col]
  have hspan_v : Module.finrank K (Submodule.span K (Set.range v)) = r := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  have hBrank : B.rank = r := by
    rw [Matrix.rank_eq_finrank_span_cols B, hBcol, hspan_v]
  have hBtrank : B.transpose.rank = r := by
    rw [Matrix.rank_transpose B, hBrank]
  -- the columns of the transpose are exactly the coordinate functionals
  have hBtcol : B.transpose.col = (fun j : Fin m => fun a : Fin r => v a j) := by
    funext j a
    simp [hB, Matrix.col, Matrix.transpose_apply]
  have hfin : Module.finrank K
      (Submodule.span K (Set.range (fun j : Fin m => fun a : Fin r => v a j))) = r := by
    rw [← hBtcol, ← Matrix.rank_eq_finrank_span_cols B.transpose, hBtrank]
  refine Submodule.eq_top_of_finrank_eq ?_
  rw [hfin, Module.finrank_fintype_fun_eq_card]
  simp

theorem exists_injective_minor {K : Type*} [Field K] {r m : ℕ} (v : Fin r → Fin m → K)
    (hli : LinearIndependent K v) :
    ∃ I : Fin r → Fin m, Function.Injective I ∧
      (Matrix.of (fun a b : Fin r => v a (I b))).det ≠ 0 := by
  classical
  set w : Fin m → (Fin r → K) := fun j a => v a j with hw
  have hspan : Submodule.span K (Set.range w) = ⊤ := by rw [hw]; exact span_range_coord_eq_top v hli
  -- extract a linearly independent sub-family of `w` spanning the same space
  obtain ⟨κ, a, ha_inj, hspana, hlia⟩ := exists_linearIndependent' K w
  have hspanW : Submodule.span K (Set.range (w ∘ a)) = ⊤ := by rw [hspana, hspan]
  -- the index type `κ` is finite, of cardinality `r`
  have hfinite : Finite κ :=
    LinearIndependent.finite_of_le_span_finite (w ∘ a) hlia (Set.range w)
      (by rw [hspan]; exact Set.subset_univ _)
  letI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = r := by
    rw [← finrank_span_eq_card hlia, hspanW, finrank_top, Module.finrank_fintype_fun_eq_card]
    simp
  let e : κ ≃ Fin r := Fintype.equivFinOfCardEq hcard
  refine ⟨fun b => a (e.symm b), ?_, ?_⟩
  · exact fun x y h => e.symm.injective (ha_inj h)
  · -- the columns of the extracted square matrix are `(w ∘ a) ∘ e.symm`, hence independent
    have hcol : (Matrix.of (fun x y : Fin r => v x (a (e.symm y)))).col = (w ∘ a) ∘ e.symm := by
      funext y x
      simp [hw, Matrix.col, Function.comp_apply]
    have hliM : LinearIndependent K (Matrix.of (fun x y : Fin r => v x (a (e.symm y)))).col := by
      rw [hcol]
      exact hlia.comp e.symm e.symm.injective
    have hunit : IsUnit (Matrix.of (fun x y : Fin r => v x (a (e.symm y)))) :=
      Matrix.linearIndependent_cols_iff_isUnit.mp hliM
    exact ((Matrix.isUnit_iff_isUnit_det _).mp hunit).ne_zero

end Work.ZeroEst2
