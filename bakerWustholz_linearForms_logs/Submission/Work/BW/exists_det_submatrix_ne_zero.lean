import Mathlib
import Submission.Work.BW.exists_finset_card_finrank_linearIndepOn

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- If the columns of `A` indexed by the finset `J` are linearly independent, then the `ρ × ρ`
minor of `A` on the columns `J` (read in increasing order) does not vanish. -/
theorem det_submatrix_ne_zero_of_linearIndepOn {K : Type*} [Field K] {ρ r : ℕ}
    (A : Matrix (Fin ρ) (Fin r) K) (J : Finset (Fin r)) (hJ : J.card = ρ)
    (h : LinearIndepOn K A.col (↑J)) :
    (A.submatrix id (J.orderEmbOfFin hJ)).det ≠ 0 := by
  have hli : LinearIndependent K
      (A.col ∘ (J.orderEmbOfFin hJ : Fin ρ → Fin r)) := by
    have hmain : LinearIndependent K
        ((fun x : ↥J => A.col (x : Fin r)) ∘ (J.orderIsoOfFin hJ : Fin ρ → ↥J)) :=
      h.comp (J.orderIsoOfFin hJ) (J.orderIsoOfFin hJ).injective
    have key : (A.col ∘ (J.orderEmbOfFin hJ : Fin ρ → Fin r))
        = ((fun x : ↥J => A.col (x : Fin r)) ∘ (J.orderIsoOfFin hJ : Fin ρ → ↥J)) := by
      funext i
      exact congrArg A.col (Finset.coe_orderIsoOfFin_apply J hJ i).symm
    rw [key]
    exact hmain
  have hcol : (A.submatrix id (J.orderEmbOfFin hJ)).col
      = A.col ∘ (J.orderEmbOfFin hJ : Fin ρ → Fin r) := rfl
  have hns : (A.submatrix id (J.orderEmbOfFin hJ)).Nonsingular :=
    Matrix.Nonsingular.of_linearIndependent_col (by rw [hcol]; exact hli)
  exact Matrix.nonsingular_iff_det_ne_zero.mp hns

/-- If the rows of a `ρ × r` matrix over a field are linearly independent, then some `ρ` columns
give a nonvanishing `ρ × ρ` minor. -/
theorem exists_det_submatrix_ne_zero {K : Type*} [Field K] {ρ r : ℕ}
    (A : Matrix (Fin ρ) (Fin r) K) (h : LinearIndependent K A.row) :
    ∃ (J : Finset (Fin r)) (hJ : J.card = ρ),
      (A.submatrix id (J.orderEmbOfFin hJ)).det ≠ 0 := by
  have hrank : A.rank = ρ := by
    have := LinearIndependent.rank_matrix h
    simpa using this
  have hfin : Module.finrank K (Submodule.span K (Set.range A.col)) = ρ := by
    rw [← Matrix.rank_eq_finrank_span_cols A, hrank]
  obtain ⟨J, hJ, hli⟩ :=
    exists_finset_card_finrank_linearIndepOn (v := A.col) hfin
  exact ⟨J, hJ, det_submatrix_ne_zero_of_linearIndepOn A J hJ hli⟩

end Work.BW
