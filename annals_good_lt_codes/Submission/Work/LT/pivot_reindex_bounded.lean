import Mathlib

namespace Work.LT

/-- Transporting a bounded two-sided transvection reduction along a reindexing equivalence:
if `M` can be reduced to diagonal form by at most `B` transvections on each side, then so can
its reindexing `reindexAlgEquiv K K e M` (the lists are obtained by applying
`Matrix.TransvectionStruct.reindexEquiv e` elementwise). -/
theorem pivot_reindex_bounded {K : Type*} [Field K] {n : ℕ} {p : Type*} [Fintype p] [DecidableEq p]
    (e : p ≃ Fin n) (B : ℕ) (M : Matrix p p K)
    (H : ∃ (L L' : List (Matrix.TransvectionStruct p K)) (D : p → K),
        (L.map Matrix.TransvectionStruct.toMatrix).prod * M *
            (L'.map Matrix.TransvectionStruct.toMatrix).prod = Matrix.diagonal D ∧
          L.length ≤ B ∧ L'.length ≤ B) :
    ∃ (L L' : List (Matrix.TransvectionStruct (Fin n) K)) (D : Fin n → K),
      (L.map Matrix.TransvectionStruct.toMatrix).prod * Matrix.reindexAlgEquiv K K e M *
          (L'.map Matrix.TransvectionStruct.toMatrix).prod = Matrix.diagonal D ∧
        L.length ≤ B ∧ L'.length ≤ B := by
  obtain ⟨L, L', D, hD, hL, hL'⟩ := H
  refine ⟨L.map (Matrix.TransvectionStruct.reindexEquiv e),
          L'.map (Matrix.TransvectionStruct.reindexEquiv e), D ∘ e.symm, ?_, ?_, ?_⟩
  · rw [List.map_map, List.map_map, Matrix.TransvectionStruct.toMatrix_reindexEquiv_prod,
        Matrix.TransvectionStruct.toMatrix_reindexEquiv_prod]
    rw [← map_mul, ← map_mul, hD]
    simp
  · simpa using hL
  · simpa using hL'

end Work.LT
