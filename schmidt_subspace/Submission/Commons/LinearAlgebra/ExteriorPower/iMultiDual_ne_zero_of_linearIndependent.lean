import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.LinearAlgebra.ExteriorPower

/-- The determinant of a square matrix over a field, whose rows are the vectors `w i`, is
nonzero when the family `w` is linearly independent. This is the "rows of the matrix are
linearly independent iff the determinant is nonzero" statement in the direction that Mathlib
spells out through `Matrix.linearIndependent_row_iff` and `Matrix.nonsingular_iff_det_ne_zero`. -/
private lemma det_of_linearIndependent_ne_zero {K : Type*} [Field K] {N : ℕ}
    (w : Fin N → (Fin N → K)) (hw : LinearIndependent K w) :
    (Matrix.of w).det ≠ 0 := by
  have hrow : LinearIndependent K (Matrix.of w).row := by
    rw [show (Matrix.of w).row = w from by ext i j; rfl]
    exact hw
  exact (Matrix.nonsingular_iff_det_ne_zero).mp ((Matrix.linearIndependent_row_iff).mp hrow)

/-- The embedding `ofFinEmbEquiv.symm` of the full set `Fin N` is the identity order
embedding. -/
private lemma ofFinEmbEquiv_symm_univ_refl {N : ℕ} :
    Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofFinEmb N (Fin N) (Function.Embedding.refl (Fin N)))
      = OrderEmbedding.id (Fin N) := by
  rw [Equiv.symm_apply_eq, Set.powersetCard.ofFinEmbEquiv_apply, OrderEmbedding.id_toEmbedding]

theorem iMultiDual_ne_zero_of_linearIndependent {K : Type*} [Field K] {N : ℕ}
    (w : Fin N → (Fin N → K)) (hw : LinearIndependent K w) :
    exteriorPower.ιMultiDual K N (Pi.basisFun K (Fin N))
      (Set.powersetCard.ofFinEmb N (Fin N) (Function.Embedding.refl (Fin N)))
      (exteriorPower.ιMulti_family K N w
        (Set.powersetCard.ofFinEmb N (Fin N) (Function.Embedding.refl (Fin N)))) ≠ 0 := by
  -- Rewrite the exterior product as `ιMulti` of the ordered family and evaluate the dual form.
  rw [show exteriorPower.ιMulti_family K N w
        (Set.powersetCard.ofFinEmb N (Fin N) (Function.Embedding.refl (Fin N)))
      = exteriorPower.ιMulti K N
        (w ∘ (Set.powersetCard.ofFinEmbEquiv.symm
          (Set.powersetCard.ofFinEmb N (Fin N) (Function.Embedding.refl (Fin N))))) from rfl]
  rw [exteriorPower.ιMultiDual_apply_ιMulti]
  -- The ordering embedding of the full set is the identity, so the coordinates are those of
  -- `w` in the standard basis `Pi.basisFun K (Fin N)`.
  rw [ofFinEmbEquiv_symm_univ_refl]
  simp only [OrderEmbedding.coe_id, Function.comp_apply, id_eq]
  have hmat : (Matrix.of fun i j : Fin N => (Pi.basisFun K (Fin N)).coord j (w i))
      = Matrix.of w := by
    ext i j
    simp [Pi.basisFun_repr]
  rw [hmat]
  exact det_of_linearIndependent_ne_zero w hw

end Commons.LinearAlgebra.ExteriorPower