import Mathlib
import Submission.Work.BW.exists_det_submatrix_ne_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- A matrix of rank `ℓ` has an invertible `ℓ × ℓ` minor, exhibited as a pair of embeddings of
`Fin ℓ` into the row and column index sets. -/
theorem exists_minor {𝕜 : Type*} [Field 𝕜] {n q ℓ : ℕ} (A : Matrix (Fin n) (Fin q) 𝕜)
    (h : A.rank = ℓ) :
    ∃ (Ji : Fin ℓ ↪ Fin n) (Ki : Fin ℓ ↪ Fin q), (A.submatrix Ji Ki).det ≠ 0 := by
  classical
  -- The rank of `A` is the dimension of the span of its rows.
  have hspan : Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range A.row)) = ℓ := by
    rw [← Matrix.rank_eq_finrank_span_row A, h]
  -- Extract `ℓ` linearly independent rows.
  obtain ⟨I, hIcard, hIind⟩ := exists_finset_card_finrank_linearIndepOn (v := A.row) hspan
  -- The corresponding rows of the row-selected submatrix are linearly independent.
  have hli : LinearIndependent 𝕜 (A.row ∘ (I.orderEmbOfFin hIcard : Fin ℓ → Fin n)) := by
    have hmain : LinearIndependent 𝕜
        ((fun x : ↥I => A.row (x : Fin n)) ∘ (I.orderIsoOfFin hIcard : Fin ℓ → ↥I)) :=
      hIind.comp (I.orderIsoOfFin hIcard) (I.orderIsoOfFin hIcard).injective
    have key : (A.row ∘ (I.orderEmbOfFin hIcard : Fin ℓ → Fin n))
        = ((fun x : ↥I => A.row (x : Fin n)) ∘ (I.orderIsoOfFin hIcard : Fin ℓ → ↥I)) := by
      funext i
      exact congrArg A.row (Finset.coe_orderIsoOfFin_apply I hIcard i).symm
    rw [key]
    exact hmain
  have hrows : LinearIndependent 𝕜 (A.submatrix (I.orderEmbOfFin hIcard) id).row := by
    have hrow : (A.submatrix (I.orderEmbOfFin hIcard) id).row
        = A.row ∘ (I.orderEmbOfFin hIcard : Fin ℓ → Fin n) := rfl
    rw [hrow]
    exact hli
  -- Now find `ℓ` columns of this `ℓ × q` matrix giving a nonvanishing minor.
  obtain ⟨J, hJcard, hJdet⟩ :=
    exists_det_submatrix_ne_zero (A.submatrix (I.orderEmbOfFin hIcard) id) hrows
  refine ⟨(I.orderEmbOfFin hIcard).toEmbedding, (J.orderEmbOfFin hJcard).toEmbedding, ?_⟩
  have hsub : (A.submatrix (I.orderEmbOfFin hIcard) id).submatrix id (J.orderEmbOfFin hJcard)
      = A.submatrix (I.orderEmbOfFin hIcard) (J.orderEmbOfFin hJcard) := by
    ext i j
    rfl
  rwa [hsub] at hJdet

end Work.BW
