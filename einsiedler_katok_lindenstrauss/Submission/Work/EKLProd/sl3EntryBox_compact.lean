import Mathlib
import Submission.Work.EKLContract.All

/-!
# The entrywise box in `SL₃(ℝ)` is compact

`G = SL₃(ℝ)` is realized as the subtype `{A : Matrix (Fin 3) (Fin 3) ℝ // A.det = 1}` of the
space of `3 × 3` real matrices (with the subspace topology and the function topology on the
matrix space).  A set defined by entrywise inequalities `a i j ≤ g i j ≤ b i j` is the preimage of
a compact box — a finite product of compact intervals — under the canonical projection
`Subtype.val`.  That projection is a *closed* embedding, since its range is the closed set
`{M | det M = 1}`; hence preimages of compact sets are compact.
-/

namespace Work.EKLProd

open Work.EKLContract

/-- The box of real `3 × 3` matrices (viewed as functions) with entrywise bounds is compact: it is
a finite product of compact intervals. -/
theorem sl3EntryBox_compact_box (a b : Fin 3 → Fin 3 → ℝ) :
    IsCompact {M : Fin 3 → Fin 3 → ℝ | ∀ i j, a i j ≤ M i j ∧ M i j ≤ b i j} := by
  have hbox : IsCompact
      (Set.univ.pi (fun i : Fin 3 => Set.univ.pi (fun j : Fin 3 => Set.Icc (a i j) (b i j)))) :=
    isCompact_univ_pi (fun i => isCompact_univ_pi (fun j => isCompact_Icc))
  have hEq : {M : Fin 3 → Fin 3 → ℝ | ∀ i j, a i j ≤ M i j ∧ M i j ≤ b i j}
      = Set.univ.pi (fun i : Fin 3 => Set.univ.pi (fun j : Fin 3 => Set.Icc (a i j) (b i j))) := by
    ext M; simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Icc]
  rw [hEq]; exact hbox

/-- `Subtype.val : SL₃(ℝ) → (Fin 3 → Fin 3 → ℝ)` is a closed embedding: it is the canonical
embedding of a subtype, and its range is the closed set `det = 1`. -/
theorem isClosedEmbedding_subtypeVal_SL3 :
    Topology.IsClosedEmbedding
      (Subtype.val : {A : Matrix (Fin 3) (Fin 3) ℝ // A.det = 1} → (Fin 3 → Fin 3 → ℝ)) := by
  refine ⟨Topology.IsEmbedding.subtypeVal, ?_⟩
  rw [Subtype.range_val_subtype]
  exact isClosed_eq (Continuous.matrix_det continuous_id) continuous_const

theorem sl3EntryBox_compact (a b : Fin 3 → Fin 3 → ℝ) :
    IsCompact {g : Work.EKLContract.SL3 | ∀ i j, a i j ≤ g i j ∧ g i j ≤ b i j} := by
  have hf := isClosedEmbedding_subtypeVal_SL3
  show IsCompact ((Subtype.val :
      {A : Matrix (Fin 3) (Fin 3) ℝ // A.det = 1} → (Fin 3 → Fin 3 → ℝ)) ⁻¹'
      {M : Fin 3 → Fin 3 → ℝ | ∀ i j, a i j ≤ M i j ∧ M i j ≤ b i j})
  exact hf.isCompact_preimage (sl3EntryBox_compact_box a b)

end Work.EKLProd
