import Mathlib
import Submission.Work.Mostow.nearStabDefs

/-!
# Compactness of `matBallToPO`

`matBall n C` is the set of matrices in `O(n,1)`-shape (satisfying both defining relations
`Aᵀ J A = J` and `A J Aᵀ = J`) all of whose entries are bounded by `C`, and `matBallToPO n C`
is its image in `PO n 1`.  This file proves that this image is compact, which is the
compactness input for `Work.Mostow.finite_nearStab` (the orbit map `g ↦ g • 0` being proper).

The proof has three ingredients.

* The set of matrices with all entries bounded by `C` is compact: it is a product of the closed
  intervals `[-C, C]`, and `isCompact_univ_pi` + `isCompact_Icc` give the product version.
* `matBall n C` is closed: each entry bound `|A i j| ≤ C` is closed, and the two matrix
  relations are preimages of the singleton `{J}` under the continuous maps `A ↦ Aᵀ J A` and
  `A ↦ A J Aᵀ`.  (Matrix multiplication and transposition are continuous; transposition is
  `continuous_matrix` applied to the coordinate swap.)
* The map `A ↦ (O1.ofMatrix A ⟨h₁, h₂⟩ : PO n 1)` is continuous on the subtype `↥(matBall n C)`
  and `PO n 1` carries the quotient topology, so the image of the compact set is compact.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity Matrix

/-- The set of matrices (indexed by `Fin n ⊕ Fin 1` in both variables) all of whose entries are
bounded by `C` in absolute value is compact: it is the product of the closed intervals
`[-C, C]`. -/
lemma isCompact_entryBoundMat (n : ℕ) (C : ℝ) :
    IsCompact {A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ | ∀ i j, |A i j| ≤ C} := by
  -- first prove the statement for the "raw" function type, then transport across the
  -- definitional equality `Matrix m n α = m → n → α`
  have h : IsCompact {f : (Fin n ⊕ Fin 1) → (Fin n ⊕ Fin 1) → ℝ | ∀ i j, |f i j| ≤ C} := by
    have hEq : {f : (Fin n ⊕ Fin 1) → (Fin n ⊕ Fin 1) → ℝ | ∀ i j, |f i j| ≤ C}
        = Set.univ.pi (fun _ : Fin n ⊕ Fin 1 =>
            Set.univ.pi (fun _ : Fin n ⊕ Fin 1 => (Set.Icc (-C) C : Set ℝ))) := by
      ext f
      simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc,
        abs_le]
    rw [hEq]
    exact isCompact_univ_pi (fun _ => isCompact_univ_pi (fun _ => isCompact_Icc))
  exact h

/-- `matBall n C` is closed: the entry bounds and the two `O(n,1)` relations are all closed
conditions. -/
lemma isClosed_matBall (n : ℕ) (C : ℝ) : IsClosed (matBall n C) := by
  have h1 : IsClosed {A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ | ∀ i j, |A i j| ≤ C} := by
    have heq : ({A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ | ∀ i j, |A i j| ≤ C} : Set _)
        = ⋂ (i : Fin n ⊕ Fin 1), ⋂ (j : Fin n ⊕ Fin 1),
            ({A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ | |A i j| ≤ C} : Set _) := by
      ext A; simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    rw [heq]
    exact isClosed_iInter (fun i => isClosed_iInter (fun j => by
      have hc : Continuous (fun A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ => |A i j|) := by
        have hf : Continuous
            (fun A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ => A i) := continuous_apply i
        have hg : Continuous (fun p : Fin n ⊕ Fin 1 → ℝ => p j) := continuous_apply j
        exact (hg.comp hf).abs
      exact isClosed_Iic.preimage hc))
  have hT : Continuous (fun A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ => Aᵀ) := by
    apply continuous_matrix
    intro i j
    exact (continuous_apply i).comp (continuous_apply j)
  have h2 : IsClosed {A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ |
      Aᵀ * pmOneMat * A = pmOneMat} :=
    isClosed_eq ((hT.mul continuous_const).mul continuous_id) continuous_const
  have h3 : IsClosed {A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ |
      A * pmOneMat * Aᵀ = pmOneMat} :=
    isClosed_eq ((continuous_id.mul continuous_const).mul hT) continuous_const
  rw [show matBall n C = ({A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ | ∀ i j, |A i j| ≤ C}
      ∩ ({A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ | Aᵀ * pmOneMat * A = pmOneMat}
      ∩ {A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ | A * pmOneMat * Aᵀ = pmOneMat})) from by
    ext A
    simp only [matBall, Set.mem_inter_iff, Set.mem_ofPred_eq]]
  exact h1.inter (h2.inter h3)

/-- `matBall n C` is compact: it is a closed subset of the compact set of matrices with entries
bounded by `C`. -/
lemma isCompact_matBall (n : ℕ) (C : ℝ) : IsCompact (matBall n C) :=
  (isCompact_entryBoundMat n C).of_isClosed_subset (isClosed_matBall n C) (fun _ hA => hA.1)

/-- The canonical map `↥(matBall n C) → PO n 1` is continuous.  On the underlying matrix space
it is given by `MatrixSum.ofMatrix` (which is the identity), so continuity follows from
continuity of the coercion `O1 n → PO n 1`, i.e. from the quotient topology on the projective
group. -/
lemma continuous_matBallToPO (n : ℕ) (C : ℝ) :
    Continuous (fun A : ↥(matBall n C) =>
      ((O1.ofMatrix A.1 ⟨A.2.2.1, A.2.2.2⟩ : O1 n) : PO n 1)) := by
  have hf : Continuous (fun A : ↥(matBall n C) => MatrixSum.ofMatrix A.1) := by fun_prop
  have hp : ∀ A : ↥(matBall n C),
      MatrixSum.ofMatrix A.1 ∈ unitary (MatrixSum (Fin n) (Fin 1) ℝ) :=
    fun A => (mem_unitary_iff _).2 (by simpa using
      (⟨A.2.2.1, A.2.2.2⟩ : A.1ᵀ * pmOneMat * A.1 = pmOneMat ∧
        A.1 * pmOneMat * A.1ᵀ = pmOneMat))
  have hg : Continuous (fun A : ↥(matBall n C) => (O1.ofMatrix A.1 ⟨A.2.2.1, A.2.2.2⟩ : O1 n)) :=
    Continuous.subtype_mk hf hp
  exact Continuous.comp QuotientGroup.continuous_mk hg

theorem isCompact_matBallToPO {n : ℕ} (C : ℝ) : IsCompact (Work.Mostow.matBallToPO n C) := by
  have hcs : CompactSpace ↥(matBall n C) :=
    isCompact_iff_compactSpace.mp (isCompact_matBall n C)
  have huniv : IsCompact (Set.univ : Set ↥(matBall n C)) := @isCompact_univ _ _ hcs
  rw [matBallToPO]
  exact IsCompact.image huniv (continuous_matBallToPO n C)

end Work.Mostow
