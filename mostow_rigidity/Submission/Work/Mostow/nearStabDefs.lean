import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.poAux

/-!
# Near-stabiliser of the origin: shared vocabulary

Vocabulary for `Work.Mostow.finite_nearStab`, the statement that a discrete subgroup `Γ ≤ PO n 1`
meets the set of elements displacing the origin by at most `R` in a finite set.

The mathematical input is that the orbit map `g ↦ g • 0` is proper: the set of `g` with
`hdist 0 (g • 0) ≤ R` is contained in a compact set.  Concretely, in the matrix model an element
`g` with `hdist 0 (g • 0) ≤ R` has a representing matrix all of whose entries are bounded by
`cosh R` (the "last column up to sign is `g • 0`" plus the orthogonality relations), so the
needed compact set is the image of the compact set of matrices

* `matBall n C` : matrices whose entries are bounded by `C` and which satisfy the two
  `O(n,1)`-relations;
* `matBallToPO n C` : its image in `PO n 1`.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity Matrix

noncomputable section

/-- Matrices in `O(n,1)`-shape with all entries bounded by `C`
(including the two relations `Aᵀ J A = J`, `A J Aᵀ = J`). -/
def matBall (n : ℕ) (C : ℝ) : Set (Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) :=
  {A | (∀ i j, |A i j| ≤ C) ∧ Aᵀ * pmOneMat * A = pmOneMat ∧ A * pmOneMat * Aᵀ = pmOneMat}

/-- The image of `matBall n C` in `PO n 1`. -/
def matBallToPO (n : ℕ) (C : ℝ) : Set (PO n 1) :=
  ((fun A : ↥(matBall n C) =>
    ((O1.ofMatrix A.1 ⟨A.2.2.1, A.2.2.2⟩ : O1 n) : PO n 1)) '' Set.univ)

end

end Work.Mostow
