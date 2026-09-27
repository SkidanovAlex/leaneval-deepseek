/-
# The a-side and b-side of the Eilenberg–Zilber shuffle lemma

The boundary of the shuffle chain `ezChainB a b` of a `(P+1)`-simplex `a` and a `(Q+1)`-simplex
`b` is the sum of the shuffle chains of the a-faces of `a` (with a Koszul sign) and the b-faces of
`b` (with a Koszul sign and the sign `(-1)^{P+1}`).  Everything is written at the boundary degree
`(P+1)+Q` so that no degree transport is needed.
-/
import Mathlib
import Submission.Work.Cohomology.EZShuffle
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.EZShuffleGen
import Submission.Work.Cohomology.EZClassify
import Submission.Work.Cohomology.EZG.cnt_succAbove
import Submission.Work.Cohomology.EZG.cnt_cross
import Submission.Work.Cohomology.EZG.cntB_cross
import Submission.Work.Cohomology.EZG.cnt_cands_lt

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

noncomputable section

variable {X Y : SSet.{0}}

/-- The `a`-side of the shuffle lemma: the shuffle chain of the a-faces of `a` against `b`. -/
def ezA (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)) :
    Submission.Cohomology.SChain (MonoidalCategoryStruct.tensorObj X Y) ℚ ((P+1)+Q) :=
  ∑ i : Fin (P+2), (-1 : ℚ) ^ (i : ℕ) •
    ∑ A : {A : Finset (Fin ((P+1)+Q)) // A.card = P},
      (sgnA A.1 : ℚ) •
        Finsupp.single
          (X.map (shA A.1 (le_of_eq A.2)).op (X.δ i a),
           Y.map (shB A.1 (by have := A.2; omega)).op b) 1

/-- The `b`-side of the shuffle lemma: the shuffle chain of `a` against the b-faces of `b`. -/
def ezB (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)) :
    Submission.Cohomology.SChain (MonoidalCategoryStruct.tensorObj X Y) ℚ ((P+1)+Q) :=
  ∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
    ∑ A : {A : Finset (Fin ((P+1)+Q)) // A.card = P+1},
      (sgnA A.1 : ℚ) •
        Finsupp.single
          (X.map (shA A.1 (by have := A.2; omega)).op a,
           Y.map (shB A.1 (by have := A.2; omega)).op (Y.δ j b)) 1

end

end Work.Cohomology
