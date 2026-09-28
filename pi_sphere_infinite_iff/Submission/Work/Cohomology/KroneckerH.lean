import Mathlib
import Submission.Work.Cohomology.kronecker_descent
import Submission.Work.Cohomology.exists_capH

/-!
# The Kronecker pairing on (co)homology, packaged

`Submission/Work/Cohomology/kronecker_descent.lean` proves the existence of the Kronecker pairing
`H^n(X;R) ⟶ (H_n(X;R) →ₗ[R] R)` as an unexplicit `∃`.  This file fixes it once and for all
(`kronH`) and records its computation rule `kronH_apply`: on the class of a cocycle `α` and the
class of a cycle `z` the value is `α z`, the evaluation of the cochain on the cycle.

For our purposes the Kronecker pairing is the tool with which the intersection form of a closed
manifold is evaluated: `⟨y ⌣ z, [M]⟩ = ⟨y, [M] ⌢ z⟩`
(`Work.Cohomology.kronH_capPair_cup`, the homology-level form of the cochain identity
`Work.Cohomology.kronecker_cap_cup`).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R] (X : SSet)

/-- **The Kronecker pairing** `H^n(X;R) ⟶ (H_n(X;R) →ₗ[R] R)`: a choice of the pairing whose
existence is `Work.Cohomology.kronecker_descent`. -/
noncomputable def kronH (n : ℕ) :
    ↑((cochainC R X).homology n) →ₗ[R] (((chainC R X).homology n) →ₗ[R] R) :=
  Classical.choose (kronecker_descent R X) n

/-- **The computation rule for the Kronecker pairing**: on the class of a cocycle `α` and the class
of a cycle `z` the value is the evaluation `α z` of the cochain on the cycle. -/
theorem kronH_apply {n : ℕ} (α : Cochain R X n)
    (hα : cochainDiff R X α = 0) (z : ↑((chainC R X).cycles n)) :
    kronH R X n (cohomologyClassOf R X α hα) (((chainC R X).homologyπ n).hom z)
      = α (((chainC R X).iCycles n).hom z) :=
  (Classical.choose_spec (kronecker_descent R X)) n α hα z

end

end Work.Cohomology
