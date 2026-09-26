import Mathlib
import Submission.Work.PTCert.QAdjOpDefs

namespace Work.PTCert

/-- An edge of the simplex is *opposite* to another exactly when the two pairs of
natural-number vertices do not share a coordinate.  This bridges the geometric
disjointness relation `RouteB.Edge.Op` and the combinatorial `PTCert.shares` predicate
used by `QAdjOp`. -/
theorem op_iff_not_shares (r : ℕ) (p q : Submission.RouteB.Edge r) :
    Submission.RouteB.Edge.Op p q ↔
      ¬ Submission.PTCert.shares (Submission.PTCert.edgePair p)
        (Submission.PTCert.edgePair q) := by
  rw [Submission.RouteB.Edge.Op, Finset.disjoint_left]
  constructor
  · intro h hsh
    rcases hsh with h' | h' | h' | h'
    · exact h (by simp : p.1.1 ∈ p.toFinset) (by rw [Fin.ext h']; simp)
    · exact h (by simp : p.1.1 ∈ p.toFinset) (by rw [Fin.ext h']; simp)
    · exact h (by simp : p.1.2 ∈ p.toFinset) (by rw [Fin.ext h']; simp)
    · exact h (by simp : p.1.2 ∈ p.toFinset) (by rw [Fin.ext h']; simp)
  · intro hns a ha hb
    rw [Submission.RouteB.Edge.mem_toFinset] at ha hb
    apply hns
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · left; exact congrArg Fin.val (ha.symm.trans hb)
    · right; left; exact congrArg Fin.val (ha.symm.trans hb)
    · right; right; left; exact congrArg Fin.val (ha.symm.trans hb)
    · right; right; right; exact congrArg Fin.val (ha.symm.trans hb)

end Work.PTCert
