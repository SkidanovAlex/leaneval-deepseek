import Mathlib
import Submission.Work.Mostow.dirichletSet_isFundamentalDomain
import Submission.Work.Mostow.exists_closest_orbit
import Submission.Work.Mostow.haarBridge

/-!
# `gaeFD`: Dirichlet fundamental domains

A local copy of `Work.Mostow.exists_fundamentalDomain_gen` (which lives in
`Submission/Work/Mostow/thinStrataGap.lean`), so that the tube inequality
`Submission/Work/Mostow/gaeTube.lean` does not have to import that (actively edited) file.
-/

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory

/-- Every discrete subgroup of `PO N 1` has a Dirichlet fundamental domain. -/
theorem gae_exists_fundamentalDomain_gen (N : ℕ) (hA : POActionProp N) (hI : HypIsometryProp N)
    (H : Subgroup (PO N 1)) (hdisc : IsDiscrete (SetLike.coe H)) :
    ∃ D : Set (E N), IsFundamentalDomain H D (volH N) := by
  haveI : Countable ↥H := countable_of_isDiscrete (PO N 1) hdisc
  obtain ⟨o, ho⟩ := exists_trivial_stabiliser N hA hI H hdisc
  exact ⟨dirichletSet H o, dirichletSet_isFundamentalDomain N hA hI H o ho
    (fun x => exists_closest_orbit N hA hI hdisc o x)⟩

end Work.Mostow
