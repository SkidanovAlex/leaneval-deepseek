import Submission.Work.Deep.GKO.NarrowImports
import Submission.Work.Deep.GKO.OneFactDefs
import Submission.Work.Deep.GKO.RegVocab

/-!
# The elementary N5 route: vocabulary (`EFL_N5_LEAD.md` §2, §3)

`uncov M` is the set of vertices uncovered by a matching `M`, and `Rematched N P v` says that the
perfect matching `P` re-matched the covered vertex `v` (i.e. `P` uses an edge at `v` that `N` does
not).  These are the two notions in which the three nodes N5a–N5c are stated.
-/

set_option autoImplicit false

namespace Work.Deep.GKO.OneFact.N5

open Classical

noncomputable section

/-- The set of vertices uncovered by `M`. -/
def uncov {n : ℕ} (M : SimpleGraph (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∀ w, ¬ M.Adj v w

/-- `P` re-matches the vertex `v` (relative to the matching `N`): `P` uses at `v` an edge that `N`
does not. -/
def Rematched {n : ℕ} (N P : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  ∃ w, P.Adj v w ∧ ¬ N.Adj v w

end

end Work.Deep.GKO.OneFact.N5
