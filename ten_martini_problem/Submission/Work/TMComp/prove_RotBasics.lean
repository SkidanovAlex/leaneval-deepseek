import Mathlib
import Submission.Work.TMContract.Components
import Submission.Work.TMComp.RotBasics.Defs
import Submission.Work.TMComp.RotBasics.RotConj

/-! Guidance from the project lead (the requester):

Component C5 (P_RotBasics) of the Ten Martini formalisation. The FROZEN statement is Work.TMContract.P_RotBasics (Submission/Work/TMContract/Components.lean; definitions in TMContract/Defs.lean; read TMContract/README.md). The proof route for C5 is in Submission/Work/TMPlan/ROUTE_LEAD.md (find the section for C5); the source is Avila–Jitomirskaya, The Ten Martini Problem (arXiv math/0503363), plus the references ROUTE_LEAD cites. Any other component's P_* that ROUTE_LEAD lists as an input for C5 may be taken as a HYPOTHESIS inside your proof only if P_RotBasics's own statement takes it; otherwise prove what you need. Decompose into lemmas right away and dispatch them in parallel with request_lemma (request_review first if unsure a statement is true). Keep every build small; no hour-long files.
-/

namespace Work.TMComp

open Work.TMContract

theorem prove_RotBasics : Work.TMContract.P_RotBasics := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro α lam E
    exact Work.TMComp.RotBasics.rotLift_tendsto α lam E
  · intro α lam
    exact Work.TMComp.RotBasics.ids_monotone α lam
  · intro lam
    change Continuous (fun p : ℝ × ℝ => 1 - rotLift p.1 lam p.2)
    exact continuous_const.sub (Work.TMComp.RotBasics.rotLift_continuous lam)
  · intro α lam E B φ k hdeg hper hdet hφcont hφper hconj
    exact Work.TMComp.RotBasics.rotLift_conjugacy α lam E B φ k hdeg hper hdet hφcont hφper hconj

end Work.TMComp
