import Mathlib
import Submission.Work.LinnikContract.Areas
import Submission.Work.LinnikAreas.A5.Main

/-! Guidance from the project lead (the requester):

CONTEXT (project lead). This is an area of the FROZEN Linnik contract (Submission/Work/LinnikContract/Areas.lean; composition
linnik_of_areas PROVED, so proving all seven areas closes the problem). Read first:
* Submission/Work/LinnikPlan/ROUTE_LEAD.md: §1.2 constants, §3.1 your area with the source and proof sketch, §4 numerics, §5 risks;
* LinnikContract/Defs.lean.
Never use the quarantined lemmas (LinnikContract/Quarantine.lean: q-dependent constants); the build guard will fail. The seeded
Submission/Commons/** is a large sorry-free analytic-number-theory library (ROUTE_LEAD §2.1 inventory); reuse it and do not re-request what
exists. Parallelise: request all independent pieces at once.

Area5 = Area1 → PerCharCert: HB Lemma 13.3, uniform in λ ∈ [0,R].
-/

namespace Work.LinnikAreas

theorem area5 : Work.LinnikContract.Area5 := by
  intro h1
  exact Work.LinnikAreas.A5.perCharCert_of_LBound13 h1.1

end Work.LinnikAreas
