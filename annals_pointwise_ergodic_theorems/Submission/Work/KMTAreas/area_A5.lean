import Mathlib
import Submission.Work.KMTAreas.A5.Final

/-! Guidance from the project lead (the requester):

CONTEXT (project lead). This is an area of the FROZEN KMT contract (Submission/Work/KMTContract/Areas.lean; composition
exists_varEstHalfFin_Cv_of_areas PROVED, so proving all eight areas closes the problem). Read first:
* Submission/Work/KMTPlan/ROUTE_LEAD.md: §1 the DAG, §3.1 your area with its proof sketch, §3.3 the quantifier order, §3.4 the audit;
* Submission/Work/KMTContract/README.md;
* KMTContract/QUARANTINE.md: never use the quarantined statements (the old Peluse/Improv/SingleScale ones are false or vacuous).
Many tools are already proved in Submission/Work/** and Submission/Commons/** (ROUTE_LEAD §2.1 lists them); reuse them and do not
re-request what exists. Parallelise: request all independent pieces at once, and write the assembly against their statements while they run.

A5 = MinorArcKMT: the minor-arc input (B) for kmtPj ρ from A1 and ImprovKMT (both hypotheses), via the §4 displays and
interpolation. Mind the constant hierarchy (∃C₀min, then ρ₀).
-/

namespace Work.KMTAreas

theorem area_A5 : Work.KMTContract.AreaA5 := Work.KMTAreas.A5.areaA5_aux

end Work.KMTAreas
