import Mathlib
import Submission.Work.KMTAreas.A7.Final

/-! Guidance from the project lead (the requester):

CONTEXT (project lead). This is an area of the FROZEN KMT contract (Submission/Work/KMTContract/Areas.lean; composition
exists_varEstHalfFin_Cv_of_areas PROVED, so proving all eight areas closes the problem). Read first:
* Submission/Work/KMTPlan/ROUTE_LEAD.md: §1 the DAG, §3.1 your area with its proof sketch, §3.3 the quantifier order, §3.4 the audit;
* Submission/Work/KMTContract/README.md;
* KMTContract/QUARANTINE.md: never use the quarantined statements (the old Peluse/Improv/SingleScale ones are false or vacuous).
Many tools are already proved in Submission/Work/** and Submission/Commons/** (ROUTE_LEAD §2.1 lists them); reuse them and do not
re-request what exists. Parallelise: request all independent pieces at once, and write the assembly against their statements while they run.

A7 = VarpLossKMT: varp at every (p₁,p₂) ≠ (2,2) with a loss 2^{Aρ·lmax}, from A1 ONLY (no number theory). Share the
model-operator definitions with A6 (KMTPlan/Model.lean).
-/

namespace Work.KMTAreas

/-- **Area A7**: Theorem `varp` at every exponent pair `(p₁,p₂) ≠ (2,2)` with the controlled loss
`2^{Aρ·max(max l₁ l₂)(max s₁ s₂)}`, from area `A1` alone.  The proof is the assembly
`Work.KMTAreas.A7.areaA7_of_halves` of the two halves of the paper's §7/§8 analysis,
`Work.KMTAreas.A7.SmallLoss` and `Work.KMTAreas.A7.LargeLoss`. -/
theorem area_A7 : Work.KMTContract.AreaA7 := Work.KMTAreas.A7.areaA7_proof

end Work.KMTAreas
