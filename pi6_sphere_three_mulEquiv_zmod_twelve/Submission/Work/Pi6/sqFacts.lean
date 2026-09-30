import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.SQ.Defs
import Submission.Work.Pi6.SQ.Bridge
import Submission.Work.Pi6.SQM.Defs
import Submission.Work.Pi6.SQ.sigmaStarAlt
import Submission.Work.Pi6.SQM.sqOneInjective
import Submission.Work.Pi6.SQM.bocksteinSqTwo
import Submission.Work.Pi6.SQM.torsionOfNonliftable
import Submission.Work.Pi6.SQM.hTwoNonzero
import Submission.Work.Pi6.SQM.cup3Coboundary
import Submission.Work.Pi6.SQ.C2.cup2Coboundary
import Submission.Work.Pi6.SQM.cup1CoboundaryR
import Submission.Work.Pi6.SQM.cupINatural
import Submission.Work.Pi6.SQM.sqCyclicCoreAsm
import Submission.Work.Pi6.SQM.emExpAsm
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-! Guidance from the project lead (the requester):

AREA SQ — CRUX A (pi6).  By the lead's restructuring (`REFS/NOTES_LEAD_SQM.md`, contracts in
`Submission/Work/Pi6/SQM/Defs.lean`) the middle of the area (the cohomology suspension `σ*`, the
injectivity of `Sq¹` on `H²`, the Bockstein identity `β₂ Sq² = Sq³`, the torsion extraction, the
cup-3 product and the two assemblies) is dispatched top-level as `Pi6/SQM/*`, and the two
assemblies `Work.Pi6.SQM.sqCyclicCoreAsm` and `Work.Pi6.SQM.emExpAsm` are already written against
those contracts.  Area SQ contributes the cochain-level facts (`∪₁`/`∪₂` coboundary formulas, the
Cartan instance, well-definedness of the Steenrod classes) through the bridges in
`Submission/Work/Pi6/SQ/Bridge.lean`, and `sqFacts` is their assembly:

`sqFacts hR hM2 = ⟨sqCyclicCoreAsm sigmaStar sqOneInjective sqOpsProp cartanProp cupINatural
cup1Cob cup2CoboundaryM hM2 hTwoNonzero, emExpAsm sigmaStar sqOneInjective (bocksteinSqTwo
cup1CoboundaryR cup2CoboundaryM) torsionOfNonliftable cup1Cob cup2CoboundaryM cup3Coboundary hM2
hTwoNonzero⟩`.
-/

namespace Work.Pi6

theorem sqFacts (hR : Work.Pi6.SerreRangeLES) (hM2 : Work.Pi6.EMMod2) :
    Work.Pi6.SqCyclicCore ∧ Work.Pi6.EMExp := by
  have hNZ : ∀ (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ), 3 ≤ N →
      Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X x₀ →
      Nontrivial (Work.Pi6.Coh (ZMod 2) X 2) :=
    Work.Pi6.SQM.hTwoNonzero
  have hS : Work.Pi6.SQM.SigmaStar :=
    Work.Pi6.SQ.sigmaStarAlt Work.Pi6.SQ.cup1Cob Work.Pi6.SQ.C2.cup2CoboundaryM
      Work.Pi6.SQM.cup3Coboundary Work.Pi6.SQM.cupINatural
  refine ⟨Work.Pi6.SQM.sqCyclicCoreAsm hS Work.Pi6.SQM.sqOneInjective
      Work.Pi6.SQ.sqOpsProp Work.Pi6.SQ.cartanProp Work.Pi6.SQM.cupINatural
      Work.Pi6.SQ.cup1Cob Work.Pi6.SQ.C2.cup2CoboundaryM hM2 hNZ, ?_⟩
  exact Work.Pi6.SQM.emExpAsm hS Work.Pi6.SQM.sqOneInjective
    (Work.Pi6.SQM.bocksteinSqTwo Work.Pi6.SQM.cup1CoboundaryR Work.Pi6.SQ.C2.cup2CoboundaryM)
    Work.Pi6.SQM.torsionOfNonliftable Work.Pi6.SQ.cup1Cob
    Work.Pi6.SQ.C2.cup2CoboundaryM Work.Pi6.SQM.cup3Coboundary hM2 hNZ

end Work.Pi6
