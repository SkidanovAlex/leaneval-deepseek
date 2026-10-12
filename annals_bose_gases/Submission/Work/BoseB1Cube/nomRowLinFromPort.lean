import ChallengeDeps
import Submission.Work.BoseB1Cube.normNodeOfPort
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.nomRowLinFromPort` — piece C of the nominal per-box route from the
# **port-rung** node `Work.BoseB1Cube.normNodeOfPort` alone

`Work.BoseB1Cube.nomRowLinWindowRow_of_normNode` (PROVED, `nomRowLinWindowRow.lean`) turns the
normalised node `NormNode` into piece C `Work.BoseB1Cube.NomRowLinWindowRow`, and
`Work.BoseB1Cube.normNodeOfPort` (delegated, `normNodeOfPort.lean`) proves `NormNode` **through the
PROVED port rung** `Work.BoseB1Cube.sbWordCube_ge_payPortR3` — *not* through the strictly stronger
`SharpRow2` (`FINDING_sharpRow2Holds_session1.md` §0: `SharpRow2` needs a *lower* bound on the
sharp rung's left-hand side, which no upper-bound rung can supply, whereas the node only needs
`demand ≤ sbWordCube`).  This module is the two-line composition, so that a consumer of piece C
(state-level `BoxState` rows) need not import the port machinery.

With pieces A (`Work.BoseB1Cube.nomRowSqWindowRow`, PROVED) and B
(`Work.BoseB1Cube.nomRowArbState`, PROVED) this gives
`Work.BoseB1Cube.nominalPerBoxRow_of_AC`, hence `Work.BoseB1Cube.PerBoxFNomSlots`, hence
`Work.BoseB1Cube.cubeCrudeBand_holds` (via the PROVED `cubeCrudeBand_of_perBoxFNomSlots`) and the
root's `hB1` (via `Work.BoseB1Cube.nodeB1B_of_perBoxFNomMu`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Piece C from the port-rung node.**  `Work.BoseB1Cube.NormNode v h R ⟹
Work.BoseB1Cube.NomRowLinWindowRow v h R` (PROVED `nomRowLinWindowRow_of_normNode`) applied to
`Work.BoseB1Cube.normNodeOfPort` (the delegated port-rung proof). -/
theorem nomRowLinWindowRow_of_port {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < a v) :
    NomRowLinWindowRow v h R :=
  nomRowLinWindowRow_of_normNode h hv hv1 hvrad hR hv_supp hav
    (normNodeOfPort h hv hv1 hvrad hR hv_supp hav)

end Work.BoseB1Cube
