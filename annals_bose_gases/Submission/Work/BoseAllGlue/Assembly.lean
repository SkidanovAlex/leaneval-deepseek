import ChallengeDeps
import Submission.Work.BoseAllGlue.NodeRestrictedFSAll
import Submission.Work.BoseAllGlue.RB67FSAllOfPieces
import Submission.Work.BoseAllGlue.ViewFSAllOfGateAll
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseAllGlue.nodeRestrictedB_of_AllRows` — the four D3 rows composed

This module is the *integration certificate* of the area: it composes the four glue rows

| row | input to this theorem |
|---|---|
| 3 | `hdom : RB4boxDomAtAll v h R J' fc fu HM` (from `RB4boxDomFSAll_of_bridge`) |
| 1 | `hgate` + `hN` ⟹ `hview` (`viewFSAll_of_gateAll`) |
| 2 | `hgate` + `hctrl` + `hbog` ⟹ `h67` (`RB67FSAll_of_pieces`) |
| far leg | `h5K : RB5FSAllK` ⟹ `h5` (`RB5FSAll_of_K`) |
| 4 | `hdom`, `hview`, `h5`, `h67` + `NodeB1B` ⟹ `∃ η₀ C, NodeRestrictedB` |

into a single call producing exactly the frozen node
`Work.BoseBoxFix.NodeRestrictedB v h J' η₀ C`.  Nothing new is proved: the theorem is the
five-line composition, and its value is that it *type-checks* — i.e. it witnesses that the
`All` vocabularies of the four rows agree (`valFSAll`/`viewFSAll`/`KzOpFSAll`, the common
`ε`-threshold of the view and of `RB67FSAll`, and the arity of `NodeB1B`'s `n ≤ 2μℓ³` row).

A caller wiring the `All` chain has to supply the chemistry (`HonestGateAtFSAll`,
`Control3QFSAll`, `BogOpBoundFSAll`, `RB5FSAllK`) and the two cube-size rows (the gate's `Ng`
and the `Ŵ₁` cut-off pin `hN`), all of which are other areas' deliverables; the *glue* is here.

The view row is applied at the gate's own threshold `εg` (which is why `εg ≤ 1` is an explicit
hypothesis: `viewFSAll_of_gateAll` needs `ε ≤ 1`, and `HonestGateAtFSAll` does not carry it —
`HonestGateFSAll` does, and a caller holding that §10 bundle destructures it into
`{Ng, εg, hεg, hεg1, hgate}` before calling this theorem).
-/

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Filter Metric

namespace Work.BoseAllGlue

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix
open Work.BoseFixR Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-- **The frozen §7–§11 node from the four `All` glue rows.** -/
theorem nodeRestrictedB_of_AllRows {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R J' : ℝ}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < _root_.BoseGases.a v)
    (hR : 0 < R) (hJ' : Work.UBB.lhyC < J') (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ)
    (hB1 : Work.BoseBoxFix.NodeB1B v h J')
    (hdom : Work.BoseBoxFock.RB4boxDomAtAll v h R J' fc fu HM)
    {K₀ b₀ : ℝ} (hb₀ : 0 < b₀) {εg : ℝ} (hεg : 0 < εg) (hεg1 : εg ≤ 1)
    (hgate : Work.BoseBoxFock.HonestGateAtFSAll v h fc fu HM εg K₀ b₀)
    (hN : ∀ μ, 0 < μ →
      4 * (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
              * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
            * Real.sqrt (μ * _root_.BoseGases.a v))
        ≤ Work.BoseBoxFock.uvRad (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N)
    (hctrl : Work.BoseBoxFock.Control3QFSAll K₀ b₀ hb₀)
    (hbog : Work.BoseBoxFock.BogOpBoundFSAll v h R (Work.BoseBoxFock.HonestBoxFam v h fc fu HM))
    (h5K : Work.BoseBoxFock.RB5FSAllK v h R (Work.BoseBoxFock.HonestBoxFam v h fc fu HM)) :
    ∃ η₀ : ℝ, 1 / 2000 < η₀ ∧ η₀ < 2 / 323 ∧
      ∃ C : ℝ, 0 ≤ C ∧ Work.BoseBoxFix.NodeRestrictedB v h J' η₀ C := by
  -- row 1: the view, at the gate's own threshold `εg`
  have hview : ∀ μ : ℝ, 0 < μ → μ * _root_.BoseGases.a v ^ 3 ≤ εg →
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ :=
    Work.BoseBoxFock.viewFSAll_of_gateAll h hav fc fu HM hN hεg1 hgate
  -- row 2: FS §10+§11 at the honest family, from the gate, Control3Q and the Bogoliubov input
  have h67 := Work.BoseBoxFock.RB67FSAll_of_pieces h hv hv1 hvrad hR hv_supp hav
    fc fu HM hb₀ hεg hgate hctrl hbog
  -- row 4: the node, with the far leg's `RB5FSAllK` converted by `RB5FSAll_of_K`
  exact Work.BoseFixR.nodeRestrictedB_of_residualsFSAllK hav (le_of_lt hR) hJ' fc fu HM hB1
    hdom hεg hεg1 hview h5K h67

end Work.BoseAllGlue
