import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.corrArithHold
import Submission.Work.BoseFixB1S.kineticCruxParsed
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.corrInputPieces` — `CorrInput` from its two remaining pieces

Written by the holder of `Submission/Work/BoseFixB1B/lowCountBound.lean`.

The intersection-mean correction `Work.BoseFixB1S.CorrInput v` (FS `eq:BSsliding2`'s last
residual, see `Submission/Work/BoseFixB1B/kineticHalfAssembly.lean`) is assembled by the proved
`Work.BoseFixB1S.cruxCorrB1_of_pieces` from six pieces.  Four of them are theorems:

* `CutWords` = `Work.BoseFixB1S.corrCutWordsSharp` (proved),
* `ChiL2` = `Work.BoseFixB1S.corrChiScaleL2` (proved),
* `PlanchMarg` = `Work.BoseFixB1S.corrPlanchMarg` (proved),
* `Arith` = `Work.BoseFixB1B.arith_holds` (proved in `corrArithHold.lean`).

Only `MeanSq` and `Marginal` remain; this file is the wiring, and is deliberately kept free of
the `MeanSq`/`Marginal` import cone (which is in flux) so that it builds independently of it.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-- **`CorrInput`** from the two pieces of `cruxCorrB1_of_pieces` that are still open
(`MeanSq`, `Marginal`): the other four are theorems —
`CorrInput`'s cut-words piece is `Work.BoseFixB1S.corrCutWordsSharp` (proved), its
combinatorial piece `ChiL2` is `Work.BoseFixB1S.corrChiScaleL2` (proved), its Plancherel piece
`PlanchMarg` is `Work.BoseFixB1S.corrPlanchMarg` (proved), and `Arith` is proved in
`Submission/Work/BoseFixB1B/corrArithHold.lean`. -/
theorem corrInput_of_pieces {v : E3 → ℝ} (h : Work.UBB.ScatSol v)
    (hMean : Work.BoseFixB1S.MeanSq v) (hMarg : Work.BoseFixB1S.Marginal v) :
    Work.BoseFixB1S.CorrInput v :=
  Work.BoseFixB1S.cruxCorrB1_of_pieces h
    (Work.BoseFixB1S.corrCutWordsSharp h) hMean hMarg arith_holds
    (fun ℓ hℓ w hw => Work.BoseFixB1S.corrChiScaleL2 (ℓ := ℓ) (w := w) hℓ hw)
    (fun ℓ d hℓ hd w hw hint heq => Work.BoseFixB1S.corrPlanchMarg hℓ hd hw hint heq)

end Work.BoseFixB1B
