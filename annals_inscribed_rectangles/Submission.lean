import ChallengeDeps
import Submission.Helpers
import Submission.Work.Theorem3Endgame
import Submission.Work.Drive.umlauf
import Submission.Work.Drive.boxParity
import Submission.Work.Drive.orderSplit_chains

open InscribedRectangles
open Manifold Real MeasureTheory
open scoped ContDiff

set_option autoImplicit false

namespace Submission

/-- **Hugelmeyer's Theorem 1**: for a smooth Jordan curve, the set of aspect ratios of inscribed
rectangles has measure at least `1/3`.

The assembly (the last step of the wall, see `HANDOFF.md` / `ORDERSPLIT_GATE_STATUS.md`): the measure
reduction `Submission.Configuration.theorem_1_of_OrderSplitHolds` consumes the geometric core
`OrderSplitHolds γ`, which is `Work.Drive.orderSplit_chains` applied to the two proved contracts
`Work.Drive.umlauf` (`UmlaufProp`, the Umlaufsatz) and `Work.Drive.boxParity` (`ParityProp`, the mod-2
boundary parity of the box). -/
theorem theorem_1 (γ : Circle → ℝ × ℝ) (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) :
    volume (X γ) ≥ 1/3 :=
  Submission.Configuration.theorem_1_of_OrderSplitHolds γ hγ
    (Work.Drive.orderSplit_chains Work.Drive.umlauf Work.Drive.boxParity γ hγ)

end Submission
