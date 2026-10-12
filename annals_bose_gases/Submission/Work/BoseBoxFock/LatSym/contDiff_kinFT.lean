import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Submission.Work.SmallBoxBridge.kinFT_analyticAt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.LatSym

/-- `p ↦ Submission.BoseGases.kinFT β p` is smooth for `β` smooth with compact support.

The `p`-convention Fourier transform `kinFT β p = ∫_y e^{−i⟪p,y⟫}β(y) dy` is the restriction of an
*entire* function of `p` (the Bochner-integral power series
`Work.SmallBoxBridge.kinFTSeries`), which is what `Work.SmallBoxBridge.kinFT_analyticAt` proves:
for continuous compactly supported `f` and every `p`, `AnalyticAt ℝ (kinFT f) p`.  Analyticity
everywhere gives smoothness everywhere (`AnalyticAt.contDiffAt`), and smoothness everywhere is
smoothness (`contDiff_iff_contDiffAt`).

Only continuity and compact support of `β` are used for the analyticity; the smoothness hypothesis
`hβ` of the statement supplies `hβ.continuous`. -/
theorem contDiff_kinFT {β : EuclideanSpace ℝ (Fin 3) → ℂ} (hβ : ContDiff ℝ (⊤ : ℕ∞) β)
    (hβc : HasCompactSupport β) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.kinFT β p) := by
  refine contDiff_iff_contDiffAt.mpr (fun p => ?_)
  exact (Work.SmallBoxBridge.kinFT_analyticAt hβ.continuous hβc p).contDiffAt

end Work.BoseBoxFock.LatSym
