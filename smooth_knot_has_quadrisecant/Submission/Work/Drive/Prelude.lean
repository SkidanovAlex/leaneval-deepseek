import ChallengeDeps
import Submission.TrisecantTransverse
import Submission.TrisecantStructure
import Submission.QuadrisecantChord
import Submission.TrisecantCover
import Submission.QuadrisecantLimit

/-- Shortcut instance (Lean v4.34 port): on v4.34 Mathlib the generic search for
`ContinuousSMul ℝ E` on real normed spaces such as `PiLp 2 _` or iterated products of `Space`
detours through `PolynormableSpace.continuousSMul` and exhausts the heartbeat budget. -/
instance (priority := high) normedSpace_continuousSMul_real {E : Type*} [SeminormedAddCommGroup E]
    [NormedSpace ℝ E] : ContinuousSMul ℝ E :=
  IsBoundedSMul.continuousSMul
