/-
# Sampled `ℓ¹` mass of the high-frequency piece of the off-diagonal decay

`Work.KMTAreas.A4.offPieceHigh` is the analytic heart of the "far window" case of the proof of
`iw-prop`(i) (`Work.KMTAreas.A4.offDecayKMT`): the sampled `ℓ¹` mass of the third kernel piece
`B - B ∗ λ_{-jv}` (with `B = λ_k - η_{≤jj} λ_k`) is at most
`C · 2^{k+jv} · (max (2^{k+jj-1}) 1)^{-N}`.

The estimate is proved as `Work.KMTAreas.A4.offPieceHighClaim` (assembled from the sampled
Young/moment estimates `offSampleConvComp`, `offBDerivBound` and `offBIteratedDeriv2Bound`); this
module only re-exports it under the name used by the rest of the `A4` development.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.offPieceHighClaim

set_option autoImplicit false
set_option maxHeartbeats 1000000

open MeasureTheory
open scoped ENNReal BigOperators

namespace Work.KMTAreas.A4

theorem offPieceHigh (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (k jj jv : ℤ), k ≤ 0 → 0 ≤ jj → 0 ≤ k + jj → ∑' j : ℤ, ‖(Work.KMTAreas.A4.lam k - Work.KMTAreas.A4.mS (Work.KMTAreas.A4.bmp jj) (Work.KMTAreas.A4.lam k) - Work.KMTAreas.A4.cS (Work.KMTAreas.A4.lam k - Work.KMTAreas.A4.mS (Work.KMTAreas.A4.bmp jj) (Work.KMTAreas.A4.lam k)) (Work.KMTAreas.A4.lam (-jv))) (j : ℝ)‖ ≤ C * (2 : ℝ) ^ (k + jv) * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) :=
  offPieceHighClaim N

end Work.KMTAreas.A4
